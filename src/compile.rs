use std::collections::HashMap;
use std::str::FromStr;

use bitcoin::opcodes;
use bitcoin::script::PushBytes;
use itertools::Itertools;
use log::{Level, debug, log_enabled};

use crate::opcodes::{self as myopcodes, StackOp};
use crate::optimize;
use crate::parse::{Expression, Program, Statement, VariableName};

#[derive(Debug, Clone, Default)]
struct Stack<'src> {
    variables: Vec<VariableName<'src>>,
    /// Maps variables to their equivalent parent variable.
    ///
    /// All equivalent variables point to the same parent.
    alias_resolver: HashMap<VariableName<'src>, VariableName<'src>>,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
enum Position {
    U8([u8; 1]),
    U16([u8; 2]),
    U32([u8; 4]),
}

impl AsRef<PushBytes> for Position {
    fn as_ref(&self) -> &PushBytes {
        match self {
            Position::U8(n) => n.as_ref(),
            Position::U16(n) => n.as_ref(),
            Position::U32(n) => n.as_ref(),
        }
    }
}

impl<'src> Stack<'src> {
    pub fn push_variable(&mut self, name: VariableName<'src>) -> Result<(), String> {
        if self.variables.contains(&name) {
            return Err(format!("Variable {name} is defined twice"));
        }
        self.variables.push(name);
        Ok(())
    }

    pub fn remove_moved_variables(&mut self, to_copy: &[VariableName]) {
        self.variables.retain(|name| to_copy.contains(name));
        self.alias_resolver
            .retain(|_, parent| to_copy.contains(parent));
    }

    pub fn push_variable_alias(&mut self, aliased: VariableName<'src>, parent: VariableName<'src>) {
        assert!(!self.alias_resolver.contains_key(aliased));

        let transitive_parent = self.alias_resolver.get(parent).copied().unwrap_or(parent);
        self.alias_resolver.insert(aliased, transitive_parent);
    }

    pub fn variables(&self) -> &[VariableName<'src>] {
        &self.variables
    }

    pub fn position(&self, name: &VariableName<'src>, pushed_args: usize) -> Option<Position> {
        debug_assert!(
            size_of::<u32>() <= size_of::<usize>(),
            "32-bit machine or higher"
        );
        let pos = self
            .variables
            .iter()
            .rev()
            .position(|x| x == name)?
            .saturating_add(pushed_args);
        let [b0, b1, b2, b3, ..] = pos.to_le_bytes();
        if pos <= u8::MAX as usize {
            Some(Position::U8([b0]))
        } else if pos <= u16::MAX as usize {
            Some(Position::U16([b0, b1]))
        } else if pos <= u32::MAX as usize {
            Some(Position::U32([b0, b1, b2, b3]))
        } else {
            panic!("Stack size exceeded u32::MAX");
        }
    }
}

/// A Bitcoin Script opcode that is a builtin function in the DSL.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Builtin(opcodes::Opcode);

impl std::hash::Hash for Builtin {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u8(self.0.to_u8());
    }
}

impl FromStr for Builtin {
    type Err = ();

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let ret = match s {
            "add" => Self(opcodes::all::OP_ADD),
            "equal_verify" => Self(opcodes::all::OP_EQUALVERIFY),
            _ => return Err(()),
        };
        Ok(ret)
    }
}

impl Builtin {
    // /// Gets the number of arguments of the opcode.
    // ///
    // /// Arguments are popped from the stack.
    // pub const fn n_args(self) -> usize {
    //     match self.0 {
    //         opcodes::all::OP_ADD => 2,
    //         opcodes::all::OP_EQUALVERIFY => 2,
    //         _ => 0,
    //     }
    // }

    /// Gets the number of return values of the opcode.
    ///
    /// Return values are pushed onto the stack.
    pub const fn n_rets(self) -> usize {
        match self.0 {
            opcodes::all::OP_ADD => 1,
            opcodes::all::OP_EQUALVERIFY => 0,
            _ => 0,
        }
    }

    /// Checks if the opcode is a unit operation.
    ///
    /// Unit operations return nothing.
    pub const fn is_unit(self) -> bool {
        self.n_rets() == 0
    }

    /// Returns the corresponding [`bitcoin::Opcode`].
    pub const fn to_opcode(self) -> bitcoin::Opcode {
        self.0
    }
}

struct Dependencies<'a, 'src> {
    depends_on: HashMap<&'a Statement<'src>, Vec<&'a Statement<'src>>>,
    uses_variables: HashMap<&'a Statement<'src>, Vec<VariableName<'src>>>,
}

fn get_statement_dependencies<'src, 'a: 'src>(
    program: &'a Program<'src>,
) -> Dependencies<'a, 'src> {
    let mut var_defined_in: HashMap<VariableName, &Statement> = HashMap::new();
    let mut depends_on: HashMap<&Statement, Vec<&Statement>> =
        HashMap::with_capacity(program.statements().len());
    let mut uses_variables: HashMap<&Statement, Vec<VariableName>> =
        HashMap::with_capacity(program.statements().len());

    for statement in program.statements().iter() {
        let expr = match statement {
            Statement::Assignment(ass) => {
                var_defined_in.insert(ass.assignee(), statement);
                ass.expression()
            }
            Statement::UnitExpr(expr) => expr,
        };
        match expr {
            Expression::Variable(x) => {
                let &stmt_x = var_defined_in.get(x).expect("var defined");
                depends_on.insert(statement, vec![stmt_x]);
                uses_variables.insert(statement, vec![x]);
            }
            Expression::Call(call) => {
                let stmts = call
                    .args()
                    .iter()
                    .map(|var| *var_defined_in.get(var).expect("var defined"))
                    .collect();
                depends_on.insert(statement, stmts);
                uses_variables.insert(statement, call.args().to_vec());
            }
            Expression::Bytes(_) => {
                depends_on.insert(statement, vec![]);
            }
        }
    }

    Dependencies {
        depends_on,
        uses_variables,
    }
}

pub fn compile(program: Program) -> Result<bitcoin::ScriptBuf, String> {
    let dependencies = get_statement_dependencies(&program);

    let mut best_script = bitcoin::ScriptBuf::new();
    let mut best_cost = usize::MAX;

    for ordered_statements in optimize::all_topological_orders(&dependencies.depends_on) {
        let mut script = bitcoin::ScriptBuf::new();
        let mut stack = Stack::default();

        for i in 0..ordered_statements.len() {
            let statement = ordered_statements[i];
            // TODO: to_copy can be cached
            let to_copy: Vec<VariableName> = ordered_statements[i + 1..]
                .iter()
                .filter_map(|&&stmt| dependencies.uses_variables.get(stmt))
                .flatten()
                .copied()
                .collect();

            match statement {
                Statement::Assignment(ass) => match ass.expression() {
                    Expression::Variable(parent) => {
                        stack.push_variable_alias(ass.assignee(), parent);
                    }
                    _ => {
                        compile_expr(ass.expression(), &mut script, &mut stack, &to_copy)?;
                        stack.push_variable(ass.assignee())?;
                    }
                },
                Statement::UnitExpr(expr) => match expr {
                    Expression::Variable(..) | Expression::Bytes(..) => {
                        return Err("Expression is not unit".to_string());
                    }
                    Expression::Call(call) => {
                        let name = Builtin::from_str(call.name()).expect("unexpected opcode");
                        if !name.is_unit() {
                            return Err("Expression is not unit".to_string());
                        } else {
                            compile_expr(expr, &mut script, &mut stack, &to_copy)?;
                        }
                    }
                },
            }
        }

        if script.len() < best_cost {
            best_cost = script.len();
            best_script = script;

            if log_enabled!(Level::Debug) {
                debug!(
                    "Found better statement order (cost {best_cost}):\n{}",
                    ordered_statements
                        .iter()
                        .map(|stmt| stmt.to_string())
                        .join("\n")
                )
            }
        }
    }

    Ok(best_script)
}

fn compile_expr(
    expr: &Expression<'_>,
    script: &mut bitcoin::ScriptBuf,
    stack: &mut Stack,
    to_copy: &[VariableName],
) -> Result<(), String> {
    match expr {
        Expression::Variable(..) => {
            unreachable!("variable alias should be caught by previous code")
        }
        Expression::Bytes(bytes) => {
            let bounded_bytes: &PushBytes = bytes
                .as_ref()
                .try_into()
                .expect("hex should not be too long");
            script.push_slice(bounded_bytes);
        }
        Expression::Call(call) => {
            // TODO: Check during AST construction
            let name = Builtin::from_str(call.name()).expect("unexpected opcode");
            assert!(
                name.n_rets() <= 1,
                "No support for operations that push multiple outputs"
            );

            match myopcodes::find_shortest_transformation2(stack.variables(), call.args(), to_copy)
            {
                None => return Err("Variable was not defined".to_string()),
                Some(transformation_script) => {
                    let mut pushed_args = 0;

                    for op in transformation_script.iter() {
                        let opcode = match op {
                            StackOp::Dup => opcodes::all::OP_DUP,
                            StackOp::_2Dup => opcodes::all::OP_2DUP,
                            StackOp::_3Dup => opcodes::all::OP_3DUP,
                            StackOp::Over => opcodes::all::OP_OVER,
                            StackOp::_2Over => opcodes::all::OP_2OVER,
                            StackOp::Tuck => opcodes::all::OP_TUCK,
                            StackOp::Pick(name) => {
                                script.push_slice(
                                    stack
                                        .position(name, pushed_args)
                                        .expect("variable should be defined"),
                                );
                                opcodes::all::OP_PICK
                            }
                            StackOp::Swap => opcodes::all::OP_SWAP,
                            StackOp::_2Swap => opcodes::all::OP_2SWAP,
                            StackOp::Rot => opcodes::all::OP_ROT,
                            StackOp::_2Rot => opcodes::all::OP_2ROT,
                            StackOp::Roll(name) => {
                                // TODO: What if OP_ROLL uses variables inside target?
                                script.push_slice(
                                    stack
                                        .position(name, pushed_args)
                                        .expect("variable should be defined"),
                                );
                                opcodes::all::OP_ROLL
                            }
                        };
                        script.push_opcode(opcode);

                        match op {
                            StackOp::Dup | StackOp::Over | StackOp::Tuck | StackOp::Pick(_) => {
                                pushed_args += 1
                            }
                            StackOp::_2Dup | StackOp::_2Over => pushed_args += 2,
                            StackOp::_3Dup => pushed_args += 3,
                            StackOp::Swap
                            | StackOp::_2Swap
                            | StackOp::Rot
                            | StackOp::_2Rot
                            | StackOp::Roll(_) => {}
                        }
                    }
                }
            }

            script.push_opcode(name.to_opcode());
        }
    }

    stack.remove_moved_variables(to_copy);
    Ok(())
}
