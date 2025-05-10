use std::collections::HashMap;

use bitcoin::opcodes;
use bitcoin::script::PushBytes;
use log::{Level, debug, log_enabled};

use crate::ir::{Expression, ExpressionInner, Program, Statement};
use crate::opcodes::{self as myopcodes, StackOp};
use crate::optimize;
use crate::parse::VariableName;

#[derive(Debug, Clone, Default)]
struct Stack<'src> {
    variables: Vec<VariableName<'src>>,
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
    pub fn push_variable(&mut self, name: VariableName<'src>) {
        debug_assert!(!self.variables.contains(&name));
        self.variables.push(name);
    }

    pub fn remove_moved_variables(&mut self, to_copy: &[VariableName]) {
        self.variables.retain(|name| to_copy.contains(name));
    }

    pub fn variables(&self) -> &[VariableName<'src>] {
        &self.variables
    }

    pub fn position(&self, name: &VariableName<'src>, pushed_args: usize) -> Position {
        debug_assert!(
            size_of::<u32>() <= size_of::<usize>(),
            "32-bit machine or higher"
        );
        let pos = self
            .variables
            .iter()
            .rev()
            .position(|x| x == name)
            .expect("variable should be defined")
            .saturating_add(pushed_args);
        let [b0, b1, b2, b3, ..] = pos.to_le_bytes();
        if pos <= u8::MAX as usize {
            Position::U8([b0])
        } else if pos <= u16::MAX as usize {
            Position::U16([b0, b1])
        } else if pos <= u32::MAX as usize {
            Position::U32([b0, b1, b2, b3])
        } else {
            unreachable!("Stack size exceeded u32::MAX");
        }
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
                match ass.expression() {
                    None => continue,
                    Some(x) => x,
                }
            }
            Statement::UnitExpr(expr) => expr,
        };
        match expr.inner() {
            ExpressionInner::Variable(x) => {
                let &stmt_x = var_defined_in.get(x).expect("var defined");
                depends_on.insert(statement, vec![stmt_x]);
                uses_variables.insert(statement, vec![x]);
            }
            ExpressionInner::Call(call) => {
                let stmts = call
                    .args()
                    .iter()
                    .map(|var| *var_defined_in.get(var).expect("var defined"))
                    .collect();
                depends_on.insert(statement, stmts);
                uses_variables.insert(statement, call.args().to_vec());
            }
            ExpressionInner::Bytes(_) => {
                depends_on.insert(statement, vec![]);
            }
        }
    }

    Dependencies {
        depends_on,
        uses_variables,
    }
}

pub fn compile(program: Program) -> bitcoin::ScriptBuf {
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
                Statement::Assignment(ass) => {
                    if let Some(expr) = ass.expression() {
                        compile_expr(expr, &mut script, &mut stack, &to_copy);
                        stack.push_variable(ass.assignee());
                    }
                }
                Statement::UnitExpr(expr) => {
                    compile_expr(expr, &mut script, &mut stack, &to_copy);
                }
            }
        }

        if script.len() < best_cost {
            best_cost = script.len();
            best_script = script;

            if log_enabled!(Level::Debug) {
                debug!("Found better statement order (cost {best_cost}):\n")
            }
        }
    }

    best_script
}

fn compile_expr(
    expr: &Expression<'_>,
    script: &mut bitcoin::ScriptBuf,
    stack: &mut Stack,
    to_copy: &[VariableName],
) {
    match expr.inner() {
        ExpressionInner::Variable(..) => {
            unreachable!("variable alias should be inlined")
        }
        ExpressionInner::Bytes(bytes) => {
            let bounded_bytes: &PushBytes = bytes
                .as_ref()
                .try_into()
                .expect("hex should not be too long");
            script.push_slice(bounded_bytes);
        }
        ExpressionInner::Call(call) => {
            match myopcodes::find_shortest_transformation2(stack.variables(), call.args(), to_copy)
            {
                None => unreachable!("variables should be defined"),
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
                                script.push_slice(stack.position(name, pushed_args));
                                opcodes::all::OP_PICK
                            }
                            StackOp::Swap => opcodes::all::OP_SWAP,
                            StackOp::_2Swap => opcodes::all::OP_2SWAP,
                            StackOp::Rot => opcodes::all::OP_ROT,
                            StackOp::_2Rot => opcodes::all::OP_2ROT,
                            StackOp::Roll(name) => {
                                // TODO: What if OP_ROLL uses variables inside target?
                                script.push_slice(stack.position(name, pushed_args));
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

            script.push_opcode(call.name().to_opcode());
        }
    }

    stack.remove_moved_variables(to_copy);
}
