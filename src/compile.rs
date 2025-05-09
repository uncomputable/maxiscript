use std::collections::HashMap;

use bitcoin::script::PushBytes;
use itertools::Itertools;
use log::{Level, debug, log_enabled};

use crate::opcodes::{StackOp, find_shortest_transformation};
use crate::optimize;
use crate::parse::{Expression, Program, Statement, VariableName};

#[derive(Debug, Clone, Default)]
struct Stack<'src> {
    variables: Vec<VariableName<'src>>,
    // aliases: HashMap<VariableName<'src>, Vec<VariableName<'src>>>,
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

    // pub fn push_alias(&mut self, original: VariableName<'src>, alias: VariableName<'src>)

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
            panic!("Script larger than u32::MAX opcode long")
        }
    }
}

fn get_statement_dependencies<'a, 'src>(
    program: &'a Program<'src>,
) -> HashMap<&'a Statement<'src>, Vec<&'a Statement<'src>>> {
    let mut var_defined_in = HashMap::new();
    let mut depends_on = HashMap::new();

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
            }
            Expression::Call(call) => {
                let stmts = call
                    .args()
                    .iter()
                    .map(|var| *var_defined_in.get(var).expect("var defined"))
                    .collect();
                depends_on.insert(statement, stmts);
            }
            Expression::Bytes(_) => {
                depends_on.insert(statement, vec![]);
            }
        }
    }

    depends_on
}

pub fn compile(program: Program) -> Result<bitcoin::ScriptBuf, String> {
    let depends_on = get_statement_dependencies(&program);

    let mut best_script = bitcoin::ScriptBuf::new();
    let mut best_len = usize::MAX;

    for ordered_statements in optimize::all_topological_orders(&depends_on) {
        let mut script = bitcoin::ScriptBuf::new();
        let mut stack = Stack::default();

        for statement in ordered_statements.iter() {
            match statement {
                Statement::Assignment(ass) => {
                    compile_expr(ass.expression(), &mut script, &mut stack)?;
                    stack.push_variable(ass.assignee())?;
                }
                Statement::UnitExpr(expr) => match expr {
                    Expression::Variable(..) | Expression::Bytes(..) => {
                        return Err("Expression is not unit".to_string());
                    }
                    Expression::Call(call) if !call.name().is_unit() => {
                        return Err("Expression is not unit".to_string());
                    }
                    _ => compile_expr(expr, &mut script, &mut stack)?,
                },
            }
        }

        if script.len() < best_len {
            best_len = script.len();
            best_script = script;

            if log_enabled!(Level::Debug) {
                debug!(
                    "Found better statement order:\n{}",
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
) -> Result<(), String> {
    match expr {
        Expression::Variable(..) => unimplemented!("variable aliases"),
        Expression::Bytes(bytes) => script.push_slice(bytes),
        Expression::Call(call) => {
            assert!(
                call.name().n_rets() <= 1,
                "No support for operations that push multiple outputs"
            );

            match find_shortest_transformation(stack.variables(), call.args()) {
                None => return Err("Variable was not defined".to_string()),
                Some(transformation_script) => {
                    let mut pushed_args = 0;

                    for op in transformation_script.iter() {
                        let opcode = match op {
                            StackOp::Dup => bitcoin::opcodes::all::OP_DUP,
                            StackOp::_2Dup => bitcoin::opcodes::all::OP_2DUP,
                            StackOp::_3Dup => bitcoin::opcodes::all::OP_3DUP,
                            StackOp::Over => bitcoin::opcodes::all::OP_OVER,
                            StackOp::_2Over => bitcoin::opcodes::all::OP_2OVER,
                            StackOp::Tuck => bitcoin::opcodes::all::OP_TUCK,
                            StackOp::Pick(name) => {
                                script.push_slice(
                                    stack
                                        .position(name, pushed_args)
                                        .expect("variable should be defined"),
                                );
                                bitcoin::opcodes::all::OP_PICK
                            }
                            StackOp::Swap => bitcoin::opcodes::all::OP_SWAP,
                            StackOp::_2Swap => bitcoin::opcodes::all::OP_2SWAP,
                            StackOp::Rot => bitcoin::opcodes::all::OP_ROT,
                            StackOp::_2Rot => bitcoin::opcodes::all::OP_2ROT,
                            StackOp::Roll(name) => {
                                // TODO: What if OP_ROLL uses variables inside target?
                                script.push_slice(
                                    stack
                                        .position(name, pushed_args)
                                        .expect("variable should be defined"),
                                );
                                bitcoin::opcodes::all::OP_ROLL
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

    Ok(())
}
