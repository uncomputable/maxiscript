use crate::opcodes::{find_shortest_transformation, StackOp};
use crate::parse::{Expression, Program, Statement, VariableName};
use bitcoin::script::PushBytes;

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

pub fn compile(program: Program) -> Result<bitcoin::ScriptBuf, String> {
    let mut script = bitcoin::ScriptBuf::new();
    let mut stack = Stack::default();

    for statement in program.statements().iter() {
        match statement {
            Statement::Assignment(ass) => {
                compile_expr(ass.expression(), &mut script, &mut stack)?;
                stack.push_variable(ass.assignee())?;
            }
            Statement::UnitExpr(expr) => match expr {
                Expression::Variable(..) | Expression::Bytes(..) => {
                    return Err("Expression is not unit".to_string())
                }
                Expression::Call(call) if !call.name().is_unit() => {
                    return Err("Expression is not unit".to_string())
                }
                _ => compile_expr(expr, &mut script, &mut stack)?,
            },
        }
    }

    Ok(script)
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

            match find_shortest_transformation(stack.variables(), call.args_target()) {
                None => return Err("Variable was not defined".to_string()),
                Some(trans_script) => {
                    let mut pushed_args = 0;

                    for op in trans_script.iter() {
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
