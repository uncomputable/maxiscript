use std::collections::{HashMap, HashSet};

use bitcoin::opcodes;
use bitcoin::script::PushBytes;
use log::{Level, debug, log_enabled};

use crate::ir::{CallName, Expression, ExpressionInner, Function, Program, Statement};
use crate::parse::{FunctionName, VariableName};
use crate::sorting;
use crate::stack::{self, StackOp};

/// Position of an item in the stack.
///
/// The position is counted from the stack top.
/// The topmost item has position 0, the second topmost item has position 1, and so on.
///
/// Positions are optimized for size in Bitcoin script.
/// Position 0 fits into 0 bytes,
/// positions 1 to 255 fits into 1 byte, and so on.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
enum Position {
    /// Position 0.
    U0,
    /// Positions `1..=255`.
    U8([u8; 1]),
    /// Positions `256..=65535`.
    U16([u8; 2]),
    /// Positions `65535..=4294967295`.
    U32([u8; 4]),
}

impl AsRef<PushBytes> for Position {
    fn as_ref(&self) -> &PushBytes {
        match self {
            Position::U0 => [].as_ref(),
            Position::U8(n) => n.as_ref(),
            Position::U16(n) => n.as_ref(),
            Position::U32(n) => n.as_ref(),
        }
    }
}

#[derive(Debug, Clone, Default)]
struct Stack<'src> {
    variables: Vec<VariableName<'src>>,
    // function_body: HashMap<FunctionName<'src>, bitcoin::ScriptBuf>,
}

impl<'src> Stack<'src> {
    /// Creates a stack for the body of the given `function`.
    ///
    /// A function body uses the function parameters
    /// and variables defined in the body itself.
    /// Function parameters are on the top of the stack when the function is called.
    ///
    /// Therefore, a function body can be compiled without knowledge of the rest of the stack.
    pub fn for_function(function: &Function<'src>) -> Self {
        Self {
            variables: function.params().to_vec(),
        }
    }

    /// Pushes a single item onto the stack, under the given `name`.
    pub fn push_variable(&mut self, name: VariableName<'src>) {
        debug_assert!(!self.variables.contains(&name));
        self.variables.push(name);
    }

    /// Removes items that have been moved from the stack.
    ///
    /// The slice `to_copy` contains items that will be used later.
    /// By retaining only items from that slice, this effectively removes moved items.
    pub fn remove_moved_variables(&mut self, to_copy: &[VariableName]) {
        self.variables.retain(|name| to_copy.contains(name));
    }

    /// Accesses the current stack.
    pub fn variables(&self) -> &[VariableName<'src>] {
        &self.variables
    }

    /// Returns the position of the given variable `name`  in the stack.
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
        // FIXME: Double check for i32 shenanigans in Bitcoin script!
        if pos == 0 {
            Position::U0
        } else if pos <= u8::MAX as usize {
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

/// Function arguments are assumed to be already on the stack.
/// Therefore, function parameters don't count towards inter-statement dependencies.
fn get_statement_dependencies<'src, 'a: 'src>(function: &'a Function) -> Dependencies<'a, 'src> {
    let params: HashSet<VariableName> = function.params().iter().copied().collect();
    let mut defined_in: HashMap<VariableName, &Statement> = HashMap::new();
    let mut depends_on: HashMap<&Statement, Vec<&Statement>> =
        HashMap::with_capacity(function.body().len());
    let mut depended_on: HashSet<&Statement> = HashSet::new();
    let mut uses_variables: HashMap<&Statement, Vec<VariableName>> =
        HashMap::with_capacity(function.body().len());

    for statement in function.body().iter() {
        let expr = match statement {
            Statement::Assignment(ass) => {
                defined_in.insert(ass.name(), statement);
                ass.expression()
            }
            Statement::UnitExpr(expr) => expr,
        };
        match expr.inner() {
            ExpressionInner::Variable(name) if !params.contains(name) => {
                let &defining_statement = defined_in.get(name).expect("variable should be defined");
                depends_on.insert(statement, vec![defining_statement]);
                depended_on.insert(defining_statement);
                uses_variables.insert(statement, vec![name]);
            }
            ExpressionInner::Call(call) => {
                let stmts: Vec<&Statement> = call
                    .args()
                    .iter()
                    .filter(|&name| !params.contains(name))
                    .map(|name| *defined_in.get(name).expect("variable should be defined"))
                    .collect();
                depended_on.extend(stmts.iter().copied());
                depends_on.insert(statement, stmts);
                uses_variables.insert(statement, call.args().to_vec());
            }
            _ => {
                depends_on.insert(statement, vec![]);
            }
        }
    }

    let useful_statement = |stmt: &Statement| match stmt {
        // Assignments are useful if their defined variable is used
        Statement::Assignment(_) => depended_on.contains(stmt),
        // Unit expressions are always useful (e.g., for witness verification)
        Statement::UnitExpr(_) => true,
    };

    depends_on.retain(|stmt, _| useful_statement(stmt));
    uses_variables.retain(|stmt, _| useful_statement(stmt));

    Dependencies {
        depends_on,
        uses_variables,
    }
}

pub fn compile(program: &Program) -> bitcoin::ScriptBuf {
    let mut compiled_bodies: HashMap<FunctionName, bitcoin::ScriptBuf> = HashMap::new();

    for function in program.items() {
        let body = compile_function_body(function, &compiled_bodies);
        debug_assert!(!compiled_bodies.contains_key(function.name()));
        compiled_bodies.insert(function.name(), body);
    }

    compiled_bodies
        .remove("main")
        .expect("main function should be compiled")
}

// TODO: Drop values (parameters) that are not consumed (ensure hygiene)
pub fn compile_function_body<'src>(
    function: &Function<'src>,
    compiled_bodies: &HashMap<FunctionName<'src>, bitcoin::ScriptBuf>,
) -> bitcoin::ScriptBuf {
    let dependencies = get_statement_dependencies(function);

    let mut best_script = bitcoin::ScriptBuf::new();
    let mut best_cost = usize::MAX;

    for ordered_statements in sorting::all_topological_orders(&dependencies.depends_on) {
        let mut script = bitcoin::ScriptBuf::new();
        let mut stack = Stack::for_function(function);

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
                    compile_expr(
                        ass.expression(),
                        compiled_bodies,
                        &mut script,
                        &mut stack,
                        &to_copy,
                    );
                    stack.push_variable(ass.name());
                }
                Statement::UnitExpr(expr) => {
                    compile_expr(expr, compiled_bodies, &mut script, &mut stack, &to_copy);
                }
            }
        }

        if script.len() < best_cost {
            best_cost = script.len();
            best_script = script;

            if log_enabled!(Level::Debug) {
                debug!(
                    "Function `{}`: found better statement order (cost {best_cost})",
                    function.name()
                );
            }
        }
    }

    best_script
}

fn compile_expr<'src>(
    expr: &Expression<'src>,
    compiled_bodies: &HashMap<FunctionName<'src>, bitcoin::ScriptBuf>,
    script: &mut bitcoin::ScriptBuf,
    stack: &mut Stack<'src>,
    to_copy: &[VariableName<'src>],
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
            // Script to get arguments onto the stack top
            match stack::find_shortest_transformation2(stack.variables(), call.args(), to_copy) {
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

            // Script that computes function body
            match call.name() {
                CallName::Builtin(operation) => {
                    script.push_opcode(operation.serialize());
                }
                CallName::Custom(function) => {
                    let body_script_bytes = compiled_bodies[function.name()].as_bytes();
                    *script = bitcoin::ScriptBuf::from_bytes(
                        script
                            .as_bytes()
                            .iter()
                            .chain(body_script_bytes.iter())
                            .copied()
                            .collect(),
                    );
                }
            }
        }
    }

    stack.remove_moved_variables(to_copy);
}
