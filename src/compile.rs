use std::collections::{HashMap, HashSet};

use bitcoin::{opcodes, script};
use log::{Level, debug, log_enabled};

use crate::ir::{CallName, Expression, ExpressionInner, Function, Program, Statement};
use crate::parse::{FunctionName, VariableName};
use crate::sorting;
use crate::stack::{self, StackOp};

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub struct MyScript(Vec<u8>);

impl MyScript {
    pub fn into_script(self) -> bitcoin::ScriptBuf {
        bitcoin::ScriptBuf::from_bytes(self.0)
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    #[expect(dead_code)]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn append(&mut self, other: Self) {
        self.0.extend(other.0)
    }

    pub fn push_int(&mut self, data: i64) {
        let builder = script::Builder::new().push_int(data);
        self.0.extend(builder.into_bytes());
    }

    pub fn push_bytes<T: AsRef<script::PushBytes>>(&mut self, data: T) {
        let data = data.as_ref();

        // Ensure minimal data pushes
        // https://github.com/bitcoin/bitcoin/blob/4b1d48a6866b24f0ed027334c6de642fc848d083/src/script/script.cpp#L373
        if data.len() == 1 && 1 <= data[0] && data[0] <= 16 {
            self.push_opcode(bitcoin::Opcode::from(0x50 + data[0]));
        } else if data.len() == 1 && data[0] == 0x81 {
            self.push_opcode(opcodes::all::OP_PUSHNUM_NEG1);
        } else {
            let builder = script::Builder::new().push_slice(data);
            self.0.extend(builder.into_bytes());
        }
    }

    pub fn push_opcode(&mut self, data: bitcoin::Opcode) {
        let builder = script::Builder::new().push_opcode(data);
        self.0.extend(builder.into_bytes());
    }
}

#[derive(Debug, Clone, Default)]
struct Stack<'src> {
    variables: Vec<VariableName<'src>>,
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
    pub fn position(&self, name: &VariableName<'src>, pushed_args: usize) -> i64 {
        debug_assert!(
            size_of::<u32>() <= size_of::<usize>(),
            "32-bit machine or higher"
        );
        self.variables
            .iter()
            .rev()
            .position(|x| x == name)
            .expect("variable should be defined")
            .saturating_add(pushed_args)
            .try_into()
            .expect("position should be within interval [0, i64::MAX]")
    }
}

// TODO: Move into IR?
struct Dependencies<'a, 'src> {
    depends_on: HashMap<&'a Statement<'src>, Vec<&'a Statement<'src>>>,
}

/// Function arguments are assumed to be already on the stack.
/// Therefore, function parameters don't count towards inter-statement dependencies.
fn get_statement_dependencies<'src, 'a: 'src>(f: &'a Function) -> Dependencies<'a, 'src> {
    let params: HashSet<VariableName> = f.params().iter().copied().collect();
    let mut defined_in: HashMap<VariableName, &Statement> = HashMap::new();
    let mut depends_on: HashMap<&Statement, Vec<&Statement>> =
        HashMap::with_capacity(f.body().len());

    for statement in f.body().iter() {
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
            }
            ExpressionInner::Call(call) => {
                let stmts: Vec<&Statement> = call
                    .args()
                    .iter()
                    .filter(|&name| !params.contains(name))
                    .map(|name| *defined_in.get(name).expect("variable should be defined"))
                    .collect();
                depends_on.insert(statement, stmts);
            }
            _ => {
                depends_on.insert(statement, vec![]);
            }
        }
    }

    Dependencies { depends_on }
}

pub fn compile(program: &Program) -> bitcoin::ScriptBuf {
    let mut compiled_bodies: HashMap<FunctionName, MyScript> = HashMap::new();

    for function in program.items() {
        let body = compile_function_body(function, &compiled_bodies);
        debug_assert!(!compiled_bodies.contains_key(function.name()));
        compiled_bodies.insert(function.name(), body);
    }

    compiled_bodies
        .remove("main")
        .expect("main function should be compiled")
        .into_script()
}

pub fn compile_function_body<'src>(
    function: &Function<'src>,
    compiled_bodies: &HashMap<FunctionName<'src>, MyScript>,
) -> MyScript {
    let dependencies = get_statement_dependencies(function);

    let mut best_script = MyScript::default();
    let mut best_cost = usize::MAX;

    for ordered_statements in sorting::all_topological_orders(&dependencies.depends_on) {
        let mut script = MyScript::default();
        let mut stack = Stack::for_function(function);

        for i in 0..ordered_statements.len() {
            let statement = ordered_statements[i];
            // TODO: to_copy can be cached
            let to_copy: Vec<VariableName> = ordered_statements[i + 1..]
                .iter()
                .map(|stmt| stmt.expression().used_variables())
                .chain(
                    function
                        .return_expr()
                        .iter()
                        .map(|expr| expr.used_variables()),
                )
                .flatten()
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
        if let Some(expr) = function.return_expr() {
            let to_copy = &[];
            compile_expr(expr, compiled_bodies, &mut script, &mut stack, to_copy);
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
    compiled_bodies: &HashMap<FunctionName<'src>, MyScript>,
    script: &mut MyScript,
    stack: &mut Stack<'src>,
    to_copy: &[VariableName<'src>],
) {
    match expr.inner() {
        ExpressionInner::Variable(x) => {
            push_args_script(script, stack, &[*x], to_copy);
        }
        ExpressionInner::Bytes(bytes) => {
            let bounded_bytes: &script::PushBytes = bytes
                .as_ref()
                .try_into()
                .expect("hex should not be too long");
            script.push_bytes(bounded_bytes);
        }
        ExpressionInner::Call(call) => {
            push_args_script(script, stack, call.args(), to_copy);
            match call.name() {
                CallName::Builtin(operation) => {
                    script.push_opcode(operation.serialize());
                }
                CallName::Custom(function) => {
                    let body_script_bytes = compiled_bodies[function.name()].clone();
                    script.append(body_script_bytes);
                }
            }
        }
    }

    stack.remove_moved_variables(to_copy);
}

fn push_args_script<'src>(
    script: &mut MyScript,
    stack: &mut Stack<'src>,
    args: &[VariableName<'src>],
    to_copy: &[VariableName<'src>],
) {
    match stack::find_shortest_transformation2(stack.variables(), args, to_copy) {
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
                        script.push_int(stack.position(name, pushed_args));
                        opcodes::all::OP_PICK
                    }
                    StackOp::Swap => opcodes::all::OP_SWAP,
                    StackOp::_2Swap => opcodes::all::OP_2SWAP,
                    StackOp::Rot => opcodes::all::OP_ROT,
                    StackOp::_2Rot => opcodes::all::OP_2ROT,
                    StackOp::Roll(name) => {
                        // TODO: What if OP_ROLL uses variables inside target?
                        script.push_int(stack.position(name, pushed_args));
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
}
