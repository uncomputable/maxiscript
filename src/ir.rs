use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::str::FromStr;
use std::sync::Arc;

use chumsky::span::SimpleSpan;

use crate::op::Operation;
use crate::parse::{FunctionName, VariableName};
use crate::util::ShallowClone;
use crate::{parse, sorting};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program<'src> {
    items: Arc<[Function<'src>]>,
    function_index: Arc<HashMap<FunctionName<'src>, Function<'src>>>,
}

impl<'src> Program<'src> {
    /// Accesses the items of the program.
    ///
    /// ## Topological order
    ///
    /// If function `g` calls function `f`, then `f` appears before `g`.
    /// The first functions that appear don't call anything.
    /// The last function that will appear is the `main` function.
    ///
    /// ## Unused functions
    ///
    /// Functions that are not (transitively) called by the `main` function
    /// are not included in this list.
    pub fn items(&self) -> &[Function<'src>] {
        &self.items
    }

    /// Gets the function of the given `name`, if it exists.
    pub fn get_function(&self, name: FunctionName<'src>) -> Option<&Function<'src>> {
        self.function_index.get(name)
    }

    /// Accesses the main function of the program.
    pub fn main_function(&self) -> &Function {
        self.items
            .iter()
            .find(|function| function.name() == "main")
            .expect("main function should exist")
    }
}

impl ShallowClone for Program<'_> {
    fn shallow_clone(&self) -> Self {
        Self {
            items: self.items.shallow_clone(),
            function_index: self.function_index.shallow_clone(),
        }
    }
}

/// Declaration of a function.
///
/// This is basically a function without its body.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Declaration<'src> {
    name: FunctionName<'src>,
    params: Arc<[VariableName<'src>]>,
    is_unit: bool,
    span_name: SimpleSpan,
    span_params_total: SimpleSpan,
    span_return: SimpleSpan,
}

impl<'src> Declaration<'src> {
    /// Accesses the name of the function.
    pub fn name(&self) -> FunctionName<'src> {
        self.name
    }

    /// Accesses the parameters of the function.
    pub fn params(&self) -> &[VariableName<'src>] {
        &self.params
    }

    /// Returns the number of arguments that this function takes as input.
    pub fn n_args(&self) -> usize {
        self.params.len()
    }

    /// Returns `true` if the function returns no values.
    pub fn is_unit(&self) -> bool {
        self.is_unit
    }

    /// Accesses the span of the name of the function.
    pub fn span_name(&self) -> SimpleSpan {
        self.span_name
    }

    /// Accesses the span over all parameters of the function.
    pub fn span_params_total(&self) -> SimpleSpan {
        self.span_params_total
    }

    /// Accesses the span of the return type of the function.
    pub fn span_return(&self) -> SimpleSpan {
        self.span_return
    }
}

impl ShallowClone for Declaration<'_> {
    fn shallow_clone(&self) -> Self {
        Self {
            name: self.name,
            params: self.params.shallow_clone(),
            is_unit: self.is_unit,
            span_name: self.span_name,
            span_params_total: self.span_params_total,
            span_return: self.span_return,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function<'src> {
    declaration: Declaration<'src>,
    body: Arc<[Statement<'src>]>,
    final_expr: Option<Arc<Expression<'src>>>,
}

impl<'src> Function<'src> {
    /// Accesses the name of the function.
    pub fn name(&self) -> FunctionName<'src> {
        self.declaration.name()
    }

    /// Accesses the parameters of the function.
    pub fn params(&self) -> &[VariableName<'src>] {
        self.declaration.params()
    }

    /// Accesses the statements of the function body.
    pub fn body(&self) -> &[Statement<'src>] {
        &self.body
    }

    /// Accesses the optional final expression in the function body, which produces the return value.
    pub fn final_expr(&self) -> Option<&Expression<'src>> {
        self.final_expr.as_ref().map(Arc::as_ref)
    }

    /// Returns the number of arguments that this function takes as input.
    pub fn n_args(&self) -> usize {
        self.declaration.n_args()
    }

    /// Returns `true` if the function returns no values.
    pub fn is_unit(&self) -> bool {
        self.declaration.is_unit
    }
}

impl ShallowClone for Function<'_> {
    fn shallow_clone(&self) -> Self {
        Self {
            declaration: self.declaration.shallow_clone(),
            body: self.body.shallow_clone(),
            final_expr: self.final_expr.shallow_clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Statement<'src> {
    /// Assignment of a variable.
    Assignment(Assignment<'src>),
    /// Unit expression, i.e., an expression that returns no value.
    UnitExpr(Expression<'src>),
}

impl ShallowClone for Statement<'_> {
    fn shallow_clone(&self) -> Self {
        match self {
            Self::Assignment(ass) => Self::Assignment(ass.shallow_clone()),
            Self::UnitExpr(expr) => Self::UnitExpr(expr.shallow_clone()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Assignment<'src> {
    name: VariableName<'src>,
    expression: Option<Expression<'src>>,
}

impl<'src> Assignment<'src> {
    /// Accesses the variable that is being assigned.
    pub fn name(&self) -> VariableName<'src> {
        self.name
    }

    /// Accesses the expression that produces the assignment value.
    ///
    /// Returns `None` if the assignment was a variable alias that was inlined.
    pub fn expression(&self) -> Option<&Expression<'src>> {
        self.expression.as_ref()
    }
}

impl ShallowClone for Assignment<'_> {
    fn shallow_clone(&self) -> Self {
        Self {
            name: self.name,
            expression: self.expression.shallow_clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Expression<'src> {
    inner: ExpressionInner<'src>,
    is_unit: bool,
}

impl<'src> Expression<'src> {
    /// Accesses the inner expression.
    pub fn inner(&self) -> &ExpressionInner<'src> {
        &self.inner
    }

    /// Returns `true` if the expression returns no values.
    pub fn is_unit(&self) -> bool {
        self.is_unit
    }
}

impl ShallowClone for Expression<'_> {
    fn shallow_clone(&self) -> Self {
        Self {
            inner: self.inner.shallow_clone(),
            is_unit: self.is_unit,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ExpressionInner<'src> {
    /// Return the value of a variable.
    Variable(VariableName<'src>),
    /// Return constant bytes.
    Bytes(Arc<[u8]>),
    /// Return the output of a function call.
    Call(Call<'src>),
}

impl ShallowClone for ExpressionInner<'_> {
    fn shallow_clone(&self) -> Self {
        match self {
            Self::Variable(name) => Self::Variable(name),
            Self::Bytes(bytes) => Self::Bytes(bytes.shallow_clone()),
            Self::Call(call) => Self::Call(call.shallow_clone()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CallName<'src> {
    Builtin(Operation),
    Custom(Declaration<'src>),
}

#[allow(clippy::needless_lifetimes)]
impl<'src> CallName<'src> {
    /// Returns the number of arguments that this function takes as input.
    pub fn n_args(&self) -> usize {
        match self {
            Self::Builtin(operation) => operation.n_args(),
            Self::Custom(function) => function.n_args(),
        }
    }

    /// Returns `true` if the called function returns no values.
    pub fn is_unit(&self) -> bool {
        match self {
            Self::Builtin(operation) => operation.is_unit(),
            Self::Custom(function) => function.is_unit(),
        }
    }
}

impl ShallowClone for CallName<'_> {
    fn shallow_clone(&self) -> Self {
        match self {
            Self::Builtin(operation) => Self::Builtin(*operation),
            Self::Custom(function) => Self::Custom(function.shallow_clone()),
        }
    }
}

impl fmt::Display for CallName<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Builtin(operation) => write!(f, "op::{operation}"),
            Self::Custom(function) => write!(f, "{}", function.name()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Call<'src> {
    name: CallName<'src>,
    args: Arc<[VariableName<'src>]>,
}

impl<'src> Call<'src> {
    /// Accesses the name of the called function.
    pub fn name(&self) -> &CallName<'src> {
        &self.name
    }

    /// Accesses the arguments of the call.
    pub fn args(&self) -> &[VariableName<'src>] {
        &self.args
    }

    /// Returns `true` if the called function returns no values.
    pub fn is_unit(&self) -> bool {
        self.name.is_unit()
    }
}

impl ShallowClone for Call<'_> {
    fn shallow_clone(&self) -> Self {
        Self {
            name: self.name.shallow_clone(),
            args: self.args.shallow_clone(),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Error {
    top: Context,
    contexts: Vec<Context>,
    contexts2: Vec<Context>,
    note: Option<String>,
}

impl Error {
    pub fn new<Str: ToString>(message: Str, span: SimpleSpan) -> Self {
        Self {
            top: Context {
                message: message.to_string(),
                span,
            },
            contexts: Vec::new(),
            contexts2: Vec::new(),
            note: None,
        }
    }

    pub fn in_context<Str: ToString>(mut self, message: Str, span: SimpleSpan) -> Self {
        self.contexts.push(Context {
            message: message.to_string(),
            span,
        });
        Self {
            top: self.top,
            contexts: self.contexts,
            contexts2: self.contexts2,
            note: self.note,
        }
    }

    pub fn in_context2<Str: ToString>(mut self, message: Str, span: SimpleSpan) -> Self {
        self.contexts2.push(Context {
            message: message.to_string(),
            span,
        });
        Self {
            top: self.top,
            contexts: self.contexts,
            contexts2: self.contexts2,
            note: self.note,
        }
    }

    pub fn with_note<Str: ToString>(self, message: Str) -> Self {
        Self {
            top: self.top,
            contexts: self.contexts,
            contexts2: self.contexts2,
            note: Some(message.to_string()),
        }
    }

    pub fn top(&self) -> &Context {
        &self.top
    }

    pub fn contexts(&self) -> &[Context] {
        &self.contexts
    }

    pub fn contexts2(&self) -> &[Context] {
        &self.contexts2
    }

    pub fn note(&self) -> Option<&String> {
        self.note.as_ref()
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Context {
    message: String,
    span: SimpleSpan,
}

impl Context {
    pub fn message(&self) -> &str {
        &self.message
    }

    pub fn span(&self) -> SimpleSpan {
        self.span
    }
}

#[derive(Debug, Clone, Default)]
struct State<'src> {
    /// The name of the current function.
    ///
    /// This value is `None` when the state is operating outside a function body.
    current_function: Option<FunctionName<'src>>,
    /// Maps function names to their function declaration.
    ///
    /// The IR is constructed in two phases:
    ///
    /// 1) The declarations of all functions are collected.
    /// 2) The body of each function is analyzed, with reference to function declarations.
    ///
    /// The two-phase designs allows functions to be used before they are defined.
    function_declaration: HashMap<FunctionName<'src>, Declaration<'src>>,
    /// Maps function names to their finalized IR form.
    function_definition: HashMap<FunctionName<'src>, Function<'src>>,
    /// Maps functions to where they call other functions.
    ///
    /// This is used for pretty error messages.
    /// ```text
    /// `f` calls `g`: `fn f() { ... g() ... }`
    /// `g` calls `f`: `fn g() { ... f() ... }`
    /// ```
    call_source: HashMap<FunctionName<'src>, Vec<(FunctionName<'src>, SimpleSpan)>>,
    /// Maps variables to the span where they were first defined.
    ///
    /// There is an error if the same variable is defined twice.
    variable_definition: HashMap<VariableName<'src>, SimpleSpan>,
    /// Maps variables to their equivalent parent variable.
    ///
    /// All equivalent variables point to the same parent.
    alias_resolver: HashMap<VariableName<'src>, VariableName<'src>>,
    /// Maps variables to their direct alias in the source code.
    ///
    /// This is used for pretty error messages.
    /// ```text
    /// `x` is aliased to `y`: `let x = y;`
    /// `y` is aliased to `z`: `let y = z;`
    /// ```
    alias_source: HashMap<VariableName<'src>, (VariableName<'src>, SimpleSpan)>,
}

impl<'src> State<'src> {
    /// Enters the scope of the function body.
    ///
    /// ## Panics
    ///
    /// This method panics if the state is currently inside another function body.
    /// Before calling this function, the state must leave the previous function body
    /// via [`State::leave_function`].
    /// Nested function definitions are not supported.
    pub fn enter_function(&mut self, f: &parse::Function<'src>) -> Result<(), Error> {
        debug_assert_eq!(f.params().len(), f.params().len());
        debug_assert!(
            self.current_function.is_none()
                && self.variable_definition.is_empty()
                && self.alias_resolver.is_empty()
                && self.alias_source.is_empty(),
            "did you forget to leave the previous function?"
        );

        self.current_function = Some(f.name());

        for i in 0..f.params().len() {
            if let Err(previous_span) = self.define_variable(f.params()[i], f.span_params()[i]) {
                let error = Error::new(
                    format!("parameter `{}` cannot appear twice", f.params()[i]),
                    f.span_params()[i],
                )
                .in_context(
                    format!("first appearance of `{}`", f.params()[i]),
                    previous_span,
                )
                .in_context(
                    format!("duplicate appearance of `{}`", f.params()[i]),
                    f.span_params()[i],
                );
                return Err(error);
            }
        }

        Ok(())
    }

    /// Leaves the scope of the current function body.
    pub fn leave_function(&mut self) {
        self.current_function = None;
        self.variable_definition.clear();
        self.alias_resolver.clear();
        self.alias_source.clear();
    }

    /// Defines the variable of the given `name` at the given `span`.
    ///
    /// Returns `Err(previous_span)` if the name has already been defined at `previous_span`.
    pub fn define_variable(
        &mut self,
        name: VariableName<'src>,
        span: SimpleSpan,
    ) -> Result<(), SimpleSpan> {
        match self.variable_definition.entry(name) {
            Entry::Occupied(entry) => Err(*entry.get()),
            Entry::Vacant(entry) => {
                entry.insert(span);
                Ok(())
            }
        }
    }

    /// Aliases the given variable `name` as the given `parent` name.
    ///
    /// ## Panics
    ///
    /// This method panics when the same `name` is aliased twice.
    pub fn define_variable_alias(
        &mut self,
        name: VariableName<'src>,
        parent: VariableName<'src>,
        span: SimpleSpan,
    ) {
        debug_assert!(
            !self.alias_resolver.contains_key(name) && !self.alias_source.contains_key(name),
            "variable should not be defined twice"
        );
        let transitive_parent = self.alias_resolver.get(parent).copied().unwrap_or(parent);
        self.alias_resolver.insert(name, transitive_parent);
        self.alias_source.insert(name, (parent, span));
    }

    /// Returns the canonical form of the given variable `name`.
    ///
    /// Variable names that are aliases form an equivalence class.
    /// All names of the same class have the same canonical form.
    ///
    /// This method returns an error if the variable has not been defined.
    pub fn resolve_alias(&self, name: VariableName<'src>) -> Result<VariableName<'src>, ()> {
        if self.variable_definition.contains_key(name) {
            Ok(self.alias_resolver.get(name).copied().unwrap_or(name))
        } else {
            Err(())
        }
    }

    /// Checks if the current function is transitively called by the `called` function.
    ///
    /// ## Panics
    ///
    /// This method panics if the state is currently outside a function body.
    pub fn check_recursive_call(
        &self,
        called: FunctionName<'src>,
        call_span: SimpleSpan,
    ) -> Result<(), Error> {
        #[derive(Debug)]
        enum Task<'src> {
            Explore((FunctionName<'src>, SimpleSpan)),
            Pop,
        }

        fn create_error<'src>(
            current: FunctionName<'src>,
            path: Vec<(FunctionName<'src>, SimpleSpan)>,
        ) -> Error {
            debug_assert!(!path.is_empty());
            let mut error = Error::new("recursive call detected", path[0].1);
            let mut caller = current;

            for (called, span) in path {
                error = error.in_context(format!("`{}` calls `{}`", caller, called), span);
                caller = called;
            }

            error.with_note(
                "Each function can only call functions of a strictly lower tier than itself.\n\
                 Functions of the lowest tier don't call any other function.",
            )
        }

        let origin = self
            .current_function
            .expect("should be inside function body");
        let mut stack = vec![Task::Explore((called, call_span))];
        let mut path = vec![];

        while let Some(task) = stack.pop() {
            match task {
                Task::Explore((f, span)) => {
                    if let Some(called_by_f) = self.call_source.get(f) {
                        stack.reserve(called_by_f.len() + 1);
                        stack.push(Task::Pop);
                        stack.extend(called_by_f.iter().copied().map(Task::Explore));
                    }
                    path.push((f, span));

                    if f == origin {
                        return Err(create_error(origin, path));
                    }
                }
                Task::Pop => {
                    debug_assert!(!path.is_empty());
                    path.pop();
                }
            }
        }
        debug_assert_eq!(path.len(), 1);

        Ok(())
    }

    /// Returns the set of functions that are transitively called by the main function.
    ///
    /// Functions outside of this list are not used and will not be included in the target code.
    pub fn called_by_main(&self) -> HashSet<FunctionName<'src>> {
        let mut visited = HashSet::new();
        let mut stack = vec!["main"];

        while let Some(f) = stack.pop() {
            visited.insert(f);
            if let Some(called) = self.call_source.get(f) {
                stack.extend(called.iter().map(|x| x.0));
            }
        }

        visited
    }
}

impl<'src> Program<'src> {
    pub fn analyze(from: &parse::Program<'src>) -> Result<Self, Error> {
        let mut state = State::default();

        // Step 1: Populate state with all declared functions
        for function in from.items() {
            Declaration::analyze(function, &mut state)?;
        }

        if !state.function_declaration.contains_key("main") {
            return Err(Error::new(
                "the `main` function is missing from the program",
                from.span(),
            )
            .with_note("every program needs to have a `main` function"));
        }

        // Step 2: Construct IR of function bodies
        let mut items: HashMap<FunctionName, Function> = from
            .items()
            .iter()
            .map(|f| Function::analyze(f, &mut state).map(|f| (f.name(), f)))
            .collect::<Result<_, _>>()?;

        // Step 3: Topologically sort functions that are called by main
        // TODO: Warn about unused functions. Requires non-error warnings
        let used_functions = state.called_by_main();
        let call_relation: HashMap<FunctionName, HashSet<FunctionName>> = state
            .call_source
            .into_iter()
            .filter(|(name, _)| used_functions.contains(name))
            .map(|(name, called)| (name, called.into_iter().map(|x| x.0).collect()))
            .collect();
        let rev_sorted = sorting::topological_sort(&call_relation);
        let items: Arc<[Function]> = rev_sorted
            .into_iter()
            .rev()
            .map(|name| items.remove(name).expect("function should be analyzed"))
            .collect();

        Ok(Self {
            items,
            function_index: Arc::new(state.function_definition),
        })
    }
}

impl<'src> Declaration<'src> {
    fn analyze(from: &parse::Function<'src>, state: &mut State<'src>) -> Result<(), Error> {
        if let Some(already_defined) = state.function_declaration.get(from.name()) {
            let error = Error::new(
                format!("function `{}` is defined multiple times", from.name()),
                from.span_name(),
            )
            .in_context(
                format!("first definition of `{}`", from.name()),
                already_defined.span_name,
            )
            .in_context(
                format!("`{}` redefined here", from.name()),
                from.span_name(),
            );
            return Err(error);
        }
        if !from.is_unit() && from.name() == "main" {
            let error = Error::new("mismatched types", from.span_total())
                .in_context(
                    "function `main` is declared to return a value",
                    from.span_return(),
                )
                .with_note("the `main` function can never return a value");
            return Err(error);
        }

        let function = Declaration {
            name: from.name(),
            params: from.params().shallow_clone(),
            is_unit: from.is_unit(),
            span_name: from.span_name(),
            span_params_total: from.span_params_total(),
            span_return: from.span_return(),
        };
        debug_assert!(!state.function_declaration.contains_key(from.name()));
        state.function_declaration.insert(from.name(), function);

        Ok(())
    }
}

// TODO: Detect unused parameters
// Warn user and effectively remove parameter from function signature
impl<'src> Function<'src> {
    fn analyze(from: &parse::Function<'src>, state: &mut State<'src>) -> Result<Self, Error> {
        state.enter_function(from)?;

        let body: Arc<[Statement]> = from
            .body()
            .iter()
            .map(|stmt| Statement::analyze(stmt, state))
            .collect::<Result<_, _>>()?;
        let final_expr = from
            .final_expr()
            .map(|expr| Expression::analyze(expr, state).map(Arc::new))
            .transpose()?;
        let body_return_span = from
            .final_expr()
            .map(|expr| expr.span())
            .unwrap_or_else(|| {
                from.body()
                    .last()
                    .map(|stmt| stmt.span())
                    .unwrap_or_else(|| from.span_body())
            });

        let body_is_unit = match &final_expr {
            Some(expr) => expr.is_unit(),
            None => true,
        };

        if from.is_unit() && !body_is_unit {
            let error = Error::new("mismatched types", from.span_total())
                .in_context(
                    format!("function `{}` is declared to return nothing", from.name()),
                    from.span_return(),
                )
                .in_context(
                    format!("the last line of `{}` returns a value", from.name()),
                    body_return_span,
                );
            return Err(error);
        }
        if !from.is_unit() && body_is_unit {
            let error = Error::new("mismatched types", from.span_total())
                .in_context(
                    format!("function `{}` is declared to return a value", from.name()),
                    from.span_return(),
                )
                .in_context(
                    format!("the last line of `{}` returns nothing", from.name()),
                    body_return_span,
                );
            return Err(error);
        }

        state.leave_function();

        let declaration = state
            .function_declaration
            .get(from.name())
            .expect("all function should be declared at this point")
            .shallow_clone();
        let function = Function {
            declaration,
            body,
            final_expr,
        };
        debug_assert!(
            !state.function_definition.contains_key(from.name()),
            "we should visit each function only once"
        );
        state
            .function_definition
            .insert(from.name(), function.shallow_clone());
        Ok(function)
    }
}

impl<'src> Statement<'src> {
    fn analyze(from: &parse::Statement<'src>, state: &mut State<'src>) -> Result<Self, Error> {
        match from {
            parse::Statement::Assignment(ass) => {
                Assignment::analyze(ass, state).map(Self::Assignment)
            }
            parse::Statement::UnitExpr(parse_expr) => {
                let expr = Expression::analyze(parse_expr, state)?;
                if !expr.is_unit {
                    let mut error = Error::new(
                        "expected expression that nothing, but got expression that returns something".to_string(),
                        parse_expr.span(),
                    ).in_context("outside a let statement, an expression is not allowed to return any output", parse_expr.span());

                    if let ExpressionInner::Call(call) = expr.inner() {
                        error = match call.name() {
                            CallName::Builtin(..) => error.with_note(format!(
                                "operation `{}` is defined to return a value",
                                call.name
                            )),
                            CallName::Custom(function) => error.in_context2(
                                format!("function `{}` is defined to return a value", call.name),
                                function.span_return,
                            ),
                        };
                    }

                    return Err(error);
                }
                Ok(Self::UnitExpr(expr))
            }
        }
    }
}

impl<'src> Assignment<'src> {
    fn analyze(from: &parse::Assignment<'src>, state: &mut State<'src>) -> Result<Self, Error> {
        if let Err(previous_span) = state.define_variable(from.name(), from.span_name()) {
            let error = Error::new(
                format!("variable `{}` cannot be defined twice", from.name()),
                from.span_name(),
            )
            .in_context(
                format!("first definition of `{}`", from.name()),
                previous_span,
            )
            .in_context(
                format!("`{}` redefined here", from.name()),
                from.span_name(),
            );
            return Err(error);
        }

        // Inline variable alias
        if let parse::ExpressionInner::Variable(parent) = from.expression().inner() {
            state.define_variable_alias(from.name(), parent, from.span_total());
            return Ok(Self {
                name: from.name(),
                expression: None,
            });
        }

        let expr = Expression::analyze(from.expression(), state)?;
        if expr.is_unit {
            let mut error = Error::new(
                "expected expression that returns something, but got expression that returns nothing",
                from.expression().span(),
            ).in_context("this expression should return something", from.expression().span())
                .in_context2(format!("the let statement binds `{}` to the output of an expression", from.name()), from.span_name());

            if let ExpressionInner::Call(call) = expr.inner() {
                error = match call.name() {
                    CallName::Builtin(..) => error.with_note(format!(
                        "operation `{}` is defined to return nothing",
                        call.name
                    )),
                    CallName::Custom(function) => error.in_context2(
                        format!("function `{}` is defined to return nothing", call.name),
                        function.span_return,
                    ),
                };
            }

            return Err(error);
        }
        Ok(Self {
            name: from.name(),
            expression: Some(expr),
        })
    }
}

impl<'src> Expression<'src> {
    fn analyze(from: &parse::Expression<'src>, state: &mut State<'src>) -> Result<Self, Error> {
        match from.inner() {
            parse::ExpressionInner::Variable(name) => state
                .resolve_alias(name)
                .map(|resolved| Self {
                    inner: ExpressionInner::Variable(resolved),
                    is_unit: false,
                })
                .map_err(|_| {
                    Error::new(
                        format!("variable `{}` has not been defined", name),
                        from.span(),
                    )
                    .in_context("cannot find definition", from.span())
                }),
            parse::ExpressionInner::Bytes(bytes) => Ok(Self {
                inner: ExpressionInner::Bytes(bytes.shallow_clone()),
                is_unit: false,
            }),
            parse::ExpressionInner::Call(call) => Call::analyze(call, state).map(|call| Self {
                is_unit: call.is_unit(),
                inner: ExpressionInner::Call(call),
            }),
        }
    }
}

impl<'src> Call<'src> {
    fn analyze(from: &parse::Call<'src>, state: &mut State<'src>) -> Result<Self, Error> {
        // Get the name and the return type of the called function
        let name = match from.name() {
            parse::CallName::Builtin(name) => match Operation::from_str(name) {
                Ok(opcode) => CallName::Builtin(opcode),
                Err(_) => {
                    return Err(
                        Error::new("unexpected operation", from.span_name()).in_context(
                            format!("`{}` is not in the list of known operations", from.name()),
                            from.span_name(),
                        ),
                    );
                }
            },
            parse::CallName::Custom(name) => match state.function_declaration.get(name) {
                Some(function) => CallName::Custom(function.shallow_clone()),
                None => {
                    return Err(Error::new(
                        format!("function `{}` has not been defined", name),
                        from.span_name(),
                    )
                    .in_context("cannot find definition", from.span_name()));
                }
            },
        };

        // Update call graph and check for recursive calls
        if let CallName::Custom(function) = &name {
            let caller = state
                .current_function
                .expect("should be inside function body");
            let called = function.name();
            state
                .call_source
                .entry(caller)
                .or_default()
                .push((called, from.span_total()));
            state.check_recursive_call(called, from.span_total())?;
        }

        // Check that actual number of arguments matches declared number of parameters
        if from.args().len() != name.n_args() {
            let mut error = Error::new(
                format!(
                    "this function takes {} arguments, but {} arguments were supplied",
                    from.args().len(),
                    name.n_args()
                ),
                from.span_args_total(),
            )
            .in_context(
                format!("{} arguments were supplied", from.args().len()),
                from.span_args_total(),
            );
            match &name {
                CallName::Builtin(operation) => {
                    error = error.with_note(format!(
                        "operation `{operation}` is defined to take {} arguments",
                        name.n_args()
                    ));
                }
                CallName::Custom(function) => {
                    error = error.in_context2(
                        format!(
                            "function `{}` is declared to take {} arguments",
                            function.name(),
                            name.n_args()
                        ),
                        function.span_params_total(),
                    );
                }
            }
            return Err(error);
        }

        // Check that all arguments have been defined
        debug_assert_eq!(from.args().len(), from.span_args().len());
        let args: Arc<[VariableName]> = (0..from.args().len())
            .map(|i| match state.resolve_alias(from.args()[i]) {
                Ok(resolved) => Ok(resolved),
                Err(_) => {
                    let error = Error::new(
                        format!("variable `{}` has not been defined", from.args()[i]),
                        from.span_args()[i],
                    )
                    .in_context("cannot find definition", from.span_args()[i]);
                    Err(error)
                }
            })
            .collect::<Result<_, _>>()?;

        // Check that no argument appears twice (counterintuitive limitation of current compiler)
        let mut arg_definition: HashMap<VariableName, SimpleSpan> = HashMap::new();
        for i in 0..args.len() {
            if let Some(&previous_span) = arg_definition.get(args[i]) {
                let mut error = Error::new(
                    format!("argument `{}` cannot appear twice", args[i]),
                    from.span_args()[i],
                )
                .in_context(format!("first appearance of `{}`", args[i]), previous_span)
                .in_context(
                    format!("duplicate appearance of `{}`", args[i]),
                    from.span_args()[i],
                );

                let mut name = &from.args()[i];
                while let Some((parent, span)) = state.alias_source.get(name) {
                    error =
                        error.in_context2(format!("`{}` is aliased to `{}`", name, parent), *span);
                    name = parent;
                }

                return Err(
                    error.with_note("unique arguments are a limitation of the current compiler")
                );
            }

            arg_definition.insert(args[i], from.span_args()[i]);
        }

        Ok(Self { name, args })
    }
}
