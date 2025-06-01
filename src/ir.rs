use std::collections::hash_map::Entry;
use std::collections::{BTreeSet, HashMap, HashSet, VecDeque};
use std::fmt;
use std::ops::Not;
use std::str::FromStr;
use std::sync::Arc;

use chumsky::span::SimpleSpan;
use hex_conservative::DisplayHex;
use itertools::Itertools;

use crate::op::Operation;
use crate::parse::{FunctionName, VariableName};
use crate::util::ShallowClone;
use crate::{Diagnostic, parse, sorting};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program<'src> {
    items: Arc<[Function<'src>]>,
}

impl<'src> Program<'src> {
    /// Accesses the items of the program.
    ///
    /// ## Topological order
    ///
    /// If function `f` is called by function `g`, then `f` appears before `g`.
    /// The first functions that appear don't call anything.
    /// The last function that will appear is the `main` function.
    ///
    /// ## Uniqueness
    ///
    /// Each (used) function appears exactly once in the list.
    ///
    /// ## Unused functions
    ///
    /// Functions that are not (transitively) called by the `main` function
    /// are not included in this list.
    pub fn items(&self) -> &[Function<'src>] {
        &self.items
    }
}

impl ShallowClone for Program<'_> {
    fn shallow_clone(&self) -> Self {
        Self {
            items: self.items.shallow_clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function<'src> {
    name: FunctionName<'src>,
    params: Arc<[VariableName<'src>]>,
    params_source: Arc<[VariableName<'src>]>,
    unused_params: Arc<BTreeSet<usize>>,
    is_unit: bool,
    body: Arc<[Statement<'src>]>,
    return_expr: Option<Arc<Expression<'src>>>,
    span_name: SimpleSpan,
    span_params: Arc<[SimpleSpan]>,
    span_params_total: SimpleSpan,
    span_return: SimpleSpan,
}

impl<'src> Function<'src> {
    /// Accesses the name of the function.
    pub fn name(&self) -> FunctionName<'src> {
        self.name
    }

    /// Accesses the (used) parameters of the function.
    pub fn params(&self) -> &[VariableName<'src>] {
        &self.params
    }

    /// Returns the number of (used) arguments that this function takes as input.
    pub fn n_args(&self) -> usize {
        self.params.len()
    }

    /// Accesses the parameters of the function, according to the source code.
    ///
    /// This list may contain _unused_ parameters.
    #[expect(dead_code)]
    pub fn params_source(&self) -> &[VariableName<'src>] {
        &self.params_source
    }

    /// Returns the number of arguments that this function takes as input,
    /// according to the source code.
    ///
    /// This number may include _unused_ arguments.
    pub fn n_source_args(&self) -> usize {
        self.params_source.len()
    }

    /// Accesses the indices of unused parameters of the function.
    pub fn unused_params(&self) -> &BTreeSet<usize> {
        &self.unused_params
    }

    /// Returns `true` if the function returns no values.
    pub fn is_unit(&self) -> bool {
        self.is_unit
    }

    /// Accesses the statements of the function body.
    pub fn body(&self) -> &[Statement<'src>] {
        &self.body
    }

    /// Accesses the optional return expression in the function body.
    pub fn return_expr(&self) -> Option<&Expression<'src>> {
        self.return_expr.as_ref().map(Arc::as_ref)
    }

    /// Accesses the span of the name of the function.
    #[expect(dead_code)]
    pub fn span_name(&self) -> SimpleSpan {
        self.span_name
    }

    /// Accesses the spans of each parameter of the function.
    #[expect(dead_code)]
    pub fn span_params(&self) -> &[SimpleSpan] {
        &self.span_params
    }

    /// Accesses the span over all parameters of the function.
    pub fn span_params_total(&self) -> SimpleSpan {
        self.span_params_total
    }

    /// Accesses the span of the return type of the function.
    #[expect(dead_code)]
    pub fn span_return(&self) -> SimpleSpan {
        self.span_return
    }
}

impl ShallowClone for Function<'_> {
    fn shallow_clone(&self) -> Self {
        Self {
            name: self.name,
            params: self.params.shallow_clone(),
            params_source: self.params_source.shallow_clone(),
            unused_params: self.unused_params.shallow_clone(),
            is_unit: self.is_unit,
            body: self.body.shallow_clone(),
            return_expr: self.return_expr.shallow_clone(),
            span_name: self.span_name,
            span_params: self.span_params.shallow_clone(),
            span_params_total: self.span_params_total,
            span_return: self.span_return,
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

impl<'src> Statement<'src> {
    /// Converts the type into an [`Assignment`], if possible.
    pub fn as_assignment(&self) -> Option<&Assignment<'src>> {
        match self {
            Self::Assignment(ass) => Some(ass),
            _ => None,
        }
    }

    /// Accesses the expression contained in the statement.
    pub fn expression(&self) -> &Expression<'src> {
        match self {
            Self::Assignment(ass) => ass.expression(),
            Self::UnitExpr(expr) => expr,
        }
    }
}

impl fmt::Display for Statement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Assignment(ass) => write!(f, "{ass};"),
            Self::UnitExpr(expr) => write!(f, "{expr};"),
        }
    }
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
    expression: Expression<'src>,
    span_name: SimpleSpan,
}

impl<'src> Assignment<'src> {
    /// Accesses the variable that is being assigned.
    pub fn name(&self) -> VariableName<'src> {
        self.name
    }

    /// Accesses the expression that produces the assignment value.
    pub fn expression(&self) -> &Expression<'src> {
        &self.expression
    }

    /// Accesses the span of the variable that is being assigned.
    pub fn span_name(&self) -> SimpleSpan {
        self.span_name
    }
}

impl fmt::Display for Assignment<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "let {} = {}", self.name, self.expression)
    }
}

impl ShallowClone for Assignment<'_> {
    fn shallow_clone(&self) -> Self {
        Self {
            name: self.name,
            expression: self.expression.shallow_clone(),
            span_name: self.span_name,
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

    /// Returns a vector of all used variables of the expression.
    pub fn used_variables(&self) -> Box<dyn Iterator<Item = VariableName<'src>> + '_> {
        match self.inner() {
            ExpressionInner::Variable(x) => Box::new(std::iter::once(*x)),
            ExpressionInner::Call(call) => Box::new(call.args().iter().cloned()),
            ExpressionInner::Bytes(..) => Box::new(std::iter::empty()),
        }
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

impl fmt::Display for Expression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.inner() {
            ExpressionInner::Variable(name) => write!(f, "{name}"),
            ExpressionInner::Bytes(bytes) => write!(f, "0x{}", bytes.to_lower_hex_string()),
            ExpressionInner::Call(call) => write!(f, "{call}"),
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
    Custom(Function<'src>),
}

impl<'src> CallName<'src> {
    /// Returns the number of (used) arguments that this function takes as input.
    pub fn n_args(&self) -> usize {
        match self {
            Self::Builtin(operation) => operation.n_args(),
            Self::Custom(function) => function.n_args(),
        }
    }

    /// Returns the number of arguments that this function takes as input,
    /// according to the source code.
    ///
    /// This number may include _unused_ arguments.
    pub fn n_source_args(&self) -> usize {
        match self {
            Self::Builtin(operation) => operation.n_args(),
            Self::Custom(function) => function.n_source_args(),
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

    /// Accesses the (used) arguments of the call.
    pub fn args(&self) -> &[VariableName<'src>] {
        &self.args
    }

    /// Returns `true` if the called function returns no values.
    pub fn is_unit(&self) -> bool {
        self.name.is_unit()
    }
}

impl fmt::Display for Call<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(", self.name)?;
        for (index, arg) in self.args.iter().enumerate() {
            write!(f, "{arg}")?;
            if index < self.args.len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, ")")
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

#[derive(Debug, Clone, Default)]
struct State<'src> {
    /// Maps function names to where they were first defined.
    ///
    /// There is an error if the same function is defined twice.
    function_definition: HashMap<FunctionName<'src>, SimpleSpan>,
    /// Maps functions to where they call other functions.
    ///
    /// This is used for pretty error messages.
    /// ```text
    /// `f` calls `g`: `fn f() { ... g() ... }`
    /// `g` calls `f`: `fn g() { ... f() ... }`
    /// ```
    call_source: HashMap<FunctionName<'src>, Vec<(FunctionName<'src>, SimpleSpan)>>,
    /// Maps function names to their IR representation.
    function_ir: HashMap<FunctionName<'src>, Function<'src>>,
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
    /// List of encountered errors.
    errors: Vec<Diagnostic>,
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
    pub fn enter_function(&mut self, f: &parse::Function<'src>) -> Option<()> {
        debug_assert_eq!(f.params().len(), f.params().len());
        debug_assert!(
            self.variable_definition.is_empty()
                && self.alias_resolver.is_empty()
                && self.alias_source.is_empty(),
            "did you forget to leave the previous function?"
        );

        for i in 0..f.params().len() {
            if let Err(previous_span) = self.define_variable(f.params()[i], f.span_params()[i]) {
                let error = Diagnostic::error(
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
                self.errors.push(error);
                return None;
            }
        }

        Some(())
    }

    /// Leaves the scope of the current function body.
    pub fn leave_function(&mut self) {
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
    pub fn resolve_alias(
        &mut self,
        name: VariableName<'src>,
        span: SimpleSpan,
    ) -> Option<VariableName<'src>> {
        if self.variable_definition.contains_key(name) {
            Some(self.alias_resolver.get(name).copied().unwrap_or(name))
        } else {
            let error = Diagnostic::error(format!("variable `{name}` has not been defined"), span)
                .in_context("cannot find definition", span);
            self.errors.push(error);

            None
        }
    }

    /// Checks if the current function is transitively called by the `called` function.
    ///
    /// ## Panics
    ///
    /// This method panics if the state is currently outside a function body.
    pub fn check_recursive_call(
        &mut self,
        caller: FunctionName<'src>,
        called: FunctionName<'src>,
        call_span: SimpleSpan,
    ) -> Option<()> {
        #[derive(Debug)]
        enum Task<'src> {
            Explore((FunctionName<'src>, SimpleSpan)),
            Pop,
        }

        fn create_error<'src>(
            mut caller: FunctionName<'src>,
            path: Vec<(FunctionName<'src>, SimpleSpan)>,
        ) -> Diagnostic {
            debug_assert!(!path.is_empty());
            let mut error = Diagnostic::error("recursive call detected", path[0].1);

            for (called, span) in path {
                error = error.in_context(format!("`{}` calls `{}`", caller, called), span);
                caller = called;
            }

            error.with_note(
                "Each function can only call functions of a strictly lower tier than itself.\n\
                 Functions of the lowest tier don't call any other function.",
            )
        }

        let origin = caller;
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
                        self.errors.push(create_error(origin, path));
                        return None;
                    }
                }
                Task::Pop => {
                    debug_assert!(!path.is_empty());
                    path.pop();
                }
            }
        }
        debug_assert_eq!(path.len(), 1);

        Some(())
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
    pub fn analyze(from: &parse::Program<'src>) -> (Option<Self>, Vec<Diagnostic>) {
        let mut state = State::default();

        // Build call graph
        // Enforce stratified program
        for function in from.items() {
            if Function::update_call_graph(function, &mut state).is_none() {
                return (None, state.errors);
            }
        }

        // Enforce definition of all called functions
        for (name, span) in state.call_source.values().flat_map(|x| x.iter().copied()) {
            if !state.function_definition.contains_key(name) {
                let error =
                    Diagnostic::error(format!("function `{}` has not been defined", name), span)
                        .in_context("cannot find definition", span);
                state.errors.push(error);
                return (None, state.errors);
            }
        }

        // Enforce existence of `main`
        if !state.function_definition.contains_key("main") {
            let error = Diagnostic::error(
                "the `main` function is missing from the program",
                from.span(),
            )
            .with_note("every program needs to have a `main` function");
            state.errors.push(error);
            return (None, state.errors);
        }
        state.call_source.entry("main").or_default();

        // Filter out unused functions
        let used_functions: HashSet<FunctionName> = state.called_by_main();
        for f in from
            .items()
            .iter()
            .filter(|f| !used_functions.contains(f.name()))
        {
            let span = f.span_name();
            let error = Diagnostic::warning("function is never used", span)
                .in_context2(format!("`{}` is never called", f.name()), span);
            state.errors.push(error);
        }

        // Topologically sort (used) functions
        // TODO: Split `State` to allow extraction of `call_source`?
        debug_assert!(state.call_source.contains_key("main"));
        let call_relation: HashMap<FunctionName, HashSet<FunctionName>> =
            std::mem::take(&mut state.call_source)
                .into_iter()
                .filter(|(name, _)| used_functions.contains(name))
                .map(|(name, called)| (name, called.into_iter().map(|x| x.0).collect()))
                .collect();
        let function_order: Vec<&parse::Function> = {
            let rev_function_order = sorting::topological_sort(&call_relation);
            debug_assert_eq!(
                rev_function_order.len(),
                used_functions.len(),
                "function order should contain all used functions"
            );
            debug_assert_eq!(
                rev_function_order.iter().duplicates().next(),
                None,
                "function order should not contain duplicates"
            );
            let mut functions: HashMap<FunctionName, &parse::Function> =
                from.items().iter().map(|f| (f.name(), f)).collect();
            rev_function_order
                .into_iter()
                .rev()
                .map(|name| functions.remove(name).unwrap())
                .collect()
        };

        // Construct IR of function bodies
        let items: Arc<[Function]> = match function_order
            .iter()
            .map(|f| Function::analyze(f, &mut state))
            .collect::<Option<_>>()
        {
            Some(items) => items,
            None => return (None, state.errors),
        };

        let program = Self { items };
        (Some(program), state.errors)
    }
}

impl<'src> Function<'src> {
    fn update_call_graph(from: &parse::Function<'src>, state: &mut State<'src>) -> Option<()> {
        if let Some(already_defined) = state.function_definition.get(from.name()).copied() {
            let error = Diagnostic::error(
                format!("function `{}` is defined multiple times", from.name()),
                from.span_name(),
            )
            .in_context(
                format!("first definition of `{}`", from.name()),
                already_defined,
            )
            .in_context(
                format!("`{}` redefined here", from.name()),
                from.span_name(),
            );
            state.errors.push(error);
            return None;
        }
        state
            .function_definition
            .insert(from.name(), from.span_name());

        let caller = from.name();
        for expr in from.expressions() {
            if let parse::ExpressionInner::Call(call) = expr.inner() {
                if let parse::CallName::Custom(called) = call.name() {
                    state
                        .call_source
                        .entry(caller)
                        .or_default()
                        .push((called, call.span_total()));
                    state.check_recursive_call(caller, called, call.span_total())?;
                }
            }
        }

        Some(())
    }
}

impl<'src> Function<'src> {
    fn analyze(from: &parse::Function<'src>, state: &mut State<'src>) -> Option<Self> {
        state.enter_function(from)?;

        if !from.is_unit() && from.name() == "main" {
            let error = Diagnostic::error("mismatched types", from.span_total())
                .in_context(
                    "function `main` is declared to return a value",
                    from.span_return(),
                )
                .with_note("the `main` function can never return a value");
            state.errors.push(error);
            return None;
        }

        let body: Vec<Option<Statement>> = from
            .body()
            .iter()
            .map(|stmt| Statement::analyze(stmt, state))
            .collect::<Option<_>>()?;
        let body: Vec<Statement> = body.into_iter().flatten().collect();
        let return_expr = match from.return_expr() {
            Some(expr) => Some(Expression::analyze(expr, state).map(Arc::new)?),
            None => None,
        };

        // Type-check function body
        let body_is_unit = match &return_expr {
            Some(expr) => expr.is_unit(),
            None => true,
        };
        if from.is_unit() && !body_is_unit {
            let error = Diagnostic::error("mismatched types", from.span_total())
                .in_context(
                    format!("function `{}` is declared to return nothing", from.name()),
                    from.span_return(),
                )
                .in_context(
                    format!("the last line of `{}` returns a value", from.name()),
                    from.span_return_expr(),
                );
            state.errors.push(error);
            return None;
        }
        if !from.is_unit() && body_is_unit {
            let error = Diagnostic::error("mismatched types", from.span_total())
                .in_context(
                    format!("function `{}` is declared to return a value", from.name()),
                    from.span_return(),
                )
                .in_context(
                    format!("the last line of `{}` returns nothing", from.name()),
                    from.span_return_expr(),
                );
            state.errors.push(error);
            return None;
        }

        let uses_variables: HashMap<&Statement, Vec<VariableName>> = body
            .iter()
            .map(|stmt| (stmt, stmt.expression().used_variables().collect()))
            .collect();
        let defined_in: HashMap<VariableName, &Statement> = body
            .iter()
            .filter_map(|stmt| stmt.as_assignment().map(|ass| (ass.name(), stmt)))
            .collect();

        // Unit expressions depend on assignments (or on parameters).
        // Assignments depend on other assignments (or on parameters).
        // Nothing ever depends on a unit expression.
        let mut used_variables_new: VecDeque<VariableName> = body
            .iter()
            .filter(|stmt| matches!(stmt, Statement::UnitExpr(..)))
            .filter_map(|stmt| uses_variables.get(stmt))
            .flat_map(|s| s.iter())
            .copied()
            .chain(return_expr.iter().flat_map(|expr| expr.used_variables()))
            .collect();
        let mut used_variables: HashSet<VariableName> = HashSet::new();
        while let Some(x) = used_variables_new.pop_front() {
            used_variables.insert(x);
            if let Some(stmt) = defined_in.get(&x) {
                if let Some(variables) = uses_variables.get(stmt) {
                    used_variables_new.extend(variables.iter());
                }
            }
        }

        // Filter out unused parameters
        let mut unused_params = BTreeSet::new();
        for i in 0..from.params().len() {
            if used_variables.contains(from.params()[i]) {
                continue;
            }
            let span = from.span_params()[i];
            let error = Diagnostic::warning("parameter is never used", span)
                .in_context2(format!("`{}` is never used", from.params()[i]), span);
            state.errors.push(error);
            unused_params.insert(i);
        }
        let params = from
            .params()
            .iter()
            .copied()
            .filter(|name| used_variables.contains(name))
            .collect();

        // Filter out unused statements,
        // which are always assignments that define unused variables
        for ass in body.iter().filter_map(|stmt| {
            stmt.as_assignment()
                .filter(|ass| !used_variables.contains(ass.name()))
        }) {
            let span = ass.span_name();
            let error = Diagnostic::warning("assigned variable is never used", span)
                .in_context2(format!("`{}` is never used", ass.name()), span);
            state.errors.push(error);
        }
        let body: Arc<[Statement]> = body
            .into_iter()
            .filter(|stmt| match stmt {
                Statement::UnitExpr(..) => true,
                Statement::Assignment(ass) => used_variables.contains(ass.name()),
            })
            .collect();

        state.leave_function();

        let function = Function {
            name: from.name(),
            params,
            params_source: from.params().shallow_clone(),
            unused_params: Arc::new(unused_params),
            is_unit: from.is_unit(),
            body,
            return_expr,
            span_name: from.span_name(),
            span_params: from.span_params().shallow_clone(),
            span_params_total: from.span_params_total(),
            span_return: from.span_return(),
        };
        debug_assert!(
            !state.function_ir.contains_key(from.name()),
            "functions should be topologically sorted"
        );
        state
            .function_ir
            .insert(from.name(), function.shallow_clone());

        Some(function)
    }
}

impl<'src> Statement<'src> {
    /// ## Returns
    ///
    /// - `Some(Some(x))` if the statement was successfully constructed.
    /// - `Some(None)` if the statement was inlined. The `state` implicitly carries this information.
    /// - `None` if there was an error in the parse tree. The `state` implicitly carries the error.
    fn analyze(from: &parse::Statement<'src>, state: &mut State<'src>) -> Option<Option<Self>> {
        match from {
            parse::Statement::Assignment(ass) => {
                Assignment::analyze(ass, state).map(|ass| ass.map(Self::Assignment))
            }
            parse::Statement::UnitExpr(parse_expr) => {
                let expr = Expression::analyze(parse_expr, state)?;
                if !expr.is_unit {
                    let mut error = Diagnostic::error(
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

                    state.errors.push(error);
                    return None;
                }

                Some(Some(Self::UnitExpr(expr)))
            }
        }
    }
}

impl<'src> Assignment<'src> {
    /// ## Returns
    ///
    /// - `Some(Some(x))` if the assignment was successfully constructed.
    /// - `Some(None)` if the assignment was inlined. The `state` implicitly carries this information.
    /// - `None` if there was an error in the parse tree. The `state` implicitly carries the error.
    fn analyze(from: &parse::Assignment<'src>, state: &mut State<'src>) -> Option<Option<Self>> {
        if let Err(previous_span) = state.define_variable(from.name(), from.span_name()) {
            let error = Diagnostic::error(
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
            state.errors.push(error);
            return None;
        }

        // Inline variable alias
        if let parse::ExpressionInner::Variable(parent) = from.expression().inner() {
            state.define_variable_alias(from.name(), parent, from.span_total());
            return Some(None);
        }

        let expr = Expression::analyze(from.expression(), state)?;
        if expr.is_unit {
            let mut error = Diagnostic::error(
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

            state.errors.push(error);
            return None;
        }

        Some(Some(Self {
            name: from.name(),
            expression: expr,
            span_name: from.span_name(),
        }))
    }
}

impl<'src> Expression<'src> {
    fn analyze(from: &parse::Expression<'src>, state: &mut State<'src>) -> Option<Self> {
        match from.inner() {
            parse::ExpressionInner::Variable(name) => {
                let resolved = state.resolve_alias(name, from.span())?;
                Some(Self {
                    inner: ExpressionInner::Variable(resolved),
                    is_unit: false,
                })
            }
            parse::ExpressionInner::Bytes(bytes) => Some(Self {
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
    fn analyze(from: &parse::Call<'src>, state: &mut State<'src>) -> Option<Self> {
        // Get the name and the return type of the called function
        let name = match from.name() {
            parse::CallName::Builtin(name) => match Operation::from_str(name) {
                Ok(opcode) => CallName::Builtin(opcode),
                Err(_) => {
                    let error = Diagnostic::error("unexpected operation", from.span_name())
                        .in_context(
                            format!("`{}` is not in the list of known operations", from.name()),
                            from.span_name(),
                        );
                    state.errors.push(error);

                    return None;
                }
            },
            parse::CallName::Custom(name) => {
                let function = state
                    .function_ir
                    .get(name)
                    .expect("all functions should be defined at this point");
                CallName::Custom(function.shallow_clone())
            }
        };

        // Check that given number of arguments matches declared number of parameters
        if from.args().len() != name.n_source_args() {
            let mut error = Diagnostic::error(
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

            state.errors.push(error);
            return None;
        }

        // Check that all arguments have been defined
        debug_assert_eq!(from.args().len(), from.span_args().len());
        let args: Vec<VariableName> = (0..from.args().len())
            .map(|i| state.resolve_alias(from.args()[i], from.span_args()[i]))
            .collect::<Option<_>>()?;

        // Check that no argument appears twice (counterintuitive limitation of current compiler)
        let mut arg_definition: HashMap<VariableName, SimpleSpan> = HashMap::new();
        for (i, arg) in args.iter().enumerate() {
            if let Some(&previous_span) = arg_definition.get(arg) {
                let mut error = Diagnostic::error(
                    format!("argument `{}` cannot appear twice", arg),
                    from.span_args()[i],
                )
                .in_context(format!("first appearance of `{}`", arg), previous_span)
                .in_context(
                    format!("duplicate appearance of `{}`", arg),
                    from.span_args()[i],
                );

                let mut name = &from.args()[i];
                while let Some((parent, span)) = state.alias_source.get(name) {
                    error =
                        error.in_context2(format!("`{}` is aliased to `{}`", name, parent), *span);
                    name = parent;
                }
                error =
                    error.with_note("unique arguments are a limitation of the current compiler");
                state.errors.push(error);

                return None;
            }

            arg_definition.insert(arg, from.span_args()[i]);
        }
        debug_assert_eq!(args.len(), name.n_source_args());

        // Filter out unused arguments
        let args: Arc<[VariableName]> = match &name {
            CallName::Builtin(..) => Arc::from(args),
            CallName::Custom(function) => args
                .into_iter()
                .enumerate()
                .filter_map(|(index, name)| {
                    function
                        .unused_params()
                        .contains(&index)
                        .not()
                        .then_some(name)
                })
                .collect(),
        };

        Some(Self { name, args })
    }
}
