use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fmt;
use std::str::FromStr;
use std::sync::Arc;

use bitcoin::opcodes;
use chumsky::span::SimpleSpan;

use crate::parse;
use crate::parse::{FunctionName, VariableName};
use crate::util::ShallowClone;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Program<'src> {
    items: Arc<[Function<'src>]>,
}

impl<'src> Program<'src> {
    /// Accesses the items of the program.
    pub fn items(&self) -> &[Function<'src>] {
        &self.items
    }

    /// Accesses the main function of the program.
    pub fn main_function(&self) -> &Function {
        self.items
            .iter()
            .find(|function| function.name == "main")
            .expect("main function should exist")
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
    body: Arc<[Statement<'src>]>,
    final_expr: Option<Arc<Expression<'src>>>,
    is_unit: bool,
    span_name: SimpleSpan,
    span_return: SimpleSpan,
}

impl<'src> Function<'src> {
    /// Accesses the name of the function.
    pub fn name(&self) -> FunctionName<'src> {
        self.name
    }

    /// Accesses the parameters of the function.
    pub fn params(&self) -> &[VariableName<'src>] {
        &self.params
    }

    /// Accesses the statements of the function body.
    pub fn body(&self) -> &[Statement<'src>] {
        &self.body
    }

    /// Accesses the optional final expression in the function body, which produces the return value.
    pub fn final_expr(&self) -> Option<&Expression<'src>> {
        self.final_expr.as_ref().map(Arc::as_ref)
    }

    /// Returns `true` if the function returns no values.
    pub fn is_unit(&self) -> bool {
        self.is_unit
    }

    /// Accesses the span of the name of the function.
    pub fn span_name(&self) -> SimpleSpan {
        self.span_name
    }

    /// Accesses the span of the return type of the function.
    pub fn span_return(&self) -> SimpleSpan {
        self.span_return
    }
}

impl ShallowClone for Function<'_> {
    fn shallow_clone(&self) -> Self {
        Self {
            name: self.name,
            params: self.params.shallow_clone(),
            body: self.body.shallow_clone(),
            final_expr: self.final_expr.shallow_clone(),
            is_unit: self.is_unit,
            span_name: self.span_name,
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
    pub fn name(&self) -> &VariableName<'src> {
        &self.name
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

/// A Bitcoin Script operation that is a builtin function.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Operation(opcodes::Opcode);

impl std::hash::Hash for Operation {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u8(self.0.to_u8());
    }
}

impl FromStr for Operation {
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

impl Operation {
    /// Returns `true` if the operation returns no values.
    pub const fn is_unit(self) -> bool {
        match self.0 {
            opcodes::all::OP_ADD => false,
            opcodes::all::OP_EQUALVERIFY => true,
            _ => true,
        }
    }

    /// Returns the corresponding [`bitcoin::Opcode`].
    pub const fn serialize(self) -> bitcoin::Opcode {
        self.0
    }
}

impl fmt::Display for Operation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            opcodes::all::OP_ADD => f.write_str("add"),
            opcodes::all::OP_EQUALVERIFY => f.write_str("equal_verify"),
            _ => f.write_str(""),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum CallName<'src> {
    Builtin(Operation),
    Custom(Function<'src>),
}

#[allow(clippy::needless_lifetimes)]
impl<'src> CallName<'src> {
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
    /// Maps function names to their finalized IR form.
    ///
    /// There is an error if the same function is defined twice.
    function_definition: HashMap<FunctionName<'src>, Function<'src>>,
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
    /// Enters the scope of the function body, registering all function parameters.
    ///
    /// ## Panics
    ///
    /// This method panics if there are defined variables.
    /// The set of defined variables must be cleared via [`State::leave_function`]
    /// before analyzing the next function.
    /// Nested function definitions are not supported.
    pub fn enter_function(
        &mut self,
        params: &[VariableName<'src>],
        span_params: &[SimpleSpan],
    ) -> Result<(), Error> {
        debug_assert_eq!(params.len(), span_params.len());
        debug_assert!(
            self.variable_definition.is_empty()
                && self.alias_resolver.is_empty()
                && self.alias_source.is_empty(),
            "did you forget to leave the previous function?"
        );

        for i in 0..params.len() {
            if let Err(previous_span) = self.define_variable(params[i], span_params[i]) {
                let error = Error::new(
                    format!("parameter `{}` cannot appear twice", params[i]),
                    span_params[i],
                )
                .in_context(
                    format!("first appearance of `{}`", params[i]),
                    previous_span,
                )
                .in_context(
                    format!("duplicate appearance of `{}`", params[i]),
                    span_params[i],
                );
                return Err(error);
            }
        }
        Ok(())
    }

    /// Leaves the scope of the current function body, clearing all variable definitions.
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
    pub fn resolve_alias(&self, name: VariableName<'src>) -> Result<VariableName<'src>, ()> {
        if self.variable_definition.contains_key(name) {
            Ok(self.alias_resolver.get(name).copied().unwrap_or(name))
        } else {
            Err(())
        }
    }
}

impl<'src> Program<'src> {
    pub fn analyze(from: &parse::Program<'src>) -> Result<Self, Error> {
        let mut state = State::default();
        let items: Arc<[Function]> = from
            .items()
            .iter()
            .map(|function| Function::analyze(function, &mut state))
            .collect::<Result<_, _>>()?;

        if items.iter().all(|function| function.name() != "main") {
            return Err(Error::new(
                "the `main` function is missing from the program",
                from.span(),
            )
            .with_note("every program needs to have a `main` function"));
        }

        Ok(Self { items })
    }
}

// TODO: Resolve functions that are defined after they are used
impl<'src> Function<'src> {
    fn analyze(from: &parse::Function<'src>, state: &mut State<'src>) -> Result<Self, Error> {
        if let Some(already_defined) = state.function_definition.get(from.name()) {
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

        state.enter_function(from.params(), from.span_params())?;

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

        let function = Function {
            name: from.name(),
            params: from.params().shallow_clone(),
            body,
            final_expr,
            is_unit: from.is_unit(),
            span_name: from.span_name(),
            span_return: from.span_return(),
        };
        debug_assert!(!state.function_definition.contains_key(from.name()));
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
                    ).in_context("outside a let statement, an expression is not allowed to return any output", from.span());

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
            parse::CallName::Custom(name) => match state.function_definition.get(name) {
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
