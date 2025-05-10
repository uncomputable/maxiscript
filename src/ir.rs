use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::str::FromStr;
use std::sync::Arc;

use bitcoin::opcodes;
use chumsky::span::SimpleSpan;

use crate::parse;
use crate::parse::VariableName;
use crate::util::ShallowClone;

/// A program is a sequence of statements.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Program<'src> {
    statements: Arc<[Statement<'src>]>,
}

impl<'src> Program<'src> {
    /// Accesses the statements of the program.
    pub fn statements(&self) -> &Arc<[Statement<'src>]> {
        &self.statements
    }
}

impl ShallowClone for Program<'_> {
    fn shallow_clone(&self) -> Self {
        Self {
            statements: Arc::clone(&self.statements),
        }
    }
}

/// A statement is either an assignment or a unit expression.
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
    assignee: VariableName<'src>,
    expression: Option<Expression<'src>>,
}

impl<'src> Assignment<'src> {
    /// Gets the variable that is being assigned.
    pub fn assignee(&self) -> &VariableName<'src> {
        &self.assignee
    }

    /// Gets the expression that produces the assignment value.
    ///
    /// Returns `None` if the assignment was a variable alias that was inlined.
    pub fn expression(&self) -> Option<&Expression<'src>> {
        self.expression.as_ref()
    }
}

impl ShallowClone for Assignment<'_> {
    fn shallow_clone(&self) -> Self {
        Self {
            assignee: self.assignee,
            expression: self.expression.shallow_clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Expression<'src> {
    inner: ExpressionInner<'src>,
    n_rets: usize,
}

impl<'src> Expression<'src> {
    pub fn inner(&self) -> &ExpressionInner<'src> {
        &self.inner
    }

    pub fn n_rets(&self) -> usize {
        self.n_rets
    }
}

impl ShallowClone for Expression<'_> {
    fn shallow_clone(&self) -> Self {
        Self {
            inner: self.inner.shallow_clone(),
            n_rets: self.n_rets,
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
            Self::Bytes(bytes) => Self::Bytes(Arc::clone(bytes)),
            Self::Call(call) => Self::Call(call.shallow_clone()),
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

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Call<'src> {
    name: Builtin,
    args: Arc<[VariableName<'src>]>,
}

impl Call<'_> {
    /// Gets the name of the called function.
    pub fn name(&self) -> &Builtin {
        &self.name
    }

    /// Gets the arguments of the function call.
    pub fn args(&self) -> &[VariableName] {
        &self.args
    }
}

impl ShallowClone for Call<'_> {
    fn shallow_clone(&self) -> Self {
        Self {
            name: self.name,
            args: Arc::clone(&self.args),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Error {
    top: Context,
    contexts: Vec<Context>,
}

impl Error {
    pub fn new<Str: ToString>(message: Str, span: SimpleSpan) -> Self {
        Self {
            top: Context {
                message: message.to_string(),
                span,
            },
            contexts: Vec::new(),
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
        }
    }

    pub fn top(&self) -> &Context {
        &self.top
    }

    pub fn contexts(&self) -> &[Context] {
        &self.contexts
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
    /// Maps variables to the span where they were first defined.
    ///
    /// There is an error if the same variable is defined twice.
    first_definition: HashMap<VariableName<'src>, SimpleSpan>,
    /// Maps variables to their equivalent parent variable.
    ///
    /// All equivalent variables point to the same parent.
    alias_resolver: HashMap<VariableName<'src>, VariableName<'src>>,
}

impl<'src> State<'src> {
    /// Defines the variable of the given `name` at the given `span`.
    ///
    /// Returns `Err(previous_span)` if the name has already been defined at `previous_span`.
    pub fn define_variable(
        &mut self,
        name: VariableName<'src>,
        span: SimpleSpan,
    ) -> Result<(), SimpleSpan> {
        match self.first_definition.entry(name) {
            Entry::Occupied(entry) => Err(*entry.get()),
            Entry::Vacant(entry) => {
                entry.insert(span);
                Ok(())
            }
        }
    }

    pub fn define_alias(&mut self, aliased: VariableName<'src>, parent: VariableName<'src>) {
        debug_assert!(
            !self.alias_resolver.contains_key(aliased),
            "variable should not be defined twice"
        );
        let transitive_parent = self.alias_resolver.get(parent).copied().unwrap_or(parent);
        self.alias_resolver.insert(aliased, transitive_parent);
    }

    pub fn resolve_alias(&self, aliased: VariableName<'src>) -> VariableName<'src> {
        self.alias_resolver.get(aliased).copied().unwrap_or(aliased)
    }
}

impl<'src> Program<'src> {
    pub fn analyze(from: &parse::Program<'src>) -> Result<Self, Error> {
        let mut state = State::default();
        let statements: Arc<[Statement]> = from
            .statements()
            .iter()
            .map(|stmt| Statement::analyze(stmt, &mut state))
            .collect::<Result<_, _>>()?;
        Ok(Self { statements })
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
                if expr.n_rets != 0 {
                    debug_assert_eq!(expr.n_rets, 1);
                    return Err(Error::new(
                        "expected expression that returns 0 values, but got expression that returns 1 value".to_string(),
                        parse_expr.span(),
                    ).in_context("outside a let statement, the expression is not allowed to return output", from.span()));
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
                format!("cannot define `{}` twice", from.name()),
                from.span_name(),
            );
            return Err(error);
        }

        // Inline variable alias
        if let parse::ExpressionInner::Variable(parent) = from.expression().inner() {
            state.define_alias(from.name(), parent);
            return Ok(Self {
                assignee: from.name(),
                expression: None,
            });
        }

        let expr = Expression::analyze(from.expression(), state)?;
        if expr.n_rets != 1 {
            debug_assert_eq!(expr.n_rets, 0);
            return Err(Error::new(
                "expected expression that returns 1 value, but got expression that returns 0 values",
                from.expression().span(),
            ).in_context(format!("the let statement binds `{}` to the output of the expression", from.name()), from.expression().span()));
        }
        Ok(Self {
            assignee: from.name(),
            expression: Some(expr),
        })
    }
}

impl<'src> Expression<'src> {
    fn analyze(from: &parse::Expression<'src>, state: &mut State<'src>) -> Result<Self, Error> {
        match from.inner() {
            parse::ExpressionInner::Variable(name) => Ok(Self {
                inner: ExpressionInner::Variable(state.resolve_alias(name)),
                n_rets: 1,
            }),
            parse::ExpressionInner::Bytes(bytes) => Ok(Self {
                inner: ExpressionInner::Bytes(bytes.shallow_clone()),
                n_rets: 1,
            }),
            parse::ExpressionInner::Call(call) => Call::analyze(call, state).map(|call| Self {
                n_rets: call.name.n_rets(),
                inner: ExpressionInner::Call(call),
            }),
        }
    }
}

impl<'src> Call<'src> {
    fn analyze(from: &parse::Call<'src>, state: &mut State<'src>) -> Result<Self, Error> {
        let name = Builtin::from_str(from.name()).map_err(|_| {
            Error::new("unexpected opcode", from.span_name()).in_context(
                format!("`{}` is not in the list of known opcodes", from.name()),
                from.span_name(),
            )
        })?;
        Ok(Self {
            name,
            args: from
                .args()
                .iter()
                .map(|name| state.resolve_alias(name))
                .collect(),
        })
    }
}
