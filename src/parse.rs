use std::fmt;
use std::sync::Arc;

use chumsky::input::ValueInput;
use chumsky::prelude::{
    IterParser, Rich, SimpleSpan, any, end, just, one_of, recursive, skip_then_retry_until,
};
use chumsky::{Parser, extra, select, text};
use hex_conservative::{DisplayHex, FromHex};

use crate::util::ShallowClone;

pub type Spanned<T> = (T, SimpleSpan);

#[derive(Clone, Debug, PartialEq)]
pub enum Token<'src> {
    Hex(&'src str),
    Opcode(&'src str),
    Ctrl(char),
    Identifier(&'src str),
    Fn,
    Let,
    ReturnArrow,
}

impl fmt::Display for Token<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Hex(x) => write!(f, "{x}"),
            Self::Opcode(x) => write!(f, "op::{x}"),
            Self::Ctrl(c) => write!(f, "{c}"),
            Self::Identifier(x) => write!(f, "{x}"),
            Self::Fn => write!(f, "fn"),
            Self::Let => write!(f, "let"),
            Self::ReturnArrow => write!(f, "-> _"),
        }
    }
}

pub fn lexer<'src>()
-> impl Parser<'src, &'src str, Vec<Spanned<Token<'src>>>, extra::Err<Rich<'src, char>>> {
    let hex = just("0x")
        .ignore_then(
            any()
                .filter(char::is_ascii_hexdigit)
                .repeated()
                .exactly(2)
                .repeated()
                .at_least(1)
                .to_slice(),
        )
        .map(Token::Hex);

    let opcode = just("op::")
        .ignore_then(text::ascii::ident().to_slice())
        .map(Token::Opcode);

    let ctrl = one_of("()[]{};,=").map(Token::Ctrl);

    let return_arrow = just("->")
        .padded()
        .ignore_then(just("_"))
        .map(|_| Token::ReturnArrow);

    let ident = text::ascii::ident().map(|ident: &str| match ident {
        "fn" => Token::Fn,
        "let" => Token::Let,
        _ => Token::Identifier(ident),
    });

    let token = hex.or(opcode).or(ctrl).or(return_arrow).or(ident);

    let comment = just("//")
        .then(any().and_is(just('\n').not()).repeated())
        .padded();

    token
        .map_with(|tok, e| (tok, e.span()))
        .padded_by(comment.repeated())
        .padded()
        // If we encounter an error, skip and attempt to lex the next character as a token instead
        .recover_with(skip_then_retry_until(any().ignored(), end()))
        .repeated()
        .collect()
}

/// A program is a sequence of items.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Program<'src> {
    items: Arc<[Function<'src>]>,
    span: SimpleSpan,
}

impl<'src> Program<'src> {
    /// Accesses the items of the program.
    pub fn items(&self) -> &[Function<'src>] {
        &self.items
    }

    /// Accesses the span of the program.
    pub fn span(&self) -> SimpleSpan {
        self.span
    }
}

impl fmt::Display for Program<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (index, item) in self.items().iter().enumerate() {
            write!(f, "{item}")?;
            if index < self.items().len() - 1 {
                writeln!(f, "\n")?;
            }
        }
        Ok(())
    }
}

impl ShallowClone for Program<'_> {
    fn shallow_clone(&self) -> Self {
        Self {
            items: self.items.shallow_clone(),
            span: self.span,
        }
    }
}

pub type FunctionName<'src> = &'src str;

// TODO: Allow block expressions and scopes
/// A function is an expression that can be called for an instantiation of its parameters.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Function<'src> {
    name: FunctionName<'src>,
    params: Arc<[VariableName<'src>]>,
    body: Arc<[Statement<'src>]>,
    final_expr: Option<Arc<Expression<'src>>>,
    is_unit: bool,
    span_total: SimpleSpan,
    span_name: SimpleSpan,
    span_params: Arc<[SimpleSpan]>,
    span_params_total: SimpleSpan,
    span_return: SimpleSpan,
    span_body: SimpleSpan,
}

impl<'src> Function<'src> {
    /// Accesses the name of the function.
    pub fn name(&self) -> FunctionName<'src> {
        self.name
    }

    /// Accesses the parameters of the function.
    pub fn params(&self) -> &Arc<[VariableName<'src>]> {
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

    /// Accesses the total span of the function.
    pub fn span_total(&self) -> SimpleSpan {
        self.span_total
    }

    /// Accesses the span of the name of the function.
    pub fn span_name(&self) -> SimpleSpan {
        self.span_name
    }

    /// Accesses the spans of each parameter of the function.
    pub fn span_params(&self) -> &[SimpleSpan] {
        &self.span_params
    }

    /// Accesses the span over all parameters of the function.
    pub fn span_params_total(&self) -> SimpleSpan {
        self.span_params_total
    }

    /// Accesses the span of the return type of the function.
    pub fn span_return(&self) -> SimpleSpan {
        self.span_return
    }

    /// Accesses the span of the body of the function.
    pub fn span_body(&self) -> SimpleSpan {
        self.span_body
    }
}

impl fmt::Display for Function<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "fn {}(", self.name())?;
        for (index, param) in self.params.iter().enumerate() {
            write!(f, "{param}")?;
            if index != self.params.len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, ") ")?;
        if !self.is_unit {
            write!(f, "-> _ ")?;
        }
        writeln!(f, "{{")?;
        for statement in self.body() {
            writeln!(f, "    {statement}")?;
        }
        if let Some(expr) = self.final_expr() {
            writeln!(f, "    {expr}")?;
        }
        write!(f, "}}")
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
            span_total: self.span_total,
            span_name: self.span_name,
            span_params: self.span_params.shallow_clone(),
            span_params_total: self.span_params_total,
            span_return: self.span_return,
            span_body: self.span_body,
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

#[allow(clippy::needless_lifetimes)]
impl<'src> Statement<'src> {
    /// Accesses the span of the statement.
    pub fn span(&self) -> SimpleSpan {
        match self {
            Self::Assignment(ass) => ass.span_total(),
            Self::UnitExpr(expr) => expr.span(),
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

/// The name of a variable.
pub type VariableName<'src> = &'src str;

/// An assignment assigns the output of an expression to a variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Assignment<'src> {
    name: VariableName<'src>,
    expression: Expression<'src>,
    span_total: SimpleSpan,
    span_name: SimpleSpan,
}

impl<'src> Assignment<'src> {
    /// Accesses the variable that is being assigned.
    pub fn name(&self) -> &VariableName<'src> {
        &self.name
    }

    /// Accesses the expression that produces the assignment value.
    pub fn expression(&self) -> &Expression<'src> {
        &self.expression
    }

    /// Accesses the total span of the assignment.
    pub fn span_total(&self) -> SimpleSpan {
        self.span_total
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
            span_total: self.span_total,
            span_name: self.span_name,
        }
    }
}

/// An expression produces an output value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Expression<'src> {
    inner: ExpressionInner<'src>,
    span: SimpleSpan,
}

impl<'src> Expression<'src> {
    /// Accesses the inner expression.
    pub fn inner(&self) -> &ExpressionInner<'src> {
        &self.inner
    }

    /// Accesses the span of the expression.
    pub fn span(&self) -> SimpleSpan {
        self.span
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

impl ShallowClone for Expression<'_> {
    fn shallow_clone(&self) -> Self {
        Self {
            inner: self.inner.shallow_clone(),
            span: self.span,
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

/// The name of an opcode.
pub type OpcodeName<'src> = &'src str;

/// The name of a called function.
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum CallName<'src> {
    /// A Bitcoin Script opcode that is a builtin function.
    Builtin(OpcodeName<'src>),
    /// A user-defined custom function.
    Custom(FunctionName<'src>),
}

impl fmt::Display for CallName<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Builtin(name) => write!(f, "{name}"),
            Self::Custom(name) => write!(f, "{name}"),
        }
    }
}

/// A call runs a function with given arguments.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Call<'src> {
    name: CallName<'src>,
    args: Arc<[VariableName<'src>]>,
    span_total: SimpleSpan,
    span_name: SimpleSpan,
    span_args: Arc<[SimpleSpan]>,
    span_args_total: SimpleSpan,
}

impl<'src> Call<'src> {
    /// Accesses the name of the called function.
    pub fn name(&self) -> &CallName<'src> {
        &self.name
    }

    /// Accesses the arguments of the function call.
    pub fn args(&self) -> &Arc<[VariableName<'src>]> {
        &self.args
    }

    /// Accesses the total span of the function call.
    pub fn span_total(&self) -> SimpleSpan {
        self.span_total
    }

    /// Accesses the span of the name of the called function.
    pub fn span_name(&self) -> SimpleSpan {
        self.span_name
    }

    /// Accesses the spans of each argument of the call.
    pub fn span_args(&self) -> &[SimpleSpan] {
        &self.span_args
    }

    /// Accesses the span over all arguments of the call.
    pub fn span_args_total(&self) -> SimpleSpan {
        self.span_args_total
    }
}

impl fmt::Display for Call<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "op::{}(", self.name)?;
        for (index, arg) in self.args.iter().enumerate() {
            write!(f, "{arg}")?;
            if index < self.args().len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, ")")
    }
}

impl ShallowClone for Call<'_> {
    fn shallow_clone(&self) -> Self {
        Self {
            name: self.name,
            args: self.args.shallow_clone(),
            span_total: self.span_total,
            span_name: self.span_name,
            span_args: self.span_args.shallow_clone(),
            span_args_total: self.span_args_total,
        }
    }
}

pub fn program_parser<'src, I>()
-> impl Parser<'src, I, Program<'src>, extra::Err<Rich<'src, Token<'src>>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    func_parser()
        .repeated()
        .collect::<Vec<Function>>()
        .map_with(|functions, e| Program {
            items: Arc::from(functions),
            span: e.span(),
        })
}

fn func_parser<'src, I>()
-> impl Parser<'src, I, Function<'src>, extra::Err<Rich<'src, Token<'src>>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    let function_name = select! { Token::Identifier(name) => name }
        .labelled("function name")
        .map_with(|name, e| (name, e.span()));

    let params = select! { Token::Identifier(name) => name }
        .map_with(|name, e| (name, e.span()))
        .separated_by(just(Token::Ctrl(',')))
        .allow_trailing()
        .collect::<Vec<(VariableName, SimpleSpan)>>()
        .map_with(|spanned_params, e| {
            let (params, span_params): (Vec<VariableName>, Vec<SimpleSpan>) =
                spanned_params.into_iter().unzip();
            (params, span_params, e.span())
        })
        .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')))
        .labelled("function parameters");

    let is_unit = just(Token::ReturnArrow)
        .or_not()
        .map(|option| option.is_none())
        .map_with(|is_unit, e| (is_unit, e.span()))
        .labelled("return type");

    // TODO: Allow final expression without trailing `;`
    // Without this, functions always return unit
    let body = stmt_parser()
        .repeated()
        .collect::<Vec<Statement>>()
        .then(expr_parser().or_not())
        .delimited_by(just(Token::Ctrl('{')), just(Token::Ctrl('}')))
        .map_with(|body, e| (body, e.span()))
        .labelled("function body");

    just(Token::Fn)
        .ignore_then(function_name)
        .then(params)
        .map(
            |((name, span_name), (params, span_params, span_params_total))| {
                (name, span_name, params, span_params, span_params_total)
            },
        )
        .then(is_unit)
        .map(
            |(
                (name, span_name, params, span_params, span_params_total),
                (is_unit, span_return),
            )| {
                (
                    name,
                    span_name,
                    params,
                    span_params,
                    span_params_total,
                    is_unit,
                    span_return,
                )
            },
        )
        .then(body)
        .map_with(
            |(
                (name, span_name, params, span_params, span_params_total, is_unit, span_return),
                ((body, final_expr), span_body),
            ),
             e| Function {
                name,
                params: Arc::from(params),
                body: Arc::from(body),
                final_expr: final_expr.map(Arc::new),
                is_unit,
                span_total: e.span(),
                span_name,
                span_params: Arc::from(span_params),
                span_params_total,
                span_return: if is_unit { span_name } else { span_return }, // prevent empty span
                span_body,
            },
        )
        .labelled("function")
}

fn stmt_parser<'src, I>()
-> impl Parser<'src, I, Statement<'src>, extra::Err<Rich<'src, Token<'src>>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    let expr = expr_parser();
    let variable_name = select! { Token::Identifier(name) => name }
        .map_with(|name, e| (name, e.span()))
        .labelled("variable name");

    // Assignment: let var = expr;
    let assignment = just(Token::Let)
        .ignore_then(variable_name)
        .then_ignore(just(Token::Ctrl('=')))
        .then(expr.clone())
        .then_ignore(just(Token::Ctrl(';')))
        .map_with(|((name, span_name), expression), e| {
            Statement::Assignment(Assignment {
                name,
                expression,
                span_total: e.span(),
                span_name,
            })
        });

    // Expression statement: expr;
    let expr_stmt = expr
        .then_ignore(just(Token::Ctrl(';')))
        .map(Statement::UnitExpr);

    // Statement can be either an assignment or an expression statement
    assignment.or(expr_stmt)
}

fn expr_parser<'src, I>()
-> impl Parser<'src, I, Expression<'src>, extra::Err<Rich<'src, Token<'src>>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = SimpleSpan>,
{
    recursive(|expr| {
        let variable_name = select! { Token::Identifier(name) => name }.labelled("variable name");
        let variable_expr = variable_name
            .map_with(|name, e| Expression {
                inner: ExpressionInner::Variable(name),
                span: e.span(),
            })
            .labelled("variable");

        let bytes_expr = select! { Token::Hex(s) => s }
            .map(|s| Vec::<u8>::from_hex(s).expect("there should be hex pairs"))
            .map_with(|bytes, e| Expression {
                inner: ExpressionInner::Bytes(Arc::from(bytes)),
                span: e.span(),
            })
            .labelled("hex literal");

        let expr_with_parentheses = expr
            .clone()
            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')));

        // Expressions at base of parse tree, which don't contain other expressions.
        let base_expr = variable_expr.or(bytes_expr).or(expr_with_parentheses);

        let function_name = select! {
            Token::Opcode(name) => CallName::Builtin(name),
            Token::Identifier(name) => CallName::Custom(name),
        }
        .map_with(|name, e| (name, e.span()))
        .labelled("function name");

        let args = variable_name
            .map_with(|name, e| (name, e.span()))
            .separated_by(just(Token::Ctrl(',')))
            .collect::<Vec<(VariableName, SimpleSpan)>>()
            .map_with(|spanned_params, e| {
                let (args, span_args): (Vec<VariableName>, Vec<SimpleSpan>) =
                    spanned_params.into_iter().unzip();
                (args, span_args, e.span())
            })
            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')))
            .labelled("call arguments");

        let call = function_name
            .then(args)
            .map_with(
                |((name, span_name), (args, span_args, span_args_total)), e| Call {
                    name,
                    args: Arc::from(args),
                    span_total: e.span(),
                    span_name,
                    span_args: Arc::from(span_args),
                    span_args_total,
                },
            )
            .map_with(|call, e| Expression {
                inner: ExpressionInner::Call(call),
                span: e.span(),
            })
            .labelled("function call");

        call.or(base_expr)
    })
}
