use chumsky::input::ValueInput;
use chumsky::prelude::{
    any, end, just, one_of, skip_then_retry_until, IterParser, Rich, SimpleSpan,
};
use chumsky::{extra, select, text, Parser};
use hex_conservative::{DisplayHex, FromHex};
use std::fmt;
use std::sync::Arc;

pub type Span = SimpleSpan;
pub type Spanned<T> = (T, Span);

#[derive(Clone, Debug, PartialEq)]
pub enum Token<'src> {
    Hex(&'src str),
    Opcode(&'src str),
    Ctrl(char),
    Identifier(&'src str),
    Fn,
    Let,
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
        }
    }
}

pub fn lexer<'src>(
) -> impl Parser<'src, &'src str, Vec<Spanned<Token<'src>>>, extra::Err<Rich<'src, char, Span>>> {
    let hex = just("0x")
        .ignore_then(
            one_of("0123456789abcdefABCDEF")
                .repeated()
                .exactly(2)
                .repeated()
                .to_slice(),
        )
        .map(Token::Hex);

    let opcode = just("op::")
        .ignore_then(text::ascii::ident().to_slice())
        .map(Token::Opcode);

    let ctrl = one_of("()[]{};,=").map(Token::Ctrl);

    let ident = text::ascii::ident().map(|ident: &str| match ident {
        "fn" => Token::Fn,
        "let" => Token::Let,
        _ => Token::Identifier(ident),
    });

    let token = hex.or(opcode).or(ctrl).or(ident);

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

/// A program is a sequence of statements.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Program<'src> {
    statements: Arc<[Statement<'src>]>,
}

impl Program<'_> {
    /// Accesses the statements of the program.
    pub fn statements(&self) -> &Arc<[Statement]> {
        &self.statements
    }
}

impl fmt::Display for Program<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (index, stmt) in self.statements().iter().enumerate() {
            write!(f, "{stmt};")?;
            if index < self.statements().len() - 1 {
                writeln!(f, "")?;
            }
        }
        Ok(())
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

impl fmt::Display for Statement<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Statement::Assignment(ass) => write!(f, "{ass}"),
            Statement::UnitExpr(expr) => write!(f, "{expr}"),
        }
    }
}

pub type VariableName<'src> = &'src str;

/// An assignment assigns the output of an expression to a variable.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Assignment<'src> {
    variable: VariableName<'src>,
    expression: Expression<'src>,
}

impl<'src> Assignment<'src> {
    /// Accesses the variable that is being assigned.
    pub fn variable(&self) -> &VariableName<'src> {
        &self.variable
    }

    /// Accesses the expression that produces the assignment value.
    pub fn expression(&self) -> &Expression<'src> {
        &self.expression
    }
}

impl fmt::Display for Assignment<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "let {} = {}", self.variable, self.expression)
    }
}

/// An expression produces an output value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Expression<'src> {
    /// Return the value of a variable.
    Variable(VariableName<'src>),
    /// Return constant bytes.
    Bytes(Arc<[u8]>),
    /// Return the output of a function call.
    Call(Call<'src>),
}

impl fmt::Display for Expression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Variable(name) => write!(f, "{name}"),
            Expression::Bytes(bytes) => write!(f, "0x{}", bytes.to_lower_hex_string()),
            Expression::Call(call) => write!(f, "{call}"),
        }
    }
}

/// A call runs a function with given arguments.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Call<'src> {
    name: OpcodeName,
    args: Arc<[VariableName<'src>]>,
}

impl Call<'_> {
    /// Accesses the name of the called function.
    pub fn name(&self) -> &OpcodeName {
        &self.name
    }

    /// Accesses the arguments of the function call.
    pub fn args(&self) -> &[VariableName] {
        &self.args
    }
}

impl fmt::Display for Call<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(", self.name)?;
        for (index, arg) in self.args().iter().enumerate() {
            write!(f, "{arg}")?;
            if index < self.args().len() - 1 {
                write!(f, ", ")?;
            }
        }
        write!(f, ")")
    }
}

/// The name of an opcode.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum OpcodeName {
    Add,
    EqualVerify,
}

impl fmt::Display for OpcodeName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Add => f.write_str("op::add"),
            Self::EqualVerify => f.write_str("op::equal_verify"),
        }
    }
}

pub fn program_parser<'src, I>(
) -> impl Parser<'src, I, Program<'src>, extra::Err<Rich<'src, Token<'src>, Span>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = Span>,
{
    let expr = expr_parser();

    // Assignment: let var = expr;
    let assignment = just(Token::Let)
        .ignore_then(select! { Token::Identifier(name) => name })
        .then_ignore(just(Token::Ctrl('=')))
        .then(expr.clone())
        .then_ignore(just(Token::Ctrl(';')))
        .map(|(var, (expr, _span))| {
            Statement::Assignment(Assignment {
                variable: var,
                expression: expr,
            })
        });

    // Expression statement: expr;
    let expr_stmt = expr
        .then_ignore(just(Token::Ctrl(';')))
        .map(|(expr, _span)| Statement::UnitExpr(expr));

    // Statement can be either an assignment or an expression statement
    let stmt = assignment.or(expr_stmt);

    // Program is a sequence of statements
    stmt.repeated()
        .collect::<Vec<Statement>>()
        .map(|statements| Program {
            statements: Arc::from(statements),
        })
}

fn expr_parser<'src, I>(
) -> impl Parser<'src, I, Spanned<Expression<'src>>, extra::Err<Rich<'src, Token<'src>, Span>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = Span>,
{
    let var = select! { Token::Identifier(name) => Expression::Variable(name) }
        .map_with(|expr, e| (expr, e.span()));

    let hex = select! { Token::Hex(s) => s }
        .map(|s| {
            debug_assert_eq!(s.len() % 2, 0, "there should be pairs of hex characters");
            Vec::<u8>::from_hex(s)
                .map(Arc::from)
                .map(Expression::Bytes)
                .expect("string should be hex")
        })
        .map_with(|expr, e| (expr, e.span()));

    let call = call_parser();

    var.or(hex).or(call)
}

fn call_parser<'src, I>(
) -> impl Parser<'src, I, Spanned<Expression<'src>>, extra::Err<Rich<'src, Token<'src>, Span>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = Span>,
{
    let function_name = select! {
        Token::Opcode("add") => OpcodeName::Add,
        Token::Opcode("equal_verify") => OpcodeName::EqualVerify,
    };

    let function_args = select! { Token::Identifier(name) => name }
        .separated_by(just(Token::Ctrl(',')))
        .collect::<Vec<VariableName<'src>>>();

    function_name
        .then_ignore(just(Token::Ctrl('(')))
        .then(function_args)
        .then_ignore(just(Token::Ctrl(')')))
        .map(|(name, args)| {
            Expression::Call(Call {
                name,
                args: Arc::from(args),
            })
        })
        .map_with(|expr, e| (expr, e.span()))
}
