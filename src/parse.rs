use std::fmt;
use std::sync::Arc;

use bitcoin::script::PushBytesBuf;
use chumsky::input::ValueInput;
use chumsky::prelude::{
    IterParser, Rich, SimpleSpan, any, end, just, one_of, recursive, skip_then_retry_until,
};
use chumsky::{Parser, extra, select, text};
use hex_conservative::{DisplayHex, FromHex};

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

pub fn lexer<'src>()
-> impl Parser<'src, &'src str, Vec<Spanned<Token<'src>>>, extra::Err<Rich<'src, char, Span>>> {
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

impl<'src> Program<'src> {
    /// Accesses the statements of the program.
    pub fn statements(&self) -> &Arc<[Statement<'src>]> {
        &self.statements
    }
}

impl fmt::Display for Program<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (index, stmt) in self.statements().iter().enumerate() {
            write!(f, "{stmt}")?;
            if index < self.statements().len() - 1 {
                writeln!(f)?;
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
            Statement::Assignment(ass) => write!(f, "{ass};"),
            Statement::UnitExpr(expr) => write!(f, "{expr};"),
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
    pub fn assignee(&self) -> &VariableName<'src> {
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
    Bytes(PushBytesBuf),
    /// Return the output of a function call.
    Call(Call<'src>),
}

impl fmt::Display for Expression<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expression::Variable(name) => write!(f, "{name}"),
            Expression::Bytes(bytes) => write!(f, "0x{}", bytes.as_bytes().to_lower_hex_string()),
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
    /// Gets the name of the called function.
    pub fn name(&self) -> &OpcodeName {
        &self.name
    }

    /// Gets the arguments of the function call.
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
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum OpcodeName {
    Add,
    EqualVerify,
}

impl OpcodeName {
    /// Gets the number of arguments of the opcode.
    ///
    /// Arguments are popped from the stack.
    pub const fn n_args(self) -> usize {
        match self {
            OpcodeName::Add => 2,
            OpcodeName::EqualVerify => 2,
        }
    }

    /// Gets the number of return values of the opcode.
    ///
    /// Return values are pushed onto the stack.
    pub const fn n_rets(self) -> usize {
        match self {
            OpcodeName::Add => 1,
            OpcodeName::EqualVerify => 0,
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
        match self {
            OpcodeName::Add => bitcoin::opcodes::all::OP_ADD,
            OpcodeName::EqualVerify => bitcoin::opcodes::all::OP_EQUALVERIFY,
        }
    }
}

impl fmt::Display for OpcodeName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Add => f.write_str("op::add"),
            Self::EqualVerify => f.write_str("op::equal_verify"),
        }
    }
}

pub fn program_parser<'src, I>()
-> impl Parser<'src, I, Program<'src>, extra::Err<Rich<'src, Token<'src>, Span>>> + Clone
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
        .map(|(variable, expression)| {
            Statement::Assignment(Assignment {
                variable,
                expression,
            })
        });

    // Expression statement: expr;
    let expr_stmt = expr
        .then_ignore(just(Token::Ctrl(';')))
        .map(Statement::UnitExpr);

    // Statement can be either an assignment or an expression statement
    let stmt = assignment.or(expr_stmt);

    // Program is a sequence of statements
    stmt.repeated()
        .collect::<Vec<Statement>>()
        .map(|statements| Program {
            statements: Arc::from(statements),
        })
}

fn expr_parser<'src, I>()
-> impl Parser<'src, I, Expression<'src>, extra::Err<Rich<'src, Token<'src>, Span>>> + Clone
where
    I: ValueInput<'src, Token = Token<'src>, Span = Span>,
{
    recursive(|expr| {
        let variable = select! { Token::Identifier(name) => name };
        let variable_expr = variable.map(Expression::Variable);

        let bytes_expr = select! { Token::Hex(s) => s }.map(|s| {
            debug_assert_eq!(s.len() % 2, 0, "there should be pairs of hex characters");
            let vec = Vec::<u8>::from_hex(s).expect("string should be hex");
            // TODO: Handle failure case when hex is too long
            let push_bytes =
                bitcoin::script::PushBytesBuf::try_from(vec).expect("hex should not be too long");
            Expression::Bytes(push_bytes)
        });

        let expr_with_parentheses = expr
            .clone()
            .delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')')));

        // Expressions at base of parse tree, which don't contain other expressions.
        let base_expr = variable_expr.or(bytes_expr).or(expr_with_parentheses);

        let function_name = select! {
            Token::Opcode("add") => OpcodeName::Add,
            Token::Opcode("equal_verify") => OpcodeName::EqualVerify,
        };

        let variable_sequence = variable
            .separated_by(just(Token::Ctrl(',')))
            .collect::<Vec<VariableName>>();

        let call = function_name
            .then(variable_sequence.delimited_by(just(Token::Ctrl('(')), just(Token::Ctrl(')'))))
            .map(|(name, args)| Call {
                name,
                args: Arc::from(args),
            })
            .map(Expression::Call);

        base_expr.or(call)
    })
}
