extern crate core;

use crate::parse::{lexer, program_parser, Program, Span, Spanned, Token};
use chumsky::prelude::{Input, Rich};
use chumsky::Parser;

pub mod opcodes;
pub mod optimize;
pub mod parse;

pub type ErrorSet<'src> = Vec<Rich<'src, String, Span>>;

pub fn lex_program(src: &str) -> (Option<Vec<Spanned<Token>>>, Vec<Rich<char>>) {
    lexer().parse(src).into_output_errors()
}

pub fn parse_program<'src>(
    src: &'src str,
    tokens: &'src [Spanned<Token<'src>>],
) -> (Option<Program<'src>>, Vec<Rich<'src, Token<'src>>>) {
    program_parser()
        .parse(tokens.map((src.len()..src.len()).into(), |(t, s)| (t, s)))
        .into_output_errors()
}

pub fn parse_program_string(src: &str) -> Option<String> {
    let (tokens, lex_errs) = lex_program(&src);

    if !lex_errs.is_empty() {
        return None;
    }

    let (program, parse_errs) = match tokens.as_ref() {
        Some(tokens) => parse_program(&src, tokens),
        None => (None, Vec::default()),
    };

    if !parse_errs.is_empty() {
        return None;
    }

    program.map(|x| x.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fuzz_regression1() {
        parse_program_string("0x0");
    }
}
