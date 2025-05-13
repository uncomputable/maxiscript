use chumsky::Parser;
use chumsky::prelude::{Input, Rich};

use crate::parse::{Spanned, Token, lexer, program_parser};

mod compile;
mod ir;
mod opcodes;
mod parse;
mod sorting;
mod util;

pub use compile::compile;

pub fn lex_program(src: &str) -> (Option<Vec<Spanned<Token>>>, Vec<Rich<String>>) {
    let (tokens, lex_errors) = lexer().parse(src).into_output_errors();
    let lex_errors = lex_errors
        .into_iter()
        .map(|e| e.map_token(|tok| tok.to_string()))
        .collect();
    (tokens, lex_errors)
}

pub fn parse_program<'src>(
    src: &'src str,
    tokens: &'src [Spanned<Token<'src>>],
) -> (Option<parse::Program<'src>>, Vec<Rich<'src, String>>) {
    let (program, parse_errors) = program_parser()
        .parse(tokens.map((src.len()..src.len()).into(), |(t, s)| (t, s)))
        .into_output_errors();
    let parse_errors = parse_errors
        .into_iter()
        .map(|e| e.map_token(|tok| tok.to_string()))
        .collect();
    (program, parse_errors)
}

pub fn analyze<'src>(program: &parse::Program<'src>) -> Result<ir::Program<'src>, ir::Error> {
    ir::Program::analyze(program)
}

pub fn parse_program_string(src: &str) -> Option<String> {
    let (tokens, lex_errs) = lex_program(src);

    if !lex_errs.is_empty() {
        return None;
    }

    let (program, parse_errs) = match tokens.as_ref() {
        Some(tokens) => parse_program(src, tokens),
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
