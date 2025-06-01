use chumsky::Parser;
use chumsky::prelude::{Input, Rich};
use log::info;

use crate::parse::{Spanned, Token, lexer, program_parser};
pub use error::{Diagnostic, Severity};

mod compile;
mod error;
mod ir;
mod op;
mod parse;
mod sorting;
mod stack;
mod util;

pub fn compile_program(source_code: &str) -> (Option<bitcoin::ScriptBuf>, Vec<Diagnostic>) {
    let mut diagnostics = vec![];

    let (tokens, lex_errors) = lex_program(source_code);
    diagnostics.extend(lex_errors.into_iter().map(Diagnostic::from));

    let program: Option<parse::Program> = tokens.as_ref().and_then(|tokens| {
        let (program, parse_errors) = parse_program(source_code, tokens);
        diagnostics.extend(parse_errors.into_iter().map(Diagnostic::from));
        program
    });

    let program: Option<ir::Program> = program.as_ref().and_then(|program| {
        info!("Compiling Bitfony program:\n{program}");
        let (program, ir_errors) = analyze(program);
        diagnostics.extend(ir_errors);
        program
    });

    let target_code: Option<bitcoin::ScriptBuf> = program.as_ref().map(|program| {
        let bitcoin_script = compile::compile(program);
        info!("Resulting Bitcoin script:\n{bitcoin_script:?}");
        bitcoin_script
    });

    (target_code, diagnostics)
}

fn lex_program(src: &str) -> (Option<Vec<Spanned<Token>>>, Vec<Rich<String>>) {
    let (tokens, lex_errors) = lexer().parse(src).into_output_errors();
    let lex_errors = lex_errors
        .into_iter()
        .map(|e| e.map_token(|tok| tok.to_string()))
        .collect();
    (tokens, lex_errors)
}

fn parse_program<'src>(
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

fn analyze<'src>(program: &parse::Program<'src>) -> (Option<ir::Program<'src>>, Vec<Diagnostic>) {
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
