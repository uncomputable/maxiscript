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
    use itertools::Itertools;

    fn assert_ok(source_code: &'static str) {
        let (target_code, diagnostics) = compile_program(source_code);
        for e in &diagnostics {
            if e.severity() == Severity::Error {
                panic!("Expected no errors, but got: `{e}`");
            }
        }
        if target_code.is_none() {
            panic!(
                "The compiler failed to produce any target code! Here are all diagnostics: {}",
                diagnostics.iter().map(|e| format!("`{e}`")).join(", ")
            );
        }
        // TODO: Execute target code
    }

    fn assert_error<Str: ToString>(source_code: &'static str, pattern: Str) {
        let (target_code, diagnostics) = compile_program(source_code);
        if let Some(target_code) = target_code {
            panic!("Expected empty target code, but got: `{target_code}`");
        }
        let pattern = pattern.to_string();
        if diagnostics
            .iter()
            .find(|e| e.severity() == Severity::Error && e.top().message().contains(&pattern))
            .is_none()
        {
            panic!(
                "Could not find the expected error `{pattern}`. Here are all diagnostics: {}",
                diagnostics.iter().map(|e| format!("`{e}`")).join(", ")
            );
        }
    }

    fn assert_warnings(source_code: &'static str, patterns: &[&'static str]) {
        let (target_code, diagnostics) = compile_program(source_code);
        if target_code.is_none() {
            panic!(
                "The compiler failed to produce any target code! Here are all diagnostics:\n{}",
                diagnostics.iter().map(|e| format!("{e}")).join("\n")
            );
        }
        for pattern in patterns {
            if diagnostics
                .iter()
                .find(|e| e.severity() == Severity::Warning && e.contains(pattern))
                .is_none()
            {
                panic!(
                    "Could not find the expected warning `{pattern}`. Here are all diagnostics:\n{}",
                    diagnostics.iter().map(|e| format!("{e}")).join("\n")
                );
            }
        }
    }

    #[test]
    fn call_function_before_definition() {
        let source_code = "
            fn main() {
                f();
            }

            fn f() {}
        ";
        assert_ok(source_code);
    }

    #[test]
    fn duplicate_argument() {
        let source_code = "
            fn main() {
                let x = 0x01;
                op::equal_verify(x, x);
            }
        ";
        assert_error(source_code, "argument `x` cannot appear twice");
    }

    #[test]
    fn duplicate_argument_alias() {
        let source_code = "
            fn eq(x, y) {
               op::equal_verify(x, y);
            }

            fn main() {
                let x = 0x01;
                let y = x;
                let z = y;
                let u = z;
                let v = u;
                let w = eq(x, u);
            }
        ";
        assert_error(source_code, "argument `x` cannot appear twice");
    }

    #[test]
    fn recursive_call() {
        let source_code = "
            fn f() {
                g();
            }

            fn g() {
                h();
            }

            fn h() {
                f();
            }

            fn main() {
                f();
            }
        ";
        assert_error(source_code, "recursive call");
    }

    #[test]
    fn unused_variables() {
        let source_code = "
            fn f(x, y) {
                let z = 0x01;
                op::equal_verify(x, z)
            } // y unused

            fn main() {
                let x_ = 0x01;
                let y_ = 0x02;
                f(x_, y_)
            } // y_ implicitly unused
        ";
        assert_warnings(source_code, &["`y` is never used", "`y_` is never used"]);
    }

    #[test]
    fn unused_variables_chain() {
        let source_code = "
            fn f(x, y, z) { g(x, y) } // z unused
            fn g(x_, y_) { h(x_) } // y_ unused
            fn h(x__) { } // x__ unused

            fn main() {
                let x___ = 0x01;
                let y___ = 0x02;
                let z___ = 0x03;
                f(x___, y___, z___);
            } // x___, y___, z___ implicitly unused
        ";
        assert_warnings(
            source_code,
            &[
                "`z` is never used",
                "`y_` is never used",
                "`x__` is never used",
            ],
        );
    }

    #[test]
    fn fuzz_regression1() {
        parse_program_string("0x0");
    }
}
