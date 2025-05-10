use std::{env, fs};

use ariadne::{Color, Label, Report, ReportKind, sources};
use bitfony::{analyze, compile, lex_program, parse_program};
use hex_conservative::DisplayHex;
use log::info;

fn main() {
    env_logger::Builder::new()
        .filter_level(log::LevelFilter::Debug)
        .init();

    let filename = env::args().nth(1).expect("Expected file argument");
    let src = fs::read_to_string(&filename).expect("Failed to read file");

    let (tokens, lex_errs) = lex_program(&src);

    let (program, parse_errs) = match tokens.as_ref() {
        Some(tokens) => parse_program(&src, tokens),
        None => (None, Vec::default()),
    };

    if let Some(program) = program {
        info!("Compiling Bitfony program:\n{program}");
        match analyze(&program) {
            Ok(program) => {
                let script = compile(program);
                info!("Resulting Bitcoin script:\n{script:?}");
                println!("{}", script.as_bytes().to_lower_hex_string());
            }
            Err(error) => {
                println!("Analysis error: {error}");
            }
        }
    }

    lex_errs
        .into_iter()
        .map(|e| e.map_token(|c| c.to_string()))
        .chain(
            parse_errs
                .into_iter()
                .map(|e| e.map_token(|tok| tok.to_string())),
        )
        .for_each(|e| {
            Report::build(ReportKind::Error, filename.clone(), e.span().start)
                .with_message(e.to_string())
                .with_label(
                    Label::new((filename.clone(), e.span().into_range()))
                        .with_message(e.reason().to_string())
                        .with_color(Color::Red),
                )
                .with_labels(e.contexts().map(|(label, span)| {
                    Label::new((filename.clone(), span.into_range()))
                        .with_message(format!("while parsing this {}", label))
                        .with_color(Color::Yellow)
                }))
                .finish()
                .print(sources([(filename.clone(), src.clone())]))
                .expect("write to stdout should not fail")
        });
}
