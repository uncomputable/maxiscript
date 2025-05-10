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

    let (tokens, mut errors) = lex_program(&src);

    let parse_program = tokens.as_ref().and_then(|tokens| {
        let (program, parse_errors) = parse_program(&src, tokens);
        errors.extend(parse_errors);
        program
    });

    let mut ir_errors = Vec::new();

    if let Some(parse_program) = parse_program {
        info!("Compiling Bitfony program:\n{parse_program}");
        match analyze(&parse_program) {
            Ok(ir_program) => {
                let bitcoin_script = compile(&ir_program);
                info!("Resulting Bitcoin script:\n{bitcoin_script:?}");
                println!("{}", bitcoin_script.as_bytes().to_lower_hex_string());
            }
            Err(error) => {
                ir_errors.push(error);
            }
        }
    }

    errors.into_iter().for_each(|e| {
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

    ir_errors.into_iter().for_each(|e| {
        Report::build(ReportKind::Error, filename.clone(), e.top().span().start)
            .with_message(e.top().message())
            .with_labels(e.contexts().iter().map(|ctx| {
                Label::new((filename.clone(), ctx.span().into_range()))
                    .with_message(ctx.message())
                    .with_color(Color::Red)
            }))
            .finish()
            .print(sources([(filename.clone(), src.clone())]))
            .expect("write to stdout should not fail")
    });
}
