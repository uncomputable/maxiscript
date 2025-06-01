use std::{env, fs};

use ariadne::{Color, Label, Report, ReportKind, sources};
use hex_conservative::DisplayHex;
use maxiscript::Severity;

fn main() {
    env_logger::Builder::new()
        .filter_level(log::LevelFilter::Debug)
        .init();

    let filename = env::args().nth(1).expect("Expected file argument");
    let source_code = fs::read_to_string(&filename).expect("Failed to read file");

    let (target_code, diagnostics) = maxiscript::compile_program(&source_code);

    if let Some(target_code) = target_code {
        println!("{}", target_code.as_bytes().to_lower_hex_string());
    }

    diagnostics.into_iter().for_each(|e| {
        let kind = match e.severity() {
            Severity::Error => ReportKind::Error,
            Severity::Warning => ReportKind::Warning,
        };
        let mut report = Report::build(kind, (filename.clone(), e.top().span().into_range()))
            .with_config(ariadne::Config::new().with_index_type(ariadne::IndexType::Byte))
            .with_message(e.top().message())
            .with_labels(e.contexts().iter().map(|ctx| {
                Label::new((filename.clone(), ctx.span().into_range()))
                    .with_message(ctx.message())
                    .with_color(Color::Red)
            }))
            .with_labels(e.contexts2().iter().map(|ctx| {
                Label::new((filename.clone(), ctx.span().into_range()))
                    .with_message(ctx.message())
                    .with_color(Color::Yellow)
            }));
        if let Some(note) = e.note() {
            report = report.with_note(note);
        }
        report
            .finish()
            .print(sources([(filename.clone(), source_code.clone())]))
            .expect("write to stdout should not fail")
    });
}
