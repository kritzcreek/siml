#[macro_use]
extern crate log;
extern crate fern;
extern crate siml;

use std::fs;
use fern::colors::{Color, ColoredLevelConfig};
use siml::eval::Eval;
use siml::expr::Expr;
use siml::grammar;
use siml::repl;
use siml::term::Term;
use siml::token;
use siml::types;

fn setup_logger() {
    let colors = ColoredLevelConfig::new()
        .info(Color::Green)
        .debug(Color::Blue);
    let _ = fern::Dispatch::new()
        .format(move |out, message, record| {
            out.finish(format_args!(
                "[{}] {}",
                colors.color(record.level()),
                message
            ))
        })
        .level(log::LevelFilter::Info)
        // .level_for("siml::bi_types", log::LevelFilter::Debug)
        .chain(std::io::stdout())
        .apply();
}

fn file() {
    let source_file = fs::read_to_string("examples.siml").expect("Failed to read the source file.");
    for line in source_file.lines() {
        info!("{}", line);
        repl::run_term(line);
        println!();
    }
}

fn main() {
    setup_logger();
    file();
    repl::run();
}
