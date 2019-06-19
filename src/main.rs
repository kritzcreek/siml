#[macro_use]
extern crate log;
extern crate fern;
extern crate notify;
extern crate siml;

use fern::colors::{Color, ColoredLevelConfig};
use notify::{RecommendedWatcher, RecursiveMode, Watcher};
use siml::repl;
use std::fs;
use std::sync::mpsc::channel;
use std::thread;
use std::time::Duration;

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

fn watch_file() -> notify::Result<()> {
    let (tx, rx) = channel();
    let mut watcher: RecommendedWatcher = Watcher::new(tx, Duration::from_secs(2))?;
    watcher.watch("examples.siml", RecursiveMode::Recursive)?;
    loop {
        match rx.recv() {
            Ok(_) => run_file(),
            Err(e) => println!("watch error: {:?}", e),
        }
    }
}

fn run_file() {
    let source_file =
        fs::read_to_string("./examples.siml").expect("Failed to read the source file.");
    for line in source_file.split(";") {
        if line.trim() == "" {
            continue;
        }
        info!("{}", line);
        repl::run_term(line);
        println!();
    }
}

fn main() {
    setup_logger();
    run_file();
    thread::spawn(move || {
        watch_file().expect("File watcher failed");
    });
    repl::run();
}
