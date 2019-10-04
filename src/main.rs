extern crate fern;
extern crate log;
extern crate notify;
extern crate siml;

use fern::colors::{Color, ColoredLevelConfig};
use notify::DebouncedEvent;
use notify::{RecommendedWatcher, RecursiveMode, Watcher};
use siml::pipeline;
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
    watcher.watch("prog.siml", RecursiveMode::Recursive)?;
    loop {
        match rx.recv() {
            Ok(DebouncedEvent::Write(_)) => run_file(),
            Ok(DebouncedEvent::Create(_)) => run_file(),
            Ok(_ev) => {
                // Uncomment if you want to debug watcher failures
                // println!("{:?}", _ev)
            }
            Err(e) => println!("watch error: {:?}", e),
        }
    }
}
fn watch_wasm_file() -> notify::Result<()> {
    let (tx, rx) = channel();
    let mut watcher: RecommendedWatcher = Watcher::new(tx, Duration::from_secs(2))?;
    watcher.watch("wasm_prog.siml", RecursiveMode::Recursive)?;
    loop {
        match rx.recv() {
            Ok(DebouncedEvent::Write(_)) => run_wasm_file(),
            Ok(DebouncedEvent::Create(_)) => run_wasm_file(),
            Ok(_ev) => {
                // Uncomment if you want to debug watcher failures
                // println!("{:?}", _ev)
            }
            Err(e) => println!("watch error: {:?}", e),
        }
    }
}

fn run_file() {
    let source_file = fs::read_to_string("prog.siml").expect("Failed to read the source file.");
    let res = pipeline::run_program(&source_file, pipeline::Backend::Term);
    println!("{:?}", res)
}

fn run_wasm_file() {
    let source_file =
        fs::read_to_string("wasm_prog.siml").expect("Failed to read the source file.");
    let res = pipeline::run_program(&source_file, pipeline::Backend::WasmRun);
    println!("{:?}", res)
}

fn main() {
    let use_wasm = true;
    setup_logger();
    if use_wasm {
        run_wasm_file();
        thread::spawn(move || {
            watch_wasm_file().expect("WASM File watcher failed");
        });
    } else {
        run_file();
        thread::spawn(move || {
            watch_file().expect("File watcher failed");
        });
    }

    loop {
        thread::sleep(Duration::from_secs(2))
    }
    // repl::run();
}
