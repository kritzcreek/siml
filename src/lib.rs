#[macro_use]
extern crate log;
extern crate rustyline;

pub mod bi_types;
pub mod types;
pub mod codegen;
pub mod expr;
pub mod grammar;
pub mod pipeline;
pub mod pretty;
pub mod repl;
pub mod term;
pub mod token;
pub mod wasm;
// pub mod ir; // implement closure conversion here
