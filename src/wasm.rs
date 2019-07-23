extern crate wabt;
extern crate wasmi;
use std::fs;
use wasmi::{ImportsBuilder, ModuleInstance, NopExternals};
use crate::codegen::*;
use crate::expr::Declaration;
use crate::bi_types::Type;

pub fn test_wasm(prog: Vec<(Declaration, Type)>) {
    // let contents =
    //     fs::read_to_string("src/prog.wat").expect("Something went wrong reading the file");

    let contents = Codegen::new().codegen(&prog);

    info!("[wasm] {}", contents);

    // Parse WAT (WebAssembly Text format) into wasm bytecode.
    let wasm_binary: Vec<u8> = match wabt::wat2wasm(contents) {
        Err(err) => {
            println!("{}", err);
            panic!("failed to parse wat")
        }
        Ok(wasm) => wasm,
    };
    let wat_again = wabt::wasm2wat(&wasm_binary).unwrap();

    // Load wasm binary and prepare it for instantiation.
    let module = wasmi::Module::from_buffer(&wasm_binary).expect("failed to load wasm");

    // Instantiate a module with empty imports and
    // assert that there is no `start` function.
    let instance = ModuleInstance::new(&module, &ImportsBuilder::default())
        .expect("failed to instantiate wasm module")
        .assert_no_start();

    println!(
        "{:?}",
        instance
            .invoke_export("test", &[], &mut NopExternals,)
            .expect("failed to execute export")
    );
}
