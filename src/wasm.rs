extern crate wabt;
extern crate wasmi;
use crate::bi_types::Type;
use crate::codegen::*;
use crate::expr::{Declaration, Var};
use wasmi::{ImportsBuilder, ModuleInstance, NopExternals};

pub fn test_wasm(prog: Vec<(Declaration<Var>, Type)>) {
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
            .invoke_export("main", &[], &mut NopExternals,)
            .expect("failed to execute export")
    );
}
