extern crate wabt;
extern crate wasmi;
use wasmi::{ImportsBuilder, ModuleInstance, NopExternals};

pub fn run_wasm(prog: String) -> Result<Option<wasmi::RuntimeValue>, wasmi::Error> {
    // Parse WAT (WebAssembly Text format) into wasm bytecode.
    let wasm_binary: Vec<u8> =
        wabt::wat2wasm(prog).map_err(|err| wasmi::Error::Validation(format!("{}", err)))?;

    // Load wasm binary and prepare it for instantiation.
    let module = wasmi::Module::from_buffer(&wasm_binary)?;

    // Instantiate a module with empty imports
    let instance = ModuleInstance::new(&module, &ImportsBuilder::default())?;

    // Assert that there is no `start` function.
    instance
        .assert_no_start()
        .invoke_export("main", &[], &mut NopExternals)
}

pub fn pretty_result(res: Result<Option<wasmi::RuntimeValue>, wasmi::Error>) -> String {
    match res {
        Err(err) => format!("{}", err),
        Ok(None) => "Failed to evaluate wasm".to_string(),
        Ok(Some(val)) => format!("{:?}", val),
    }
}
