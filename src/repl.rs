use crate::bi_types;
use crate::types;
use crate::grammar;
use crate::term;
use crate::term::Term;
use crate::token;
use rustyline::error::ReadlineError;
use rustyline::Editor;

fn print_ty_res(ty_res: Result<types::Type, types::TypeError>) -> String {
    match ty_res {
        Err(err) => err.print(),
        Ok(ty) => ty.print(),
    }
}

fn print_bi_ty_res(ty_res: Result<bi_types::Type, bi_types::TypeError>) -> String {
    match ty_res {
        Err(err) => err.print(),
        Ok(ty) => ty.print(),
    }
}

fn print_eval_res(ty_res: Result<term::Term, term::EvalError>) -> String {
    match ty_res {
        Err(err) => err.print(),
        Ok(ty) => ty.print(),
    }
}

pub fn run_term(input: &str) {
    let lexer = token::Lexer::new(input);
    let res = grammar::ExprParser::new().parse(lexer);
    match res {
        Err(err) => error!("Parse failure: {:?}", err),
        Ok(res) => {
            let mut type_checker = bi_types::TypeChecker::new();
            let ty_res = type_checker.synth(&res);
            info!("BiInferred: {}", print_bi_ty_res(ty_res));
            let mut type_checker = types::TypeChecker::new();
            let ty_res = type_checker.infer_expr(&res);
            info!("Inferred: {}", print_ty_res(ty_res));
            let eval_res = Term::eval_expr(&res);
            info!("Evaled: {}", print_eval_res(eval_res));
        }
    }
}

fn run_type(input: &str) {
    let lexer = token::Lexer::new(input);
    let res = grammar::TypeParser::new().parse(lexer);
    match res {
        Err(err) => error!("Parse failure: {:?}", err),
        Ok(res) => {
            info!("{}", res.print());
            info!("Free vars: {:#?}", res.free_vars());
        }
    }
}

pub fn run() {
    // `()` can be used when no completer is required
    let mut rl = Editor::<()>::new();
    if rl.load_history("history.txt").is_err() {
        println!("No previous history.");
    }

    loop {
        let readline = rl.readline(">> ");
        match readline {
            Ok(line) => {
                rl.add_history_entry(line.as_ref());
                if line.starts_with(":ty") {
                    run_type(line.trim_start_matches(":ty "));
                } else {
                    run_term(&line);
                }
            }
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break;
            }
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }
    rl.save_history("history.txt").unwrap();
}
