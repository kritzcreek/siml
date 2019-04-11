use rustyline::error::ReadlineError;
use rustyline::Editor;
use crate::token;
use crate::grammar;
use crate::term::Term;

fn run_term(input: &str) -> Term {
    let lexer = token::Lexer::new(input);
    let res = grammar::ExprParser::new().parse(lexer).unwrap();
    let eval_res = Term::eval_expr(&res);
    info!("TFinished: {}", eval_res.print());
    eval_res
}

pub fn repl() {
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
                run_term(&line);
            },
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break
            },
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break
            },
            Err(err) => {
                println!("Error: {:?}", err);
                break
            }
        }
    }
    rl.save_history("history.txt").unwrap();
}
