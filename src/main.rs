#[macro_use]
extern crate log;
extern crate fern;
extern crate siml;

use fern::colors::{Color, ColoredLevelConfig};
use siml::eval::Eval;
use siml::expr::Expr;
use siml::grammar;
use siml::repl::repl;
use siml::term::Term;
use siml::token;
use siml::types;

fn setup_logger() {
    let colors = ColoredLevelConfig::new()
        .info(Color::Green)
        .debug(Color::Blue);
    let _ = fern::Dispatch::new()
        .format(move |out, message, record| out.finish(format_args!("[{}] {}", colors.color(record.level()), message)))
        .level(log::LevelFilter::Info)
        // .level_for("siml::bi_types", log::LevelFilter::Debug)
        .chain(std::io::stdout())
        .apply();
}

fn run_expr(input: &str) -> Expr {
    let lexer = token::Lexer::new(input);
    let res = grammar::ExprParser::new().parse(lexer).unwrap();
    let mut e = Eval::new();
    let eval_res = e.eval(res);
    info!("EFinished: {}", eval_res.print());
    eval_res
}

fn print_ty_res(ty_res: Result<types::Type, types::TypeError>) -> String {
    match ty_res {
        Err(err) => err.print(),
        Ok(ty) => ty.print(),
    }
}

fn run_term(input: &str) -> Term {
    let lexer = token::Lexer::new(input);
    let res = grammar::ExprParser::new().parse(lexer).unwrap();
    let mut type_checker = types::TypeChecker::new();
    let ty_res = type_checker.infer_expr(&res);
    info!("TInferred: {}", print_ty_res(ty_res));
    let eval_res = Term::eval_expr(&res).unwrap();
    info!("TFinished: {}", eval_res.print());
    eval_res
}

fn batch() {
    run_expr("(\\x. x) y");
    run_expr("(\\y.(\\x. x y)) x");
    run_expr("(\\y.(\\x. x y)) ((\\l. l) x)");
    run_expr("(\\y.(\\x. x y) (\\x. x y)) x");
    run_expr("(\\x.(\\x. x y) x) k");
    println!();
    run_expr("(\\x. (\\y.(\\x. x y)) x)(\\l. l)");
    run_term("(\\x. (\\y.(\\x. x y)) x)(\\l. l)");
    println!();
    run_expr("(\\x. (\\y.(\\x. x y)) x)(\\l. l)(\\k. k)");
    run_term("(\\x. (\\y.(\\x. x y)) x)(\\l. l)(\\k. k)");
    println!();
    run_expr("(\\x. x) true");
    run_term("(\\x. x) true");
    println!();
    run_expr("(\\x. x) 100");
    run_term("(\\x. x) 100");
    println!();
    run_expr("(\\x. x) pi");
    run_term("(\\x. x) pi");
    println!();
    run_term("add ((\\x. x) 4) ((\\x. x) 4)");
    run_term("add (add 1 2) 3");
    run_term("\\f. (\\x. \\y. x) 1 (f true)");
    run_term("\\x. x x");

    run_term("(\\x. (x: Int)) true");

    // run_expr("(\\x. x x) (\\x. x x)");
    // run_term("(\\x. x x) (\\x. x x)");
}

fn main() {
    setup_logger();
    batch();
    repl();
}
