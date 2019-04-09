extern crate siml;
use siml::token;
use siml::grammar;
use siml::ast::Expr;

fn parse_expr(input: &str) -> Expr {
    let lexer = token::Lexer::new(input);
    let res = grammar::ExprParser::new().parse(lexer);
    println!("{:?}", &res);
    // println!("{:?}", &res.map(|e| e.print()));
    res.unwrap()
}

fn main() {
    parse_expr("x");
    parse_expr("\\y. x y z");
    parse_expr("\\y. x (\\z.z)");
    parse_expr("x (y z)");
    parse_expr("(x x) (y z)");
    let expr = parse_expr("\\z. (x x) (y z)");
    println!("{}", expr.substitute(&"x".to_string(), &"y".to_string()).print())
}
