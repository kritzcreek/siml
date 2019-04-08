extern crate siml;
use siml::token;
use siml::grammar;

fn parse_expr(input: &str) {
    let lexer = token::Lexer::new(input);
    let res = grammar::ExprParser::new().parse(lexer);
    println!("{:?}", &res);
    println!("{:?}", res.map(|e| e.print()));
}

fn main() {
    parse_expr("x");
    parse_expr("\\y. x y z");
    parse_expr("\\y. x (\\z.z)");
    parse_expr("x (y z)");
    parse_expr("(x x) (y z)");
}
