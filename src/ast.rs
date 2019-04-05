#[derive(Debug, PartialEq, Eq)]
pub enum Expr {
    App { func: Box<Expr>, args: Vec<Expr> },
    Lambda { binder: String, body: Box<Expr> },
    Var(String),
}
