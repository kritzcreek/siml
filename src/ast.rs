#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    App { func: Box<Expr>, arg: Box<Expr> },
    Lambda { binder: String, body: Box<Expr> },
    Var(String),
}
