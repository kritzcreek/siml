#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    App { func: Box<Expr>, arg: Box<Expr> },
    Lambda { binder: String, body: Box<Expr> },
    Var(String),
}

impl Expr {
    pub fn print(&self) -> String {
        self.print_inner(0)
    }

    fn print_inner(&self, depth: u32) -> String {
        match self {
            Expr::Var(s) => s.clone(),
            Expr::Lambda {binder, body} =>
                format!("(\\{}. {})", binder, body.print()),
            Expr::App {func, arg} => {
                parens_if(depth>0, format!("{} {}", func.print_inner(depth), arg.print_inner(depth+1)))
            }
        }
    }

}

fn parens_if(p: bool, s: String) -> String {
    if p {
        format!("({})", s)
    } else {
        s
    }
}