use crate::bi_types::Type;
use crate::utils::parens_if;
use std::collections::HashSet;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Literal {
    Int(i32),
    Bool(bool),
}

impl Literal {
    pub fn print(&self) -> String {
        match self {
            Literal::Int(i) => i.to_string(),
            Literal::Bool(b) => b.to_string(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    App { func: Box<Expr>, arg: Box<Expr> },
    Lambda { binder: String, body: Box<Expr> },
    Var(String),
    Literal(Literal),
    Ann { expr: Box<Expr>, ty: Type },
}

impl Expr {
    pub fn print(&self) -> String {
        self.print_inner(0)
    }

    fn print_inner(&self, depth: u32) -> String {
        match self {
            Expr::Var(s) => s.clone(),
            Expr::Lambda { binder, body } => format!("(\\{}. {})", binder, body.print()),
            Expr::App { func, arg } => parens_if(
                depth > 0,
                format!("{} {}", func.print_inner(depth), arg.print_inner(depth + 1)),
            ),
            Expr::Literal(lit) => lit.print(),
            Expr::Ann { expr, ty } => format!("({} : {})", expr.print(), ty.print()),
        }
    }

    pub fn free_vars(&self) -> HashSet<&String> {
        match self {
            Expr::Var(s) => {
                let mut res = HashSet::new();
                res.insert(s);
                res
            }
            Expr::Lambda { binder, body } => {
                let mut res = body.free_vars();
                res.remove(binder);
                res
            }
            Expr::App { func, arg } => func.free_vars().union(&arg.free_vars()).cloned().collect(),
            Expr::Literal(_) => HashSet::new(),
            Expr::Ann { expr, ty: _ } => expr.free_vars(),
        }
    }
}
