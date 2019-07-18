use crate::bi_types::Type;
use crate::pretty::{render_doc, parens_if};
use pretty::{BoxDoc, Doc};
use std::collections::HashSet;
use std::fmt;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Declaration {
    Value(Expr),
    Type {
        name: String,
        constructors: Vec<DataConstructor>,
    },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataConstructor {
    pub name: String,
}

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

    pub fn to_doc(&self) -> Doc<BoxDoc<()>> {
        match self {
            Literal::Int(i) => Doc::text(i.to_string()),
            Literal::Bool(b) => Doc::text(b.to_string()),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    App {
        func: Box<Expr>,
        arg: Box<Expr>,
    },
    Lambda {
        binder: String,
        body: Box<Expr>,
    },
    Let {
        binder: String,
        expr: Box<Expr>,
        body: Box<Expr>,
    },
    Var(String),
    Literal(Literal),
    Ann {
        expr: Box<Expr>,
        ty: Type,
    },
}

impl fmt::Display for Expr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", render_doc(self.to_doc()))
    }
}

impl Expr {
    pub fn print(&self) -> String {
        self.print_inner(0)
    }

    fn print_inner(&self, depth: u32) -> String {
        match self {
            Expr::Var(s) => s.clone(),
            Expr::Lambda { binder, body } => format!("(\\{}. {})", binder, body),
            Expr::Let { binder, expr, body } => format!("let {} = {} in {}", binder, expr, body),
            Expr::App { func, arg } => parens_if(
                depth > 0,
                format!("{} {}", func.print_inner(depth), arg.print_inner(depth + 1)),
            ),
            Expr::Literal(lit) => lit.print(),
            Expr::Ann { expr, ty } => format!("({} : {})", expr, ty),
        }
    }

    pub fn subst(&self, var: &String, replacement: &Expr) -> Expr {
        let mut expr = self.clone();
        expr.subst_mut(var, replacement);
        expr
    }

    pub fn subst_mut(&mut self, var: &String, replacement: &Expr) {
        match self {
            Expr::Var(v) if v == var => {
                *self = replacement.clone();
            }
            Expr::Ann { expr, .. } => {
                expr.subst_mut(var, replacement);
            }
            Expr::Lambda { binder, body } if binder != var => {
                body.subst_mut(var, replacement);
            }
            Expr::Let { binder, expr, body } => {
                expr.subst_mut(var, replacement);
                if binder != var {
                    body.subst_mut(var, replacement);
                }
            }
            Expr::App { func, arg } => {
                func.subst_mut(var, replacement);
                arg.subst_mut(var, replacement);
            }
            _ => {}
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
            Expr::Let { binder, expr, body } => {
                let mut res = expr.free_vars();
                let mut body_vars = body.free_vars();
                body_vars.remove(binder);
                res.extend(body_vars);
                res
            }
            Expr::App { func, arg } => func.free_vars().union(&arg.free_vars()).cloned().collect(),
            Expr::Literal(_) => HashSet::new(),
            Expr::Ann { expr, ty: _ } => expr.free_vars(),
        }
    }

    pub fn to_doc(&self) -> Doc<BoxDoc<()>> {
        self.to_doc_inner(0)
    }

    fn to_doc_inner(&self, depth: u32) -> Doc<BoxDoc<()>> {
        match self {
            Expr::App { func, arg } => {
                let inner = func.to_doc()
                    .append(Doc::space())
                    .append(arg.to_doc_inner(depth + 1));
                if depth > 0 {
                    Doc::text("(")
                        .append(inner.nest(2).group())
                        .append(Doc::text(")"))
                } else {
                    inner
                }
            }
            Expr::Let { binder, expr, body } => Doc::text("let")
                .append(Doc::space())
                .nest(2)
                .append(
                    Doc::text(binder)
                        .append(Doc::space())
                        .append(Doc::text("="))
                        .append(Doc::space())
                        .append(expr.to_doc())
                        .group(),
                )
                .append(Doc::space())
                .append(Doc::text("in"))
                .append(Doc::space())
                .append(body.to_doc_inner( 0))
                .group(),
            Expr::Literal(lit) => lit.to_doc(),
            Expr::Lambda { binder, body } => Doc::text("(\\")
                .append(Doc::text(binder))
                .append(Doc::text("."))
                .append(Doc::space())
                .append(body.to_doc().nest(2))
                .append(Doc::text(")"))
                .group(),
            Expr::Var(v) => Doc::text(v),
            Expr::Ann { expr, ty } => Doc::text("(")
                .append(expr.to_doc())
                .append(Doc::space())
                .append(Doc::text(":"))
                .append(Doc::space())
                .append(ty.to_doc())
                .append(Doc::text(")"))
                .group(),
        }
    }
}
