use crate::bi_types::Type;
use crate::pretty::render_doc_width;
use pretty::{BoxDoc, Doc};
use std::collections::HashSet;
use std::fmt;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Declaration {
    Value { name: String, expr: Expr<String> },
    // Type {
    //     name: String,
    //     constructors: Vec<DataConstructor>,
    // },
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

pub trait RenderIdent {
    fn ident(&self) -> String;
}

impl RenderIdent for String {
    fn ident(&self) -> String {
        self.clone()
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Var {
    name: String,
    ty: Type,
}

impl RenderIdent for Var {
    fn ident(&self) -> String {
        self.name.clone()
    }
}

/// The AST for expressions. It's parameterized over it's variable
/// names. This is done so the type checker can insert type
/// information on every variable.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr<B> {
    App {
        func: Box<Expr<B>>,
        arg: Box<Expr<B>>,
    },
    Lambda {
        binder: B,
        body: Box<Expr<B>>,
    },
    Let {
        binder: B,
        expr: Box<Expr<B>>,
        body: Box<Expr<B>>,
    },
    Var(B),
    Literal(Literal),
    Ann {
        expr: Box<Expr<B>>,
        ty: Type,
    },
}

pub type ParserExpr = Expr<String>;
pub type TypedExpr = Expr<Var>;

impl<B: RenderIdent> fmt::Display for Expr<B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", render_doc_width(self.to_doc(), 60))
    }
}

impl<B> Expr<B> {
    pub fn map<A: Sized, F>(self, f: F) -> Expr<A>
    where
        F: Fn(B) -> A,
    {
        match self {
            Expr::Var(v) => Expr::Var(f(v)),
            Expr::Lambda { binder, body } => Expr::Lambda {
                binder: f(binder),
                body: Box::new(body.map(f)),
            },
            Expr::Let { binder, expr, body } => Expr::Let {
                binder: f(binder),
                expr: Box::new(expr.map(&f)),
                body: Box::new(body.map(f)),
            },
            Expr::App { func, arg } => Expr::App {
                func: Box::new(func.map(&f)),
                arg: Box::new(arg.map(f)),
            },
            Expr::Ann { ty, expr } => Expr::Ann {
                ty,
                expr: Box::new(expr.map(f)),
            },
            Expr::Literal(lit) => Expr::Literal(lit),
        }
    }

    pub fn to_doc(&self) -> Doc<BoxDoc<()>>
    where
        B: RenderIdent,
    {
        self.to_doc_inner(0)
    }

    fn to_doc_inner(&self, depth: u32) -> Doc<BoxDoc<()>>
    where
        B: RenderIdent,
    {
        match self {
            Expr::App { func: _, arg: _ } => {
                let inner = Doc::intersperse(
                    self.unfold_apps().into_iter().map(|x| x.to_doc_inner(1)),
                    Doc::space(),
                )
                .nest(2)
                .group();
                if depth > 0 {
                    Doc::text("(").append(inner).append(Doc::text(")")).group()
                } else {
                    inner
                }
            }
            Expr::Let { binder, expr, body } => Doc::text("let")
                .append(Doc::space())
                .append(
                    Doc::text(binder.ident())
                        .append(Doc::space())
                        .append(Doc::text("="))
                        .group()
                        .append(Doc::space())
                        .append(expr.to_doc())
                        .nest(2)
                        .group(),
                )
                .group()
                .nest(2)
                .append(Doc::space())
                .append(
                    Doc::text("in")
                        .append(Doc::space())
                        .append(body.to_doc_inner(0))
                        .nest(2),
                )
                .group(),
            Expr::Literal(lit) => lit.to_doc(),
            Expr::Lambda { binder, body } => Doc::text("(\\")
                .append(Doc::text(binder.ident()))
                .append(Doc::text("."))
                .append(Doc::space())
                .append(body.to_doc().nest(2))
                .append(Doc::text(")"))
                .group(),
            Expr::Var(v) => Doc::text(v.ident()),
            Expr::Ann { expr, ty } => Doc::text("(")
                .append(expr.to_doc())
                .append(Doc::space())
                .append(
                    Doc::text(":")
                        .append(Doc::space())
                        .append(ty.to_doc())
                        .nest(2)
                        .group(),
                )
                .append(Doc::text(")"))
                .group(),
        }
    }

    pub fn subst<F>(&self, p: F, replacement: &Expr<B>) -> Expr<B>
    where
        F: Fn(&B) -> bool,
        B: Clone,
    {
        let mut expr = self.clone();
        expr.subst_mut(p, replacement);
        expr
    }

    pub fn subst_mut<F>(&mut self, p: F, replacement: &Expr<B>)
    where
        F: Fn(&B) -> bool,
        B: Clone,
    {
        match self {
            Expr::Var(v) if p(v) => {
                *self = replacement.clone();
            }
            Expr::Ann { expr, .. } => {
                expr.subst_mut(p, replacement);
            }
            Expr::Lambda { binder, body } if p(binder) => {
                body.subst_mut(p, replacement);
            }
            Expr::Let { binder, expr, body } => {
                expr.subst_mut(&p, replacement);
                if p(binder) {
                    body.subst_mut(p, replacement);
                }
            }
            Expr::App { func, arg } => {
                func.subst_mut(&p, replacement);
                arg.subst_mut(p, replacement);
            }
            _ => {}
        }
    }

    pub fn collapse_lambdas(&self) -> (Vec<&B>, &Expr<B>) {
        let mut bod = self;
        let mut args = vec![];
        loop {
            match bod {
                Expr::Lambda { binder, body } => {
                    args.push(binder);
                    bod = body;
                }
                Expr::Ann { ty: _, expr } => {
                    bod = expr;
                }
                _ => break,
            }
        }
        (args, bod)
    }

    fn unfold_apps(&self) -> Vec<&Self> {
        match self {
            Expr::App { func, arg } => {
                let mut res = func.unfold_apps();
                res.push(arg);
                res
            }
            _ => vec![self],
        }
    }

    pub fn free_vars(&self) -> HashSet<String>
    where
        B: RenderIdent,
    {
        match self {
            Expr::Var(s) => {
                let mut res = HashSet::new();
                res.insert(s.ident());
                res
            }
            Expr::Lambda { binder, body } => {
                let mut res = body.free_vars();
                res.remove(&binder.ident());
                res
            }
            Expr::Let { binder, expr, body } => {
                let mut res = expr.free_vars();
                let mut body_vars = body.free_vars();
                body_vars.remove(&binder.ident());
                res.extend(body_vars);
                res
            }
            Expr::App { func, arg } => func.free_vars().union(&arg.free_vars()).cloned().collect(),
            Expr::Literal(_) => HashSet::new(),
            Expr::Ann { expr, ty: _ } => expr.free_vars(),
        }
    }
}
