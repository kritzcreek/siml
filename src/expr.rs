use crate::bi_types::Type;
use crate::pretty::render_doc_width;
use pretty::{BoxDoc, Doc};
use std::collections::HashSet;
use std::fmt;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Declaration<B> {
    Value(ValueDeclaration<B>),
    Type(TypeDeclaration),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ValueDeclaration<B> {
    pub name: String,
    pub expr: Expr<B>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TypeDeclaration {
    pub name: String,
    pub constructors: Vec<DataConstructor>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct DataConstructor {
    pub name: String,
    pub fields: Vec<Type>,
}

impl DataConstructor {
    pub fn to_doc(&self) -> Doc<BoxDoc<()>> {
        Doc::text(&self.name)
            .append(Doc::text("("))
            .append(Doc::intersperse(
                self.fields.iter().map(|ty| ty.to_doc()),
                Doc::text(",").append(Doc::space()),
            ))
            .append(Doc::text(")"))
    }
}

impl fmt::Display for DataConstructor {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", render_doc_width(self.to_doc(), 80))
    }
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

pub trait HasIdent {
    fn ident(&self) -> String;
    fn ident_with_ty(&self) -> String {
        self.ident()
    }
}

impl HasIdent for String {
    fn ident(&self) -> String {
        self.clone()
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Var {
    pub name: String,
    pub ty: Type,
}

impl HasIdent for Var {
    fn ident(&self) -> String {
        self.name.clone()
    }

    fn ident_with_ty(&self) -> String {
        format!("{} : {}", self.name, self.ty)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Case<B> {
    pub data_constructor: Dtor,
    pub binders: Vec<B>,
    pub expr: Expr<B>,
}

impl<B> Case<B> {
    pub fn map<A: Sized, F>(self, f: &F) -> Case<A>
    where
        F: Fn(B) -> A,
    {
        Case {
            data_constructor: self.data_constructor,
            binders: self.binders.into_iter().map(|binder| f(binder)).collect(),
            expr: self.expr.map(f),
        }
    }

    pub fn free_vars(&self) -> HashSet<String>
    where
        B: HasIdent,
    {
        let mut res = self.expr.free_vars();
        for binder in self.binders.iter() {
            res.remove(&binder.ident());
        }
        res
    }

    pub fn subst_mut(&mut self, var: &str, replacement: &Expr<B>)
    where
        B: HasIdent + Clone,
    {
        if !self.binders.iter().any(|binder| var == binder.ident()) {
            self.expr.subst_mut(var, replacement)
        }
    }

    pub fn to_doc(&self) -> Doc<BoxDoc<()>>
    where
        B: HasIdent,
    {
        Doc::text(&self.data_constructor.ty)
            .append(Doc::text("::"))
            .append(Doc::text(&self.data_constructor.name))
            .append(Doc::space())
            .append(Doc::intersperse(
                self.binders.iter().map(|x| Doc::text(x.ident())),
                Doc::space(),
            ))
            .append(Doc::space())
            .append(Doc::text("=>"))
            .append(Doc::space())
            .append(self.expr.to_doc())
    }
}

impl Case<Var> {
    pub fn subst_var_mut(&mut self, var: &str, replacement: &str) {
        if !self.binders.iter().any(|binder| var == binder.name) {
            self.expr.subst_var_mut(var, replacement)
        }
    }
}
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Dtor {
    pub ty: String,
    pub name: String,
}

impl fmt::Display for Dtor {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}::{}", self.ty, self.name)
    }
}

/// The AST for expressions. It's parameterized over its variable
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
    Tuple(Box<Expr<B>>, Box<Expr<B>>),
    Construction {
        dtor: Dtor,
        args: Vec<Expr<B>>,
    },
    Match {
        expr: Box<Expr<B>>,
        cases: Vec<Case<B>>,
    },
    Ann {
        expr: Box<Expr<B>>,
        ty: Type,
    },
}

pub type ParserExpr = Expr<String>;
pub type TypedExpr = Expr<Var>;

impl<B: HasIdent> fmt::Display for Expr<B> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", render_doc_width(self.to_doc(), 60))
    }
}

impl<B> Expr<B> {
    pub fn map<A: Sized, F>(self, f: &F) -> Expr<A>
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
                expr: Box::new(expr.map(f)),
                body: Box::new(body.map(f)),
            },
            Expr::App { func, arg } => Expr::App {
                func: Box::new(func.map(f)),
                arg: Box::new(arg.map(f)),
            },
            Expr::Ann { ty, expr } => Expr::Ann {
                ty,
                expr: Box::new(expr.map(f)),
            },
            Expr::Literal(lit) => Expr::Literal(lit),
            Expr::Tuple(fst, snd) => Expr::Tuple(Box::new(fst.map(f)), Box::new(snd.map(f))),
            Expr::Construction { dtor, args } => Expr::Construction {
                dtor,
                args: args.into_iter().map(|e| e.map(f)).collect(),
            },
            Expr::Match { expr, cases } => Expr::Match {
                expr: Box::new(expr.map(f)),
                cases: cases.into_iter().map(|case| case.map(f)).collect(),
            },
        }
    }

    pub fn to_doc(&self) -> Doc<BoxDoc<()>>
    where
        B: HasIdent,
    {
        self.to_doc_inner(0)
    }

    fn to_doc_inner(&self, depth: u32) -> Doc<BoxDoc<()>>
    where
        B: HasIdent,
    {
        match self {
            Expr::App { .. } => {
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
            Expr::Let { binder, expr, body } => {
                let inner = Doc::text("let")
                    .append(Doc::space())
                    .append(
                        Doc::text(binder.ident_with_ty())
                            .append(Doc::space())
                            .append(Doc::text("="))
                            .group()
                            .append(Doc::space())
                            .append(
                                expr.to_doc()
                                    .append(Doc::space())
                                    .append(Doc::text("in"))
                                    .group(),
                            )
                            .nest(2)
                            .group(),
                    )
                    .nest(2)
                    .group()
                    .append(Doc::space())
                    .append(body.to_doc_inner(0));
                if depth > 0 {
                    Doc::text("(").append(inner).append(Doc::text(")")).group()
                } else {
                    inner
                }
            }
            Expr::Literal(lit) => lit.to_doc(),
            Expr::Lambda { binder, body } => Doc::text("(\\")
                .append(Doc::text(binder.ident_with_ty()))
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
            Expr::Construction { dtor, args } => Doc::text(&dtor.ty)
                .append(Doc::text("::"))
                .append(Doc::text(&dtor.name))
                .append(Doc::text("("))
                .append(Doc::intersperse(
                    args.iter().map(|arg| arg.to_doc()),
                    Doc::text(",").append(Doc::space()),
                ))
                .append(Doc::text(")"))
                .group(),
            Expr::Match { expr, cases } => Doc::text("match")
                .append(Doc::space())
                .append(expr.to_doc())
                .append(Doc::text("{"))
                .append(Doc::intersperse(
                    cases.iter().map(|case| case.to_doc()),
                    Doc::text(","),
                ))
                .append(Doc::text("}")),
            Expr::Tuple(fst, snd) => Doc::text("(")
                .append(fst.to_doc())
                .append(Doc::text(","))
                .append(Doc::space())
                .append(snd.to_doc())
                .append(Doc::text(")"))
                .group(),
        }
    }

    pub fn subst(&self, var: &str, replacement: &Expr<B>) -> Expr<B>
    where
        B: HasIdent + Clone,
    {
        let mut expr = self.clone();
        expr.subst_mut(var, replacement);
        expr
    }

    pub fn subst_mut(&mut self, var: &str, replacement: &Expr<B>)
    where
        B: HasIdent + Clone,
    {
        match self {
            Expr::Var(v) => {
                if var == v.ident() {
                    *self = replacement.clone();
                }
            }
            Expr::Ann { expr, .. } => {
                expr.subst_mut(var, replacement);
            }
            Expr::Lambda { binder, body } => {
                if var != binder.ident() {
                    body.subst_mut(var, replacement);
                }
            }
            Expr::Let { binder, expr, body } => {
                expr.subst_mut(var, replacement);
                if var != binder.ident() {
                    body.subst_mut(var, replacement);
                }
            }
            Expr::App { func, arg } => {
                func.subst_mut(var, replacement);
                arg.subst_mut(var, replacement);
            }
            Expr::Tuple(fst, snd) => {
                fst.subst_mut(var, replacement);
                snd.subst_mut(var, replacement);
            }
            Expr::Construction { args, .. } => {
                for arg in args {
                    arg.subst_mut(var, replacement);
                }
            }
            Expr::Match { expr, cases } => {
                expr.subst_mut(var, replacement);
                for case in cases {
                    case.subst_mut(var, replacement);
                }
            }
            Expr::Literal(_) => {}
        }
    }

    pub fn collapse_lambdas(self) -> (Vec<B>, Expr<B>) {
        let mut bod = self;
        let mut args = vec![];
        loop {
            match bod {
                Expr::Lambda { binder, body } => {
                    args.push(binder);
                    bod = *body;
                }
                Expr::Ann { expr, .. } => {
                    bod = *expr;
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
        B: HasIdent,
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
            Expr::Tuple(fst, snd) => fst.free_vars().union(&snd.free_vars()).cloned().collect(),
            Expr::Literal(_) => HashSet::new(),
            Expr::Ann { expr, .. } => expr.free_vars(),
            Expr::Construction { args, .. } => {
                let mut res = HashSet::new();
                for arg in args {
                    res.extend(arg.free_vars())
                }
                res
            }
            Expr::Match { expr, cases } => {
                let mut res = expr.free_vars();
                for case in cases {
                    res.extend(case.free_vars())
                }
                res
            }
        }
    }

    pub fn int(i: i32) -> Self {
        Expr::Literal(Literal::Int(i))
    }

    pub fn bool(b: bool) -> Self {
        Expr::Literal(Literal::Bool(b))
    }

    pub fn tuple(fst: Expr<B>, snd: Expr<B>) -> Self {
        Expr::Tuple(Box::new(fst), Box::new(snd))
    }
}

impl TypedExpr {
    pub fn subst_var(mut self, var: &str, replacement: &str) -> TypedExpr {
        self.subst_var_mut(var, replacement);
        self
    }

    pub fn subst_var_mut(&mut self, var: &str, replacement: &str) {
        match self {
            Expr::Var(v) => {
                if var == v.name {
                    *self = Expr::Var(Var {
                        name: replacement.to_string(),
                        ty: v.ty.clone(),
                    })
                }
            }
            Expr::Ann { expr, .. } => {
                expr.subst_var_mut(var, replacement);
            }
            Expr::Lambda { binder, body } => {
                if var != binder.name {
                    body.subst_var_mut(var, replacement);
                }
            }
            Expr::Let { binder, expr, body } => {
                expr.subst_var_mut(var, replacement);
                if var != binder.name {
                    body.subst_var_mut(var, replacement);
                }
            }
            Expr::App { func, arg } => {
                func.subst_var_mut(&var, replacement);
                arg.subst_var_mut(var, replacement);
            }
            Expr::Tuple(fst, snd) => {
                fst.subst_var_mut(&var, replacement);
                snd.subst_var_mut(var, replacement);
            }
            Expr::Construction { args, .. } => {
                for arg in args {
                    arg.subst_var_mut(var, replacement);
                }
            }
            Expr::Match { expr, cases } => {
                expr.subst_var_mut(&var, replacement);
                for case in cases {
                    case.subst_var_mut(var, replacement);
                }
            }
            Expr::Literal(_) => {}
        }
    }
}
