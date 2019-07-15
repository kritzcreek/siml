use crate::bi_types::Type;
use crate::expr::{Expr, Literal};
use crate::grammar::{ExprParser, BiTypeParser};
use crate::token::Lexer;
use pretty::{BoxDoc, Doc};

fn expr(input: &str) -> Expr {
    let lexer = Lexer::new(input);
    let res = ExprParser::new().parse(lexer);
    match res {
        Err(err) => panic!("{:?}", err),
        Ok(ty) => ty,
    }
}

fn ty(input: &str) -> Type {
    let lexer = Lexer::new(input);
    let res = BiTypeParser::new().parse(lexer);
    match res {
        Err(err) => panic!("{:?}", err),
        Ok(ty) => ty,
    }
}

fn lit_doc(lit: &Literal) -> Doc<BoxDoc<()>> {
    match lit {
        Literal::Int(i) => Doc::text(i.to_string()),
        Literal::Bool(b) => Doc::text(b.to_string()),
    }
}

fn ty_doc(ty: &Type, depth: u32) -> Doc<BoxDoc<()>> {
    match ty {
        Type::Constructor(c) => Doc::text(c),
        Type::Existential(evar) => Doc::text(evar),
        Type::Var(v) => Doc::text(v),
        Type::App {
            type_constructor,
            arguments,
        } => Doc::text("app"),
        Type::Poly { vars, ty } => Doc::text("forall ")
            .append(Doc::intersperse(
                vars.into_iter().map(|x| Doc::text(x)),
                Doc::space(),
            ))
            .append(Doc::text("."))
            .append(Doc::space())
            .append(ty_doc(ty, 0))
            .group(),
        Type::Fun { arg, result } => {
            let inner = ty_doc(arg, 1)
                .append(Doc::space())
                .append(Doc::text("->"))
                .append(Doc::space())
                .append(ty_doc(result, 0))
                .group();
            if depth > 0 {
                Doc::text("(")
                    .append(inner.nest(2).group())
                    .append(Doc::text(")"))
            } else {
                inner
            }
        }
    }
}

pub fn to_doc(expr: &Expr, depth: u32) -> Doc<BoxDoc<()>> {
    match expr {
        Expr::App { func, arg } => {
            let inner = to_doc(func, 0)
                .append(Doc::space())
                .append(to_doc(arg, depth + 1));
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
                    .append(to_doc(expr, 0))
                    .group(),
            )
            .append(Doc::space())
            .append(Doc::text("in"))
            .append(Doc::space())
            .append(to_doc(body, 0))
            .group(),
        Expr::Literal(lit) => lit_doc(lit),
        Expr::Lambda { binder, body } => Doc::text("(\\")
            .append(Doc::text(binder))
            .append(Doc::text("."))
            .append(Doc::space())
            .append(to_doc(body, 0).nest(2))
            .append(Doc::text(")"))
            .group(),
        Expr::Var(v) => Doc::text(v),
        Expr::Ann { expr, ty } => Doc::text("(")
            .append(to_doc(expr, 0))
            .append(Doc::space())
            .append(Doc::text(":"))
            .append(Doc::space())
            .append(ty_doc(ty, 0))
            .append(Doc::text(")"))
            .group(),
    }
}

pub fn to_pretty(expr: &Expr, width: usize) -> String {
    let mut w = Vec::new();
    to_doc(expr, 0).render(width, &mut w).unwrap();
    String::from_utf8(w).unwrap()
}

pub fn to_pretty_ty(ty: &Type, width: usize) -> String {
    let mut w = Vec::new();
    ty_doc(ty, 0).render(width, &mut w).unwrap();
    String::from_utf8(w).unwrap()
}

pub fn run() {
    let e = expr("let id = (\\x. x : a -> a) in id (\\func. func (g (well 12 true)))");
    let t = ty("forall a b. a -> b");
    println!("{}", to_pretty(&e, 50));
    println!("{}", to_pretty_ty(&t, 50));
}
