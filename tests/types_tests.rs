use pretty_assertions::assert_eq;
use siml::expr::Expr;
use siml::grammar::{ExprParser, TypeParser};
use siml::token::Lexer;
use siml::types::{Scheme, Substitution, Type, TypeChecker};

fn ty(input: &str) -> Type {
    let lexer = Lexer::new(input);
    let res = TypeParser::new().parse(lexer);
    match res {
        Err(err) => panic!("{:?}", err),
        Ok(ty) => ty,
    }
}

fn expr(input: &str) -> Expr {
    let lexer = Lexer::new(input);
    let res = ExprParser::new().parse(lexer);
    match res {
        Err(err) => panic!("{:?}", err),
        Ok(ty) => ty,
    }
}

fn test_ty_eq_subst(ty1: Type, ty2: Type, subst: Substitution) {
    assert_eq!(ty1.generalize(&subst), ty2.generalize(&subst))
}

fn test_ty_eq(ty1: Type, ty2: Type) {
    test_ty_eq_subst(ty1, ty2, Substitution::new())
}

fn test_infer(expr: Expr, ty: Type) {
    test_ty_eq(TypeChecker::new().infer_expr(&expr).unwrap(), ty)
}

#[test]
fn it_infers_int_literals() {
    test_infer(expr("1"), ty("Int"));
    test_infer(expr("true"), ty("Bool"));
    test_infer(expr("\\x. x"), ty("a -> a"));
}

#[test]
fn it_generalizes() {
    assert_eq!(
        ty("a -> b").generalize(&Substitution::new()),
        Scheme {
            vars: vec!["gen0".to_string(), "gen1".to_string()],
            ty: ty("gen0 -> gen1")
        }
    );
}

#[test]
fn it_generalizes_while_ignoring_vars_in_the_subst() {
    assert_eq!(
        ty("a -> b").generalize(&Substitution::singleton("u1".to_string(), ty("a"))),
        Scheme {
            vars: vec!["gen0".to_string()],
            ty: ty("a -> gen0")
        }
    );
}

#[test]
fn it_figures_out_test_equality() {
    test_ty_eq(ty("a -> b"), ty("b -> c"));

    test_ty_eq_subst(
        ty("a -> b"),
        ty("a -> c"),
        Substitution::singleton("a".to_string(), ty("Int")),
    );
}

#[test]
fn it_prints_schemes() {
    let scheme = Scheme {
        vars: vec!["a".to_string()],
        ty: ty("a -> a"),
    };
    assert_eq!(scheme.print(), "forall a. a -> a".to_string());

    let scheme = Scheme {
        vars: vec!["a".to_string(), "b".to_string()],
        ty: ty("a -> b"),
    };
    assert_eq!(scheme.print(), "forall a b. a -> b".to_string());

    let scheme = Scheme {
        vars: vec![],
        ty: ty("a -> a"),
    };
    assert_eq!(scheme.print(), "a -> a".to_string());
}
