use crate::expr::{Expr, Literal};
use std::collections::HashMap;

type Env = HashMap<String, Term>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Term {
    App {
        func: Box<Term>,
        arg: Box<Term>,
    },
    Lambda {
        binder: String,
        body: Box<Term>,
    },
    Var(String),
    Closure {
        binder: String,
        body: Box<Term>,
        env: Env,
    },
    Literal(Literal),
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum EvalError {
    UnknownVar(String),
    ApplyingNonLambda(Term),
}

impl EvalError {
    pub fn print(&self) -> String {
        match self {
            EvalError::UnknownVar(var) => format!("Unknown variable: {}", var),
            EvalError::ApplyingNonLambda(term) => format!("{} is not a function", term.print()),
        }
    }
}

fn initial_env() -> Env {
    let mut env = HashMap::new();
    let builtin_add: Term = Term::Closure {
        binder: "#add1".to_string(),
        env: HashMap::new(),
        body: Box::new(Term::Lambda {
            binder: "#add2".to_string(),
            body: Box::new(Term::Var("#add".to_string())),
        }),
    };
    env.insert("pi".to_string(), Term::Literal(Literal::Int(3)));
    env.insert("add".to_string(), builtin_add);
    env
}

impl Term {
    fn from_expr(expr: &Expr) -> Term {
        match expr {
            Expr::App { func, arg } => Term::App {
                func: Box::new(Term::from_expr(func)),
                arg: Box::new(Term::from_expr(arg)),
            },
            Expr::Lambda { binder, body } => Term::Lambda {
                binder: binder.clone(),
                body: Box::new(Term::from_expr(body)),
            },
            Expr::Var(s) => Term::Var(s.clone()),
            Expr::Literal(lit) => Term::Literal(lit.clone()),
        }
    }

    pub fn eval_expr(expr: &Expr) -> Result<Term, EvalError> {
        Term::eval(&initial_env(), Term::from_expr(expr))
    }

    fn eval(env: &Env, term: Term) -> Result<Term, EvalError> {
        match term {
            Term::Var(s) => match s.as_ref() {
                "#add" => match (env.get("#add1"), env.get("#add2")) {
                    (
                        Some(Term::Literal(Literal::Int(i1))),
                        Some(Term::Literal(Literal::Int(i2))),
                    ) => Ok(Term::Literal(Literal::Int(i1 + i2))),
                    (e1, e2) => panic!("Attempting to add non-numbers: {:?} {:?}", e1, e2),
                },
                _ => match env.get(&s) {
                    Some(t) => Ok(t.clone()),
                    None => Err(EvalError::UnknownVar(s)),
                },
            },
            Term::Lambda { binder, body } => Ok(Term::Closure {
                binder,
                body,
                env: env.clone(),
            }),
            Term::Closure { .. } => Ok(term),
            Term::Literal(_) => Ok(term),
            Term::App { func, arg } => match Term::eval(env, *func)? {
                Term::Closure {
                    binder,
                    body,
                    env: closed_env,
                } => {
                    let evaled_arg = Term::eval(&env, *arg)?;
                    let mut new_env = env.clone();
                    new_env.extend(closed_env);
                    new_env.insert(binder, evaled_arg);
                    Term::eval(&new_env, *body)
                }
                t => Err(EvalError::ApplyingNonLambda(t)),
            },
        }
    }

    pub fn print(&self) -> String {
        self.print_inner(0)
    }

    fn print_inner(&self, depth: u32) -> String {
        match self {
            Term::Var(s) => s.clone(),
            Term::Literal(lit) => lit.print(),
            Term::Lambda { binder, body } => format!("(\\{}. {})", binder, body.print()),
            Term::Closure {
                binder,
                body,
                env: _,
            } => format!("(\\{}. {})", binder, body.print()),
            Term::App { func, arg } => parens_if(
                depth > 0,
                format!("{} {}", func.print_inner(depth), arg.print_inner(depth + 1)),
            ),
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
