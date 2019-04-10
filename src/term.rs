use crate::expr::Expr;
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
        }
    }

    pub fn eval_expr(expr: &Expr) -> Term {
        let mut initial_env = HashMap::new();
        // initial_env.insert("defined".to_string(), Term::Var("k".to_string()));
        Term::eval(&initial_env, Term::from_expr(expr))
    }

    fn eval(env: &Env, term: Term) -> Term {
        match term {
            Term::Var(s) => match env.get(&s) {
                Some(t) => t.clone(),
                None => panic!("Unknown variable: {}", s),
            },
            Term::Lambda { binder, body } => Term::Closure {
                binder,
                body,
                env: env.clone(),
            },
            Term::Closure { .. } => term,
            Term::App { func, arg } => match Term::eval(env, *func) {
                Term::Closure {
                    binder,
                    body,
                    env: closed_env,
                } => {
                    let evaled_arg = Term::eval(&env, *arg);
                    let mut new_env = env.clone();
                    new_env.extend(closed_env);
                    new_env.insert(binder, evaled_arg);
                    Term::eval(&new_env, *body)
                }
                _ => panic!("Can't apply a non-lambda"),
            },
        }
    }

    pub fn print(&self) -> String {
        self.print_inner(0)
    }

    fn print_inner(&self, depth: u32) -> String {
        match self {
            Term::Var(s) => s.clone(),
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
