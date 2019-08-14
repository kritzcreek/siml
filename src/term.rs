use crate::expr::{Declaration, Expr, HasIdent, Literal};
use std::collections::HashMap;
use std::fmt;

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
    Pack {
        tag: u32,
        arity: u32,
        values: Vec<Term>,
    },
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.print())
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum EvalError {
    UnknownVar(String),
    ApplyingNonLambda(Term),
    AddingNonNumbers(Term, Term),
    ProjectingFst(Term),
}

impl EvalError {
    pub fn print(&self) -> String {
        match self {
            EvalError::UnknownVar(var) => format!("Unknown variable: {}", var),
            EvalError::ApplyingNonLambda(term) => format!("{} is not a function", term),
            EvalError::AddingNonNumbers(t1, t2) => {
                format!("Attempting to add non-ints: {} + {}", t1, t2)
            }
            EvalError::ProjectingFst(term) => {
                format!("Attempting to project from a non-tuple: {}", term)
            }
        }
    }
}

fn initial_env() -> Env {
    HashMap::new()
}

impl Term {
    fn from_expr<B: HasIdent>(expr: &Expr<B>) -> Term {
        match expr {
            Expr::App { func, arg } => Term::App {
                func: Box::new(Term::from_expr(func)),
                arg: Box::new(Term::from_expr(arg)),
            },
            Expr::Lambda { binder, body } => Term::Lambda {
                binder: binder.ident(),
                body: Box::new(Term::from_expr(body)),
            },
            Expr::Let { binder, expr, body } => Term::App {
                func: Box::new(Term::Lambda {
                    binder: binder.ident(),
                    body: Box::new(Term::from_expr(body)),
                }),
                arg: Box::new(Term::from_expr(expr)),
            },
            Expr::Var(s) => Term::Var(s.ident()),
            Expr::Literal(lit) => Term::Literal(lit.clone()),
            Expr::Ann { expr, ty: _ } => Term::from_expr(expr),
            Expr::Tuple(fst, snd) => Term::Pack {
                tag: 1,
                arity: 2,
                values: vec![Term::from_expr(fst), Term::from_expr(snd)],
            },
        }
    }

    pub fn eval_expr<B: HasIdent>(expr: &Expr<B>) -> Result<Term, EvalError> {
        Term::eval(&initial_env(), Term::from_expr(expr))
    }

    pub fn eval_prog<B: HasIdent>(prog: Vec<Declaration<B>>) -> Result<Term, EvalError> {
        let mut env = initial_env();
        let mut res = Term::Var("nuttin".to_string());
        for Declaration::Value { name, expr } in prog {
            res = Term::eval(&env, Term::from_expr(&expr))?;
            env.insert(name, res.clone());
        }
        Ok(res)
    }

    fn eval(env: &Env, term: Term) -> Result<Term, EvalError> {
        match term {
            Term::Var(s) => match s.as_ref() {
                "primadd" => match (env.get("x"), env.get("y")) {
                    (
                        Some(Term::Literal(Literal::Int(i1))),
                        Some(Term::Literal(Literal::Int(i2))),
                    ) => Ok(Term::Literal(Literal::Int(i1 + i2))),
                    (Some(term1), Some(term2)) => {
                        panic!("Attempting to add non-numbers: {:?} {:?}", term1, term2)
                    }
                    (_, _) => panic!("Bad implementation for add"),
                },
                "primfst" => match env.get("x") {
                    Some(Term::Pack {
                        tag: _,
                        arity: _,
                        values,
                    }) => Ok(values[0].clone()),
                    Some(term) => Err(EvalError::ProjectingFst(term.clone())),
                    None => panic!("Bad implementation for fst"),
                },
                "primsnd" => match env.get("x") {
                    Some(Term::Pack {
                        tag: _,
                        arity: _,
                        values,
                    }) => Ok(values[1].clone()),
                    Some(term) => Err(EvalError::ProjectingFst(term.clone())),
                    None => panic!("Bad implementation for fst"),
                },
                "primtuple" => match (env.get("x"), env.get("y")) {
                    (Some(t1), Some(t2)) => Ok(Term::Pack {
                        tag: 1,
                        arity: 2,
                        values: vec![t1.clone(), t2.clone()],
                    }),
                    _ => panic!("Bad implementation for fst"),
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
            Term::Pack { tag, arity, values } => {
                let mut evaled_values = vec![];
                for t in values {
                    let evaled_t = Term::eval(env, t.clone())?;
                    evaled_values.push(evaled_t);
                }
                Ok(Term::Pack {
                    tag,
                    arity,
                    values: evaled_values,
                })
            }
        }
    }

    pub fn print(&self) -> String {
        self.print_inner(0)
    }

    fn print_inner(&self, depth: u32) -> String {
        match self {
            Term::Var(s) => s.clone(),
            Term::Literal(lit) => lit.print(),
            Term::Lambda { binder, body } => format!("(\\{}. {})", binder, body),
            Term::Closure {
                binder,
                body,
                env: _,
            } => format!("(\\{}. {})", binder, body),
            Term::App { func, arg } => parens_if(
                depth > 0,
                format!("{} {}", func.print_inner(depth), arg.print_inner(depth + 1)),
            ),
            Term::Pack { tag, arity, values } => format!(
                "Pack {{{}, {}, [{}]}}",
                tag,
                arity,
                values
                    .into_iter()
                    .map(|t| t.print())
                    .collect::<Vec<String>>()
                    .join(", ")
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
