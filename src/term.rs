use crate::expr::{Declaration, Expr, HasIdent, Literal, Match, TypeDeclaration};
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
    Case {
        expr: Box<Term>,
        cases: Vec<TermMatch>,
    },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct TermMatch {
    pub tag: u32,
    pub binders: Vec<String>,
    pub expr: Term,
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.print())
    }
}

struct Lowering {
    /// All type declarations in the to-be-lowered program
    types: Vec<TypeDeclaration>,
}

impl Lowering {
    pub fn new() -> Lowering {
        Lowering { types: vec![] }
    }

    pub fn lower_prog<B: HasIdent>(mut self, prog: Vec<Declaration<B>>) -> Vec<(String, Term)> {
        let mut values = vec![];
        for decl in prog {
            match decl {
                Declaration::Value(v) => values.push(v),
                Declaration::Type(t) => self.types.push(t),
            }
        }
        values
            .into_iter()
            .map(|value| (value.name, self.lower_expr(value.expr)))
            .collect()
    }

    pub fn lower_expr<B: HasIdent>(&self, expr: Expr<B>) -> Term {
        match expr {
            Expr::App { func, arg } => Term::App {
                func: Box::new(self.lower_expr(*func)),
                arg: Box::new(self.lower_expr(*arg)),
            },
            Expr::Lambda { binder, body } => Term::Lambda {
                binder: binder.ident(),
                body: Box::new(self.lower_expr(*body)),
            },
            Expr::Let { binder, expr, body } => Term::App {
                func: Box::new(Term::Lambda {
                    binder: binder.ident(),
                    body: Box::new(self.lower_expr(*body)),
                }),
                arg: Box::new(self.lower_expr(*expr)),
            },
            Expr::Var(s) => match self.tag_for_constructor(s.ident()) {
                None => Term::Var(s.ident()),
                Some(tag) => Term::Pack {
                    tag,
                    arity: 0,
                    values: vec![],
                },
            },
            Expr::Literal(lit) => Term::Literal(lit.clone()),
            Expr::Ann { expr, .. } => self.lower_expr(*expr),
            Expr::Tuple(fst, snd) => Term::Pack {
                tag: 1,
                arity: 2,
                values: vec![self.lower_expr(*fst), self.lower_expr(*snd)],
            },
            Expr::Construction { dtor, args } => {
                let tag = self.tag_for_constructor(dtor.name).unwrap();
                Term::Pack {
                    tag,
                    arity: args.len() as u32,
                    values: args.into_iter().map(|arg| self.lower_expr(arg)).collect(),
                }
            }
            Expr::Case { expr, cases } => Term::Case {
                expr: Box::new(self.lower_expr(*expr)),
                cases: cases.into_iter().map(|m| self.lower_match(m)).collect(),
            },
        }
    }

    fn lower_match<B: HasIdent>(&self, match_: Match<B>) -> TermMatch {
        TermMatch {
            tag: self
                .tag_for_constructor(match_.data_constructor.name)
                .expect("Failed to find data constructor during lowering"),
            binders: vec![],
            expr: self.lower_expr(match_.expr),
        }
    }

    fn tag_for_constructor(&self, ctor: String) -> Option<u32> {
        self.types.iter().find_map(|t| {
            t.constructors.iter().enumerate().find_map(|(ix, c)| {
                if c.name == ctor {
                    Some(ix as u32)
                } else {
                    None
                }
            })
        })
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum EvalError {
    UnknownVar(String),
    ApplyingNonLambda(Term),
    AddingNonNumbers(Term, Term),
    ProjectingFst(Term),
    MatchOnNonPack(Term),
    FailedPatternMatch(Term),
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.print())
    }
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
            EvalError::MatchOnNonPack(term) => format!("Attempting to pattern match on: {}", term),
            EvalError::FailedPatternMatch(term) => {
                format!("Failed to find a matching pattern for: {}", term)
            }
        }
    }
}

fn initial_env() -> Env {
    HashMap::new()
}

impl Term {
    pub fn eval_prog<B: HasIdent>(prog: Vec<Declaration<B>>) -> Result<Term, EvalError> {
        let lowered = Lowering::new().lower_prog(prog);
        let mut env = initial_env();
        let mut res = Term::Var("nuttin".to_string());
        for (name, term) in lowered {
            res = Term::eval(&env, term)?;
            env.insert(name, res.clone());
        }
        Ok(res)
    }

    pub fn eval_expr<B: HasIdent>(expr: Expr<B>) -> Result<Term, EvalError> {
        let lowered = Lowering::new().lower_expr(expr);
        Term::eval(&initial_env(), lowered)
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
                    Some(Term::Pack { values, .. }) => Ok(values[0].clone()),
                    Some(term) => Err(EvalError::ProjectingFst(term.clone())),
                    None => panic!("Bad implementation for fst"),
                },
                "primsnd" => match env.get("x") {
                    Some(Term::Pack { values, .. }) => Ok(values[1].clone()),
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
                    None => {
                        // warn!("{:?}", env);
                        Err(EvalError::UnknownVar(s))
                    }
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
            Term::Case { expr, cases } => {
                let evaled_expr = Term::eval(env, *expr)?;
                match evaled_expr {
                    Term::Pack { tag, .. } => {
                        let matched_case = cases.into_iter().find_map(|case| {
                            if case.tag == tag {
                                Some(case.expr)
                            } else {
                                None
                            }
                        });

                        match matched_case {
                            None => Err(EvalError::FailedPatternMatch(evaled_expr)),
                            Some(term) => Term::eval(env, term),
                        }
                    }
                    t => Err(EvalError::MatchOnNonPack(t)),
                }
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
            Term::Closure { binder, body, .. } => format!("(\\{}. {})", binder, body),
            Term::App { func, arg } => parens_if(
                depth > 0,
                format!("{} {}", func.print_inner(depth), arg.print_inner(depth + 1)),
            ),
            Term::Pack { tag, arity, values } => format!(
                "Pack {{{}, {}, [{}]}}",
                tag,
                arity,
                values
                    .iter()
                    .map(|t| t.print())
                    .collect::<Vec<String>>()
                    .join(", ")
            ),
            Term::Case { expr, cases } => format!("match {} {{}}", expr),
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
