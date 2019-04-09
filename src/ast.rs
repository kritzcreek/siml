use std::collections::HashSet;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Expr {
    App { func: Box<Expr>, arg: Box<Expr> },
    Lambda { binder: String, body: Box<Expr> },
    Var(String),
}

impl Expr {
    pub fn print(&self) -> String {
        self.print_inner(0)
    }

    fn print_inner(&self, depth: u32) -> String {
        match self {
            Expr::Var(s) => s.clone(),
            Expr::Lambda {binder, body} =>
                format!("(\\{}. {})", binder, body.print()),
            Expr::App {func, arg} => {
                parens_if(depth>0, format!("{} {}", func.print_inner(depth), arg.print_inner(depth+1)))
            }
        }
    }

    pub fn free_vars(&self) -> HashSet<&String> {
        match self {
            Expr::Var(s) => {
                let mut res = HashSet::new();
                res.insert(s);
                res
            },
            Expr::Lambda{binder, body} => {
                let mut res = body.free_vars();
                res.remove(binder);
                res
            },
            Expr::App{ func, arg } => {
                func.free_vars().union(&arg.free_vars()).cloned().collect()
            },
        }
    }

    pub fn substitute(&self, old: &String, new: &String) -> Expr {
        match self {
            Expr::Var(x) => { if old == x {
                Expr::Var(new.clone())
            } else {
                Expr::Var(x.clone())
            }}
            Expr::Lambda{ binder, body } => {
                let mut free_vars: HashSet<&String> = body.free_vars();
                free_vars.remove(binder);
                let new_body;
                if free_vars.contains(&new) {
                    new_body = body.substitute(old, &format!("{}'", new.clone()))
                } else {
                    new_body = body.substitute(old, new)
                }
                Expr::Lambda { binder: binder.to_string(), body: Box::new(new_body.clone()) }
            }
            Expr::App { func, arg } => {
                Expr::App { func: Box::new(func.substitute(old, new).clone()), arg: Box::new(arg.substitute(old, new).clone()) }
            }
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
