use crate::ast::Expr;
use std::collections::HashSet;

pub struct Eval {
    supply: u32,
}

impl Eval {
    pub fn new() -> Eval {
        Eval { supply: 0 }
    }

    pub fn eval(&mut self, expr: &Expr) -> Expr {
        match expr {
            Expr::App { func, arg } => match self.eval(func) {
                Expr::Lambda { binder, body } => {
                    let e1 = Expr::App {
                        func: Box::new(Expr::Lambda {
                            binder: binder.clone(),
                            body: body.clone(),
                        }),
                        arg: arg.clone(),
                    };
                    println!("==> {} [eval func]", e1.print());
                    let arg = self.eval(arg);
                    let e2 = Expr::App {
                        func: Box::new(Expr::Lambda {
                            binder: binder.clone(),
                            body: body.clone(),
                        }),
                        arg: Box::new(arg.clone()),
                    };
                    println!("==> {} [eval arg]", e2.print());
                    let new_body = self.substitute(&body, &binder, &arg);
                    println!("==> {} [eval subst]", &new_body.print());
                    self.eval(&new_body)
                }
                _ => expr.clone(),
            },
            _ => expr.clone(),
        }
    }

    fn fresh_var(&mut self, var: &String) -> String {
        self.supply = self.supply + 1;
        format!("{}{}", self.supply, var)
    }

    fn substitute(&mut self, expr: &Expr, scrutinee: &String, replacement: &Expr) -> Expr {
        match expr {
            Expr::Var(x) => {
                if scrutinee == x {
                    replacement.clone()
                } else {
                    expr.clone()
                }
            }
            Expr::Lambda { binder, body } => {
                if binder == scrutinee {
                    return expr.clone();
                }
                let free_vars: HashSet<&String> = replacement.free_vars();
                if free_vars.contains(&binder) {
                    let new_binder = self.fresh_var(&binder);
                    let renamed_body =
                        self.substitute(body, &binder, &Expr::Var(new_binder.clone()));
                    let new_body = self.substitute(&renamed_body, scrutinee, replacement);
                    Expr::Lambda {
                        binder: new_binder,
                        body: Box::new(new_body),
                    }
                } else {
                    let new_body = self.substitute(body, scrutinee, replacement);
                    Expr::Lambda {
                        binder: binder.to_string(),
                        body: Box::new(new_body),
                    }
                }
            }
            Expr::App { func, arg } => Expr::App {
                func: Box::new(self.substitute(func, scrutinee, replacement)),
                arg: Box::new(self.substitute(arg, scrutinee, replacement)),
            },
        }
    }
}
