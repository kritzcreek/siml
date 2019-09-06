use crate::expr::Expr;

type EvalExpr = Expr<String>;

#[derive(Default)]
pub struct Eval {
    supply: u32,
}

impl Eval {
    pub fn eval(&mut self, expr: EvalExpr) -> EvalExpr {
        match expr {
            Expr::App { func, arg } => {
                debug!(
                    "Evaling: {}",
                    Expr::App {
                        func: func.clone(),
                        arg: arg.clone()
                    }
                );
                match self.eval(*func) {
                    Expr::Lambda { binder, body } => {
                        let e1 = Expr::App {
                            func: Box::new(Expr::Lambda {
                                binder: binder.clone(),
                                body: body.clone(),
                            }),
                            arg: arg.clone(),
                        };
                        debug!("[fun] ==>\n  {} ", e1);
                        let arg = self.eval(*arg);
                        let e2 = Expr::App {
                            func: Box::new(Expr::Lambda {
                                binder: binder.clone(),
                                body: body.clone(),
                            }),
                            arg: Box::new(arg.clone()),
                        };
                        debug!("[arg] ==>\n  {}", e2);
                        let new_body = self.substitute(&body, &binder, &arg);
                        debug!("[sub] ==>\n  {}", &new_body);
                        self.eval(new_body)
                    }
                    new_func => Expr::App {
                        func: Box::new(new_func),
                        arg,
                    },
                }
            }
            Expr::Ann { expr, .. } => self.eval(*expr),
            _ => expr,
        }
    }

    fn fresh_var(&mut self, var: &str) -> String {
        self.supply += 1;
        format!("{}{}", self.supply, var)
    }

    fn substitute(&mut self, expr: &EvalExpr, scrutinee: &str, replacement: &EvalExpr) -> EvalExpr {
        match expr {
            Expr::Var(x) => {
                if scrutinee == x {
                    replacement.clone()
                } else {
                    expr.clone()
                }
            }
            Expr::Let { binder, expr, body } => {
                let new_expr = self.substitute(expr, scrutinee, replacement);
                let new_body = if scrutinee != binder {
                    self.substitute(body, scrutinee, replacement)
                } else {
                    *body.clone()
                };
                Expr::Let {
                    binder: binder.clone(),
                    expr: Box::new(new_expr),
                    body: Box::new(new_body),
                }
            }
            Expr::Lambda { binder, body } => {
                if binder == scrutinee {
                    return expr.clone();
                }
                let free_vars = replacement.free_vars();
                if free_vars.contains(binder) {
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
            Expr::Ann { expr, ty } => Expr::Ann {
                ty: ty.clone(),
                expr: Box::new(self.substitute(expr, scrutinee, replacement)),
            },
            Expr::Literal(_) => expr.clone(),
            Expr::Tuple(fst, snd) => Expr::tuple(
                self.substitute(fst, scrutinee, replacement),
                self.substitute(snd, scrutinee, replacement),
            ),
            Expr::Case { .. } => unreachable!("TODO"),
        }
    }
}
