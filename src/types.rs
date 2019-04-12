use crate::expr::{Expr, Literal};
use crate::utils::*;
use std::collections::{HashMap, HashSet};

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Type {
    Int,
    Bool,
    Var(String),
    Fun { arg: Box<Type>, result: Box<Type> },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Scheme {
    vars: Vec<String>,
    ty: Type,
}

impl Type {
    pub fn print(&self) -> String {
        self.print_inner(0)
    }

    fn print_inner(&self, depth: u32) -> String {
        match self {
            Type::Int => "Int".to_string(),
            Type::Bool => "Bool".to_string(),
            Type::Var(s) => s.clone(),
            Type::Fun { arg, result } => parens_if(
                depth > 0,
                format!(
                    "{} -> {}",
                    arg.print_inner(depth + 1),
                    result.print_inner(0)
                ),
            ),
        }
    }

    pub fn free_vars(&self) -> HashSet<String> {
        let mut res = HashSet::new();
        match self {
            Type::Var(x) => {
                res.insert(x.clone());
            }
            Type::Fun { arg, result } => {
                res.extend(arg.free_vars());
                res.extend(result.free_vars());
            }
            _ => {}
        }
        res
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TypeError {
    Unification(Type, Type),
    UnboundName(String),
    OccursCheck(String),
}

impl TypeError {
    pub fn print(&self) -> String {
        match self {
            TypeError::Unification(ty1, ty2) => {
                format!("Couldn't match type {} with {}", ty1.print(), ty2.print())
            }
            TypeError::UnboundName(name) => format!("Unbound name: {} ", name),
            TypeError::OccursCheck(name) => format!("The occurs check failed for: {}", name),
        }
    }
}

type Environment = HashMap<String, Scheme>;

type Substitution = HashMap<String, Type>;

pub struct TypeChecker {
    supply: u32,
}

impl TypeChecker {
    pub fn new() -> TypeChecker {
        TypeChecker { supply: 0 }
    }

    fn fresh_name(&mut self, name: &String) -> String {
        self.supply = self.supply + 1;
        format!("{}{}", self.supply.to_string(), name)
    }

    fn fresh_var(&mut self) -> Type {
        Type::Var(self.fresh_name(&"u".to_string()))
    }

    fn apply_subst_scheme(subst: &Substitution, scheme: Scheme) -> Scheme {
        let mut new_subst = subst.clone();
        scheme.vars.iter().for_each(|var| {
            new_subst.remove(var);
        });
        Scheme {
            vars: scheme.vars,
            ty: TypeChecker::apply_subst(&new_subst, scheme.ty),
        }
    }

    fn apply_subst_env(subst: &Substitution, env: &Environment) -> Environment {
        let mut new_env = env.clone();
        for scheme in new_env.values_mut() {
            *scheme = TypeChecker::apply_subst_scheme(subst, scheme.clone());
        }
        new_env
    }

    fn apply_subst(subst: &Substitution, ty: Type) -> Type {
        match ty {
            Type::Var(x) => match subst.get(&x) {
                None => Type::Var(x),
                Some(ty) => ty.clone(),
            },
            Type::Fun { arg, result } => Type::Fun {
                arg: Box::new(TypeChecker::apply_subst(subst, *arg)),
                result: Box::new(TypeChecker::apply_subst(subst, *result)),
            },
            t => t,
        }
    }

    fn compose_subst(subst1: Substitution, subst2: Substitution) -> Substitution {
        let mut res = subst1.clone();
        for (var, ty) in subst2.clone().iter() {
            res.insert(
                var.to_string(),
                TypeChecker::apply_subst(&subst1, ty.clone()),
            );
        }
        res
    }

    fn instantiate(&mut self, scheme: &Scheme) -> Type {
        let subst: Substitution = scheme
            .vars
            .iter()
            .map(|v| (v.clone(), Type::Var(self.fresh_name(v))))
            .collect();
        TypeChecker::apply_subst(&subst, scheme.ty.clone())
    }

    fn var_bind(var: String, ty: Type) -> Result<Substitution, TypeError> {
        match ty {
            Type::Var(x) => {
                if x == var {
                    Ok(HashMap::new())
                } else {
                    let mut res = HashMap::new();
                    res.insert(var, Type::Var(x));
                    Ok(res)
                }
            }
            t => {
                if t.free_vars().contains(&var) {
                    Err(TypeError::OccursCheck(var))
                } else {
                    let mut res = HashMap::new();
                    res.insert(var, t);
                    Ok(res)
                }
            }
        }
    }

    fn unify(t1: Type, t2: Type) -> Result<Substitution, TypeError> {
        match (t1, t2) {
            (Type::Int, Type::Int) => Ok(HashMap::new()),
            (Type::Bool, Type::Bool) => Ok(HashMap::new()),
            (Type::Var(x), t) => TypeChecker::var_bind(x, t),
            (t, Type::Var(x)) => TypeChecker::var_bind(x, t),
            (
                Type::Fun {
                    arg: arg1,
                    result: result1,
                },
                Type::Fun {
                    arg: arg2,
                    result: result2,
                },
            ) => {
                let s1 = TypeChecker::unify(*arg1, *arg2)?;
                let s2 = TypeChecker::unify(
                    TypeChecker::apply_subst(&s1, *result1),
                    TypeChecker::apply_subst(&s1, *result2),
                )?;
                Ok(TypeChecker::compose_subst(s1, s2))
            }
            (t1, t2) => Err(TypeError::Unification(t1, t2)),
        }
    }

    pub fn infer_expr(&mut self, expr: &Expr) -> Result<Type, TypeError> {
        let mut init_env = HashMap::new();
        init_env.insert(
            "add".to_string(),
            Scheme {
                vars: vec![],
                ty: Type::Fun {
                    arg: Box::new(Type::Int),
                    result: Box::new(Type::Fun {
                        arg: Box::new(Type::Int),
                        result: Box::new(Type::Int),
                    }),
                },
            },
        );
        self.infer(&init_env, expr).map(|(ty, _)| ty)
    }

    fn infer(&mut self, env: &Environment, expr: &Expr) -> Result<(Type, Substitution), TypeError> {
        match expr {
            Expr::Var(x) => match env.get(x) {
                None => Err(TypeError::UnboundName(x.clone())),
                Some(scheme) => Ok((self.instantiate(scheme), HashMap::new())),
            },
            Expr::Lambda { binder, body } => {
                let ty_binder = self.fresh_var();
                let mut tmp_env = env.clone();
                tmp_env.insert(
                    binder.to_string(),
                    Scheme {
                        vars: vec![],
                        ty: ty_binder.clone(),
                    },
                );
                let (ty_body, s) = self.infer(&tmp_env, body)?;
                Ok((
                    Type::Fun {
                        arg: Box::new(TypeChecker::apply_subst(&s, ty_binder)),
                        result: Box::new(ty_body),
                    },
                    s,
                ))
            }
            Expr::App { func, arg } => {
                let ty_res = self.fresh_var();
                let (ty_fun, s1) = self.infer(env, func)?;
                let (ty_arg, s2) = self.infer(&TypeChecker::apply_subst_env(&s1, env), arg)?;
                let s3 = TypeChecker::unify(
                    TypeChecker::apply_subst(&s2, ty_fun),
                    Type::Fun {
                        arg: Box::new(ty_arg),
                        result: Box::new(ty_res.clone()),
                    },
                )?;
                let ty_res = TypeChecker::apply_subst(&s3, ty_res);
                let s = TypeChecker::compose_subst(TypeChecker::compose_subst(s1, s2), s3);
                Ok((ty_res, s))
            }
            Expr::Literal(Literal::Int(_)) => Ok((Type::Int, HashMap::new())),
            Expr::Literal(Literal::Bool(_)) => Ok((Type::Bool, HashMap::new())),
        }
    }
}
