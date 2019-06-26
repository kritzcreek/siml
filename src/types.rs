use crate::bi_types;
use crate::expr::{Expr, Literal};
use crate::utils::*;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::iter;
use std::iter::FromIterator;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Type {
    Int,
    Bool,
    Var(String),
    Fun { arg: Box<Type>, result: Box<Type> },
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.print())
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Scheme {
    pub vars: Vec<String>,
    pub ty: Type,
}

impl Scheme {
    pub fn print(&self) -> String {
        if self.vars.is_empty() {
            self.ty.print()
        } else {
            format!("forall {}. {}", self.vars.join(" "), self.ty.print())
        }
    }
}

impl Type {
    pub fn from_bi_type(ty: bi_types::Type) -> Self {
        match ty {
            bi_types::Type::Var(v) => Type::Var(v),
            bi_types::Type::Fun { arg, result } => Type::Fun {
                arg: Box::new(Type::from_bi_type(*arg)),
                result: Box::new(Type::from_bi_type(*result)),
            },
            ref ty if *ty == bi_types::Type::int() => Type::Int,
            ref ty if *ty == bi_types::Type::boolean() => Type::Bool,
            t => {
                error!("Type can't handle {}", t);
                Type::Int
            }
        }
    }

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

    pub fn free_vars_ordered(&self) -> Vec<String> {
        let mut res = vec![];
        match self {
            Type::Var(x) => res.push(x.clone()),
            Type::Fun { arg, result } => {
                res.append(&mut arg.free_vars_ordered());
                res.append(&mut result.free_vars_ordered());
            }
            _ => {}
        }
        res
    }

    pub fn free_vars(&self) -> HashSet<String> {
        HashSet::from_iter(self.free_vars_ordered().into_iter())
    }

    pub fn generalize(&self, substitution: &Substitution) -> Scheme {
        let subst_free = substitution.free_vars();
        let free_vars: Vec<String> = self
            .free_vars_ordered()
            .into_iter()
            .filter(|x| !subst_free.contains(x))
            .collect();

        let new_vars: Vec<String> = (0..free_vars.len()).map(|v| format!("gen{}", v)).collect();

        let subst: Substitution = free_vars
            .into_iter()
            .zip(new_vars.iter().map(|v| Type::Var(v.clone())))
            .collect();

        Scheme {
            vars: new_vars.to_vec(),
            ty: subst.apply(self.clone()),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TypeError {
    Unification(Type, Type),
    UnboundName(String),
    OccursCheck(String),
    AnnotationMismatch { ann: Type, ty: Type },
}

impl TypeError {
    pub fn print(&self) -> String {
        match self {
            TypeError::Unification(ty1, ty2) => format!("Couldn't match type {} with {}", ty1, ty2),
            TypeError::UnboundName(name) => format!("Unbound name: {} ", name),
            TypeError::OccursCheck(name) => format!("The occurs check failed for: {}", name),
            TypeError::AnnotationMismatch { ann, ty } => format!(
                "The type: {} failed to check against the annotation: {}",
                ty, ann
            ),
        }
    }
}

type Environment = HashMap<String, Scheme>;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Substitution(pub HashMap<String, Type>);

impl Substitution {
    pub fn new() -> Substitution {
        Substitution(HashMap::new())
    }

    pub fn singleton(var: String, ty: Type) -> Substitution {
        Substitution(HashMap::from_iter(iter::once((var, ty))))
    }

    pub fn free_vars(&self) -> HashSet<String> {
        self.0.values().flat_map(|ty| ty.free_vars()).collect()
    }

    fn remove(&self, vars: &Vec<String>) -> Substitution {
        let mut new_subst = self.0.clone();
        vars.iter().for_each(|var| {
            new_subst.remove(var);
        });
        Substitution(new_subst)
    }

    fn get(&self, var: &String) -> Option<&Type> {
        self.0.get(var)
    }

    fn compose(mut self, other: Substitution) -> Substitution {
        for (var, ty) in other.0.into_iter() {
            self.0.insert(var, self.apply(ty));
        }
        self
    }

    fn apply(&self, ty: Type) -> Type {
        match ty {
            Type::Var(x) => match self.get(&x) {
                None => Type::Var(x),
                Some(ty) => ty.clone(),
            },
            Type::Fun { arg, result } => Type::Fun {
                arg: Box::new(self.apply(*arg)),
                result: Box::new(self.apply(*result)),
            },
            t => t,
        }
    }

    fn apply_scheme(&self, scheme: Scheme) -> Scheme {
        Scheme {
            ty: self.remove(&scheme.vars).apply(scheme.ty),
            vars: scheme.vars,
        }
    }

    fn apply_env(&self, env: &Environment) -> Environment {
        let mut new_env = env.clone();
        for scheme in new_env.values_mut() {
            *scheme = self.apply_scheme(scheme.clone());
        }
        new_env
    }
}

impl FromIterator<(String, Type)> for Substitution {
    fn from_iter<I: IntoIterator<Item = (String, Type)>>(iter: I) -> Self {
        Substitution(iter.into_iter().collect())
    }
}

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

    fn instantiate(&mut self, scheme: &Scheme) -> Type {
        let subst: Substitution = scheme
            .vars
            .iter()
            .map(|v| (v.clone(), Type::Var(self.fresh_name(v))))
            .collect();
        subst.apply(scheme.ty.clone())
    }

    fn var_bind(var: String, ty: Type) -> Result<Substitution, TypeError> {
        match ty {
            Type::Var(x) => {
                if x == var {
                    Ok(Substitution::new())
                } else {
                    Ok(Substitution::singleton(var, Type::Var(x)))
                }
            }
            t => {
                if t.free_vars().contains(&var) {
                    Err(TypeError::OccursCheck(var))
                } else {
                    Ok(Substitution::singleton(var, t))
                }
            }
        }
    }

    fn unify(t1: Type, t2: Type) -> Result<Substitution, TypeError> {
        match (t1, t2) {
            (Type::Int, Type::Int) => Ok(Substitution::new()),
            (Type::Bool, Type::Bool) => Ok(Substitution::new()),
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
                let s2 = TypeChecker::unify(s1.apply(*result1), s1.apply(*result2))?;
                Ok(s1.compose(s2))
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

    pub fn infer(
        &mut self,
        env: &Environment,
        expr: &Expr,
    ) -> Result<(Type, Substitution), TypeError> {
        match expr {
            Expr::Var(x) => match env.get(x) {
                None => Err(TypeError::UnboundName(x.clone())),
                Some(scheme) => Ok((self.instantiate(scheme), Substitution::new())),
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
                        arg: Box::new(s.apply(ty_binder)),
                        result: Box::new(ty_body),
                    },
                    s,
                ))
            }
            Expr::Let { binder, expr, body } => {
                let (ty_binder, s1) = self.infer(env, expr)?;
                let mut tmp_env = env.clone();
                tmp_env.insert(
                    binder.to_string(),
                    Scheme {
                        vars: vec![],
                        ty: ty_binder.clone(),
                    },
                );
                let (ty_body, s2) = self.infer(&tmp_env, body)?;
                Ok((ty_body, s1.compose(s2)))
            }
            Expr::App { func, arg } => {
                let ty_res = self.fresh_var();
                let (ty_fun, s1) = self.infer(env, func)?;
                let (ty_arg, s2) = self.infer(&s1.apply_env(&env), arg)?;
                let s3 = TypeChecker::unify(
                    s2.apply(ty_fun),
                    Type::Fun {
                        arg: Box::new(ty_arg),
                        result: Box::new(ty_res.clone()),
                    },
                )?;
                let ty_res = s3.apply(ty_res);
                let s = s3.compose(s2).compose(s1);
                Ok((ty_res, s))
            }
            Expr::Ann { expr, ty } => {
                let ty = Type::from_bi_type(ty.clone());
                let (ty_inf, s) = self.infer(env, expr)?;
                match TypeChecker::unify(ty.clone(), ty_inf.clone()) {
                    Ok(s1) => Ok((s1.apply(ty_inf), s.compose(s1))),
                    Err(_) => Err(TypeError::AnnotationMismatch {
                        ty: ty_inf,
                        ann: ty.clone(),
                    }),
                }
            }
            Expr::Literal(Literal::Int(_)) => Ok((Type::Int, Substitution::new())),
            Expr::Literal(Literal::Bool(_)) => Ok((Type::Bool, Substitution::new())),
        }
    }
}
