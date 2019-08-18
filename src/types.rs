/// An implementation of AlgorithmW
use crate::bi_types;
use crate::expr::{Expr, Literal, ParserExpr};
use crate::pretty::parens_if;
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
    Tuple(Box<Type>, Box<Type>),
    Error,
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

    pub fn free_vars(&self) -> HashSet<String> {
        let mut res = self.ty.free_vars();
        for var in &self.vars {
            res.remove(var);
        }
        res
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
            bi_types::Type::Tuple(fst, snd) => Type::Tuple(
                Box::new(Type::from_bi_type(*fst)),
                Box::new(Type::from_bi_type(*snd)),
            ),
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

    fn is_error(&self) -> bool {
        match self {
            Type::Error => true,
            _ => false,
        }
    }

    fn print_inner(&self, depth: u32) -> String {
        match self {
            Type::Int => "Int".to_string(),
            Type::Bool => "Bool".to_string(),
            Type::Var(s) => s.clone(),
            Type::Error => "ERR".to_string(),
            Type::Fun { arg, result } => parens_if(
                depth > 0,
                format!(
                    "{} -> {}",
                    arg.print_inner(depth + 1),
                    result.print_inner(0)
                ),
            ),
            Type::Tuple(fst, snd) => format!("({}, {})", fst.print(), snd.print()),
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
            Type::Tuple(fst, snd) => {
                res.append(&mut fst.free_vars_ordered());
                res.append(&mut snd.free_vars_ordered());
            }
            _ => {}
        }
        res
    }

    pub fn free_vars(&self) -> HashSet<String> {
        HashSet::from_iter(self.free_vars_ordered().into_iter())
    }

    pub fn generalize(&self, env: &Environment) -> Scheme {
        let env_free = env.free_vars();
        let free_vars: Vec<String> = self
            .free_vars_ordered()
            .into_iter()
            .filter(|x| !env_free.contains(x))
            .collect();

        let new_vars: Vec<String> = (0..free_vars.len()).map(|v| format!("gen{}", v)).collect();

        let subst: Substitution = free_vars
            .into_iter()
            .zip(new_vars.iter().map(|v| Type::Var(v.clone())))
            .collect();

        Scheme {
            vars: new_vars,
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

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Environment(pub HashMap<String, Scheme>);

impl Environment {
    pub fn new() -> Environment {
        Environment(HashMap::new())
    }

    pub fn insert(&self, var: String, scheme: Scheme) -> Environment {
        let mut res = self.0.clone();
        res.insert(var, scheme);
        Environment(res)
    }

    pub fn insert_mono(&self, var: String, ty: Type) -> Environment {
        self.insert(var, Scheme { vars: vec![], ty })
    }

    pub fn get(&self, var: &String) -> Option<&Scheme> {
        self.0.get(var)
    }

    pub fn free_vars(&self) -> HashSet<String> {
        let mut res = HashSet::new();
        for (_, scheme) in &self.0 {
            res.extend(scheme.free_vars())
        }
        res
    }
}

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
        for scheme in new_env.0.values_mut() {
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
    errors: Vec<TypeError>,
}

impl TypeChecker {
    pub fn new() -> TypeChecker {
        TypeChecker {
            supply: 0,
            errors: vec![],
        }
    }

    fn fresh_name(&mut self, name: &String) -> String {
        self.supply = self.supply + 1;
        format!("{}{}", self.supply.to_string(), name)
    }

    fn fresh_var(&mut self) -> Type {
        Type::Var(self.fresh_name(&"u".to_string()))
    }

    fn report_error(&mut self, error: TypeError) {
        self.errors.push(error)
    }

    fn error_sentinel() -> (Type, Substitution) {
        (Type::Error, Substitution::new())
    }

    fn instantiate(&mut self, scheme: &Scheme) -> Type {
        let subst: Substitution = scheme
            .vars
            .iter()
            .map(|v| (v.clone(), Type::Var(self.fresh_name(v))))
            .collect();
        subst.apply(scheme.ty.clone())
    }

    fn var_bind(&mut self, var: String, ty: Type) -> Option<Substitution> {
        match ty {
            Type::Var(x) => {
                if x == var {
                    Some(Substitution::new())
                } else {
                    Some(Substitution::singleton(var, Type::Var(x)))
                }
            }
            t => {
                if t.free_vars().contains(&var) {
                    self.report_error(TypeError::OccursCheck(var));
                    None
                } else {
                    Some(Substitution::singleton(var, t))
                }
            }
        }
    }

    fn unify(&mut self, t1: Type, t2: Type) -> Option<Substitution> {
        match (t1, t2) {
            (Type::Error, _) => None,
            (_, Type::Error) => None,
            (Type::Int, Type::Int) => Some(Substitution::new()),
            (Type::Bool, Type::Bool) => Some(Substitution::new()),
            (Type::Var(x), t) => self.var_bind(x, t),
            (t, Type::Var(x)) => self.var_bind(x, t),
            (
                Type::Fun {
                    arg: arg1,
                    result: result1,
                },
                Type::Fun {
                    arg: arg2,
                    result: result2,
                },
            ) => match self.unify(*arg1, *arg2) {
                None => {
                    // Even if unifying the argument types failed, we
                    // try to unify the result types to find potential
                    // unrelated errors
                    self.unify(*result1, *result2);
                    None
                }
                Some(s1) => self
                    .unify(s1.apply(*result1), s1.apply(*result2))
                    .map(|s2| s1.compose(s2)),
            },
            (Type::Tuple(fst1, snd1), Type::Tuple(fst2, snd2)) => match self.unify(*fst1, *fst2) {
                None => {
                    self.unify(*snd1, *snd2);
                    None
                }
                Some(s1) => self
                    .unify(s1.apply(*snd1), s1.apply(*snd2))
                    .map(|s2| s1.compose(s2)),
            },
            (t1, t2) => {
                self.report_error(TypeError::Unification(t1, t2));
                None
            }
        }
    }

    pub fn infer_expr(&mut self, expr: &ParserExpr) -> Result<Type, Vec<TypeError>> {
        let init_env = Environment::new().insert_mono(
            "add".to_string(),
            Type::Fun {
                arg: Box::new(Type::Int),
                result: Box::new(Type::Fun {
                    arg: Box::new(Type::Int),
                    result: Box::new(Type::Int),
                }),
            },
        );
        let (ty, _) = self.infer(&init_env, expr);
        if self.errors.is_empty() {
            Ok(ty)
        } else {
            Err(self.errors.clone())
        }
    }

    pub fn infer(&mut self, env: &Environment, expr: &ParserExpr) -> (Type, Substitution) {
        match expr {
            Expr::Var(x) => match env.get(x) {
                None => {
                    self.report_error(TypeError::UnboundName(x.clone()));
                    TypeChecker::error_sentinel()
                }
                Some(scheme) => (self.instantiate(scheme), Substitution::new()),
            },
            Expr::Lambda { binder, body } => {
                let ty_binder = self.fresh_var();
                let tmp_env = env.insert_mono(binder.to_string(), ty_binder.clone());
                let (ty_body, s) = self.infer(&tmp_env, body);
                if ty_body.is_error() {
                    return TypeChecker::error_sentinel();
                }
                (
                    Type::Fun {
                        arg: Box::new(s.apply(ty_binder)),
                        result: Box::new(ty_body),
                    },
                    s,
                )
            }
            Expr::Let { binder, expr, body } => {
                let (ty_binder, s1) = self.infer(env, expr);
                let tmp_env = env.insert(binder.to_string(), ty_binder.generalize(env));
                let (ty_body, s2) = self.infer(&tmp_env, body);
                if ty_binder.is_error() || ty_body.is_error() {
                    TypeChecker::error_sentinel()
                } else {
                    (ty_body, s1.compose(s2))
                }
            }
            Expr::App { func, arg } => {
                let ty_res = self.fresh_var();
                let (ty_fun, s1) = self.infer(env, func);
                let (ty_arg, s2) = self.infer(&s1.apply_env(&env), arg);
                if ty_fun.is_error() || ty_arg.is_error() {
                    return TypeChecker::error_sentinel();
                }
                let unify_result = self.unify(
                    s2.apply(ty_fun),
                    Type::Fun {
                        arg: Box::new(ty_arg),
                        result: Box::new(ty_res.clone()),
                    },
                );
                match unify_result {
                    Some(s3) => {
                        let ty_res = s3.apply(ty_res);
                        let s = s3.compose(s2).compose(s1);
                        (ty_res, s)
                    }
                    None => TypeChecker::error_sentinel(),
                }
            }
            Expr::Ann { expr, ty } => {
                let ty = Type::from_bi_type(ty.clone());
                let (ty_inf, s) = self.infer(env, expr);
                match self.unify(ty.clone(), ty_inf.clone()) {
                    Some(s1) => (s1.apply(ty_inf), s.compose(s1)),
                    None => {
                        self.report_error(TypeError::AnnotationMismatch {
                            ty: ty_inf,
                            ann: ty.clone(),
                        });
                        TypeChecker::error_sentinel()
                    }
                }
            }
            Expr::Tuple(fst, snd) => {
                let (ty_fst, s1) = self.infer(env, fst);
                let (ty_snd, s2) = self.infer(env, snd);
                if ty_fst.is_error() || ty_snd.is_error() {
                    return TypeChecker::error_sentinel();
                }
                let ty_fst = s2.apply(ty_fst);
                let s = s2.compose(s1);
                (Type::Tuple(Box::new(ty_fst), Box::new(ty_snd)), s)
            }
            Expr::Case{..} => unreachable!("TODO"),
            Expr::Literal(Literal::Int(_)) => (Type::Int, Substitution::new()),
            Expr::Literal(Literal::Bool(_)) => (Type::Bool, Substitution::new()),
        }
    }
}
