use crate::expr::Expr;
use crate::utils::parens_if;
use std::collections::HashSet;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Type {
    Int,
    Bool,
    Var(String),
    Existential(String),
    Poly { vars: Vec<String>, ty: Box<Type> },
    Fun { arg: Box<Type>, result: Box<Type> },
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
            Type::Existential(e) => format!("{{{}}}", e.clone()),
            Type::Poly { vars, ty } => {
                let vars_printed: String = vars
                    .iter()
                    .fold("".to_string(), |acc, var| format!("{} {}", acc, var));
                format!("∀{}. {}", vars_printed, ty.print())
            }
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

    pub fn is_mono(&self) -> bool {
        match self {
            Type::Var(_) | Type::Existential(_) | Type::Int | Type::Bool => true,
            Type::Poly { .. } => false,
            Type::Fun { arg, result } => arg.is_mono() && result.is_mono(),
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
            Type::Existential(v) => {
                res.insert(v.clone());
            }
            Type::Poly { vars, ty } => {
                let mut free_in_ty = ty.free_vars();
                vars.iter().for_each(|var| {
                    free_in_ty.remove(var);
                });
                res.extend(free_in_ty);
            }
            Type::Int | Type::Bool => {}
        }
        res
    }

    pub fn subst(&self, var: &String, replacement: &Type) -> Type {
        match self {
            Type::Bool => Type::Bool,
            Type::Int => Type::Int,
            Type::Var(v) | Type::Existential(v) => {
                if v == var {
                    replacement.clone()
                } else {
                    self.clone()
                }
            }
            Type::Poly { vars, ty } => {
                if vars.contains(var) {
                    self.clone()
                } else {
                    Type::Poly {
                        vars: vars.clone(),
                        ty: Box::new(ty.subst(var, replacement)),
                    }
                }
            }
            Type::Fun { arg, result } => Type::Fun {
                arg: Box::new(arg.subst(var, replacement)),
                result: Box::new(result.subst(var, replacement)),
            },
        }
    }
    pub fn subst_mut(&mut self, var: &String, replacement: &Type) {
        match self {
            Type::Bool | Type::Int => {}
            Type::Var(v) | Type::Existential(v) => {
                if v == var {
                    *self = replacement.clone();
                }
            }
            Type::Poly { vars, ty } => {
                if !vars.contains(var) {
                    ty.subst_mut(var, replacement);
                }
            }
            Type::Fun { arg, result } => {
                arg.subst_mut(var, replacement);
                result.subst_mut(var, replacement);
            }
        }
    }
}

// Smart constructors
impl Type {
    fn var(str: &str) -> Self {
        Type::Var(str.to_string())
    }
    fn ex(str: &str) -> Self {
        Type::Existential(str.to_string())
    }

    fn fun(arg: Type, result: Type) -> Self {
        Type::Fun {
            arg: Box::new(arg),
            result: Box::new(result),
        }
    }

    fn poly(vars: Vec<&str>, ty: Type) -> Self {
        Type::Poly {
            vars: vars.into_iter().map(|s| s.to_string()).collect(),
            ty: Box::new(ty),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
struct TypeChecker {
    name_gen: NameGen,
}

#[derive(Debug, PartialEq, Eq)]
struct NameGen {
    ty_gen: u32,
    ex_gen: u32,
}

impl NameGen {
    pub fn new() -> NameGen {
        NameGen {
            ty_gen: 0,
            ex_gen: 0,
        }
    }

    pub fn fresh_var(&mut self) -> String {
        self.ty_gen = self.ty_gen + 1;
        format!("{}v", self.ty_gen)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Context {
    elems: Vec<ContextElem>,
}

impl Context {
    fn split_at(&self, elem: &ContextElem) -> Option<(&[ContextElem], &[ContextElem])> {
        let pos = self.elems.iter().position(|x| x == elem);
        pos.map(|pos| self.elems.split_at(pos))
    }

    fn elem(&self, elem: &ContextElem) -> bool {
        // TODO: Only unsolved?
        self.split_at(elem).is_some()
    }

    fn push(&mut self, elem: ContextElem) {
        self.elems.push(elem)
    }

    fn push_elems(&mut self, elems: Vec<ContextElem>) {
        self.elems.extend(elems.into_iter())
    }

    fn drop_marker(&mut self, marker: ContextElem) {
        let (before_marker, _) = self.split_at(&marker).expect("dropping non-existent marker");
        self.elems = before_marker.to_vec();
    }

    fn break_marker(&self, marker: ContextElem) -> (Vec<ContextElem>, Vec<ContextElem>) {
        let (before_marker, after_marker) = self.split_at(&marker).expect("breaking non-existent marker");
        (before_marker.to_vec(), after_marker.split_last().unwrap().1.to_vec())
    }

    fn existentials(&self) -> Vec<String> {
        self.elems
            .iter()
            .filter_map(|x| match x {
                ContextElem::ExVar(v) => Some(v.clone()),
                ContextElem::ExVarSolved(v, _) => Some(v.clone()),
                _ => None,
            })
            .collect()
    }

    fn find_solved(&self, ex: &String) -> Option<&Type> {
        self.elems.iter().find_map(|e| match e {
            ContextElem::ExVarSolved(var, ty) => {
                if var == ex {
                    Some(ty)
                } else {
                    None
                }
            },
            _ => None,
        })
    }

    fn find_var(&self, var: &String) -> Option<&Type> {
        self.elems.iter().find_map(|e| match e {
            ContextElem::Anno(v, ty) => {
                if var == v {
                    Some(ty)
                } else {
                    None
                }
            },
            _ => None,
        })
    }

    fn u_var_wf(&self, var: &String) -> bool {
        self.elem(&ContextElem::Var(var.clone()))
    }

    fn arrow_wf(&self, a: &Type, b: &Type) -> bool {
        self.wf_type(a) && self.wf_type(b)
    }

    fn forall_wf(&self, vars: &Vec<String>, ty: &Type) -> bool {
        let mut tmp_elems = self.elems.clone();
        tmp_elems.extend(vars.iter().map(|v| ContextElem::Var(v.clone())));
        let tmp_ctx = Context { elems: tmp_elems };

        tmp_ctx.wf_type(ty)
    }

    fn evar_wf(&self, evar: &String) -> bool {
        self.elem(&ContextElem::ExVar(evar.clone()))
    }
    fn solved_evar_wf(&self, evar: &String) -> bool {
        self.elems
            .iter()
            .find(|el| match el {
                ContextElem::ExVarSolved(var, _) => var == evar,
                _ => false,
            })
            .is_some()
    }

    fn wf_type(&self, ty: &Type) -> bool {
        match ty {
            Type::Bool => true,
            Type::Int => true,
            Type::Poly { vars, ty } => self.forall_wf(vars, ty),
            Type::Fun { arg, result } => self.arrow_wf(arg, result),
            Type::Var(var) => self.u_var_wf(var),
            Type::Existential(var) => self.evar_wf(var) || self.solved_evar_wf(var),
        }
    }

    fn apply(&self, ty: &Type) -> Option<Type> {
        match ty {
            Type::Bool => Some(Type::Bool),
            Type::Int => Some(Type::Int),
            Type::Var(v) => {
                if self.elem(&ContextElem::Var(v.clone())) {
                    Some(Type::Var(v.clone()))
                } else {
                    None
                }
            }
            Type::Existential(ex) => None,
            _ => None,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum ContextElem {
    Var(String),
    ExVar(String),
    ExVarSolved(String, Type),
    Marker(String),
    Anno(String, Type),
}

impl TypeChecker {
    pub fn new() -> TypeChecker {
        TypeChecker {
            name_gen: NameGen::new(),
        }
    }

    fn check(&mut self, ctx: &Context, expr: &Expr, ty: &Type) -> bool {
        false
    }

    fn infer(&mut self, ctx: &Context, expr: &Expr) -> Type {
        Type::Int
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subst_mut() {
        let mut ty = Type::var("x");
        ty.subst_mut(&"x".to_string(), &Type::Int);
        assert_eq!(ty, Type::Int);
    }

    #[test]
    fn subst_mut_fun() {
        let mut ty = Type::fun(Type::var("a"), Type::var("b"));
        ty.subst_mut(&"a".to_string(), &Type::Int);
        assert_eq!(ty, Type::fun(Type::Int, Type::var("b")));
    }
}
