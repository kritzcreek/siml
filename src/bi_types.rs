#![allow(dead_code)]

use crate::expr::{
    Case, DataConstructor, Declaration, Dtor, Expr, Literal, ParserExpr, TypeDeclaration,
    TypedExpr, ValueDeclaration, Var,
};
use crate::pretty::render_doc;
use pretty::{BoxDoc, Doc};
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Type {
    Constructor { name: String, arguments: Vec<Type> },
    Var(String),
    Existential(String),
    Poly { vars: Vec<String>, ty: Box<Type> },
    Fun { arg: Box<Type>, result: Box<Type> },
    Tuple(Box<Type>, Box<Type>),
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", render_doc(self.to_doc()))
    }
}

impl Type {
    pub fn is_mono(&self) -> bool {
        match self {
            Type::Var(_) | Type::Existential(_) | Type::Constructor { .. } => true,
            Type::Poly { .. } => false,
            Type::Fun { arg, result } => arg.is_mono() && result.is_mono(),
            Type::Tuple(fst, snd) => fst.is_mono() && snd.is_mono(),
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
            Type::Constructor { arguments, .. } => {
                for arg in arguments {
                    res.extend(arg.free_vars())
                }
            }
            Type::Tuple(fst, snd) => {
                res.extend(fst.free_vars());
                res.extend(snd.free_vars());
            }
        }
        res
    }

    fn unfold_fun_inner(&self) -> Vec<&Self> {
        match self {
            Type::Fun { arg, result } => {
                let mut res = result.unfold_fun_inner();
                res.push(arg);
                res
            }
            _ => vec![self],
        }
    }

    pub fn unfold_fun(&self) -> Vec<&Self> {
        let mut res = self.unfold_fun_inner();
        res.reverse();
        res
    }

    pub fn subst(&self, var: &str, replacement: &Type) -> Type {
        match self {
            Type::Constructor { name, arguments } => Type::Constructor {
                name: name.clone(),
                arguments: arguments
                    .iter()
                    .map(|arg| arg.subst(var, replacement))
                    .collect(),
            },
            Type::Var(v) | Type::Existential(v) => {
                if v == var {
                    replacement.clone()
                } else {
                    self.clone()
                }
            }
            Type::Poly { vars, ty } => {
                if vars.contains(&var.to_string()) {
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
            Type::Tuple(fst, snd) => Type::Tuple(
                Box::new(fst.subst(var, replacement)),
                Box::new(snd.subst(var, replacement)),
            ),
        }
    }

    pub fn subst_many(mut self, subst: &[(String, Type)]) -> Type {
        for (v, t) in subst {
            self.subst_mut(v, t);
        }
        self
    }

    pub fn subst_mut(&mut self, var: &str, replacement: &Type) {
        match self {
            Type::Constructor { arguments, .. } => {
                for arg in arguments {
                    arg.subst_mut(var, replacement)
                }
            }
            Type::Var(v) | Type::Existential(v) => {
                if v == var {
                    *self = replacement.clone();
                }
            }
            Type::Poly { vars, ty } => {
                if !vars.contains(&var.to_string()) {
                    ty.subst_mut(var, replacement);
                }
            }
            Type::Fun { arg, result } => {
                arg.subst_mut(var, replacement);
                result.subst_mut(var, replacement);
            }
            Type::Tuple(fst, snd) => {
                fst.subst_mut(var, replacement);
                snd.subst_mut(var, replacement);
            }
        }
    }
}

// Smart constructors
impl Type {
    pub fn int() -> Self {
        Type::Constructor {
            name: "Int".to_string(),
            arguments: vec![],
        }
    }
    pub fn bool() -> Self {
        Type::Constructor {
            name: "Bool".to_string(),
            arguments: vec![],
        }
    }

    fn var(str: &str) -> Self {
        Type::Var(str.to_string())
    }

    fn ex(str: &str) -> Self {
        Type::Existential(str.to_string())
    }

    pub fn fun(arg: Type, result: Type) -> Self {
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

    fn tuple(fst: Type, snd: Type) -> Self {
        Type::Tuple(Box::new(fst), Box::new(snd))
    }
}

// Pretty printing
impl Type {
    pub fn to_doc(&self) -> Doc<BoxDoc<()>> {
        self.to_doc_inner(0)
    }
    fn to_doc_inner(&self, depth: u32) -> Doc<BoxDoc<()>> {
        match self {
            Type::Constructor { name, arguments } => {
                if arguments.is_empty() {
                    Doc::text(name)
                } else {
                    Doc::text(name)
                        .append(Doc::text("<"))
                        .append(Doc::intersperse(
                            arguments.iter().map(|arg| arg.to_doc()),
                            Doc::text(",").append(Doc::space()),
                        ))
                        .append(Doc::text(">"))
                        .group()
                }
            }

            Type::Existential(evar) => Doc::text(evar),
            Type::Var(v) => Doc::text(v),
            Type::Poly { vars, ty } => {
                let inner = Doc::text("∀ ")
                    .append(Doc::intersperse(vars.iter().map(Doc::text), Doc::space()))
                    .append(Doc::text("."))
                    .group()
                    .append(Doc::space())
                    .append(ty.to_doc())
                    .nest(2)
                    .group();
                if depth > 0 {
                    Doc::text("(").append(inner).append(Doc::text(")")).group()
                } else {
                    inner
                }
            }
            Type::Fun { arg, result } => {
                let inner = arg
                    .to_doc_inner(1)
                    .append(Doc::space())
                    .append(Doc::text("→"))
                    .group()
                    .append(Doc::space())
                    .append(result.to_doc())
                    .group();
                if depth > 0 {
                    Doc::text("(").append(inner).append(Doc::text(")"))
                } else {
                    inner
                }
            }
            Type::Tuple(fst, snd) => Doc::text("(")
                .append(fst.to_doc())
                .append(Doc::text(","))
                .append(Doc::space())
                .append(snd.to_doc())
                .append(Doc::text(")"))
                .group(),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Context {
    types: HashMap<String, Vec<DataConstructor>>,
    elems: Vec<ContextElem>,
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.print())
    }
}

impl Context {
    pub fn new(elems: Vec<ContextElem>) -> Context {
        Context {
            types: HashMap::new(),
            elems,
        }
    }

    pub fn print(&self) -> String {
        let mut res = "{\n".to_string();
        self.elems
            .iter()
            .for_each(|ce| res += &format!("  {},\n", &ce));
        self.types.iter().for_each(|(ty, dtors)| {
            res += &format!(
                "  type {} ({}),\n",
                ty,
                dtors
                    .iter()
                    .map(|dtor| format!("{}", dtor))
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        });
        res += "}";
        res
    }

    fn split_at(&self, elem: &ContextElem) -> Option<(&[ContextElem], &[ContextElem])> {
        let pos = self.elems.iter().position(|x| x == elem);
        pos.map(|pos| self.elems.split_at(pos))
    }

    /// Splits the context at the introduction of ExVar(ex)
    fn split_at_ex(&self, ex: &str) -> Option<(&[ContextElem], &ContextElem, &[ContextElem])> {
        let pos = self.elems.iter().position(|e| match e {
            ContextElem::ExVar(e) if e == ex => true,
            _ => false,
        });
        pos.map(|pos| {
            let (before, after) = self.elems.split_at(pos);
            let (ex, after) = after.split_first().unwrap();
            (before, ex, after)
        })
    }

    fn elem(&self, elem: &ContextElem) -> bool {
        self.split_at(elem).is_some()
    }

    fn push(&mut self, elem: ContextElem) {
        self.elems.push(elem)
    }

    fn push_elems(&mut self, elems: Vec<ContextElem>) {
        self.elems.extend(elems.into_iter())
    }

    fn insert_at_ex(&self, ex: &str, elems: Vec<ContextElem>) -> Context {
        match self.split_at_ex(ex) {
            // TODO: Could accept a function that could use the ContextElem here, instead of discarding it
            Some((before, _, after)) => {
                let mut new_elems = vec![];
                new_elems.extend_from_slice(before);
                new_elems.extend(elems.into_iter());
                new_elems.extend_from_slice(after);
                Context {
                    elems: new_elems,
                    types: self.types.clone(),
                }
            }
            None => unreachable!(),
        }
    }

    fn drop_marker(&mut self, marker: ContextElem) {
        let (before_marker, _) = self
            .split_at(&marker)
            .expect("dropping non-existent marker");
        self.elems = before_marker.to_vec();
    }

    fn break_marker(&self, marker: ContextElem) -> (Vec<ContextElem>, Vec<ContextElem>) {
        let (before_marker, after_marker) = self
            .split_at(&marker)
            .unwrap_or_else(|| panic!("breaking non-existent marker: {} {}", self, marker));
        (
            before_marker.to_vec(),
            after_marker.split_first().unwrap().1.to_vec(),
        )
    }

    fn markers(&self) -> Vec<String> {
        self.elems
            .iter()
            .filter_map(|x| match x {
                ContextElem::Marker(m) => Some(m.clone()),
                _ => None,
            })
            .collect()
    }
    fn vars(&self) -> Vec<String> {
        self.elems
            .iter()
            .filter_map(|x| match x {
                ContextElem::Anno(v, _) => Some(v.clone()),
                _ => None,
            })
            .collect()
    }
    fn foralls(&self) -> Vec<String> {
        self.elems
            .iter()
            .filter_map(|x| match x {
                ContextElem::Universal(v) => Some(v.clone()),
                _ => None,
            })
            .collect()
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

    fn find_solved(&self, ex: &str) -> Option<&Type> {
        self.elems.iter().find_map(|e| match e {
            ContextElem::ExVarSolved(var, ty) if var == ex => Some(ty),
            _ => None,
        })
    }

    fn find_var(&self, var: &str) -> Option<Type> {
        self.elems.iter().find_map(|e| match e {
            ContextElem::Anno(v, ty) if v == var => Some(ty.clone()),
            _ => None,
        })
    }

    /// solve (ΓL,α^,ΓR) α τ = (ΓL,α = τ,ΓR)
    fn solve(&self, ex: &str, ty: Type) -> Option<Context> {
        let (gamma_l, gamma_r) = self.break_marker(ContextElem::ExVar(ex.to_string()));
        let mut ctx = Context {
            elems: gamma_l,
            types: self.types.clone(),
        };
        if ctx.wf_type(&ty) {
            ctx.push(ContextElem::ExVarSolved(ex.to_string(), ty));
            ctx.push_elems(gamma_r);
            Some(ctx)
        } else {
            None
        }
    }

    /// existentials_ordered Γ α β = True <=> Γ[α^][β^]
    fn existentials_ordered(&self, ex1: &str, ex2: &str) -> bool {
        let (gamma_l, _) = self.break_marker(ContextElem::ExVar(ex2.to_string()));
        gamma_l.contains(&ContextElem::ExVar(ex1.to_string()))
    }

    fn u_var_wf(&self, var: &str) -> bool {
        self.elem(&ContextElem::Universal(var.to_string()))
    }

    fn forall_wf(&self, vars: &[String], ty: &Type) -> bool {
        let mut tmp_elems = self.elems.clone();
        tmp_elems.extend(vars.iter().map(|v| ContextElem::Universal(v.clone())));
        let tmp_ctx = Context {
            types: self.types.clone(),
            elems: tmp_elems,
        };

        tmp_ctx.wf_type(ty)
    }

    fn evar_wf(&self, evar: &str) -> bool {
        self.elem(&ContextElem::ExVar(evar.to_string()))
    }
    fn solved_evar_wf(&self, evar: &str) -> bool {
        self.elems.iter().any(|el| match el {
            ContextElem::ExVarSolved(var, _) => var == evar,
            _ => false,
        })
    }

    fn wf_type(&self, ty: &Type) -> bool {
        match ty {
            Type::Constructor { arguments, .. } => arguments.iter().all(|arg| self.wf_type(arg)),
            Type::Poly { vars, ty } => self.forall_wf(vars, ty),
            Type::Fun { arg, result } => self.wf_type(arg) && self.wf_type(result),
            Type::Var(var) => self.u_var_wf(var),
            Type::Existential(var) => self.evar_wf(var) || self.solved_evar_wf(var),
            Type::Tuple(fst, snd) => self.wf_type(fst) && self.wf_type(snd),
        }
    }

    fn wf(&self) -> bool {
        self.clone().wf_mut()
    }

    fn wf_mut(&mut self) -> bool {
        if let Some(el) = self.elems.pop() {
            match el {
                // UvarCtx
                ContextElem::Universal(v) => !self.foralls().contains(&v),
                // VarCtx
                ContextElem::Anno(v, ty) => !self.vars().contains(&v) && self.wf_type(&ty),
                //EvarCtx
                ContextElem::ExVar(ex) => !self.existentials().contains(&ex),
                //SolvedEvarCtx
                ContextElem::ExVarSolved(ex, ty) => {
                    !self.existentials().contains(&ex) && self.wf_type(&ty)
                }
                // MarkerCtx
                ContextElem::Marker(m) => {
                    !self.markers().contains(&m) && !self.existentials().contains(&m)
                }
            }
        } else {
            true
        }
    }

    fn apply(&self, ty: &Type) -> Type {
        match ty {
            Type::Constructor { name, arguments } => Type::Constructor {
                name: name.clone(),
                arguments: arguments.iter().map(|arg| self.apply(arg)).collect(),
            },
            Type::Var(v) => Type::Var(v.clone()),
            Type::Existential(ex) => self
                .find_solved(&ex)
                .map_or_else(|| ty.clone(), |ty| self.apply(ty)),
            Type::Fun { arg, result } => Type::Fun {
                arg: Box::new(self.apply(arg)),
                result: Box::new(self.apply(result)),
            },
            Type::Poly { vars, ty } => Type::Poly {
                vars: vars.clone(),
                ty: Box::new(self.apply(ty)),
            },
            Type::Tuple(fst, snd) => {
                Type::Tuple(Box::new(self.apply(fst)), Box::new(self.apply(snd)))
            }
        }
    }

    fn apply_(&self, ty: Type) -> Type {
        match ty {
            Type::Constructor { name, arguments } => Type::Constructor {
                name,
                arguments: arguments.into_iter().map(|arg| self.apply_(arg)).collect(),
            },
            Type::Var(_) => ty,
            Type::Existential(ref ex) => {
                self.find_solved(ex).map_or_else(|| ty, |ty| self.apply(ty))
            }
            Type::Fun { arg, result } => Type::Fun {
                arg: Box::new(self.apply_(*arg)),
                result: Box::new(self.apply_(*result)),
            },
            Type::Poly { vars, ty } => Type::Poly {
                vars: vars.clone(),
                ty: Box::new(self.apply_(*ty)),
            },
            Type::Tuple(fst, snd) => {
                Type::Tuple(Box::new(self.apply_(*fst)), Box::new(self.apply_(*snd)))
            }
        }
    }

    fn apply_expr(&self, expr: TypedExpr) -> TypedExpr {
        expr.map(&|var: Var| Var {
            name: var.name,
            ty: self.apply_(var.ty),
        })
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum ContextElem {
    Universal(String),
    ExVar(String),
    ExVarSolved(String, Type),
    Marker(String),
    Anno(String, Type),
}

impl fmt::Display for ContextElem {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.print())
    }
}

impl ContextElem {
    pub fn print(&self) -> String {
        match self {
            ContextElem::Universal(u) => u.clone(),
            ContextElem::ExVar(ex) => format!("{{{}}}", ex),
            ContextElem::ExVarSolved(ex, ty) => format!("{{{}}} = {}", ex, ty),
            ContextElem::Marker(marker) => format!("|> {}", marker),
            ContextElem::Anno(var, ty) => format!("{} : {}", var, ty),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum TypeError {
    Subtype(Type, Type),
    UnknownVar(String),
    UnknownType(String),
    UnknownDataConstructor(Dtor),
    WrongConstructorArity(Dtor, usize, usize),
    InvalidAnnotation(Type),
    IsNotAFunction(Type),
    ExistentialEscaped(Context, Type, String),
    OccursCheck(String, Type),
    Unification(Type, Type),
    CantInferMatch,
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.print())
    }
}

impl TypeError {
    pub fn print(&self) -> String {
        match self {
            TypeError::Subtype(ty1, ty2) => {
                format!("Can't figure out subtyping between: {} <: {}", ty1, ty2)
            }
            TypeError::UnknownVar(var) => format!("Unknown variable: {}", var),
            TypeError::UnknownType(ty) => format!("Unknown type: {}", ty),
            TypeError::UnknownDataConstructor(dtor) => {
                format!("Unknown data constructor: {}", dtor)
            }
            TypeError::WrongConstructorArity(dtor, expected, actual) => format!(
                "Wrong constructor arity {} arguments we're supplied, but {} expects {}",
                actual, dtor, expected
            ),
            TypeError::InvalidAnnotation(ty) => format!("{} is not a valid annotation here.", ty),
            TypeError::IsNotAFunction(ty) => format!("{} is not a function", ty),
            TypeError::ExistentialEscaped(ctx, ty, ex) => {
                format!("An existential escaped, go get it! {} {} {}", ctx, ty, ex)
            }
            TypeError::OccursCheck(var, ty) => {
                format!("Occurs check failed when unifying {} with type {}", var, ty)
            }
            TypeError::Unification(ty1, ty2) => format!("Failed to unify {} with {}", ty1, ty2),
            TypeError::CantInferMatch => {
                "Can't infer type for a match, please provide an annotation".to_string()
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq, Default)]
pub struct TypeInfo {
    type_arguments: Vec<String>,
    constructors: Vec<DataConstructor>,
}

#[derive(Debug, PartialEq, Eq, Default)]
pub struct TypeChecker {
    name_gen: NameGen,
    types: HashMap<String, TypeInfo>,
}

#[derive(Debug, PartialEq, Eq, Default)]
struct NameGen {
    ty_gen: u32,
    ex_gen: u32,
}

impl NameGen {
    pub fn fresh_ty_var(&mut self) -> String {
        self.ty_gen += 1;
        format!("{}u", self.ty_gen)
    }

    pub fn fresh_var(&mut self) -> String {
        self.ty_gen += 1;
        format!("{}v", self.ty_gen)
    }
}

impl TypeChecker {
    pub fn new() -> TypeChecker {
        Default::default()
    }

    fn add_type_declaration(&mut self, ty_decl: TypeDeclaration) {
        self.types.insert(
            ty_decl.name,
            TypeInfo {
                type_arguments: ty_decl.arguments,
                constructors: ty_decl.constructors,
            },
        );
    }

    fn find_data_constructor(
        &self,
        dtor: &Dtor,
    ) -> Result<(DataConstructor, Vec<String>), TypeError> {
        let type_info = self
            .types
            .get(&dtor.ty)
            .ok_or_else(|| TypeError::UnknownType(dtor.ty.to_string()))?;
        let constructor = type_info
            .constructors
            .iter()
            .find(|d| d.name == dtor.name)
            .cloned()
            .ok_or_else(|| TypeError::UnknownDataConstructor(dtor.clone()))?;
        Ok((constructor, type_info.type_arguments.clone()))
    }

    /// Instantiates all bound type variables for a Polytype with fresh vars,
    /// and returns the renamed type as well as the freshly generated vars
    fn rename_poly<F>(&mut self, vars: &[String], ty: &Type, f: F) -> (Type, Vec<String>)
    where
        F: Fn(String) -> Type,
    {
        let fresh_vars: Vec<(String, String)> = vars
            .iter()
            .map(|v| (v.clone(), self.name_gen.fresh_ty_var()))
            .collect();
        let renamed_ty = {
            let mut tmp_ty = ty.clone();
            for (old, new) in &fresh_vars {
                tmp_ty.subst_mut(old, &f(new.to_string()));
            }
            tmp_ty
        };
        (renamed_ty, fresh_vars.into_iter().map(|x| x.1).collect())
    }

    fn var_bind(&mut self, ctx: Context, var: &str, ty: &Type) -> Result<Context, TypeError> {
        if ty.free_vars().contains(var) {
            Err(TypeError::OccursCheck(var.to_string(), ty.clone()))
        } else {
            Ok(ctx
                .solve(var, ty.clone())
                .expect("Something went wrong in var_bind"))
        }
    }

    pub fn unify(&mut self, ctx: Context, ty1: &Type, ty2: &Type) -> Result<Context, TypeError> {
        debug!("[unify] \n{} ({}) ({})", ctx, ty1, ty2);
        match (ty1, ty2) {
            (ty1, ty2) if ty1 == ty2 => Ok(ctx),
            (
                Type::Constructor {
                    name: name1,
                    arguments: args1,
                },
                Type::Constructor {
                    name: name2,
                    arguments: args2,
                },
            ) if name1 == name2 => {
                if args1.len() != args2.len() {
                    return Err(TypeError::Unification(ty1.clone(), ty2.clone()));
                }
                let mut ctx = ctx;
                for (arg1, arg2) in args1.iter().zip(args2) {
                    let arg1 = ctx.apply(arg1);
                    let arg2 = ctx.apply(arg2);
                    ctx = self.unify(ctx, &arg1, &arg2)?;
                }
                Ok(ctx)
            }
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
                let tmp_ctx = self.unify(ctx, arg1, arg2)?;
                let res1 = tmp_ctx.apply(result1);
                let res2 = tmp_ctx.apply(result2);
                self.unify(tmp_ctx, &res1, &res2)
            }
            (Type::Tuple(fst1, snd1), Type::Tuple(fst2, snd2)) => {
                let tmp_ctx = self.unify(ctx, fst1, fst2)?;
                let snd1 = tmp_ctx.apply(snd1);
                let snd2 = tmp_ctx.apply(snd2);
                self.unify(tmp_ctx, &snd1, &snd2)
            }
            (Type::Existential(ex1), Type::Existential(ex2))
                if ctx.existentials_ordered(ex1, ex2) =>
            {
                Ok(ctx.solve(ex2, Type::Existential(ex1.clone())).unwrap())
            }
            (Type::Existential(ex), ty) => self.var_bind(ctx, ex, ty),
            (ty, Type::Existential(ex)) => self.var_bind(ctx, ex, ty),
            (_, _) => Err(TypeError::Unification(ty1.clone(), ty2.clone())),
        }
    }

    pub fn subtype(&mut self, ctx: Context, ty1: &Type, ty2: &Type) -> Result<Context, TypeError> {
        debug!("[subtype] \n{} ({}) ({})", ctx, ty1, ty2);
        assert!(ctx.wf_type(ty1));
        assert!(ctx.wf_type(ty2));

        match (ty1, ty2) {
            (
                Type::Constructor {
                    name: name1,
                    arguments: args1,
                },
                Type::Constructor {
                    name: name2,
                    arguments: args2,
                },
            ) if name1 == name2 => {
                if args1.len() != args2.len() {
                    Err(TypeError::Unification(ty1.clone(), ty2.clone()))
                } else {
                    let mut ctx = ctx;
                    // For now all type constructors are invariant in their arguments (except for functions)
                    for (arg1, arg2) in args1.iter().zip(args2) {
                        ctx = self.unify(ctx, arg1, arg2)?;
                    }
                    Ok(ctx)
                }
            }
            (Type::Var(v1), Type::Var(v2)) if v1 == v2 => Ok(ctx),
            (Type::Existential(e1), Type::Existential(e2)) if e1 == e2 => Ok(ctx),
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
                let tmp_ctx = self.subtype(ctx, arg2, arg1)?;
                let res1 = tmp_ctx.apply(result1);
                let res2 = tmp_ctx.apply(result2);
                self.subtype(tmp_ctx, &res1, &res2)
            }
            (Type::Tuple(..), Type::Tuple(..)) => self.unify(ctx, ty1, ty2),
            (ty1, Type::Poly { vars, ty: ty2 }) => {
                let (renamed_ty, fresh_vars) = self.rename_poly(vars, ty2, Type::Var);

                let marker_var = fresh_vars[0].clone();
                let mut tmp_ctx = ctx.clone();
                tmp_ctx.push_elems(fresh_vars.into_iter().map(ContextElem::Universal).collect());

                let mut res = self.subtype(tmp_ctx, ty1, &renamed_ty)?;
                res.drop_marker(ContextElem::Universal(marker_var));
                Ok(res)
            }
            (Type::Poly { vars, ty: ty1 }, ty2) => {
                let (renamed_ty, fresh_vars) = self.rename_poly(vars, ty1, Type::Existential);

                let marker_var = fresh_vars[0].clone();
                let mut tmp_ctx = ctx.clone();
                tmp_ctx.push_elems(
                    fresh_vars
                        .into_iter()
                        .flat_map(|v| vec![ContextElem::Marker(v.clone()), ContextElem::ExVar(v)])
                        .collect(),
                );
                let mut res = self.subtype(tmp_ctx, &renamed_ty, ty2)?;
                res.drop_marker(ContextElem::Marker(marker_var));
                Ok(res)
            }
            (Type::Existential(ex), ty) if !ty.free_vars().contains(ex) => {
                self.instantiate_l(ctx, ex, ty)
            }
            (ty, Type::Existential(ex)) if !ty.free_vars().contains(ex) => {
                self.instantiate_r(ctx, ty, ex)
            }
            _ => Err(TypeError::Subtype(ty1.clone(), ty2.clone())),
        }
    }

    fn instantiate_l(&mut self, ctx: Context, ex: &str, ty: &Type) -> Result<Context, TypeError> {
        debug!("[instantiate_l]\n{} ({}) <=: ({})", ctx, ex, ty);
        match ty {
            Type::Existential(ex2) if ctx.existentials_ordered(ex, ex2) => {
                // InstLReac
                let new_ctx = ctx
                    .solve(ex2, Type::Existential(ex.to_string()))
                    .expect("InstLReach, attempted to solve non-existent existential.");
                Ok(new_ctx)
            }
            Type::Fun { arg, result } => {
                // InstLArr
                let a2 = self.name_gen.fresh_ty_var();
                let a1 = self.name_gen.fresh_ty_var();
                let tmp_ctx = ctx.insert_at_ex(
                    ex,
                    vec![
                        ContextElem::ExVar(a2.clone()),
                        ContextElem::ExVar(a1.clone()),
                        ContextElem::ExVarSolved(
                            ex.to_string(),
                            Type::Fun {
                                arg: Box::new(Type::Existential(a1.clone())),
                                result: Box::new(Type::Existential(a2.clone())),
                            },
                        ),
                    ],
                );
                let omega_ctx = self.instantiate_r(tmp_ctx, arg, &a1)?;
                let applied_res = omega_ctx.apply(result);
                self.instantiate_l(omega_ctx, &a2, &applied_res)
            }
            Type::Poly { vars, ty } => {
                //InstLAIIR
                let mut new_ctx = ctx;
                let (renamed_ty, fresh_vars) = self.rename_poly(vars, ty, Type::Existential);
                new_ctx.push_elems(
                    fresh_vars
                        .clone()
                        .into_iter()
                        .map(ContextElem::Universal)
                        .collect(),
                );
                let mut res_ctx = self.instantiate_r(new_ctx, &renamed_ty, ex)?;
                res_ctx.drop_marker(ContextElem::Marker(fresh_vars[0].clone()));
                Ok(res_ctx)
            }
            ty if ty.is_mono() => {
                // InstLSolve
                let mut tmp_ctx = ctx.clone();
                tmp_ctx.drop_marker(ContextElem::ExVar(ex.to_string()));
                if tmp_ctx.wf_type(ty) {
                    Ok(ctx.solve(ex, ty.clone()).unwrap())
                } else {
                    Err(TypeError::ExistentialEscaped(
                        tmp_ctx,
                        ty.clone(),
                        ex.to_string(),
                    ))
                }
            }
            _ => unreachable!("InstLSolve, How did we get here?"),
        }
    }
    fn instantiate_r(&mut self, ctx: Context, ty: &Type, ex: &str) -> Result<Context, TypeError> {
        debug!("[instantiate_r] \n{} ({}) <=: ({})", ctx, ty, ex);
        match ty {
            Type::Existential(ex2) if ctx.existentials_ordered(ex, ex2) => {
                // InstRReach
                Ok(ctx.solve(ex2, Type::Existential(ex.to_string())).unwrap())
            }
            Type::Fun { arg, result } => {
                // InstRArr
                let a1 = self.name_gen.fresh_ty_var();
                let a2 = self.name_gen.fresh_ty_var();
                let tmp_ctx = ctx.insert_at_ex(
                    ex,
                    vec![
                        ContextElem::ExVar(a2.clone()),
                        ContextElem::ExVar(a1.clone()),
                        ContextElem::ExVarSolved(
                            ex.to_string(),
                            Type::Fun {
                                arg: Box::new(Type::Existential(a1.clone())),
                                result: Box::new(Type::Existential(a2.clone())),
                            },
                        ),
                    ],
                );
                let omega_ctx = self.instantiate_l(tmp_ctx, &a1, arg)?;
                let applied_res = omega_ctx.apply(result);
                self.instantiate_r(omega_ctx, &applied_res, &a2)
            }
            Type::Poly { vars, ty } => {
                //InstRAIIL
                let (renamed_ty, fresh_vars) =
                    self.rename_poly(vars, ty, |v| Type::Existential(v.clone()));
                let mut new_ctx = ctx;
                let marker = ContextElem::Marker(fresh_vars[0].clone());
                new_ctx.push_elems(
                    fresh_vars
                        .into_iter()
                        .flat_map(|v| vec![ContextElem::Marker(v.clone()), ContextElem::ExVar(v)])
                        .collect(),
                );
                let mut res_ctx = self.instantiate_r(new_ctx, &renamed_ty, ex)?;
                res_ctx.drop_marker(marker);
                Ok(res_ctx)
            }
            ty if ty.is_mono() => {
                // InstRSolve
                debug!("[InstRSolve] {} := {}", ex, ty);
                let mut tmp_ctx = ctx.clone();
                tmp_ctx.drop_marker(ContextElem::ExVar(ex.to_string()));
                if tmp_ctx.wf_type(ty) {
                    Ok(ctx.solve(ex, ty.clone()).unwrap())
                } else {
                    Err(TypeError::ExistentialEscaped(
                        tmp_ctx.clone(),
                        ty.clone(),
                        ex.to_string(),
                    ))
                }
            }
            _ => unreachable!("InstRSolve, how does this happen?"),
        }
    }

    fn check_case(
        &mut self,
        ctx: Context,
        case: &Case<String>,
        ty_match: &Type,
        ty_body: &Type,
    ) -> Result<(Context, Case<Var>), TypeError> {
        let (data_constructor, ty_args) = self.find_data_constructor(&case.data_constructor)?;

        let mut ctx = ctx;
        let fresh_vars: Vec<(String, Type)> = ty_args
            .into_iter()
            .map(|arg| {
                let fresh = self.name_gen.fresh_ty_var();
                ctx.push(ContextElem::ExVar(fresh.clone()));
                (arg, Type::Existential(fresh))
            })
            .collect();

        // Make sure the type of the case constructor matches the type of the matched expression
        let ty_dtor: Type = Type::Constructor {
            name: case.data_constructor.ty.clone(),
            arguments: fresh_vars.iter().map(|(_, ty)| ty.clone()).collect(),
        };
        let ctx = self.unify(ctx, &ty_dtor, ty_match)?;

        let binders: Vec<(String, Type)> = case
            .binders
            .clone()
            .into_iter()
            .zip(data_constructor.fields)
            .map(|(binder, ty)| (binder, ctx.apply_(ty.subst_many(&fresh_vars))))
            .collect();

        let (ctx, typed_body, typed_binders) =
            self.check_renamed_many(ctx, binders, &case.expr, ty_body)?;
        let applied_body = ctx.apply_expr(typed_body);

        Ok((
            ctx,
            Case {
                data_constructor: case.data_constructor.clone(),
                binders: typed_binders,
                expr: applied_body,
            },
        ))
    }

    fn check_renamed(
        &mut self,
        ctx: Context,
        binder: (String, Type),
        expr: &ParserExpr,
        type_check: &Type,
    ) -> Result<(Context, TypedExpr, Var), TypeError> {
        self.check_renamed_many(ctx, vec![binder], expr, type_check)
            .map(|(ctx, expr, vars)| (ctx, expr, vars[0].clone()))
    }

    fn check_renamed_many(
        &mut self,
        ctx: Context,
        binders: Vec<(String, Type)>,
        expr: &ParserExpr,
        type_check: &Type,
    ) -> Result<(Context, TypedExpr, Vec<Var>), TypeError> {
        let binder_mapping: Vec<(String, Type, String)> = binders
            .into_iter()
            .map(|(name, ty)| (name, ty, self.name_gen.fresh_var()))
            .collect();
        // Insert fresh names
        let expr = expr.subst_many(
            binder_mapping
                .iter()
                .map(|(b, _, fresh)| (b.clone(), Expr::Var(fresh.clone())))
                .collect(),
        );
        let mut binder_iter = binder_mapping.iter();

        let mut typed_binders = vec![];

        let (ctx, typed_expr) = match binder_iter.next() {
            None => self.check(ctx, &expr, type_check)?,
            Some((_, first_ty, first_binder)) => {
                // Setting up the context by adding binders
                let mut ctx = ctx;
                let marker = ContextElem::Anno(first_binder.clone(), first_ty.clone());
                ctx.push(marker.clone());
                for (_, ty, binder) in binder_iter {
                    ctx.push(ContextElem::Anno(binder.to_string(), ty.clone()));
                }

                // Actually check the case's body
                let (mut ctx, typed_case) = self.check(ctx, &expr, type_check)?;

                typed_binders = binder_mapping
                    .iter()
                    .map(|(name, _, fresh)| {
                        let ty_binder = ctx
                            .find_var(&fresh)
                            .expect("var disappeared in bracket_rename")
                            .clone();
                        Var {
                            name: name.clone(),
                            ty: ty_binder.clone(),
                        }
                    })
                    .collect();
                // clean up the context
                ctx.drop_marker(marker);
                (ctx, typed_case)
            }
        };

        // Reversing the renaming
        let typed_expr = typed_expr.subst_many(
            binder_mapping
                .into_iter()
                .map(|(binder, ty, fresh_binder)| {
                    (
                        fresh_binder,
                        Expr::Var(Var {
                            name: binder,
                            ty: ty.clone(),
                        }),
                    )
                })
                .collect(),
        );

        Ok((ctx, typed_expr, typed_binders))
    }

    fn check(
        &mut self,
        ctx: Context,
        expr: &ParserExpr,
        ty: &Type,
    ) -> Result<(Context, TypedExpr), TypeError> {
        debug!("[checking] {} |- {} : {}", ctx, expr, ty);
        match (expr, ty) {
            (Expr::Literal(Literal::Int(i)), ty) if ty == &Type::int() => Ok((ctx, Expr::int(*i))),
            (Expr::Literal(Literal::Bool(b)), ty) if ty == &Type::bool() => {
                Ok((ctx, Expr::bool(*b)))
            }
            (Expr::Lambda { binder, body }, Type::Fun { arg, result }) => {
                let (res_ctx, typed_body, typed_binder) =
                    self.check_renamed(ctx, (binder.clone(), *arg.clone()), body, result)?;
                Ok((
                    res_ctx,
                    Expr::Lambda {
                        binder: typed_binder,
                        body: Box::new(typed_body),
                    },
                ))
            }
            (Expr::Tuple(fst, snd), Type::Tuple(ty_fst, ty_snd)) => {
                let (ctx, typed_fst) = self.check(ctx, fst, ty_fst)?;
                let (ctx, typed_snd) = self.check(ctx, snd, ty_snd)?;
                let typed_fst = ctx.apply_expr(typed_fst);
                Ok((ctx, Expr::tuple(typed_fst, typed_snd)))
            }
            (Expr::Let { binder, expr, body }, ty) => {
                let (ctx, ty_binder, typed_expr) = self.infer(ctx, expr)?;
                let (ctx, typed_body, typed_binder) =
                    self.check_renamed(ctx, (binder.clone(), ty_binder.clone()), body, ty)?;
                Ok((
                    ctx,
                    Expr::Let {
                        binder: typed_binder,
                        expr: Box::new(typed_expr),
                        body: Box::new(typed_body),
                    },
                ))
            }
            (Expr::Match { expr, cases }, ty) => {
                let (mut ctx, ty_match, typed_expr) = self.infer(ctx, expr)?;
                let mut typed_cases = vec![];
                for case in cases.iter() {
                    let ty_expr = &ctx.apply(&ty_match);
                    let (new_ctx, typed_case) = self.check_case(ctx, case, &ty_expr, ty)?;
                    ctx = new_ctx;
                    typed_cases.push(typed_case);
                }
                Ok((
                    ctx,
                    Expr::Match {
                        expr: Box::new(typed_expr),
                        cases: typed_cases,
                    },
                ))
            }
            (_, Type::Poly { vars, ty }) => {
                //forall_l
                let mut tmp_ctx = ctx;
                let (renamed_ty, fresh_vars) =
                    self.rename_poly(&vars, &ty, |v| Type::Var(v.clone()));
                let marker = ContextElem::Universal(fresh_vars[0].clone());
                tmp_ctx.push_elems(fresh_vars.into_iter().map(ContextElem::Universal).collect());
                // TODO: Can I reverse the fresh_vars to their original name here safely?
                let (mut res_ctx, typed_expr) = self.check(tmp_ctx, expr, &renamed_ty)?;
                res_ctx.drop_marker(marker);
                Ok((res_ctx, typed_expr))
            }
            _ => {
                // Sub
                let (ctx, inferred, typed_expr) = self.infer(ctx, expr)?;
                let inferred = ctx.apply(&inferred);
                let ty = ctx.apply(ty);
                let new_ctx = self.subtype(ctx, &inferred, &ty)?;
                let new_typed_expr = new_ctx.apply_expr(typed_expr);
                Ok((new_ctx, new_typed_expr))
            }
        }
    }

    fn infer(
        &mut self,
        ctx: Context,
        expr: &ParserExpr,
    ) -> Result<(Context, Type, TypedExpr), TypeError> {
        match expr {
            Expr::Literal(Literal::Int(i)) => Ok((ctx, Type::int(), Expr::int(*i))),
            Expr::Literal(Literal::Bool(b)) => Ok((ctx, Type::bool(), Expr::bool(*b))),
            Expr::Var(var) => {
                // Var
                let res = match ctx.find_var(var) {
                    Some(ty) => Ok(ty.clone()),
                    None => Err(TypeError::UnknownVar(var.clone())),
                };
                res.map(|ty| {
                    (
                        ctx,
                        ty.clone(),
                        Expr::Var(Var {
                            name: var.to_string(),
                            ty,
                        }),
                    )
                })
            }
            Expr::Ann { expr, ty } => {
                // Anno
                if ctx.wf_type(ty) {
                    let (new_ctx, typed_expr) = self.check(ctx, expr, ty)?;
                    let typed_expr = new_ctx.apply_expr(typed_expr);
                    Ok((new_ctx, ty.clone(), typed_expr))
                } else {
                    Err(TypeError::InvalidAnnotation(ty.clone()))
                }
            }
            Expr::Let { binder, expr, body } => {
                let (ctx, ty_binder, typed_expr) = self.infer(ctx, expr)?;
                let binder_fresh = self.name_gen.fresh_var();
                let mut tmp_ctx = ctx;
                let marker = ContextElem::Anno(binder_fresh.clone(), ty_binder.clone());
                tmp_ctx.push(marker.clone());
                let body = body.subst(binder, &Expr::Var(binder_fresh.clone()));
                let (mut res_ctx, ty_body, typed_body) = self.infer(tmp_ctx, &body)?;
                let ty_binder = res_ctx.apply(&ty_binder);
                res_ctx.drop_marker(marker);
                let typed_body = typed_body.subst_var(&binder_fresh, binder);
                Ok((
                    res_ctx,
                    ty_body,
                    Expr::Let {
                        binder: Var {
                            name: binder.to_string(),
                            ty: ty_binder,
                        },
                        expr: Box::new(typed_expr),
                        body: Box::new(typed_body),
                    },
                ))
            }
            Expr::Lambda { binder, body } => {
                // ->l=>
                let mut tmp_ctx = ctx;
                let binder_fresh = self.name_gen.fresh_var();
                let a = self.name_gen.fresh_ty_var();
                let b = self.name_gen.fresh_ty_var();
                let marker = ContextElem::Anno(binder_fresh.clone(), Type::Existential(a.clone()));
                tmp_ctx.push_elems(vec![
                    ContextElem::ExVar(a.clone()),
                    ContextElem::ExVar(b.clone()),
                    marker.clone(),
                ]);

                let (mut res_ctx, typed_body) = self.check(
                    tmp_ctx,
                    &body.subst(binder, &Expr::Var(binder_fresh.clone())),
                    &Type::Existential(b.clone()),
                )?;
                res_ctx.drop_marker(marker);
                let typed_body = typed_body.subst_var(&binder_fresh, binder);
                Ok((
                    res_ctx,
                    Type::fun(Type::ex(&a), Type::ex(&b)),
                    Expr::Lambda {
                        binder: Var {
                            name: binder.clone(),
                            ty: Type::ex(&a),
                        },
                        body: Box::new(typed_body),
                    },
                ))
            }
            Expr::App { func, arg } => {
                let (ctx, func_ty, typed_func) = self.infer(ctx, func)?;
                let applied_func_ty = ctx.apply(&func_ty);
                let (ctx, app_ty, typed_arg) =
                    self.infer_application(ctx, &applied_func_ty, arg)?;
                Ok((
                    ctx,
                    app_ty,
                    Expr::App {
                        func: Box::new(typed_func),
                        arg: Box::new(typed_arg),
                    },
                ))
            }
            Expr::Construction { dtor, args } => {
                let (DataConstructor { fields, .. }, ty_args) =
                    self.find_data_constructor(&dtor)?;
                if args.len() != fields.len() {
                    return Err(TypeError::WrongConstructorArity(
                        dtor.clone(),
                        fields.len(),
                        args.len(),
                    ));
                }

                let mut ctx = ctx;
                let fresh_vars: Vec<(String, Type)> = ty_args
                    .into_iter()
                    .map(|arg| {
                        let fresh = self.name_gen.fresh_ty_var();
                        ctx.push(ContextElem::ExVar(fresh.clone()));
                        (arg, Type::Existential(fresh))
                    })
                    .collect();

                let mut typed_fields = vec![];
                for (arg, ty) in args.iter().zip(fields.clone()) {
                    let (new_ctx, typed_field) =
                        self.check(ctx, &arg, &ty.subst_many(&fresh_vars))?;
                    ctx = new_ctx;
                    typed_fields.push(typed_field);
                }

                let type_arguments = fresh_vars
                    .into_iter()
                    .map(|(_, ty)| ctx.apply_(ty))
                    .collect();
                Ok((
                    ctx,
                    Type::Constructor {
                        name: dtor.ty.to_string(),
                        arguments: type_arguments,
                    },
                    Expr::Construction {
                        dtor: dtor.clone(),
                        args: typed_fields,
                    },
                ))
            }

            Expr::Tuple(fst, snd) => {
                let (ctx, fst_ty, typed_fst) = self.infer(ctx, fst)?;
                let (ctx, snd_ty, typed_snd) = self.infer(ctx, snd)?;
                Ok((
                    ctx,
                    Type::tuple(fst_ty, snd_ty),
                    Expr::tuple(typed_fst, typed_snd),
                ))
            }
            Expr::Match { .. } => Err(TypeError::CantInferMatch),
        }
    }

    fn infer_application(
        &mut self,
        ctx: Context,
        ty: &Type,
        expr: &ParserExpr,
    ) -> Result<(Context, Type, TypedExpr), TypeError> {
        match ty {
            Type::Poly { vars, ty: ty1 } => {
                // forall App
                debug!("[forall App] {} {} . {}", ctx, ty, expr);
                let (renamed_ty, fresh_vars) =
                    self.rename_poly(vars, ty1, |v| Type::Existential(v.clone()));
                let mut new_ctx = ctx;
                new_ctx.push_elems(fresh_vars.into_iter().map(ContextElem::ExVar).collect());
                self.infer_application(new_ctx, &renamed_ty, expr)
            }
            Type::Existential(ex) => {
                // alpha^app
                let a1 = self.name_gen.fresh_ty_var();
                let a2 = self.name_gen.fresh_ty_var();
                let new_ctx = ctx.insert_at_ex(
                    ex,
                    vec![
                        ContextElem::ExVar(a2.clone()),
                        ContextElem::ExVar(a1.clone()),
                        ContextElem::ExVarSolved(
                            ex.clone(),
                            Type::Fun {
                                arg: Box::new(Type::Existential(a1.clone())),
                                result: Box::new(Type::Existential(a2.clone())),
                            },
                        ),
                    ],
                );
                let (res_ctx, typed_expr) = self.check(new_ctx, expr, &Type::Existential(a1))?;
                Ok((res_ctx, Type::Existential(a2), typed_expr))
            }
            Type::Fun { arg, result } => {
                // ->App
                debug!("[->App] {} . {}", ty, expr);
                let (res_ctx, typed_expr) = self.check(ctx, expr, arg)?;
                let applied_res = res_ctx.apply(result);
                Ok((res_ctx, applied_res, typed_expr))
            }
            ty => Err(TypeError::IsNotAFunction(ty.clone())),
        }
    }

    pub fn synth(&mut self, expr: &ParserExpr) -> Result<Type, TypeError> {
        let initial_ctx = Context::new(vec![
            ContextElem::Anno("primadd".to_string(), Type::int()),
            ContextElem::Anno("pi".to_string(), Type::int()),
        ]);
        self.infer(initial_ctx, expr).map(|x| {
            debug!("synth_ctx: {:?}", x.0);
            x.0.apply(&x.1)
        })
    }
    pub fn synth_prog(
        &mut self,
        prog: Vec<Declaration<String>>,
    ) -> Result<Vec<(Declaration<Var>, Type)>, TypeError> {
        let mk_prim = |name: &str| {
            ContextElem::Anno(
                name.to_string(),
                Type::Poly {
                    vars: vec!["a".to_string()],
                    ty: Box::new(Type::var("a")),
                },
            )
        };

        let mut ctx = Context::new(vec![
            mk_prim("primadd"),
            mk_prim("primtuple"),
            mk_prim("primfst"),
            mk_prim("primsnd"),
        ]);
        let mut result = vec![];

        for decl in prog {
            match decl {
                Declaration::Type(type_decl) => {
                    self.add_type_declaration(type_decl.clone());
                    result.push((Declaration::Type(type_decl), Type::int()))
                }
                Declaration::Value(ValueDeclaration { name, expr }) => {
                    debug!(
                        "Inferring declaration {}: \n=============================",
                        name
                    );
                    let (mut new_ctx, ty, expr) = self.infer(ctx, &expr)?;
                    new_ctx.push(ContextElem::Anno(name.to_string(), new_ctx.apply(&ty)));

                    ctx = new_ctx;
                    result.push((
                        Declaration::Value(ValueDeclaration {
                            name: name.clone(),
                            expr,
                        }),
                        ty,
                    ));
                }
            }
        }

        Ok(result)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subst_mut() {
        let mut ty = Type::var("x");
        ty.subst_mut(&"x".to_string(), &Type::int());
        assert_eq!(ty, Type::int());
    }

    #[test]
    fn subst_mut_fun() {
        let mut ty = Type::fun(Type::var("a"), Type::var("b"));
        ty.subst_mut(&"a".to_string(), &Type::int());
        assert_eq!(ty, Type::fun(Type::int(), Type::var("b")));
    }

    #[test]
    fn solve_ex() {
        let ctx = Context::new(vec![
            ContextElem::Universal("x".to_string()),
            ContextElem::ExVar("alpha".to_string()),
            ContextElem::Anno("var".to_string(), Type::int()),
        ]);
        let expected = Context::new(vec![
            ContextElem::Universal("x".to_string()),
            ContextElem::ExVarSolved("alpha".to_string(), Type::Var("x".to_string())),
            ContextElem::Anno("var".to_string(), Type::int()),
        ]);
        let new_ctx = ctx.solve(&"alpha".to_string(), Type::Var("x".to_string()));
        assert_eq!(new_ctx, Some(expected));
    }

    #[test]
    fn subty() {
        let mut tc = TypeChecker::new();
        let ctx = Context::new(vec![]);
        let a = Type::poly(vec!["a"], Type::var("a"));
        let b = Type::int();
        // (forall a. a) <: Int
        let res = tc.subtype(ctx, &a, &b);
        assert_eq!(res, Ok(Context::new(vec![])));
    }
}
