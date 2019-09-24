#![allow(dead_code)]

use crate::expr::{
    Case, DataConstructor, Declaration, Dtor, Expr, HasIdent, Literal, NewTypedExpr, NewVar,
    ParserExpr, TypeDeclaration, ValueDeclaration,
};
use crate::pretty::render_doc;
use pretty::{BoxDoc, Doc};
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Type {
    Constructor { name: String, arguments: Vec<Type> },
    Var(String),
    Unknown(u32),
    Poly { vars: Vec<String>, ty: Box<Type> },
    Fun { arg: Box<Type>, result: Box<Type> },
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", render_doc(self.to_doc()))
    }
}

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

    fn fun(arg: Type, result: Type) -> Type {
        Type::Fun {
            arg: Box::new(arg),
            result: Box::new(result),
        }
    }

    pub fn unknowns(&self) -> HashSet<u32> {
        let mut res = HashSet::new();
        match self {
            Type::Unknown(u) => {
                res.insert(u.clone());
            }
            Type::Fun { arg, result } => {
                res.extend(arg.unknowns());
                res.extend(result.unknowns());
            }
            Type::Var(_) => {}
            Type::Poly { ty, .. } => {
                res.extend(ty.unknowns());
            }
            Type::Constructor { arguments, .. } => {
                for arg in arguments {
                    res.extend(arg.unknowns())
                }
            }
        }
        res
    }

    fn unfold_fun_inner(self) -> Vec<Self> {
        match self {
            Type::Fun { arg, result } => {
                let mut res = result.unfold_fun_inner();
                res.push(*arg);
                res
            }
            _ => vec![self],
        }
    }

    pub fn unfold_fun(self) -> Vec<Self> {
        let mut res = self.unfold_fun_inner();
        res.reverse();
        res
    }

    pub fn subst(self, unknown: u32, replacement: &Type) -> Type {
        match self {
            Type::Constructor { name, arguments } => Type::Constructor {
                name,
                arguments: arguments
                    .into_iter()
                    .map(|arg| arg.subst(unknown, replacement))
                    .collect(),
            },
            Type::Var(_) => self,
            Type::Unknown(u) => {
                if u == unknown {
                    replacement.clone()
                } else {
                    self
                }
            }
            Type::Poly { vars, ty } => Type::Poly {
                vars,
                ty: Box::new(ty.subst(unknown, replacement)),
            },
            Type::Fun { arg, result } => Type::Fun {
                arg: Box::new(arg.subst(unknown, replacement)),
                result: Box::new(result.subst(unknown, replacement)),
            },
        }
    }

    pub fn subst_mut(&mut self, unknown: u32, replacement: &Type) {
        match self {
            Type::Constructor { arguments, .. } => {
                for arg in arguments {
                    arg.subst_mut(unknown, replacement)
                }
            }
            Type::Var(_) => {}
            Type::Unknown(u) => {
                if *u == unknown {
                    *self = replacement.clone();
                }
            }
            Type::Poly { ty, .. } => {
                ty.subst_mut(unknown, replacement);
            }
            Type::Fun { arg, result } => {
                arg.subst_mut(unknown, replacement);
                result.subst_mut(unknown, replacement);
            }
        }
    }

    pub fn subst_many(mut self, subst: &[(u32, Type)]) -> Type {
        for (v, t) in subst {
            self.subst_mut(*v, t);
        }
        self
    }

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

            Type::Unknown(u) => Doc::text(format!("u{}", u)),
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
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum TypeError {
    UnknownVar(String),
    UnknownType(String),
    UnknownDataConstructor(Dtor),
    WrongConstructorArity(Dtor, usize, usize),
    InvalidAnnotation(Type),
    IsNotAFunction(Type),
    OccursCheck(u32, Type),
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
            TypeError::OccursCheck(u, ty) => {
                format!("Occurs check failed when unifying u{} with type {}", u, ty)
            }
            TypeError::Unification(ty1, ty2) => format!("Failed to unify {} with {}", ty1, ty2),
            TypeError::CantInferMatch => {
                "Can't infer type for a match, please provide an annotation".to_string()
            }
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
struct TypedValue {
    expr: NewTypedExpr,
    ty: Type,
}

#[derive(Debug, PartialEq, Default)]
pub struct CheckState {
    unknown_supply: u32,
    types: HashMap<String, Vec<DataConstructor>>,
    subst: HashMap<u32, Type>,
    context: HashMap<String, Type>,
}

#[derive(Debug, Default)]
pub struct TypeChecker {
    state: CheckState,
}

impl TypeChecker {
    fn new() -> TypeChecker {
        Default::default()
    }

    fn fresh_unknown(&mut self) -> Type {
        self.state.unknown_supply += 1;
        Type::Unknown(self.state.unknown_supply)
    }

    fn zonk_type(&self, ty: Type) -> Type {
        match ty {
            Type::Var(_) => ty,
            Type::Fun { arg, result } => Type::fun(self.zonk_type(*arg), self.zonk_type(*result)),
            Type::Constructor { name, arguments } => Type::Constructor {
                name,
                arguments: arguments.into_iter().map(|t| self.zonk_type(t)).collect(),
            },
            Type::Poly { vars, ty } => Type::Poly {
                vars,
                ty: Box::new(self.zonk_type(*ty)),
            },
            Type::Unknown(u) => match self.state.subst.get(&u) {
                None => ty,
                Some(ty) => self.zonk_type(ty.clone()),
            },
        }
    }

    fn zonk_expr(&self, expr: NewTypedExpr) -> NewTypedExpr {
        expr.map(&|NewVar { name, ty }| NewVar {
            name,
            ty: self.zonk_type(ty),
        })
    }

    fn lookup_name(&self, name: &str) -> Result<Type, TypeError> {
        match self.state.context.get(name) {
            Some(ty) => Ok(ty.clone()),
            None => Err(TypeError::UnknownVar(name.to_string())),
        }
    }

    fn bind_name<F, A>(&mut self, name: String, ty: Type, action: F) -> A
    where
        F: FnOnce(&mut Self) -> A,
    {
        self.bind_names(vec![(name, ty)], action)
    }

    fn bind_names<F, A>(&mut self, binders: Vec<(String, Type)>, action: F) -> A
    where
        F: FnOnce(&mut Self) -> A,
    {
        let old_context = self.state.context.clone();
        for (name, ty) in binders {
            self.state.context.insert(name, ty);
        }
        let result = action(self);
        self.state.context = old_context;
        result
    }

    fn occurs_check(&self, unknown: u32, ty: &Type) -> Result<(), TypeError> {
        match ty {
            Type::Unknown(_) => {}
            ty => {
                if ty.unknowns().contains(&unknown) {
                    return Err(TypeError::OccursCheck(unknown, ty.clone()));
                }
            }
        }
        Ok(())
    }

    fn solve_type(&mut self, unknown: u32, ty: Type) -> Result<(), TypeError> {
        self.occurs_check(unknown, &ty)?;
        self.state.subst.insert(unknown, ty);
        Ok(())
    }

    fn unify(&mut self, ty1: Type, ty2: Type) -> Result<(), TypeError> {
        let ty1 = self.zonk_type(ty1);
        let ty2 = self.zonk_type(ty2);

        match (ty1, ty2) {
            (ref ty1, ref ty2) if ty1 == ty2 => {}
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
                self.unify(*arg1, *arg2)?;
                self.unify(*result1, *result2)?;
            }
            (
                Type::Constructor {
                    name: name1,
                    arguments: arguments1,
                },
                Type::Constructor {
                    name: name2,
                    arguments: arguments2,
                },
            ) => {
                if name1 != name2 || arguments1.len() != arguments2.len() {
                    return Err(TypeError::Unification(
                        Type::Constructor {
                            name: name1,
                            arguments: arguments1,
                        },
                        Type::Constructor {
                            name: name2,
                            arguments: arguments2,
                        },
                    ));
                }

                for (arg1, arg2) in arguments1.into_iter().zip(arguments2) {
                    self.unify(arg1, arg2)?
                }
            }
            (Type::Unknown(u), ty2) => self.solve_type(u, ty2)?,
            (ty1, Type::Unknown(u)) => self.solve_type(u, ty1)?,
            (ty1, ty2) => return Err(TypeError::Unification(ty1, ty2)),
        }
        Ok(())
    }

    fn check<B: HasIdent>(&mut self, expr: Expr<B>, ty: Type) -> Result<TypedValue, TypeError> {
        Err(TypeError::CantInferMatch)
    }

    fn check_application<B: HasIdent>(
        &mut self,
        fun: TypedValue,
        arg: Expr<B>,
    ) -> Result<TypedValue, TypeError> {
        let TypedValue {
            expr: fun,
            ty: ty_fun,
        } = fun;
        match ty_fun {
            Type::Fun {
                arg: ty_arg,
                result,
            } => {
                let typed_arg = self.check(arg, *ty_arg)?;
                Ok(TypedValue {
                    expr: Expr::app(fun, typed_arg.expr),
                    ty: *result,
                })
            }
            ty_fun => {
                let typed_arg = self.infer(arg)?;
                let ty_res = self.fresh_unknown();
                self.unify(ty_fun, Type::fun(typed_arg.ty, ty_res.clone()))?;
                Ok(TypedValue {
                    expr: Expr::app(fun, typed_arg.expr),
                    ty: ty_res,
                })
            }
        }
    }

    fn infer<B: HasIdent>(&mut self, expr: Expr<B>) -> Result<TypedValue, TypeError> {
        match expr {
            Expr::App { func, arg } => {
                let typed_fun = self.infer(*func)?;
                self.check_application(typed_fun, *arg)
            }
            Expr::Lambda { binder, body } => {
                let ty_binder = self.fresh_unknown();
                let typed_body =
                    self.bind_name(binder.ident(), ty_binder.clone(), |tc| tc.infer(*body))?;
                Ok(TypedValue {
                    expr: Expr::Lambda {
                        binder: NewVar {
                            name: binder.ident(),
                            ty: ty_binder.clone(),
                        },
                        body: Box::new(typed_body.expr),
                    },
                    ty: Type::fun(ty_binder, typed_body.ty),
                })
            }
            Expr::Let { binder, expr, body } => {
                let typed_expr = self.infer(*expr)?;
                let typed_body =
                    self.bind_name(binder.ident(), typed_expr.ty.clone(), |tc| tc.infer(*body))?;
                Ok(TypedValue {
                    expr: Expr::Let {
                        binder: NewVar {
                            name: binder.ident(),
                            ty: typed_expr.ty,
                        },
                        expr: Box::new(typed_expr.expr),
                        body: Box::new(typed_body.expr),
                    },
                    ty: typed_body.ty,
                })
            }
            Expr::Var(v) => {
                let var = v.ident();
                let ty_var = self.lookup_name(&var)?;
                // TODO: instantiate
                Ok(TypedValue {
                    expr: Expr::Var(NewVar {
                        name: var,
                        ty: ty_var.clone(),
                    }),
                    ty: ty_var,
                })
            }
            Expr::Literal(Literal::Int(i)) => Ok(TypedValue {
                expr: Expr::Literal(Literal::Int(i)),
                ty: Type::int(),
            }),
            Expr::Literal(Literal::Bool(b)) => Ok(TypedValue {
                expr: Expr::Literal(Literal::Bool(b)),
                ty: Type::bool(),
            }),
            _ => Err(TypeError::CantInferMatch), // App {func: Box<Expr<B>>, arg: Box<Expr<B>>,},
                                                 // Lambda {binder: B, body: Box<Expr<B>>,},
                                                 // Let {binder: B, expr: Box<Expr<B>>, body: Box<Expr<B>>,},
                                                 // Var(B),
                                                 // Literal(Literal),
                                                 // Construction {dtor: Dtor, args: Vec<Expr<B>>,},
                                                 // Match {expr: Box<Expr<B>>, cases: Vec<Case<B>>,},
                                                 // Ann {expr: Box<Expr<B>>, ty: Type,},
                                                 // Tuple(Box<Expr<B>>, Box<Expr<B>>),
        }
    }
}
