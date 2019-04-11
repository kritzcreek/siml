use crate::expr::Expr;
use std::collections::HashMap;

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Type {
    Int,
    Bool,
    Fun { arg: Box<Type>, result: Box<Type> },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Scheme {
    vars: Vec<String>,
    ty: Type,
}

impl Type {
    pub fn print(&self) -> String {
        match self {
            Type::Int => "Int".to_string(),
            Type::Bool => "Bool".to_string(),
            Type::Fun { arg, result } => format!("({}) -> {}", arg.print(), result.print()),
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum TypeError {
    Unification(Type, Type),
    UnboundName(String),
}

impl TypeError {
    pub fn print(&self) -> String {
        match self {
            TypeError::Unification(ty1, ty2) => {
                format!("Couldn't match type {} with {}", ty1.print(), ty2.print())
            }
            TypeError::UnboundName(name) => format!("Unbound name: {} ", name),
        }
    }
}

type Environment = HashMap<String, Scheme>;

pub struct TypeChecker {
    supply: u32,
}

impl TypeChecker {
    pub fn new() -> TypeChecker {
        TypeChecker { supply: 0 }
    }

    fn fresh_name(&mut self, name: String) -> String {
        self.supply = self.supply + 1;
        format!("{}{}", self.supply.to_string(), name)
    }

    pub fn infer_expr(&mut self, expr: &Expr) -> Result<Type, TypeError> {
        self.infer(HashMap::new(), expr)
    }

    fn infer(&mut self, env: Environment, expr: &Expr) -> Result<Type, TypeError> {
        Err(TypeError::UnboundName("Lol".to_string()))
    }
}
