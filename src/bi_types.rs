use crate::types::Type;
use crate::expr::Expr;

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
        NameGen { ty_gen: 0, ex_gen: 0}
    }

    pub fn fresh_var(&mut self) -> String {
        self.ty_gen = self.ty_gen + 1;
        format!("{}v", self.ty_gen)
    }
}

#[derive(Debug, PartialEq, Eq, Clone)]
struct Context {
    elems: Vec<ContextElem>
}

impl Context {

    fn split_at(&self, elem: &ContextElem) -> Option<(&[ContextElem], &[ContextElem])> {
        let pos = self.elems.iter().position(|x| x == elem);
        pos.map(|pos| self.elems.split_at(pos))
    }

    fn elem(&self, elem: ContextElem) -> bool {
        self.split_at(&elem).is_some()
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
        TypeChecker{ name_gen: NameGen::new() }
    }

    fn check(&mut self, expr: Expr, ty: Type) -> bool {
        false
    }

    fn infer(&mut self, expr: Expr) -> Type {
        Type::Int
    }
}
