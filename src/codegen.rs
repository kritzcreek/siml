use crate::bi_types::Type;
use crate::expr::{Case, Declaration, Expr, HasIdent, Literal, TypedExpr, ValueDeclaration, Var};
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Debug, Default)]
pub struct Lowering {
    supply: u32,
}

impl Lowering {
    pub fn new() -> Lowering {
        Default::default()
    }

    fn fresh_name(&mut self, s: String) -> String {
        self.supply += 1;
        format!("{}{}", s, self.supply)
    }

    fn fresh_top_name(&mut self) -> String {
        self.fresh_name("$".to_owned())
    }

    pub fn lower(
        &mut self,
        prog: Vec<(Declaration<Var>, Type)>,
    ) -> Result<Vec<(Declaration<Var>, Type)>, CodegenError> {
        let mut res = vec![];
        for (decl, ty) in prog {
            match decl {
                Declaration::Type(..) => res.push((decl, ty)),
                Declaration::Value(value_decl) => {
                    let (expr, decls) = self.lambda_lift(value_decl.expr)?;
                    res.extend(
                        decls
                            .into_iter()
                            .map(|(vd, ty)| (Declaration::Value(vd), ty)),
                    );
                    res.push((
                        Declaration::Value(ValueDeclaration {
                            name: value_decl.name,
                            expr,
                        }),
                        ty,
                    ))
                }
            }
        }
        Ok(res)
    }

    pub fn lambda_lift(
        &mut self,
        expr: TypedExpr,
    ) -> Result<(TypedExpr, Vec<(ValueDeclaration<Var>, Type)>), CodegenError> {
        match expr {
            Expr::Lambda { .. } => {
                let (binders, body) = expr.collapse_lambdas();
                let (lifted_body, ds) = self.lambda_lift_inner(body)?;
                let lam = binders
                    .into_iter()
                    .rev()
                    .fold(lifted_body, |expr, b| Expr::Lambda {
                        binder: b,
                        body: Box::new(expr),
                    });
                Ok((lam, ds))
            }
            _ => self.lambda_lift_inner(expr),
        }
    }

    pub fn lambda_lift_inner(
        &mut self,
        expr: TypedExpr,
    ) -> Result<(TypedExpr, Vec<(ValueDeclaration<Var>, Type)>), CodegenError> {
        match expr {
            Expr::Var(_) => Ok((expr, vec![])),
            Expr::Literal(_) => Ok((expr, vec![])),
            Expr::App { func, arg } => {
                let (lifted_func, mut d1) = self.lambda_lift_inner(*func)?;
                let (lifted_arg, d2) = self.lambda_lift_inner(*arg)?;
                d1.extend(d2);
                Ok((
                    Expr::App {
                        func: Box::new(lifted_func),
                        arg: Box::new(lifted_arg),
                    },
                    d1,
                ))
            }
            Expr::Ann { ty, expr } => {
                let (lifted_expr, ds) = self.lambda_lift_inner(*expr)?;
                Ok((
                    Expr::Ann {
                        ty,
                        expr: Box::new(lifted_expr),
                    },
                    ds,
                ))
            }
            Expr::Let { binder, expr, body } => {
                let (lifted_expr, mut d1) = self.lambda_lift_inner(*expr)?;
                let (lifted_body, d2) = self.lambda_lift_inner(*body)?;
                d1.extend(d2);
                Ok((
                    Expr::Let {
                        binder,
                        expr: Box::new(lifted_expr),
                        body: Box::new(lifted_body),
                    },
                    d1,
                ))
            }
            Expr::Lambda { .. } => {
                let (binders, body) = expr.collapse_lambdas();
                let binders_len = binders.len();
                let fresh_name = self.fresh_top_name();
                let (lifted_body, mut ds) = self.lambda_lift_inner(body)?;
                let value_decl = ValueDeclaration {
                    name: fresh_name.clone(),
                    expr: binders
                        .into_iter()
                        .rev()
                        .fold(lifted_body, |e, b| Expr::Lambda {
                            binder: b,
                            body: Box::new(e),
                        }),
                };

                // TODO Figure out the actual type here
                // So far we're just creating a function type with enough arguments
                // so we generate the right WASM signature
                let ty = std::iter::repeat(Type::int())
                    .take(binders_len)
                    .fold(Type::int(), |acc, ty| Type::fun(ty, acc));

                ds.push((value_decl, ty.clone()));
                Ok((
                    Expr::Var(Var {
                        name: fresh_name,
                        ty,
                    }),
                    ds,
                ))
            }
            Expr::Construction { dtor, args } => {
                let mut ds = vec![];
                let mut lifted_args = vec![];
                for arg in args {
                    let (lifted_expr, current_ds) = self.lambda_lift_inner(arg)?;
                    lifted_args.push(lifted_expr);
                    ds.extend(current_ds);
                }
                Ok((
                    Expr::Construction {
                        dtor,
                        args: lifted_args,
                    },
                    ds,
                ))
            }
            Expr::Match { expr, cases } => {
                let (lifted_expr, mut ds) = self.lambda_lift_inner(*expr)?;
                let mut lifted_cases = vec![];
                for Case {
                    data_constructor,
                    binders,
                    expr,
                } in cases
                {
                    let (lifted_case, current_ds) = self.lambda_lift_inner(expr)?;
                    lifted_cases.push(Case {
                        data_constructor,
                        binders,
                        expr: lifted_case,
                    });
                    ds.extend(current_ds)
                }
                Ok((
                    Expr::Match {
                        expr: Box::new(lifted_expr),
                        cases: lifted_cases,
                    },
                    ds,
                ))
            }
            Expr::Tuple { .. } => Err(CodegenError::NotImplemented("tuple".to_string())),
        }
    }
}

#[derive(Debug)]
pub enum CodegenError {
    NotImplemented(String),
}

impl fmt::Display for CodegenError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            match self {
                CodegenError::NotImplemented(str) => {
                    format!("Codegen not implemented for: {}", str)
                }
            }
        )
    }
}

#[derive(Default)]
pub struct Codegen {
    supply: u32,
    /// A mapping from names to their index in the function table as well as their type
    global_names: HashMap<String, (u32, Type)>,
    out: String,
}

impl Codegen {
    pub fn new() -> Codegen {
        Codegen {
            supply: 0,
            global_names: HashMap::new(),
            out: String::new(),
        }
    }

    fn fresh_name(&mut self, s: &str) -> String {
        self.supply += 1;
        format!("${}{}", s, self.supply)
    }

    fn populate_global_names(&mut self, prog: &[(Declaration<Var>, Type)]) {
        let mut index_supply: u32 = 0;
        let mut global_names = HashMap::new();
        for decl in prog {
            if let (Declaration::Value(ValueDeclaration { name, .. }), ty) = decl {
                global_names.insert(name.to_string(), (index_supply, ty.clone()));
                index_supply += 1;
            }
        }
        self.global_names = global_names;
    }

    pub fn codegen(mut self, prog: &[(Declaration<Var>, Type)]) -> Result<String, CodegenError> {
        self.populate_global_names(prog);
        self.out += "(module\n";
        self.rts();
        for decl in prog {
            if let (Declaration::Value(ValueDeclaration { name, expr }), ty) = decl {
                self.fun(name, &expr, ty)?;
            }
        }
        self.entry_point();
        self.function_table();
        self.out += "\n)";
        Ok(self.out)
    }

    fn rts(&mut self) {
        self.out += ALLOCATOR_RTS;
        self.out += CLOSURE_RTS;
    }

    pub fn case_lift(
        &mut self,
        expr: TypedExpr,
    ) -> Result<(TypedExpr, HashSet<String>), CodegenError> {
        let mut used: HashSet<String> = HashSet::new();
        Ok((self.case_lift_inner(&mut used, expr)?, used))
    }

    fn case_lift_inner(
        &mut self,
        used: &mut HashSet<String>,
        expr: TypedExpr,
    ) -> Result<Expr<Var>, CodegenError> {
        match expr {
            Expr::App { func, arg } => Ok(Expr::App {
                func: Box::new(self.case_lift_inner(used, *func)?),
                arg: Box::new(self.case_lift_inner(used, *arg)?),
            }),
            Expr::Lambda { binder, body } => Ok(Expr::Lambda {
                binder,
                body: Box::new(self.case_lift_inner(used, *body)?),
            }),
            Expr::Let { binder, expr, body } => Ok(Expr::Let {
                binder,
                expr: Box::new(self.case_lift_inner(used, *expr)?),
                body: Box::new(self.case_lift_inner(used, *body)?),
            }),
            Expr::Var(var) => Ok(Expr::Var(var)),
            Expr::Literal(lit) => Ok(Expr::Literal(lit)),
            Expr::Ann { expr, ty } => Ok(Expr::Ann {
                expr: Box::new(self.case_lift_inner(used, *expr)?),
                ty,
            }),
            Expr::Tuple(..) => Err(CodegenError::NotImplemented("tuple".to_string())),
            Expr::Construction { dtor, args } => {
                let mut lifted_args = vec![];
                for arg in args {
                    lifted_args.push(self.case_lift_inner(used, arg)?)
                }
                Ok(Expr::Construction {
                    dtor,
                    args: lifted_args,
                })
            }
            Expr::Match { expr, cases } => {
                let lifted_expr = self.case_lift_inner(used, *expr)?;
                let max_binders = cases
                    .iter()
                    .fold(0, |acc, case| usize::max(acc, case.binders.len()));
                let mut fresh_binders = Vec::with_capacity(max_binders);
                for _ in 1..=max_binders {
                    fresh_binders.push(self.fresh_name("case"))
                }
                used.extend(fresh_binders.clone());

                let mut lifted_cases: Vec<Case<Var>> = Vec::with_capacity(cases.len());
                for Case {
                    data_constructor,
                    binders,
                    expr,
                } in cases
                {
                    let case_binders: Vec<(&Var, &String)> = binders.iter().zip(fresh_binders.iter()).collect();
                    let renamed_expr = expr.subst_var_many(case_binders.iter().map(|(v, fresh)| (v.name.as_str(), fresh.as_str())).collect());
                    let lifted_expr = self.case_lift_inner(used, renamed_expr)?;
                    lifted_cases.push(Case {
                        data_constructor,
                        binders: case_binders.into_iter().map(|(v, new)| Var { name: new.to_string(), ty: v.ty.clone() }).collect(),
                        expr: lifted_expr,
                    })
                }
                Ok(Expr::Match {
                    expr: Box::new(lifted_expr),
                    cases: lifted_cases,
                })
            }
        }
    }

    pub fn let_lift(
        &mut self,
        expr: TypedExpr,
    ) -> Result<(TypedExpr, HashSet<String>), CodegenError> {
        let mut used: HashSet<String> = HashSet::new();
        Ok((self.let_lift_inner(&mut used, expr)?, used))
    }

    fn let_lift_inner(
        &mut self,
        used: &mut HashSet<String>,
        expr: TypedExpr,
    ) -> Result<Expr<Var>, CodegenError> {
        match expr {
            Expr::App { func, arg } => Ok(Expr::App {
                func: Box::new(self.let_lift_inner(used, *func)?),
                arg: Box::new(self.let_lift_inner(used, *arg)?),
            }),
            Expr::Lambda { binder, body } => Ok(Expr::Lambda {
                binder,
                body: Box::new(self.let_lift_inner(used, *body)?),
            }),
            Expr::Let { binder, expr, body } => {
                let fresh_binder;
                let mut body = body;
                if used.contains(&binder.ident()) {
                    fresh_binder = self.fresh_name(&binder.ident());
                    body.subst_mut(
                        &binder.ident(),
                        &Expr::Var(Var {
                            name: fresh_binder.clone(),
                            ty: binder.ty.clone(),
                        }),
                    )
                } else {
                    fresh_binder = binder.ident()
                }
                used.insert(fresh_binder.clone());
                Ok(Expr::Let {
                    binder: Var {
                        name: fresh_binder,
                        ty: binder.ty,
                    },
                    expr: Box::new(self.let_lift_inner(used, *expr)?),
                    body: Box::new(self.let_lift_inner(used, *body)?),
                })
            }
            Expr::Var(var) => Ok(Expr::Var(var)),
            Expr::Literal(lit) => Ok(Expr::Literal(lit)),
            Expr::Ann { expr, ty } => Ok(Expr::Ann {
                expr: Box::new(self.let_lift_inner(used, *expr)?),
                ty,
            }),
            Expr::Tuple(..) => Err(CodegenError::NotImplemented("tuple".to_string())),
            Expr::Construction { dtor, args } => {
                let mut lifted_args = vec![];
                for arg in args {
                    lifted_args.push(self.let_lift_inner(used, arg)?)
                }
                Ok(Expr::Construction {
                    dtor,
                    args: lifted_args,
                })
            }
            Expr::Match { expr, cases } => {
                let mut lifted_cases = vec![];
                let lifted_expr = self.let_lift_inner(used, *expr)?;
                for Case {
                    data_constructor,
                    binders,
                    expr,
                } in cases
                {
                    lifted_cases.push(Case {
                        data_constructor,
                        binders,
                        expr: self.let_lift_inner(used, expr)?,
                    });
                }
                Ok(Expr::Match {
                    expr: Box::new(lifted_expr),
                    cases: lifted_cases,
                })
            }
        }
    }

    fn function_table(&mut self) {
        self.out += &format!("(table {} anyfunc)", self.global_names.len());
        for (name, (n, _)) in self.global_names.iter() {
            self.out += &format!("(elem (i32.const {}) ${})", n, name)
        }
    }

    fn gen_expr(&mut self, expr: Expr<Var>) -> Result<(), CodegenError> {
        match expr {
            Expr::Ann { expr, .. } => self.gen_expr(*expr),
            Expr::Var(v) => {
                if &v.name == "primadd" {
                    self.out += "(i32.add (local.get $x) (local.get $y))"
                } else if self.global_names.contains_key(&v.name) {
                    self.out += &format!("(call ${}_c)", v.name)
                } else {
                    self.out += &format!("(local.get ${})", v.name)
                }
                Ok(())
            }
            Expr::Literal(Literal::Int(i)) => {
                self.out += &format!("(i32.const {})", i);
                Ok(())
            }
            Expr::App { func, arg } => {
                self.gen_expr(*func)?;
                self.out += "(call $apply ";
                self.gen_expr(*arg)?;
                self.out += ")";
                Ok(())
            }
            Expr::Let { binder, expr, body } => {
                self.out += &format!("(local.set ${}", binder.ident());
                self.gen_expr(*expr)?;
                self.out += ")";
                self.gen_expr(*body)
            }
            Expr::Literal(Literal::Bool(_)) => {
                Err(CodegenError::NotImplemented("bool".to_string()))
            }
            Expr::Lambda { .. } => Err(CodegenError::NotImplemented("lambda".to_string())),
            Expr::Tuple(..) => Err(CodegenError::NotImplemented("tuple".to_string())),
            Expr::Construction { .. } => {
                Err(CodegenError::NotImplemented("construction".to_string()))
            }
            Expr::Match { .. } => Err(CodegenError::NotImplemented("case".to_string())),
        }
    }

    fn fun(&mut self, name: &str, expr: &TypedExpr, ty: &Type) -> Result<(), CodegenError> {
        info!("{} : {} =\n{}", name, ty, expr);
        // TODO Got to handle duplicate binders here (or somewhere earlier)
        let (binders, body) = expr.clone().collapse_lambdas();
        let (body, let_binders) = self.let_lift(body)?;
        let (body, case_binders) = self.case_lift(body)?;
        let mut args = ty.unfold_fun();
        // All results are i32's anyway
        let _res = args.pop();
        self.out += &format!("\n(func ${}", name);
        let binder_count = binders.len();
        if binder_count != 0 {
            self.out += " (param $args i32)"
        }
        self.out += " (result i32)\n";

        for binder in binders.iter() {
            self.out += &format!("(local ${} i32)\n", binder.name)
        }
        for binder in let_binders.iter() {
            self.out += &format!("(local ${} i32)\n", binder)
        }
        for binder in case_binders.iter() {
            self.out += &format!("(local ${} i32)\n", binder)
        }
        for (ix, binder) in binders.iter().enumerate() {
            self.out += &format!(
                "(set_local ${} (i32.load (i32.add (get_local $args) (i32.const {}))))\n",
                binder.name,
                ix * 4
            )
        }

        self.gen_expr(body)?;
        self.out += ")\n";

        if binder_count == 0 {
            self.out += &format!("(func ${}_c (result i32) (call ${}))", name, name)
        } else {
            // generate the wrapper
            self.out += &format!(
                "(func ${}_c (result i32) (call $make_closure (i32.const {}) (i32.const {})))",
                name,
                binder_count,
                self.global_names.get(name).unwrap().0
            )
        }
        Ok(())
    }

    fn entry_point(&mut self) {
        self.out += "\n(export \"main\" (func $main))"
    }
}

const ALLOCATOR_RTS: &str = r#"
 (memory 1)
 (global $watermark (mut i32) (i32.const 0))

 (func $allocate (param $bytes i32) (result i32)
       (local $res i32)
       (set_local $res (global.get $watermark))
       (global.set $watermark (i32.add (get_local $res) (get_local $bytes)))
       (get_local $res))
"#;

const CLOSURE_RTS: &str = r#"
 (func $make_closure (param $arity i32) (param $code_pointer i32) (result i32)
       (local $closure_start i32)
       ;; The size of a closure is 12bytes + 4bytes per argument
       (set_local $closure_start
                  (call $allocate
                        (i32.add (i32.const 12)
                                 (i32.mul (i32.const 4) (get_local $arity)))))
       ;; Initializes arity
       (i32.store
        (get_local $closure_start)
        (get_local $arity))
       ;; Initializes applied arg counter to 0
       (i32.store
        (i32.add (get_local $closure_start) (i32.const 4))
        (i32.const 0))
       ;; writes the code pointer
       (i32.store
        (i32.add (i32.add (get_local $closure_start) (i32.const 8)) ;; skips over arity and applied counter
                 (i32.mul (get_local $arity) (i32.const 4))) ;; skips over arguments
        (get_local $code_pointer))
       (get_local $closure_start))

 (type $i32_to_i32 (func (param i32) (result i32)))
 (func $apply (param $closure i32) (param $arg i32) (result i32)
       (local $arity i32)
       (local $applied i32)
       (local $arg_start i32)
       (local $next_arg i32)
       (local $code_pointer_offset i32)

       (set_local $arity (i32.load (get_local $closure)))
       (set_local $applied (i32.load (i32.add (get_local $closure) (i32.const 4))))
       (set_local $arg_start (i32.add (get_local $closure) (i32.const 8)))
       (set_local $next_arg (i32.add (get_local $arg_start)
                                     (i32.mul (get_local $applied)
                                              (i32.const 4))))
       (set_local $code_pointer_offset
                  (i32.add (get_local $arg_start)
                           (i32.mul (get_local $arity)
                                    (i32.const 4))))

       ;; write the supplied argument into its spot
       ;; TODO: We should be copying the closure here
       (i32.store (get_local $next_arg) (get_local $arg))
       (if (result i32)
           (i32.eq (get_local $arity) (i32.add (get_local $applied) (i32.const 1)))
         (then
          ;; if all arguments have been supplied we're ready to execute the body
          (call_indirect (type $i32_to_i32) (get_local $arg_start) (i32.load (get_local $code_pointer_offset))))
         (else
          ;; If we're still missing arguments we bump the applied counter and return the new closure
          (i32.store (i32.add (get_local $closure) (i32.const 4)) (i32.add (get_local $applied) (i32.const 1)))
          (get_local $closure))))

 (func $construct_pack_1 (param $tag i32) (param $val1 i32) (result i32)
       (local $pack_start i32)
       (set_local $pack_start (call $allocate (i32.const 12)))
       (i32.store (local.get $pack_start) (local.get $tag))
       ;; Writing the arity
       (i32.store (i32.add (local.get $pack_start) (i32.const 4)) (i32.const 1))
       ;; Writing the values
       (i32.store (i32.add (local.get $pack_start) (i32.const 8)) (local.get $val1))
       (local.get $pack_start))

 (func $construct_pack_2 (param $tag i32) (param $val1 i32) (param $val2 i32) (result i32)
       (local $pack_start i32)
       (set_local $pack_start (call $allocate (i32.const 16)))
       (i32.store (local.get $pack_start) (local.get $tag))
       ;; Writing the arity
       (i32.store (i32.add (local.get $pack_start) (i32.const 4)) (i32.const 2))
       ;; Writing the values
       (i32.store (i32.add (local.get $pack_start) (i32.const 8)) (local.get $val1))
       (i32.store (i32.add (local.get $pack_start) (i32.const 12)) (local.get $val2))
       (local.get $pack_start))

 (func $construct_pack_3 (param $tag i32) (param $val1 i32) (param $val2 i32) (param $val3 i32) (result i32)
       (local $pack_start i32)
       (set_local $pack_start (call $allocate (i32.const 16)))
       (i32.store (local.get $pack_start) (local.get $tag))
       ;; Writing the arity
       (i32.store (i32.add (local.get $pack_start) (i32.const 4)) (i32.const 3))
       ;; Writing the values
       (i32.store (i32.add (local.get $pack_start) (i32.const 8)) (local.get $val1))
       (i32.store (i32.add (local.get $pack_start) (i32.const 12)) (local.get $val2))
       (i32.store (i32.add (local.get $pack_start) (i32.const 16)) (local.get $val4))
       (local.get $pack_start))

 (func $get_pack_tag (param $pack_start i32) (result i32)
       (i32.load (local.get $pack_start)))

 (func $get_pack_field (param $pack_start i32) (param $ix i32) (result i32)
       (if (result i32)
           (i32.lt_s (local.get $ix) (i32.load (i32.add (local.get $pack_start) (i32.const 4))))
         (then
          (i32.load
           (i32.add
            (i32.add (i32.const 8)
                     (i32.mul (local.get $ix) (i32.const 4)))
            (local.get $pack_start))))
         (else unreachable)))

"#;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grammar::ExprParser;
    use crate::token::Lexer;
    use std::iter::FromIterator;

    fn expr(input: &str) -> TypedExpr {
        let lexer = Lexer::new(input);
        let res = ExprParser::new().parse(lexer);
        match res {
            Err(err) => panic!("{:?}", err),
            Ok(expr) => expr.map(&|v| Var {
                name: v,
                ty: Type::int(),
            }),
        }
    }

    #[test]
    fn let_lifting() {
        let my_expr = expr("let hello = x in (let hello = x in hello)");

        let mut cg = Codegen::new();
        let (lifted, names) = cg.let_lift(my_expr).unwrap();
        assert_eq!(lifted, expr("let hello = x in (let hello1 = x in hello1)"));
        assert_eq!(
            names,
            HashSet::from_iter(vec!["hello1".to_string(), "hello".to_string()].into_iter())
        );
    }

    #[test]
    fn case_lifting() {
        let my_expr = expr("match x { E::R(x) => match x { E::R(x) => x, E::L(y) => y }, E::L(x) => x }");

        let mut cg = Codegen::new();
        let (lifted, names) = cg.case_lift(my_expr).unwrap();
        println!("{}", lifted);
        println!("{:?}", names);
        assert!(true);
    }

    #[test]
    fn lambda_lifting() {
        let my_expr = expr("(\\x. add 1 ((\\y. \\x. add y x) 4 6)) ((\\x. x) 3)");

        let mut cg = Lowering::new();
        let (lifted, ds) = cg.lambda_lift_inner(my_expr).unwrap();
        println!("{}", lifted);
        for (vd, _) in ds {
            println!("{} = {}", vd.name, vd.expr);
        }
        assert!(true) // change to false to start debugging
    }
}
