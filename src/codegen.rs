use crate::bi_types::Type;
use crate::expr::{Declaration, Expr, HasIdent, Literal, TypedExpr, Var};
use std::collections::{HashMap, HashSet};

pub struct Codegen {
    supply: u32,
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

    fn fresh_name(&mut self, s: String) -> String {
        self.supply += 1;
        format!("{}{}", s, self.supply)
    }

    fn populate_global_names(&mut self, prog: &Vec<(Declaration<Var>, Type)>) {
        let mut index_supply: u32 = 0;
        let mut global_names = HashMap::new();
        for decl in prog {
            let (Declaration::Value { name, expr: _ }, ty) = decl;
            global_names.insert(name.to_string(), (index_supply, ty.clone()));
            index_supply += 1;
        }
        self.global_names = global_names;
    }

    pub fn codegen(mut self, prog: &Vec<(Declaration<Var>, Type)>) -> String {
        self.populate_global_names(prog);
        self.out += "(module\n";
        self.function_table();
        self.rts();
        for decl in prog {
            let (Declaration::Value { name, expr }, ty) = decl;
            self.fun(name, expr, ty);
        }
        self.entry_point();
        self.out += "\n)";
        return self.out;
    }

    fn rts(&mut self) {
        self.out += ALLOCATOR_RTS;
        self.out += CLOSURE_RTS;
    }

    pub fn let_lift(&mut self, expr: TypedExpr) -> (TypedExpr, HashSet<String>) {
        let mut used: HashSet<String> = HashSet::new();
        (self.let_lift_inner(&mut used, expr), used)
    }

    fn let_lift_inner(&mut self, used: &mut HashSet<String>, expr: TypedExpr) -> Expr<Var> {
        match expr {
            Expr::App { func, arg } => Expr::App {
                func: Box::new(self.let_lift_inner(used, *func)),
                arg: Box::new(self.let_lift_inner(used, *arg)),
            },
            Expr::Lambda { binder, body } => Expr::Lambda {
                binder,
                body: Box::new(self.let_lift_inner(used, *body)),
            },
            Expr::Let { binder, expr, body } => {
                let fresh_binder;
                let mut body = body;
                if used.contains(&binder.ident()) {
                    fresh_binder = self.fresh_name(binder.ident());
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
                Expr::Let {
                    binder: Var {
                        name: fresh_binder,
                        ty: binder.ty,
                    },
                    expr: Box::new(self.let_lift_inner(used, *expr)),
                    body: Box::new(self.let_lift_inner(used, *body)),
                }
            }
            Expr::Var(var) => Expr::Var(var),
            Expr::Literal(lit) => Expr::Literal(lit),
            Expr::Ann { expr, ty } => Expr::Ann {
                expr: Box::new(self.let_lift_inner(used, *expr)),
                ty,
            },
        }
    }

    fn function_table(&mut self) {
        self.out += &format!("(table {} anyfunc)", self.global_names.len());
        for (name, (n, _)) in self.global_names.iter() {
            self.out += &format!("(elem (i32.const {}) ${})", n, name)
        }
    }

    fn gen_expr(&mut self, expr: Expr<Var>) {
        match expr {
            Expr::Ann { ty: _, expr } => self.gen_expr(*expr),
            Expr::Var(v) => {
                if &v.name == "primadd" {
                    self.out += "(i32.add (local.get $x) (local.get $y))"
                } else if self.global_names.contains_key(&v.name) {
                    self.out += &format!("(call ${}_c)", v.name)
                } else {
                    self.out += &format!("(local.get ${})", v.name)
                }
            }
            Expr::Literal(Literal::Int(i)) => self.out += &format!("(i32.const {})", i),
            Expr::App { func, arg } => {
                self.gen_expr(*func);
                self.out += &format!("(call $apply ");
                self.gen_expr(*arg);
                self.out += &format!(")");
            }
            Expr::Let { binder, expr, body } => {
                self.out += &format!("(local.set ${}", binder.ident());
                self.gen_expr(*expr);
                self.out += &format!(")");
                self.gen_expr(*body);
            }
            _ => panic!("Unknown Expr codegen {:?}", expr),
        }
    }

    fn fun(&mut self, name: &str, expr: &TypedExpr, ty: &Type) {
        info!("{} : {} =\n{}", name, ty, expr);
        // TODO Got to handle duplicate binders here (or somewhere earlier)
        let (binders, body) = expr.collapse_lambdas();
        let (body, let_binders) = self.let_lift(body.clone());
        let mut args = ty.unfold_fun();
        // All results are i32's anyway
        let _res = args.pop();
        self.out += &format!("\n(func ${}", name);
        let binder_count = binders.len();
        if binder_count != 0 {
            self.out += &format!(" (param $args i32)")
        }
        self.out += &format!(" (result i32)\n");

        for binder in binders.iter() {
            self.out += &format!("(local ${} i32)\n", binder.name)
        }

        for binder in let_binders.iter() {
            self.out += &format!("(local ${} i32)\n", binder)
        }
        for (ix, binder) in binders.iter().enumerate() {
            self.out += &format!(
                "(set_local ${} (i32.load (i32.add (get_local $args) (i32.const {}))))\n",
                binder.name,
                ix * 4
            )
        }

        self.gen_expr(body.clone());
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
        let (lifted, names) = cg.let_lift(my_expr);
        assert_eq!(lifted, expr("let hello = x in (let hello1 = x in hello1)"));
        assert_eq!(
            names,
            HashSet::from_iter(vec!["hello1".to_string(), "hello".to_string()].into_iter())
        );
    }
}
