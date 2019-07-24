use crate::bi_types::Type;
use crate::expr::{Declaration, Expr, Literal};
use std::collections::HashMap;

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
        format!("${}{}", s, self.supply)
    }

    fn populate_global_names(&mut self, prog: &Vec<(Declaration, Type)>) {
        let mut index_supply: u32 = 0;
        let mut global_names = HashMap::new();
        for decl in prog {
            if let (Declaration::Value { name, expr: _ }, ty) = decl {
                global_names.insert(name.to_string(), (index_supply, ty.clone()));
                index_supply += 1;
            }
        }
        self.global_names = global_names;
    }

    pub fn codegen(mut self, prog: &Vec<(Declaration, Type)>) -> String {
        self.populate_global_names(prog);
        self.out += "(module\n";
        self.function_table();
        self.rts();
        for decl in prog {
            if let (Declaration::Value { name, expr }, ty) = decl {
                self.fun(name, expr, ty);
            }
        }
        self.entry_point();
        self.out += "\n)";
        return self.out;
    }

    fn rts(&mut self) {
        self.out += ALLOCATOR_RTS;
        self.out += CLOSURE_RTS;
    }

    fn function_table(&mut self) {
        self.out += &format!("(table {} anyfunc)", self.global_names.len());
        for (name, (n, _)) in self.global_names.iter() {
            self.out += &format!("(elem (i32.const {}) ${})", n, name)
        }
    }

    fn gen_expr(&mut self, expr: Expr) {
        match expr {
            Expr::Ann { ty, expr } => self.gen_expr(*expr),
            Expr::Var(v) => {
                if &v == "primadd" {
                    self.out += "(i32.add (local.get $x) (local.get $y))"
                } else if self.global_names.contains_key(&v) {
                    self.out += &format!("(call ${}_c)", v)
                } else {
                    self.out += &format!("(local.get ${})", v)
                }
            }
            Expr::Literal(Literal::Int(i)) => self.out += &format!("(i32.const {})", i),
            Expr::App { func, arg } => {
                self.gen_expr(*func);
                self.out += &format!("(call $apply ");
                self.gen_expr(*arg);
                self.out += &format!(")");
            }
            _ => panic!("Unknown Expr codegen {:?}", expr),
        }
    }

    fn fun(&mut self, name: &str, expr: &Expr, ty: &Type) {
        let (binders, body) = expr.collapse_lambdas();
        let mut args = ty.unfold_fun();
        let res = args.pop();
        self.out += &format!("\n(func ${}", name);
        let binder_count = binders.len();
        if binder_count != 0 {
            self.out += &format!(" (param $args i32)")
        }
        self.out += &format!(" (result i32)\n");

        for binder in binders.iter() {
            self.out += &format!("(local ${} i32)\n", binder)
        }
        for (ix, binder) in binders.iter().enumerate() {
            self.out += &format!(
                "(set_local ${} (i32.load16_u (i32.add (get_local $args) (i32.const {}))))\n",
                binder,
                ix * 2
            )
        }

        self.gen_expr(body);
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
       ;; The size of a closure is 6bytes + 2bytes per argument
       (set_local $closure_start
                  (call $allocate
                        (i32.add (i32.const 6)
                                 (i32.mul (i32.const 2) (get_local $arity)))))
       ;; Initializes arity
       (i32.store16
        (get_local $closure_start)
        (get_local $arity))
       ;; Initializes applied arg counter to 0
       (i32.store16
        (i32.add (get_local $closure_start) (i32.const 2))
        (i32.const 0))
       ;; writes the code pointer
       (i32.store16
        (i32.add (i32.add (get_local $closure_start) (i32.const 4)) ;; skips over arity and applied counter
                 (i32.mul (get_local $arity) (i32.const 2))) ;; skips over arguments
        (get_local $code_pointer))
       (get_local $closure_start))

 (type $i32_to_i32 (func (param i32) (result i32)))
 (func $apply (param $closure i32) (param $arg i32) (result i32)
       (local $arity i32)
       (local $applied i32)
       (local $arg_start i32)
       (local $next_arg i32)
       (local $code_pointer_offset i32)

       (set_local $arity (i32.load16_u (get_local $closure)))
       (set_local $applied (i32.load16_u (i32.add (get_local $closure) (i32.const 2))))
       (set_local $arg_start (i32.add (get_local $closure) (i32.const 4)))
       (set_local $next_arg (i32.add (get_local $arg_start)
                                     (i32.mul (get_local $applied)
                                              (i32.const 2))))
       (set_local $code_pointer_offset
                  (i32.add (get_local $arg_start)
                           (i32.mul (get_local $arity)
                                    (i32.const 2))))

       ;; write the supplied argument into its spot
       ;; TODO: We should be copying the closure here
       (i32.store16 (get_local $next_arg) (get_local $arg))
       (if (result i32)
           (i32.eq (get_local $arity) (i32.add (get_local $applied) (i32.const 1)))
         (then
          ;; if all arguments have been supplied we're ready to execute the body
          (call_indirect (type $i32_to_i32) (get_local $arg_start) (i32.load16_u (get_local $code_pointer_offset))))
         (else
          ;; If we're still missing arguments we bump the applied counter and return the new closure
          (i32.store16 (i32.add (get_local $closure) (i32.const 2)) (i32.add (get_local $applied) (i32.const 1)))
          (get_local $closure))))
"#;
