use crate::bi_types::Type;
use crate::expr::{
    Case, DataConstructor, Declaration, Dtor, Expr, HasIdent, Literal, TypeDeclaration, TypedExpr,
    ValueDeclaration, Var,
};
use std::collections::HashMap;
use std::fmt;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IR {
    pub globals: Vec<IRDeclaration>,
    pub entry_point: String,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IRDeclaration {
    pub name: String,
    pub arguments: Vec<String>,
    pub locals: Vec<String>,
    pub expr: IRExpression,
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum IRExpression {
    App {
        func: Box<IRExpression>,
        args: Vec<IRExpression>,
    },
    Let {
        binder: String,
        expr: Box<IRExpression>,
        body: Box<IRExpression>,
    },
    // Is there an opportunity to differentiate locals from globals here?
    Var(String),
    Literal(Literal),
    Pack {
        tag: u32,
        args: Vec<IRExpression>,
    },
    Match {
        expr_local: String,
        expr: Box<IRExpression>,
        cases: Vec<IRCase>,
    },
}

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct IRCase {
    tag: u32,
    binders: Vec<String>,
    expr: IRExpression,
}

#[derive(Debug, Default)]
pub struct Lowering {
    supply: u32,
    types: HashMap<String, Vec<DataConstructor>>,
}

impl Lowering {
    pub fn new() -> Lowering {
        Default::default()
    }

    fn add_type_declaration(&mut self, ty_decl: TypeDeclaration) {
        self.types.insert(ty_decl.name, ty_decl.constructors);
    }

    fn fresh_name(&mut self, s: &str) -> String {
        self.supply += 1;
        format!("${}{}", s, self.supply)
    }

    fn fresh_top_name(&mut self) -> String {
        self.fresh_name("")
    }

    fn find_data_constructor(&self, dtor: &Dtor) -> Result<(usize, usize), CodegenError> {
        let dtors = self
            .types
            .get(&dtor.ty)
            .ok_or_else(|| CodegenError::UnknownType(dtor.ty.to_string()))?;
        dtors
            .iter()
            .enumerate()
            .find_map(|(ix, d)| {
                if d.name == dtor.name {
                    Some((ix + 1, d.fields.len()))
                } else {
                    None
                }
            })
            .ok_or_else(|| CodegenError::UnknownDataConstructor(dtor.clone()))
    }

    pub fn lower<B: HasIdent + Clone, T>(
        &mut self,
        prog: Vec<(Declaration<B>, T)>,
    ) -> Result<IR, CodegenError> {
        let mut globals = vec![];
        for (decl, _) in prog {
            match decl {
                Declaration::Value(vd) => {
                    let (g, gs) = self.lower_decl(vd)?;
                    globals.extend(gs);
                    globals.push(g);
                }
                Declaration::Type(td) => self.add_type_declaration(td),
            }
        }

        Ok(IR {
            globals,
            entry_point: "main".to_string(),
        })
    }

    fn lower_decl<B: HasIdent + Clone>(
        &mut self,
        decl: ValueDeclaration<B>,
    ) -> Result<(IRDeclaration, Vec<IRDeclaration>), CodegenError> {
        let (arguments, expr) = decl.expr.collapse_lambdas();
        let (lowered_expr, locals, globals) = self.lower_expr(expr)?;
        Ok((
            IRDeclaration {
                name: decl.name,
                arguments: arguments.into_iter().map(|v| v.ident()).collect(),
                expr: lowered_expr,
                locals,
            },
            globals,
        ))
    }

    fn lower_lambda<B: HasIdent + Clone>(
        &mut self,
        expr: Expr<B>,
        is_recursive: Option<&str>,
    ) -> Result<(IRExpression, Vec<String>, Vec<IRDeclaration>), CodegenError> {
        let (binders, mut body) = expr.collapse_lambdas();
        let fresh_name = self.fresh_top_name();
        if let Some(recursive_binder) = is_recursive {
            body.subst_var_mut(recursive_binder, &fresh_name);
        }
        let (lowered_body, locals, mut gs) = self.lower_expr(body)?;
        let ir_decl = IRDeclaration {
            name: fresh_name.clone(),
            arguments: binders.into_iter().map(|v| v.ident()).collect(),
            locals,
            expr: lowered_body,
        };

        gs.push(ir_decl);
        Ok((IRExpression::Var(fresh_name), vec![], gs))
    }

    fn lower_expr<B: HasIdent + Clone>(
        &mut self,
        expr: Expr<B>,
    ) -> Result<(IRExpression, Vec<String>, Vec<IRDeclaration>), CodegenError> {
        match expr {
            Expr::Ann { expr, .. } => self.lower_expr(*expr),
            Expr::Literal(lit) => Ok((IRExpression::Literal(lit), vec![], vec![])),
            Expr::Var(v) => Ok((IRExpression::Var(v.ident()), vec![], vec![])),
            Expr::Tuple { .. } => Err(CodegenError::NotImplemented(
                "Can't lower tuples".to_string(),
            )),
            Expr::App { .. } => {
                let mut args = expr.unfold_applications().into_iter();
                let func = args.next().unwrap();
                let (lowered_func, mut ls, mut gs) = self.lower_expr(func)?;

                let mut lowered_args = vec![];
                for arg in args {
                    let (lowered_arg, arg_ls, arg_gs) = self.lower_expr(arg)?;
                    ls.extend(arg_ls);
                    gs.extend(arg_gs);
                    lowered_args.push(lowered_arg);
                }
                Ok((
                    IRExpression::App {
                        func: Box::new(lowered_func),
                        args: lowered_args,
                    },
                    ls,
                    gs,
                ))
            }
            Expr::Construction { dtor, args } => {
                let mut lowered_args = vec![];
                let mut ls = vec![];
                let mut gs = vec![];
                for arg in args {
                    let (lowered_arg, arg_ls, arg_gs) = self.lower_expr(arg)?;
                    ls.extend(arg_ls);
                    gs.extend(arg_gs);
                    lowered_args.push(lowered_arg);
                }

                let (tag, arity) = self.find_data_constructor(&dtor)?;
                assert_eq!(arity, lowered_args.len());
                Ok((
                    IRExpression::Pack {
                        tag: tag as u32,
                        args: lowered_args,
                    },
                    ls,
                    gs,
                ))
            }
            Expr::Lambda { .. } => self.lower_lambda(expr, None),
            Expr::Let { binder, expr, body } => {
                let fresh_local = self.fresh_name(&binder.ident());
                let renamed_body = body.subst_var(&binder.ident(), &fresh_local);
                let mut locals = vec![fresh_local.clone()];
                let (lowered_expr, ls, mut gs) = self.lower_expr(*expr)?;
                let (lowered_body, ls_body, gs_body) = self.lower_expr(renamed_body)?;
                locals.extend(ls);
                locals.extend(ls_body);
                gs.extend(gs_body);
                Ok((
                    IRExpression::Let {
                        binder: fresh_local,
                        expr: Box::new(lowered_expr),
                        body: Box::new(lowered_body),
                    },
                    locals,
                    gs,
                ))
            }
            Expr::LetRec { binder, expr, body } => {
                let fresh_local = self.fresh_name(&binder.ident());
                let mut locals = vec![fresh_local.clone()];
                let (lowered_expr, ls, mut gs) = if let Expr::Lambda { .. } = *expr {
                    // We only allow recursive bindings if the thing being bound is a lambda
                    self.lower_lambda(*expr, Some(&binder.ident()))?
                } else {
                    self.lower_expr(*expr)?
                };
                let renamed_body = body.subst_var(&binder.ident(), &fresh_local);
                let (lowered_body, ls_body, gs_body) = self.lower_expr(renamed_body)?;
                locals.extend(ls);
                locals.extend(ls_body);
                gs.extend(gs_body);
                Ok((
                    IRExpression::Let {
                        binder: fresh_local,
                        expr: Box::new(lowered_expr),
                        body: Box::new(lowered_body),
                    },
                    locals,
                    gs,
                ))
            }
            Expr::Match { expr, cases } => {
                let expr_local = self.fresh_name("match");
                let (lowered_expr, mut ls, mut gs) = self.lower_expr(*expr)?;
                ls.push(expr_local.clone());
                let max_binders = cases
                    .iter()
                    .fold(0, |acc, case| usize::max(acc, case.binders.len()));
                let mut fresh_binders = Vec::with_capacity(max_binders);
                for _ in 1..=max_binders {
                    fresh_binders.push(self.fresh_name("case"))
                }
                ls.extend(fresh_binders.clone());

                let mut lowered_cases = vec![];
                for Case {
                    data_constructor,
                    binders,
                    expr,
                } in cases
                    {
                        let case_binders: Vec<(String, &str)> = binders
                            .iter()
                            .zip(fresh_binders.iter())
                            .map(|(v, fresh)| (v.ident(), fresh.as_str()))
                            .collect();
                        let renamed_expr = expr.subst_var_many_(case_binders.clone());
                        let (tag, arity) = self.find_data_constructor(&data_constructor)?;
                        assert_eq!(arity, case_binders.len());
                        let (lowered_expr, ls_case, gs_case) = self.lower_expr(renamed_expr)?;
                        ls.extend(ls_case);
                        gs.extend(gs_case);
                        lowered_cases.push(IRCase {
                            tag: tag as u32,
                            binders: case_binders
                                .into_iter()
                                .map(|(_, new)| new.to_string())
                                .collect(),
                            expr: lowered_expr,
                        });
                    }
                Ok((
                    IRExpression::Match {
                        expr_local,
                        expr: Box::new(lowered_expr),
                        cases: lowered_cases,
                    },
                    ls,
                    gs,
                ))
            }
        }
    }
}

#[derive(Debug)]
pub enum CodegenError {
    NotImplemented(String),
    UnknownType(String),
    UnknownDataConstructor(Dtor),
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
                CodegenError::UnknownType(ty) => format!("Couldn't lower unknown type: {}", ty),
                CodegenError::UnknownDataConstructor(dtor) => {
                    format!("Couldn't lower unknown dataconstructor: {}", dtor)
                }
            }
        )
    }
}

#[derive(Default)]
pub struct Codegen {
    /// A mapping from names to their index in the function table
    global_names: HashMap<String, u32>,
    out: String,
}

impl Codegen {
    pub fn new() -> Codegen {
        Codegen {
            global_names: HashMap::new(),
            out: String::new(),
        }
    }

    fn populate_global_names(&mut self, ir: &IR) {
        let mut global_names = HashMap::new();
        for (index, global) in ir.globals.iter().enumerate() {
            global_names.insert(global.name.clone(), index as u32);
        }
        self.global_names = global_names;
    }

    pub fn codegen(mut self, ir: IR) -> String {
        self.populate_global_names(&ir);

        self.out += "(module\n";
        self.function_table();
        self.rts();
        for ir_decl in ir.globals {
            self.gen_decl(ir_decl);
        }
        self.entry_point();
        self.out += "\n)";
        self.out
    }

    fn gen_decl(&mut self, decl: IRDeclaration) {
        // info!("{} : {} =\n{}", name, ty, expr);
        self.out += &format!("\n(func ${}", decl.name);
        let arg_count = decl.arguments.len();
        if arg_count != 0 {
            self.out += " (param $args i32)"
        }
        self.out += " (result i32)\n";

        for binder in decl.arguments.iter() {
            self.out += &format!("(local ${} i32)\n", binder)
        }
        for local in decl.locals {
            self.out += &format!("(local ${} i32)\n", local)
        }
        for (ix, binder) in decl.arguments.iter().enumerate() {
            self.out += &format!(
                "(set_local ${} (i32.load (i32.add (get_local $args) (i32.const {}))))\n",
                binder,
                ix * 4
            )
        }

        self.gen_expr(decl.expr);
        self.out += ")\n";

        if arg_count == 0 {
            self.out += &format!("(func ${}_c (result i32) (call ${}))", decl.name, decl.name)
        } else {
            // generate the wrapper
            self.out += &format!(
                "(func ${}_c (result i32) (call $make_closure (i32.const {}) (i32.const {})))",
                decl.name,
                arg_count,
                self.global_names.get(&decl.name).unwrap()
            )
        }
    }

    fn gen_expr(&mut self, expr: IRExpression) {
        match expr {
            IRExpression::Literal(Literal::Int(i)) => {
                self.out += &format!("(i32.const {})", i);
            }
            IRExpression::Literal(Literal::Bool(b)) => {
                self.out += &format!("(i32.const {})", if b { 1 } else { 0 });
            }
            IRExpression::Pack { tag, args } => {
                self.out += &format!("(i32.const {})\n", tag);
                let args_len = args.len();
                for arg in args {
                    self.gen_expr(arg);
                    self.out += "\n";
                }
                self.out += &format!("(call $construct_pack_{})", args_len);
            }
            IRExpression::Let { binder, expr, body } => {
                self.gen_expr(*expr);
                self.out += &format!("(local.set ${})", binder);
                self.gen_expr(*body)
            }
            IRExpression::Var(v) => {
                if &v == "primadd" {
                    self.out += "(i32.add (local.get $x) (local.get $y))"
                } else if self.global_names.contains_key(&v) {
                    self.out += &format!("(call ${}_c)", v)
                } else {
                    self.out += &format!("(local.get ${})", v)
                }
            }
            IRExpression::App { func, args } => {
                self.gen_expr(*func);
                for arg in args {
                    self.out += "(call $apply ";
                    self.gen_expr(arg);
                    self.out += ")";
                }
            }
            IRExpression::Match {
                expr_local,
                expr,
                cases,
            } => {
                self.gen_expr(*expr);
                self.out += &format!("(local.set ${})\n", expr_local);
                let cases_len = cases.len();
                for case in cases {
                    self.out += &format!("(if (result i32) (i32.eq (call $get_pack_tag (local.get ${})) (i32.const {}))", expr_local, case.tag);
                    self.out += "\n(then\n";
                    for (ix, binder) in case.binders.into_iter().enumerate() {
                        self.out += &format!("(local.set ${} (call $get_pack_field (local.get ${}) (i32.const {})))\n", binder, expr_local, ix);
                    }
                    self.gen_expr(case.expr);
                    self.out += ")\n(else ";
                }
                self.out += "(unreachable)";
                for _ in 1..=cases_len {
                    self.out += "))"; // closes open (else 's and (if 's
                }
            }
        }
    }

    fn rts(&mut self) {
        self.out += ALLOCATOR_RTS;
        self.out += CLOSURE_RTS;
    }

    fn function_table(&mut self) {
        self.out += &format!("(table {} anyfunc)", self.global_names.len());
        for (name, n) in self.global_names.iter() {
            self.out += &format!("(elem (i32.const {}) ${})", n, name)
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

 (func $copy_closure (param $closure i32) (result i32)
       (local $new_closure i32)
       (local $size i32)
       (local $arity i32)
       (local $x i32)
       (set_local $arity (i32.load (get_local $closure)))
       (set_local $size
                  (i32.add (i32.const 12)
                           (i32.mul (i32.const 4)
                                    (get_local $arity))))
       (set_local $new_closure (call $allocate (get_local $size)))
       (set_local $x (i32.const 0))
       (block
        (loop
         (br_if 1 (i32.ge_s (get_local $x) (get_local $size)))
         (i32.store
          (i32.add (get_local $x) (get_local $new_closure))
          (i32.load (i32.add (get_local $x) (get_local $closure))))
         (set_local $x (i32.add (i32.const 4) (get_local $x)))
         (br 0)))
       (get_local $new_closure))

 (type $i32_to_i32 (func (param i32) (result i32)))
 (func $apply (param $closure i32) (param $arg i32) (result i32)
       (local $arity i32)
       (local $applied i32)
       (local $arg_start i32)
       (local $next_arg i32)
       (local $code_pointer_offset i32)

       (set_local $closure (call $copy_closure (get_local $closure)))

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

 (func $construct_pack_0 (param $tag i32) (result i32)
       (local $pack_start i32)
       (set_local $pack_start (call $allocate (i32.const 8)))
       (i32.store (local.get $pack_start) (local.get $tag))
       ;; Writing the arity
       (i32.store (i32.add (local.get $pack_start) (i32.const 4)) (i32.const 0))
       (local.get $pack_start))

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
       (i32.store (i32.add (local.get $pack_start) (i32.const 16)) (local.get $val3))
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
