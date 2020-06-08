// Based on https://github.com/TheDan64/inkwell/blob/master/examples/kaleidoscope/main.rs
extern crate inkwell;
extern crate l3_llvm_runtime;

use super::ast::*;

use std::collections::HashMap;

use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::Module;
use inkwell::passes::PassManager;
use inkwell::types::{BasicType, BasicTypeEnum, IntType};
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue};
use inkwell::{FloatPredicate, OptimizationLevel};

type CgResult<T> = Result<T, &'static str>;

pub struct Codegen<'a, 'ctx> {
  pub context: &'ctx Context,
  pub builder: &'a Builder<'ctx>,
  pub fpm: &'a PassManager<FunctionValue<'ctx>>,
  pub module: &'a Module<'ctx>,
  rt_funs: RtFunctions<'a, 'ctx>,
  pub program: &'a Program<'a>,
}

fn value_type<'ctx>(ctx: &'ctx Context) -> IntType<'ctx> {
  ctx.i32_type()
}

fn make_value<'ctx>(ctx: &'ctx Context, v: u32) -> IntValue<'ctx> {
  value_type(ctx).const_int(v.into(), false)
}

// Register a function in the given LLVM module.
// The return and parameter types are always `value_type`.
fn add_function<'a, 'ctx>(
  ctx: &'ctx Context,
  module: &Module<'ctx>,
  name: Name<'a>,
  args: &Params<'a>,
) -> FunctionValue<'ctx> {
  let ret_type = value_type(ctx);
  let arg_types = std::iter::repeat(ret_type)
    .take(args.len())
    .map(|f| f.into())
    .collect::<Vec<BasicTypeEnum>>();
  let fn_type = ret_type.fn_type(&arg_types, false);

  let fn_value = module.add_function(name.0, fn_type, None);
  for (arg, arg_name) in fn_value.get_param_iter().zip(args.iter()) {
    arg.into_int_value().set_name(arg_name.0);
  }
  fn_value
}

// Codegen encapsulates the state for compiling an entire L3CPS program
impl<'a, 'ctx> Codegen<'a, 'ctx> {
  pub fn compile(
    context: &'ctx Context,
    builder: &'a Builder<'ctx>,
    fpm: &'a PassManager<FunctionValue<'ctx>>,
    module: &'a Module<'ctx>,
    program: &'a Program<'a>,
  ) -> CgResult<()> {
    let rt_funs = RtFunctions::new(context, module);
    let mut cg = Codegen {
      context,
      builder,
      fpm,
      module,
      rt_funs,
      program,
    };

    for fun in cg.program.functions() {
      cg.compile_fun(fun)?;
    }
    Ok(())
  }

  fn compile_fun(&mut self, fun: Rc<Fun<'a>>) -> CgResult<FunctionValue<'ctx>> {
    use Tree::*;
    let fun = fun.as_ref();

    // Visit all continuations bound in `tree`
    fn visit_cnts<'a, F: FnMut(Rc<Cnt<'a>>) -> ()>(tree: &Tree<'a>, mut f: F) -> () {
      match tree {
        LetC { cnts, body } => {
          for cnt in cnts {
            f(cnt.clone());
          }
          visit_cnts(body, f)
        }
        LetF { .. } => unreachable!(),
        _ => (),
      }
    }

    // Visit all parts of the straightline code given by `tree`
    fn visit_bb<'a, FBind, FTerm>(tree: &Tree<'a>, mut f_bind: FBind, mut f_term: FTerm) -> ()
    where
      FBind: FnMut(Name<'a>, ValuePrimitive, &Args<'a>) -> (),
      FTerm: FnMut(&Tree<'a>) -> (),
    {
      match tree {
        LetC { body, .. } => visit_bb(body, f_bind, f_term),
        LetF { .. } => unreachable!(),
        LetP {
          name,
          prim,
          args,
          body,
        } => {
          f_bind(*name, *prim, args);
          visit_bb(body, f_bind, f_term)
        }
        _ => f_term(tree),
      }
    }

    struct State<'a, 'ctx> {
      context: &'ctx Context,
      builder: Builder<'ctx>,
      rt_funs: &'a RtFunctions<'a, 'ctx>,
      ret_cnt_name: Name<'a>,
      blocks: HashMap<Name<'a>, BasicBlock<'ctx>>,
      vars: HashMap<Name<'a>, PointerValue<'ctx>>,
      all_cnts: HashMap<Name<'a>, Rc<Cnt<'a>>>,
    }

    impl<'a, 'ctx> State<'a, 'ctx> {
      fn new(context: &'ctx Context, rt_funs: &'a RtFunctions<'a, 'ctx>, ret_cnt_name: Name<'a>) -> Self {
        let builder = context.create_builder();
        Self {
          context: context,
          builder: builder,
          rt_funs: rt_funs,
          ret_cnt_name: ret_cnt_name,
          blocks: HashMap::new(),
          vars: HashMap::new(),
          all_cnts: HashMap::new(),
        }
      }

      fn get_rt_fun(&self, name: &'a str) -> FunctionValue<'ctx> {
        *self.rt_funs.fn_values.get(&Name(name)).expect("Unknown runtime function")
      }

      fn add_var(&mut self, name: &Name<'a>) -> PointerValue<'ctx> {
        let ptr_value = self.builder.build_alloca(value_type(self.context), name.0);
        self.vars.insert(*name, ptr_value).unwrap();
        ptr_value
      }

      fn arg_value(&self, arg: &Atom<'a>) -> IntValue<'ctx> {
        match arg {
          Atom::AtomL(value) => make_value(self.context, *value),
          Atom::AtomN(arg_name) => {
            let var = self.vars.get(arg_name).unwrap();
            self.builder.build_load(*var, arg_name.0).into_int_value()
          }
        }
      }

      fn emit_assignment<V: BasicValue<'ctx>>(&self, name: &Name<'a>, value: V) {
        let ptr_value = self.vars.get(name).unwrap();
        self.builder.build_store(*ptr_value, value);
      }

      fn emit_jump_to(&self, cnt_name: &Name<'a>) {
        let block = self.blocks.get(cnt_name).unwrap();
        self.builder.build_unconditional_branch(*block);
      }

      fn emit_block(&self, tree: &Tree<'a>) {
        visit_bb(
          tree,
          // Handle value primitives
          |name, prim, args| {
            // TODO: Handle ValuePrimitives
            unimplemented!()
          },
          // Handle rest of the continuation
          |tree| match tree {
            AppC { cnt, args } if *cnt == self.ret_cnt_name => {
              assert_eq!(args.len(), 1);
              let result = self.arg_value(args.first().unwrap());
              self.builder.build_return(Some(&result));
            }

            AppF { .. } => unimplemented!(),

            AppC {
              cnt: cnt_name,
              args,
            } => {
              let cnt = self.all_cnts.get(cnt_name).unwrap();
              for (param_name, arg) in cnt.args.iter().zip(args.iter()) {
                self.emit_assignment(param_name, self.arg_value(arg));
              }
              self.emit_jump_to(cnt_name);
            }

            If {
              cond,
              args,
              thenC,
              elseC,
            } => unimplemented!(),

            Halt { arg } => {
              let fn_value = self.get_rt_fun("rt_halt");
              let call = self.builder.build_call(fn_value, &[self.arg_value(arg).into()], "halt");
              let call = call.try_as_basic_value().left().expect("Failed to generate halt call").into_int_value();
              self.builder.build_return(Some(&call));
            }

            _ => unreachable!(),
          },
        );
      }
    }

    let mut state = State::new(self.context, &self.rt_funs, fun.retC);
    let fn_value = add_function(self.context, self.module, fun.name, &fun.args);
    let entry = self.context.append_basic_block(fn_value, "entry");
    state.builder.position_at_end(entry);

    // Create stack allocations for all bindings

    // Allocate function parameter bindings
    for (arg, name) in fn_value.get_param_iter().zip(fun.args.iter()) {
      let var = state.add_var(name);
      state.builder.build_store(var, arg);
    }

    // Allocate continuation parameter and local bindings, register continuations
    visit_cnts(&fun.body, |cnt| {
      for arg_name in &cnt.args {
        state.add_var(arg_name);
      }

      visit_bb(
        &cnt.body,
        |name, prim, args| {
          state.add_var(&name);
        },
        |tree| {},
      );

      let block = self.context.append_basic_block(fn_value, cnt.name.0);
      state.blocks.insert(cnt.name, block);
      state.all_cnts.insert(cnt.name, cnt.clone());
    });

    // Emit code

    // Complete the function entry block
    state.builder.position_at_end(entry);
    state.emit_block(&fun.body);

    // Emit one basic block per continuation
    visit_cnts(&fun.body, |cnt| {
      let block = state.blocks.get(&cnt.name).unwrap();
      state.builder.position_at_end(*block);
      state.emit_block(&cnt.body);
    });

    // Verify and run through LLVM's compilation pipeline
    if fn_value.verify(true) {
      self.fpm.run_on(&fn_value);
      Ok(fn_value)
    } else {
      unsafe {
        fn_value.delete();
      }
      Err("Failed to verify and generate function")
    }
  }
}

/// Runtime functions

struct RtFunctions<'a, 'ctx> {
  fn_values: HashMap<Name<'a>, FunctionValue<'ctx>>,
}

impl<'a, 'ctx> RtFunctions<'a, 'ctx> {
  fn new(ctx: &'ctx Context, module: &Module<'ctx>) -> Self {
    let rt_funs = [
      ("rt_bytewrite", vec!["x"]),
      ("rt_byteread", vec![]),
      ("rt_halt", vec!["x"]),
    ];
    let mut fn_values = HashMap::new();
    for (name, params) in rt_funs.iter() {
      let name = Name(name);
      let params = params.iter().map(|p| Name(p)).collect();
      fn_values.insert(name, add_function(ctx, module, name, &params));
    }
    Self { fn_values }
  }
}

// Make sure the actual runtime functions are linked (l3_llvm_runtime is a dynamic library)
use l3_llvm_runtime::*;

#[used]
static RT_BYTEWRITE: extern "C" fn(u32) -> u32 = rt_bytewrite;
#[used]
static RT_BYTEREAD: extern "C" fn() -> u32 = rt_byteread;
#[used]
static RT_HALT: extern "C" fn(u32) -> u32 = rt_halt;

/// Entrypoint
pub fn compile_and_run_program(program: &Program) -> () {
  let context = Context::create();
  let module = context.create_module("the_module");
  let builder = context.create_builder();

  let fpm = PassManager::create(&module);
  fpm.add_instruction_combining_pass();
  fpm.add_reassociate_pass();
  fpm.add_gvn_pass();
  fpm.add_cfg_simplification_pass();
  fpm.add_basic_alias_analysis_pass();
  fpm.add_promote_memory_to_register_pass();
  fpm.add_instruction_combining_pass();
  fpm.add_reassociate_pass();
  fpm.initialize();

  // Compile
  Codegen::compile(&context, &builder, &fpm, &module, program)
    .unwrap_or_else(|e| panic!("Failed to compile program: {}", e));

  // Run
  {
    let engine = module
      .create_jit_execution_engine(OptimizationLevel::None)
      .unwrap();

    let jitted_fn = (unsafe { engine.get_function::<unsafe extern "C" fn() -> u32>(MAIN_FN) })
      .unwrap_or_else(|e| panic!("Failed to jit program: {:?}", e));

    unsafe {
      jitted_fn.call();
      // Won't get here since all L3 programs end in a halt, which calls `std::process::exit`.
      unreachable!()
    }
  }
}
