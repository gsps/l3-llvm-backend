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
use inkwell::types::{BasicTypeEnum, FunctionType, IntType};
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, IntValue, PointerValue};
use inkwell::{AddressSpace, IntPredicate, OptimizationLevel};

type CgResult<T> = Result<T, &'static str>;

pub struct Codegen<'a, 'ctx> {
  pub context: &'ctx Context,
  pub builder: &'a Builder<'ctx>,
  pub fpm: &'a PassManager<FunctionValue<'ctx>>,
  pub module: &'a Module<'ctx>,
  pub program: &'a Program<'a>,
}

fn value_type<'ctx>(ctx: &'ctx Context) -> IntType<'ctx> {
  ctx.i32_type()
}

fn make_value<'ctx>(ctx: &'ctx Context, v: u32) -> IntValue<'ctx> {
  value_type(ctx).const_int(v.into(), false)
}

fn fn_type_for_values<'ctx>(ctx: &'ctx Context, n: usize) -> FunctionType<'ctx> {
  let ret_type = value_type(ctx);
  let param_types = std::iter::repeat(ret_type)
    .take(n)
    .map(|f| f.into())
    .collect::<Vec<BasicTypeEnum>>();
  ret_type.fn_type(&param_types, false)
}

fn get_fn_value<'a, 'ctx>(module: &Module<'ctx>, name: &'a str) -> FunctionValue<'ctx> {
  module
    .get_function(name)
    .expect("Expected function to be pre-registered")
}

// Register a function in the given LLVM module.
// The return and parameter types are always `value_type`.
fn add_function<'a, 'ctx>(
  ctx: &'ctx Context,
  module: &Module<'ctx>,
  name: Name<'a>,
  params: &Params<'a>,
) -> FunctionValue<'ctx> {
  let fn_type = fn_type_for_values(ctx, params.len());
  let fn_value = module.add_function(name.0, fn_type, None);
  for (param, param_name) in fn_value.get_param_iter().zip(params.iter()) {
    param.into_int_value().set_name(param_name.0);
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
    register_rt_functions(context, module);
    let mut cg = Codegen {
      context,
      builder,
      fpm,
      module,
      program,
    };

    // let g_memory = module.add_global(
    //   value_type(cg.context).ptr_type(AddressSpace::Generic),
    //   None,
    //   "MEMORY",
    // );
    // g_memory.set_linkage(Linkage::Internal);
    // assert!(g_memory.is_declaration());

    let funs = cg.program.functions();
    for fun in &funs {
      add_function(cg.context, cg.module, fun.name, &fun.params);
    }
    for fun in funs {
      cg.compile_fun(fun)?;
    }
    Ok(())
  }

  fn compile_fun(&mut self, fun: Rc<Fun<'a>>) -> CgResult<FunctionValue<'ctx>> {
    use Tree::*;
    let fun = fun.as_ref();

    // Visit all continuations bound in `tree`
    fn visit_cnts<'a, F: FnMut(Rc<Cnt<'a>>) -> ()>(tree: &Tree<'a>, f: &mut F) -> () {
      match tree {
        LetC { cnts, body } => {
          for cnt in cnts {
            f(cnt.clone());
            visit_cnts(&cnt.body, f);
          }
          visit_cnts(body, f)
        }
        LetF { .. } => unreachable!(),
        LetP { body, .. } => visit_cnts(body, f),
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
      module: &'a Module<'ctx>,
      ret_cnt_name: Name<'a>,
      blocks: HashMap<Name<'a>, BasicBlock<'ctx>>,
      vars: HashMap<Name<'a>, PointerValue<'ctx>>,
      all_cnts: HashMap<Name<'a>, Rc<Cnt<'a>>>,
    }

    impl<'a, 'ctx> State<'a, 'ctx> {
      fn add_var(&mut self, name: &Name<'a>) -> PointerValue<'ctx> {
        let ptr_value = self.builder.build_alloca(value_type(self.context), name.0);
        let old_opt = self.vars.insert(*name, ptr_value);
        assert!(old_opt.is_none());
        ptr_value
      }

      fn add_vars_for_locals(&mut self, tree: &Tree<'a>) {
        visit_bb(
          tree,
          |name, _prim, _args| {
            self.add_var(&name);
          },
          |_tree| {},
        );
      }

      fn arg_value(&self, arg: &Atom<'a>) -> IntValue<'ctx> {
        match arg {
          Atom::AtomL(value) => make_value(self.context, *value),
          Atom::AtomN(arg_name) => match self.vars.get(arg_name) {
            Some(var) => self.builder.build_load(*var, arg_name.0).into_int_value(),
            None => {
              // Load a function pointer
              // NOTE: This is currently very brittle, since we rely on the upper 32 bits being
              // insignificant, in the sense that the main function pointer's upper 32 bits are
              // assumed to be equivalent to all the other functions'. This justifies only storing
              // the lower 32 bits in closure blocks.
              // In principle, we should be able to force this behavior during linking, but I have
              // not discovered how to do this yet, so currently we just hope that our functions
              // all lie within the same 32 upper bits.
              let fn_value = get_fn_value(self.module, arg_name.0);
              let fn_global_value = fn_value.as_global_value();
              let fn_ptr_value = fn_global_value.as_pointer_value();

              let offset = self.builder.build_ptr_to_int(
                fn_ptr_value,
                value_type(self.context),
                "fn_ptr_to_int",
              );
              offset
            }
          },
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

      fn emit_call(
        &self,
        name: &'a str,
        args: &[BasicValueEnum<'ctx>],
        node_name: &str,
      ) -> IntValue<'ctx> {
        let fn_value = get_fn_value(self.module, name);
        let call = self.builder.build_call(fn_value, args, node_name);
        call
          .try_as_basic_value()
          .left()
          .expect("Failed to generate direct call")
          .into_int_value()
      }

      fn emit_indirect_call(
        &self,
        fun_arg_name: Name<'a>,
        args: &[BasicValueEnum<'ctx>],
        node_name: &str,
      ) -> IntValue<'ctx> {
        let b = &self.builder;
        // See `arg_value()` for an explanation of how function pointers are stored
        let fn_ptr = {
          let i64_type = self.context.i64_type();
          let mask_upper = i64_type.const_int(0xffffffff00000000, false);
          let fn_ptr_main = get_fn_value(self.module, MAIN_FN)
            .as_global_value()
            .as_pointer_value();
          let fn_ptr_main = b.build_ptr_to_int(fn_ptr_main, i64_type, "fn_ptr_main_as_i64");
          let fn_ptr_main = b.build_and(fn_ptr_main, mask_upper, "fn_ptr_main_mask_upper");
          let fn_ptr_lower = self.arg_value(&Atom::AtomN(fun_arg_name));
          let fn_ptr_lower = b.build_int_z_extend(fn_ptr_lower, i64_type, "fn_ptr_lower_as_i64");
          let fn_ptr_main = b.build_or(fn_ptr_main, fn_ptr_lower, "fn_ptr_combine");
          let fn_ptr_type =
            fn_type_for_values(self.context, args.len()).ptr_type(AddressSpace::Generic);
          b.build_int_to_ptr(fn_ptr_main, fn_ptr_type, "fn_ptr_cast")
        };
        b.build_call(fn_ptr, args, node_name)
          .try_as_basic_value()
          .left()
          .expect("Failed to generate indirect call")
          .into_int_value()
      }

      // Call a local continuation
      fn emit_cnt_call_direct(&self, cnt_name: &Name<'a>, args: &[BasicValueEnum<'ctx>],) {
        let cnt = self.all_cnts.get(cnt_name).unwrap();
        assert_eq!(cnt.params.len(), args.len());
        for (param_name, value) in cnt.params.iter().zip(args.iter()) {
          self.emit_assignment(param_name, *value);
        }
        self.emit_jump_to(cnt_name);
      }

      // Call the return continuation (i.e., return)
      fn emit_cnt_call_indirect(&self, value: IntValue<'ctx>) {
        self.builder.build_return(Some(&value));
      }

      fn emit_block(&self, tree: &Tree<'a>) {
        let b = &self.builder;
        visit_bb(
          tree,
          // Handle value primitives
          |name, prim, args| {
            let var = self.vars.get(&name).unwrap();
            let mut args = args.clone();
            let mut args = args.drain(..);
            let mut next_arg = || self.arg_value(&args.next().unwrap());

            use ValuePrimitive::*;
            let result = match prim {
              CPSAdd => b.build_int_add(next_arg(), next_arg(), "cpsadd"),
              CPSSub => b.build_int_sub(next_arg(), next_arg(), "cpssub"),
              CPSMul => b.build_int_mul(next_arg(), next_arg(), "cpsmul"),
              CPSDiv => b.build_int_signed_div(next_arg(), next_arg(), "cpsdiv"),
              // TODO: Check that `srem` behaves like L3's `%`
              CPSMod => b.build_int_signed_rem(next_arg(), next_arg(), "cpsmod"),
              CPSShiftLeft => b.build_left_shift(next_arg(), next_arg(), "cpsshiftleft"),
              CPSShiftRight => b.build_right_shift(next_arg(), next_arg(), true, "cpsshiftright"),
              CPSXOr => b.build_xor(next_arg(), next_arg(), "cpsxor"),
              CPSAnd => b.build_and(next_arg(), next_arg(), "cpsand"),
              CPSOr => b.build_or(next_arg(), next_arg(), "cpsor"),
              CPSId => next_arg(),
              CPSByteRead => self.emit_call("rt_byteread", &[], "cpsbyteread"),
              CPSByteWrite => self.emit_call("rt_bytewrite", &[next_arg().into()], "cpsbytewrite"),
              CPSBlockAlloc(block_tag) => self.emit_call(
                "rt_blockalloc",
                &[
                  make_value(self.context, block_tag as u32).into(),
                  next_arg().into(),
                ],
                "cpsblockalloc",
              ),
              CPSBlockTag => self.emit_call("rt_blocktag", &[next_arg().into()], "cpsblocktag"),
              CPSBlockLength => {
                self.emit_call("rt_blocklength", &[next_arg().into()], "cpsblocklength")
              }
              CPSBlockGet => self.emit_call(
                "rt_blockget",
                &[next_arg().into(), next_arg().into()],
                "cpsblockget",
              ),
              CPSBlockSet => self.emit_call(
                "rt_blockset",
                &[next_arg().into(), next_arg().into(), next_arg().into()],
                "cpsblockset",
              ),
            };
            self.builder.build_store(*var, result);
          },
          // Handle rest of the continuation
          |tree| match tree {
            AppC { cnt, args } => {
              if *cnt == self.ret_cnt_name {
                assert_eq!(args.len(), 1);
                let result = self.arg_value(args.first().unwrap());
                self.emit_cnt_call_indirect(result);
              } else {
                let args = args
                  .iter()
                  .map(|arg| self.arg_value(arg).into())
                  .collect::<Vec<BasicValueEnum>>();
                self.emit_cnt_call_direct(cnt, &args);
              }
            }

            AppF {
              fun: Atom::AtomN(fun_name),
              ret_cnt,
              args,
            } => {
              let args = args
                .iter()
                .map(|arg| self.arg_value(arg).into())
                .collect::<Vec<BasicValueEnum>>();

              let result = if let Some(fn_value) = self.module.get_function(fun_name.0) {
                // Direct call
                assert_eq!(fn_value.count_params() as usize, args.len());
                self.emit_call(fun_name.0, &args, "call_fun")
              } else {
                // Indirect call
                self.emit_indirect_call(*fun_name, &args, "call_closure")
              };

              if *ret_cnt == self.ret_cnt_name {
                self.emit_cnt_call_indirect(result);
              } else {
                self.emit_cnt_call_direct(ret_cnt, &[result.as_basic_value_enum()]);
              }
            }

            If {
              cond,
              args,
              then_cnt,
              else_cnt,
            } => {
              // TODO: Add Phi nodes where we need them!
              assert_eq!(args.len(), 2);
              let arg1 = self.arg_value(args.first().unwrap());
              let arg2 = self.arg_value(args.last().unwrap());
              let block_then = self.blocks.get(then_cnt).unwrap();
              let block_else = self.blocks.get(else_cnt).unwrap();
              let cond = match cond {
                TestPrimitive::CPSLt => IntPredicate::SLT,
                TestPrimitive::CPSLe => IntPredicate::SLE,
                TestPrimitive::CPSEq => IntPredicate::EQ,
              };
              let cond_value = self
                .builder
                .build_int_compare(cond, arg1, arg2, "if_branch");
              self
                .builder
                .build_conditional_branch(cond_value, *block_then, *block_else);
            }

            Halt { arg } => {
              let call = self.emit_call("rt_halt", &[self.arg_value(arg).into()], "halt");
              self.builder.build_return(Some(&call));
            }

            _ => unreachable!(),
          },
        );
      }
    }

    let mut state = State {
      context: self.context,
      builder: self.context.create_builder(),
      module: self.module,
      ret_cnt_name: fun.ret_cnt,
      blocks: HashMap::new(),
      vars: HashMap::new(),
      all_cnts: HashMap::new(),
    };

    let fn_value = get_fn_value(self.module, fun.name.0);
    let entry = self.context.append_basic_block(fn_value, "entry");
    state.builder.position_at_end(entry);

    // Create stack allocations for all bindings
    // (LLVM should promote these to temporary registers during compilation.)

    // Allocate function parameter bindings and locals
    for (param, name) in fn_value.get_param_iter().zip(fun.params.iter()) {
      let var = state.add_var(name);
      state.builder.build_store(var, param);
    }

    state.add_vars_for_locals(&fun.body);

    // Allocate continuation parameters and locals, register continuations
    visit_cnts(&fun.body, &mut |cnt| {
      for param_name in &cnt.params {
        state.add_var(param_name);
      }

      state.add_vars_for_locals(&cnt.body);

      let block = self.context.append_basic_block(fn_value, cnt.name.0);
      state.blocks.insert(cnt.name, block);
      state.all_cnts.insert(cnt.name, cnt.clone());
    });

    // Emit code

    // Complete the function entry block
    state.builder.position_at_end(entry);

    // // Initialize memory global, if this is the program entry point
    // if fun.name.0 == MAIN_FN {
    //   let fn_value = get_fn_value(self.module, "rt_get_memory");
    //   let call = state
    //     .builder
    //     .build_call(fn_value, &[], "fetch_memory_ptr")
    //     .try_as_basic_value()
    //     .left()
    //     .expect("Failed to generate call")
    //     .into_pointer_value();
    //   let g_memory = self.module.get_global("MEMORY").unwrap();
    //   state
    //     .builder
    //     .build_store(g_memory.as_basic_value_enum().into_pointer_value(), call);
    // }

    // Emit the actual function body
    state.emit_block(&fun.body);

    // Emit one basic block per continuation
    visit_cnts(&fun.body, &mut |cnt| {
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

fn register_rt_functions<'ctx>(ctx: &'ctx Context, module: &Module<'ctx>) -> () {
  let rt_funs = [
    ("rt_halt", vec!["x"]),
    ("rt_bytewrite", vec!["x"]),
    ("rt_byteread", vec![]),
    ("rt_blockalloc", vec!["tag", "size"]),
    ("rt_blocktag", vec!["block"]),
    ("rt_blocklength", vec!["block"]),
    ("rt_blockget", vec!["block", "offset"]),
    ("rt_blockset", vec!["block", "offset", "value"]),
  ];
  for (name, params) in rt_funs.iter() {
    let name = Name(name);
    let params = params.iter().map(|p| Name(p)).collect();
    add_function(ctx, module, name, &params);
  }

  // // Add get_memory function, which returns the start of the program MEMORY
  // {
  //   let ret_type = value_type(ctx).ptr_type(AddressSpace::Generic);
  //   let fn_type = ret_type.fn_type(&vec![], false);
  //   module.add_function("rt_get_memory", fn_type, None);
  // }
}

use l3_llvm_runtime::*;

// Make sure the actual runtime functions are linked (l3_llvm_runtime is a dynamic library)
#[used]
static RT_HALT: extern "C" fn(Value) -> Value = rt_halt;
#[used]
static RT_BYTEWRITE: extern "C" fn(Value) -> Value = rt_bytewrite;
#[used]
static RT_BYTEREAD: extern "C" fn() -> Value = rt_byteread;
#[used]
static RT_BLOCKALLOC: extern "C" fn(Value, Value) -> Value = rt_blockalloc;
#[used]
static RT_BLOCKTAG: extern "C" fn(Value) -> Value = rt_blocktag;
#[used]
static RT_BLOCKLENGTH: extern "C" fn(Value) -> Value = rt_blocklength;
#[used]
static RT_BLOCKGET: extern "C" fn(Value, Value) -> Value = rt_blockget;
#[used]
static RT_BLOCKSET: extern "C" fn(Value, Value, Value) -> Value = rt_blockset;

// type Value = u32;
// extern "C" {
//   pub fn rt_halt(x: Value) -> Value;
//   pub fn rt_bytewrite(x: Value) -> Value;
//   pub fn rt_byteread() -> Value;
//   pub fn rt_get_memory() -> *mut u32;
//   pub fn rt_blockalloc(tag: u32, size: Value) -> Value;
//   pub fn rt_blocktag(block: Value) -> Value;
//   pub fn rt_blocklength(block: Value) -> Value;
//   pub fn rt_blockget(block: Value, offset: Value) -> Value;
//   pub fn rt_blockset(block: Value, offset: Value, value: Value) -> Value;
// }

/// Entrypoint
pub fn compile_and_run_program(program: &Program) -> () {
  // // Doesn't do anything, but forces the runtime library to be linked
  // unsafe { rt_get_memory() };

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
  // module.print_to_stderr();
  // eprintln!("-----");

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
