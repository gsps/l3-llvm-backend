#![allow(non_snake_case, dead_code)]

use std::collections::{BTreeMap, HashSet};
use std::hash::Hash;
pub use std::rc::Rc;

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Name<'a>(pub &'a str);

type BlockTag = u8;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum ValuePrimitive {
  CPSAdd,
  CPSSub,
  CPSMul,
  CPSDiv,
  CPSMod,
  CPSShiftLeft,
  CPSShiftRight,
  CPSAnd,
  CPSOr,
  CPSXOr,
  CPSByteRead,
  CPSByteWrite,
  CPSBlockAlloc(BlockTag),
  CPSBlockTag,
  CPSBlockLength,
  CPSBlockGet,
  CPSBlockSet,
  CPSId,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum TestPrimitive {
  CPSLt,
  CPSLe,
  CPSEq,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Atom<'a> {
  AtomN(Name<'a>),
  AtomL(u32),
}

pub type Arg<'a> = Atom<'a>;
pub type Args<'a> = Vec<Arg<'a>>;
pub type Params<'a> = Vec<Name<'a>>;

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Cnt<'a> {
  pub name: Name<'a>,
  pub params: Params<'a>,
  pub body: Box<Tree<'a>>,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Fun<'a> {
  pub name: Name<'a>,
  pub ret_cnt: Name<'a>,
  pub params: Params<'a>,
  pub body: Box<Tree<'a>>,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Tree<'a> {
  LetP {
    name: Name<'a>,
    prim: ValuePrimitive,
    args: Args<'a>,
    body: Box<Tree<'a>>,
  },
  LetC {
    cnts: Vec<Rc<Cnt<'a>>>,
    body: Box<Tree<'a>>,
  },
  LetF {
    funs: Vec<Rc<Fun<'a>>>,
    body: Box<Tree<'a>>,
  },
  AppC {
    cnt: Name<'a>,
    args: Args<'a>,
  },
  AppF {
    fun: Arg<'a>,
    ret_cnt: Name<'a>,
    args: Args<'a>,
  },
  If {
    cond: TestPrimitive,
    args: Args<'a>,
    then_cnt: Name<'a>,
    else_cnt: Name<'a>,
  },
  Halt {
    arg: Atom<'a>,
  },
}

#[derive(Debug)]
pub struct Symbols<'a> {
  cnts: BTreeMap<Name<'a>, Rc<Cnt<'a>>>,
  funs: BTreeMap<Name<'a>, Rc<Fun<'a>>>,
}

impl<'a> Symbols<'a> {
  fn new() -> Self {
    Self {
      cnts: BTreeMap::new(),
      funs: BTreeMap::new(),
    }
  }

  fn register_cnt(&mut self, cnt: Rc<Cnt<'a>>) -> () {
    assert!(!self.cnts.contains_key(&cnt.name));
    self.cnts.insert(cnt.name, cnt);
  }

  fn register_fun(&mut self, fun: Rc<Fun<'a>>) -> () {
    assert!(!self.funs.contains_key(&fun.name));
    self.funs.insert(fun.name, fun);
  }
}

#[derive(Debug)]
pub struct Program<'a> {
  symbols: Symbols<'a>,
}

pub const MAIN_FN: &'static str = "main";
pub const MAIN_FN_RETC: &'static str = "__main_ret_cnt";

impl<'a> Program<'a> {
  pub fn from_raw_tree(tree: Box<Tree<'a>>) -> Self {
    use Tree::*;

    // During parsing, all applications are represented as AppCs, to avoid the need for
    // name analyis. This function rewrites AppCs into AppFs when they refer to functions.
    fn fix_apps<'a>(seen_funs: &mut HashSet<Name<'a>>, tree: &mut Tree<'a>) -> () {
      match tree {
        LetP { body, .. } => fix_apps(seen_funs, body),
        LetC { cnts, body } => {
          for cnt in cnts {
            let body = &mut Rc::get_mut(cnt).unwrap().body;
            fix_apps(seen_funs, body)
          }
          fix_apps(seen_funs, body)
        }
        LetF { funs, body } => {
          for fun in &*funs {
            seen_funs.insert(fun.name);
          }
          for fun in funs {
            let body = &mut Rc::get_mut(fun).unwrap().body;
            fix_apps(seen_funs, body)
          }
          fix_apps(seen_funs, body)
        }
        AppC { cnt: name, args } => {
          if seen_funs.contains(&name) {
            assert!(args.len() > 0);
            let dummy = Halt {
              arg: Atom::AtomL(0),
            };
            if let AppC {
              cnt: name,
              mut args,
            } = std::mem::replace(tree, dummy)
            {
              let first_arg: Vec<_> = args.drain(0..1).collect();
              if let Atom::AtomN(ret_cnt) = first_arg.first().unwrap() {
                *tree = Tree::AppF {
                  fun: Atom::AtomN(name),
                  ret_cnt: *ret_cnt,
                  args: args,
                };
                return; // Success
              }
            }
            unreachable!()
          }
        }
        _ => (),
      }
    }

    // Populates `symbols` with the functions and continuations found in `tree`.
    // (We assume that all names are globally unique.)
    fn register_symbols<'a>(symbols: &mut Symbols<'a>, tree: &Tree<'a>) -> () {
      match tree {
        LetP { body, .. } => register_symbols(symbols, body),
        LetC { cnts, body } => {
          for cnt in cnts {
            register_symbols(symbols, &cnt.body);
            symbols.register_cnt(cnt.clone())
          }
          register_symbols(symbols, body)
        }
        LetF { funs, body } => {
          for fun in funs {
            register_symbols(symbols, &fun.body);
            symbols.register_fun(fun.clone())
          }
          register_symbols(symbols, body)
        }
        _ => (),
      }
    }

    // Registers the main function (assuming all functions have been hoisted)
    fn register_main<'a>(symbols: &mut Symbols<'a>, tree: Box<Tree<'a>>) -> () {
      match *tree {
        LetF { body, .. } => register_main(symbols, body),
        _ => {
          let fun = Fun {
            name: Name(MAIN_FN),
            ret_cnt: Name(MAIN_FN_RETC),
            params: vec![],
            body: tree,
          };
          symbols.register_fun(Rc::new(fun))
        }
      }
    }

    let mut tree = tree;
    let mut symbols = Symbols::new();

    fix_apps(&mut HashSet::new(), &mut tree);
    register_symbols(&mut symbols, &tree);
    register_main(&mut symbols, tree);

    Self { symbols }
  }

  pub fn continuations(&self) -> Vec<Rc<Cnt<'a>>> {
    self.symbols.cnts.values().map(|cnt| cnt.clone()).collect()
  }

  pub fn functions(&self) -> Vec<Rc<Fun<'a>>> {
    self.symbols.funs.values().map(|fun| fun.clone()).collect()
  }

  pub fn get_function(&self, name: &Name<'a>) -> Rc<Fun<'a>> {
    self.symbols.funs.get(name).unwrap().clone()
  }
}
