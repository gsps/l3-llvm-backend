#![allow(non_snake_case, dead_code)]

use std::collections::{HashMap, HashSet};
use std::hash::Hash;
pub use std::rc::Rc;

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Name<'a>(pub &'a str);

// impl<'a> PartialEq for Name<'a> {
//   fn eq(&self, other: &Self) -> bool {
//     *self.0 == *other.0
//   }
// }
// impl<'a> Eq for Name<'a> {}

// impl<'a> Hash for Name<'a> {
//   fn hash<H: Hasher>(&self, state: &mut H) {
//     (*self.0).hash(state);
//   }
// }

type BlockTag = u8;

#[derive(Debug, PartialEq, Eq, Hash)]
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

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum TestPrimitive {
  CPSLt,
  CPSLe,
  CPSEq,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub enum Atom<'a> {
  AtomN(Name<'a>),
  AtomL(i32),
}

pub type Arg<'a> = Atom<'a>;
pub type Args<'a> = Vec<Arg<'a>>;
pub type Params<'a> = Vec<Name<'a>>;

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Cnt<'a> {
  pub name: Name<'a>,
  pub args: Params<'a>,
  pub body: Box<Tree<'a>>,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Fun<'a> {
  pub name: Name<'a>,
  pub retC: Name<'a>,
  pub args: Params<'a>,
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
    retC: Name<'a>,
    args: Args<'a>,
  },
  If {
    cond: TestPrimitive,
    args: Args<'a>,
    thenC: Name<'a>,
    elseC: Name<'a>,
  },
  Halt {
    arg: Atom<'a>,
  },
}

#[derive(Debug)]
pub struct Symbols<'a> {
  cnts: HashMap<Name<'a>, Rc<Cnt<'a>>>,
  funs: HashMap<Name<'a>, Rc<Fun<'a>>>,
}

impl<'a> Symbols<'a> {
  fn new() -> Self {
    Self {
      cnts: HashMap::new(),
      funs: HashMap::new(),
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
  tree: Box<Tree<'a>>,
  symbols: Symbols<'a>,
}

impl<'a> Program<'a> {
  fn new(tree: Box<Tree<'a>>) -> Self {
    Self {
      tree: tree,
      symbols: Symbols::new(),
    }
  }

  pub fn from_raw_tree(tree: Box<Tree<'a>>) -> Self {
    use Tree::*;

    // Rewrite AppC into AppF if name refers to a function
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
                  retC: *ret_cnt,
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

    let mut program = Self::new(tree);
    fix_apps(&mut HashSet::new(), &mut program.tree);
    register_symbols(&mut program.symbols, &program.tree);
    program
  }
}
