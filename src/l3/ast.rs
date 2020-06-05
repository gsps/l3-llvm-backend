#![allow(non_snake_case, dead_code)]

use std::hash::{Hash, Hasher};
use std::collections::HashMap;
pub use std::rc::Rc;

#[derive(Debug, Copy, Clone)]
pub struct Name<'a>(pub &'a str);

impl<'a> PartialEq for Name<'a> {
  fn eq(&self, other: &Self) -> bool {
    *self.0 == *other.0
  }
}
impl<'a> Eq for Name<'a> {}

impl<'a> Hash for Name<'a> {
  fn hash<H: Hasher>(&self, state: &mut H) {
    (*self.0).hash(state);
  }
}

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

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Atom<'a> {
  AtomN(Name<'a>),
  AtomL(i32),
}

pub type Arg<'a>  = Atom<'a>;
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
  LetP { name: Name<'a>, prim: ValuePrimitive, args: Args<'a>, body: Box<Tree<'a>> },
  LetC { cnts: Vec<Rc<Cnt<'a>>>, body: Box<Tree<'a>> },
  LetF { funs: Vec<Rc<Fun<'a>>>, body: Box<Tree<'a>> },
  AppC { cnt: Name<'a>, args: Args<'a> },
  AppF { fun: Arg<'a>, retC: Name<'a>, args: Args<'a> },
  If { cond: TestPrimitive, args: Args<'a>, thenC: Name<'a>, elseC: Name<'a> },
  Halt { arg: Atom<'a> },
}

#[derive(Debug)]
pub struct Program<'a> {
  tree: Box<Tree<'a>>,
  symbols: Symbols<'a>,
}

#[derive(Debug)]
pub struct Symbols<'a> {
  cnts: HashMap<Name<'a>, Rc<Cnt<'a>>>,
  funs: HashMap<Name<'a>, Rc<Fun<'a>>>,
}

impl<'a> Symbols<'a> {
  fn register_cnt(&mut self, cnt: Rc<Cnt<'a>>) -> () {
    assert!(!self.cnts.contains_key(&cnt.name));
    self.cnts.insert(cnt.name, cnt);
  }

  fn register_fun(&mut self, fun: Rc<Fun<'a>>) -> () {
    assert!(!self.funs.contains_key(&fun.name));
    self.funs.insert(fun.name, fun);
  }
}

impl<'a> Program<'a> {
  fn new(tree: Box<Tree<'a>>) -> Self {
    Self {
      tree: tree,
      symbols: Symbols {
        cnts: HashMap::new(),
        funs: HashMap::new()
      }
    }
  }

  pub fn build_from_tree(tree: Box<Tree<'a>>) -> Self {
    fn traverse<'a>(symbols: &mut Symbols<'a>, tree: &Tree<'a>) -> () {
      use Tree::*;
      match &tree {
        LetP { body, .. } => traverse(symbols, body),
        LetC { cnts, body } => {
          for cnt in cnts {
            symbols.register_cnt(cnt.clone());
            traverse(symbols, &cnt.body)
          }
          traverse(symbols, body)
        },
        LetF { funs, body } => {
          for fun in funs {
            symbols.register_fun(fun.clone());
            traverse(symbols, &fun.body)
          }
          traverse(symbols, body)
        },
        _ => ()
      }
    }

    let mut program = Self::new(tree);
    traverse(&mut program.symbols, &program.tree);
    program
  }
}
