#![allow(non_snake_case)]

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Name<'a>(pub &'a str);

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

#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Tree<'a> {
  LetP { name: Name<'a>, prim: ValuePrimitive, args: Args<'a>, body: Box<Tree<'a>> },
  AppC { cnt: Name<'a>, args: Args<'a> },
  AppF { fun: Arg<'a>, retC: Name<'a>, args: Args<'a> },
  If { cond: TestPrimitive, args: Args<'a>, thenC: Name<'a>, elseC: Name<'a> },
  Halt { arg: Atom<'a> },
}
