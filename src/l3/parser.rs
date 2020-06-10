extern crate pest;

use super::ast::*;

use pest::error::Error;
pub use pest::Parser;

#[derive(Parser)]
#[grammar = "l3/l3-cps.pest"]
pub struct L3CPSParser;

pub fn parse_l3cps_program(input: &str) -> Result<Program, Error<Rule>> {
  use pest::iterators::{Pair, Pairs};

  fn parse_name(pair: Pair<Rule>) -> Name {
    Name(pair.as_str())
  }

  fn parse_arg(pair: Pair<Rule>) -> Arg {
    match pair.as_rule() {
      Rule::name => Atom::AtomN(parse_name(pair)),
      Rule::literal => Atom::AtomL(pair.as_str().parse::<i32>().unwrap() as u32),
      _ => unreachable!(),
    }
  }

  fn parse_args(pairs: Pairs<Rule>) -> Args {
    pairs.map(|pair| parse_arg(pair)).collect()
  }

  fn parse_test_prim(pair: Pair<Rule>) -> TestPrimitive {
    use TestPrimitive::*;
    match pair.as_str() {
      "<" => CPSLt,
      "<=" => CPSLe,
      "=" => CPSEq,
      _ => unreachable!(),
    }
  }

  fn parse_value_prim(pair: Pair<Rule>) -> ValuePrimitive {
    use ValuePrimitive::*;
    match pair.as_str() {
      "+" => CPSAdd,
      "-" => CPSSub,
      "*" => CPSMul,
      "/" => CPSDiv,
      "%" => CPSMod,
      "shift-left" => CPSShiftLeft,
      "shift-right" => CPSShiftRight,
      "and" => CPSAnd,
      "or" => CPSOr,
      "xor" => CPSXOr,
      "byte-read" => CPSByteRead,
      "byte-write" => CPSByteWrite,
      "block-tag" => CPSBlockTag,
      "block-length" => CPSBlockLength,
      "block-get" => CPSBlockGet,
      "block-set!" => CPSBlockSet,
      "id" => CPSId,
      s => {
        if s.starts_with("block-alloc-") {
          let mut pairs = pair.into_inner();
          let tag = pairs.next().unwrap().as_str();
          CPSBlockAlloc(tag.parse().unwrap())
        } else {
          unreachable!()
        }
      }
    }
  }

  // Update body if it is a LetC, otherwise wrap in new LetC
  fn push_cnt<'a>(
    name: Name<'a>,
    params: Params<'a>,
    cnt_body: Box<Tree<'a>>,
    body: Box<Tree<'a>>,
  ) -> Box<Tree<'a>> {
    let mut body = body;
    let cnt = Rc::new(Cnt {
      name: name,
      params: params,
      body: cnt_body,
    });
    match body.as_mut() {
      Tree::LetC { cnts, .. } => {
        cnts.push(cnt);
        body
      }
      _ => Box::new(Tree::LetC {
        cnts: vec![cnt],
        body: body,
      }),
    }
  }

  // Update body if it is a LetF, otherwise wrap in new LetF
  fn push_fun<'a>(
    name: Name<'a>,
    ret_cnt: Name<'a>,
    params: Params<'a>,
    fun_body: Box<Tree<'a>>,
    body: Box<Tree<'a>>,
  ) -> Box<Tree<'a>> {
    let mut body = body;
    let fun = Rc::new(Fun {
      name: name,
      ret_cnt: ret_cnt,
      params: params,
      body: fun_body,
    });
    match body.as_mut() {
      Tree::LetF { funs, .. } => {
        funs.push(fun);
        body
      }
      _ => Box::new(Tree::LetF {
        funs: vec![fun],
        body: body,
      }),
    }
  }

  fn parse_binding<'a>(pair: Pair<'a, Rule>, body: Box<Tree<'a>>) -> Box<Tree<'a>> {
    let mut pairs = pair.into_inner();
    let name = parse_name(pairs.next().unwrap());
    let rhs_pair = pairs.next().unwrap();

    match rhs_pair.as_rule() {
      Rule::prim_bdg => {
        let mut pairs = rhs_pair.into_inner();
        let prim = parse_value_prim(pairs.next().unwrap());
        let args = parse_args(pairs);
        Box::new(Tree::LetP {
          name: name,
          prim: prim,
          args: args,
          body: body,
        })
      }
      Rule::cnt_bdg => {
        let mut pairs = rhs_pair.into_inner();
        let params = pairs
          .next()
          .unwrap()
          .into_inner()
          .map(|pair| parse_name(pair))
          .collect();
        let cnt_body = parse_tree(pairs.next().unwrap());
        push_cnt(name, params, cnt_body, body)
      }
      Rule::fun_bdg => {
        let mut pairs = rhs_pair.into_inner();
        let ret_cnt = parse_name(pairs.next().unwrap());
        let params = pairs
          .next()
          .unwrap()
          .into_inner()
          .map(|pair| parse_name(pair))
          .collect();
        let fun_body = parse_tree(pairs.next().unwrap());
        push_fun(name, ret_cnt, params, fun_body, body)
      }
      _ => unreachable!(),
    }
  }

  fn parse_tree(pair: Pair<Rule>) -> Box<Tree> {
    match pair.as_rule() {
      Rule::lett => {
        let mut pairs = pair.into_inner();
        let bindings_pairs = pairs.next().unwrap().into_inner();
        let body = parse_tree(pairs.next().unwrap());
        bindings_pairs.rfold(body, |acc, pair| parse_binding(pair, acc))
      }
      Rule::app => {
        let mut pairs = pair.into_inner();
        let name = parse_name(pairs.next().unwrap());
        let args = parse_args(pairs);
        Box::new(Tree::AppC {
          cnt: name,
          args: args,
        })
      }
      Rule::iff => {
        let mut pairs = pair.into_inner();
        let cond = parse_test_prim(pairs.next().unwrap());
        let arg1 = parse_arg(pairs.next().unwrap());
        let arg2 = parse_arg(pairs.next().unwrap());
        let then_cnt = parse_name(pairs.next().unwrap());
        let else_cnt = parse_name(pairs.next().unwrap());
        Box::new(Tree::If {
          cond: cond,
          args: vec![arg1, arg2],
          then_cnt: then_cnt,
          else_cnt: else_cnt,
        })
      }
      Rule::halt => Box::new(Tree::Halt {
        arg: parse_arg(pair.into_inner().next().unwrap()),
      }),
      Rule::tree | Rule::EOI | Rule::WHITESPACE => unreachable!(),
      _ => unreachable!(),
    }
  }

  let parsed = L3CPSParser::parse(Rule::tree, input)?.next().unwrap();
  let tree = parse_tree(parsed);
  let program = Program::from_raw_tree(tree);
  Ok(program)
}

macro_rules! parse_test {
  ($name:ident, $example:expr) => {
    #[test]
    fn $name() {
      let _res = parse_l3cps_program($example).unwrap_or_else(|e| panic!("Parsing error: {}", e));
      // println!("Successfully parsed: {:#?}", res);
    }
  };
}

parse_test!(test_halt, "(halt 0)");
parse_test!(test_halt_withnl, "(halt\nb)");
parse_test!(test_app_f0, "(f 0)");
parse_test!(test_app_fn, "(f n)");
parse_test!(test_app_fabc, "(f a b 123 c)");
parse_test!(test_app_fwithnums, "(f999 r88 g7)");
parse_test!(test_if_lt, "(if (@< 0 x) c1 c2)");
parse_test!(test_if_le, "(if (@<= x y) c1 c2)");
parse_test!(test_if_eq, "(if (@= x y) c1 c2)");
parse_test!(test_let_one_prim, "(let ((a (@id 0))) (halt a))");
parse_test!(
  test_let_many_prims,
  "(let* ((a (@id 0)) (b (@+ 1 2))) (halt b))"
);
parse_test!(test_let_cnt1, "(let* ((c (cnt () (halt 0)))) (c))");
parse_test!(
  test_let_cnt2,
  "(let* ((c1 (cnt () (c2 0))) (c2 (cnt (x) (halt x)))) (c1))"
);
parse_test!(test_let_fun1, "(let* ((f (fun (r x) (r x)))) (halt 0))");
parse_test!(
  test_let_fun2,
  "(let* ((f (fun (r x) (r x))) (g (fun (r x) (f r x)))) (halt 0))"
);
parse_test!(
  test_let_fun3,
  "(let* ((f (fun (r x) (r x))) (g (fun (r x) (f r x))) (c (cnt (x) (halt x)))) (g c 0))"
);
// parse_test!(test_let_fun_bad,     "(let* ((f (fun (r x) (r x))) (f (fun (r x) (f r x)))) (halt 0))");
parse_test!(
  test_fact_example,
  "\
(let* ((fact_1
  (fun (ret-fact x)
    (let* ((then_1 (cnt () (ret-fact 3)))
           (else_1
            (cnt ()
              (let* ((v_9 (@- x 2))
                     (rc_1
                      (cnt (r_2)
                        (let* ((x_2 (@xor x 1))
                               (r_3 (@shift-right r_2 1))
                               (x_1 (@* x_2 r_3))
                               (v_10 (@xor x_1 1)))
                          (ret-fact v_10)))))
                (fact_1 rc_1 v_9)))))
      (if (@= 1 x) then_1 else_1))))
 (t_1 (@byte-read))
 (t (@shift-left t_1 1))
 (v (@xor t 1))
 (then (cnt () (let ((v_8 (@byte-write -54))) (halt 0))))
 (else
  (cnt ()
    (let* ((v_1 (@- v 2))
           (rc
            (cnt (r)
              (let* ((v_6 (@xor v 1))
                     (r_1 (@shift-right r 1))
                     (v_5 (@* v_6 r_1))
                     (v_4 (@xor v_5 1))
                     (v_3 (@- v_4 110))
                     (v_2 (@shift-right v_3 1))
                     (v_7 (@byte-write v_2)))
                (halt 0)))))
      (fact_1 rc v_1)))))
(if (@= 1 v) then else))"
);
