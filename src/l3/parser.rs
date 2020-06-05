extern crate pest;

use super::ast::*;

pub use pest::Parser;
use pest::error::Error;

#[derive(Parser)]
#[grammar = "l3/l3-cps.pest"]
pub struct L3CPSParser;

fn parse_l3cps(input: &str) -> Result<Box<Tree>, Error<Rule>> {
    use pest::iterators::Pair;

    fn parse_name(pair: Pair<Rule>) -> Name {
      Name(pair.as_str())
    }

    fn parse_arg(pair: Pair<Rule>) -> Atom {
      match pair.as_rule() {
        Rule::name => Atom::AtomN(parse_name(pair)),
        Rule::literal => Atom::AtomL(pair.as_str().parse().unwrap()),
        _ => unreachable!(),
      }
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
            pairs.next();
            CPSBlockAlloc(pairs.next().unwrap().as_str().parse().unwrap())
          } else {
            unreachable!()
          }
        },
      }
    }

    // fn parse_binding(pair: Pair<Rule>, body: Box<Tree>) -> Box<Tree> {
    //   let mut pairs = pair.into_inner();
    //   let name = parise_name(pairs.next().unwrap());
    //   let
    // }

    fn parse_tree(pair: Pair<Rule>) -> Box<Tree> {
      Box::new(match pair.as_rule() {
        Rule::lett => {
          let mut pairs = pair.into_inner();
          let bindings_pairs = pairs.next().unwrap().into_inner().rev();
          let body = parse_tree(pairs.next().unwrap());
          println!("XXX body: {:#?}\nYYY bindings: {:#?}", body, bindings_pairs);
          unreachable!()
        },
        Rule::app => {
          let mut pairs = pair.into_inner();
          let name = parse_name(pairs.next().unwrap());
          let args: Args = pairs.map(|pair| parse_arg(pair)).collect();
          // TODO: Implement this stuff properly
          if (args.is_empty()) {
            Tree::AppC { cnt: name, args: vec![] }
          } else {
            Tree::AppF { fun: Atom::AtomN(name.clone()), retC: name, args: args }
          }
        },
        Rule::iff => {
          let mut pairs = pair.into_inner();
          let cond = parse_test_prim(pairs.next().unwrap());
          let arg1 = parse_arg(pairs.next().unwrap());
          let arg2 = parse_arg(pairs.next().unwrap());
          let cnt1 = parse_name(pairs.next().unwrap());
          let cnt2 = parse_name(pairs.next().unwrap());
          Tree::If { cond: cond, args: vec![arg1, arg2], thenC: cnt1, elseC: cnt2 }
        },
        Rule::halt => Tree::Halt { arg: parse_arg(pair.into_inner().next().unwrap()) },
        Rule::tree
        | Rule::EOI
        | Rule::WHITESPACE => unreachable!(),
        ru => { println!("Rule: {:?}", ru); panic!("UH") }
      })
    }

    let tree = L3CPSParser::parse(Rule::tree, input)?.next().unwrap();
    Ok(parse_tree(tree))
}


macro_rules! parse_test {
  ($name:ident, $example:expr) => {
    #[test]
    fn $name() {
      println!("RES: {:?}", parse_l3cps($example)
        .unwrap_or_else(|e| { panic!("Parsing error: {}", e) }));
    }
  }
}

// parse_test!(test_halt, "(halt 0)");
// parse_test!(test_halt_withnl, "(halt\nb)");
// parse_test!(test_app_f0, "(f 0)");
// parse_test!(test_app_fn, "(f n)");
// parse_test!(test_app_fabc, "(f a b 123 c)");
// parse_test!(test_app_fwithnums, "(f999 r88 g7)");
// parse_test!(test_if_lt, "(if (@< 0 x) c1 c2)");
// parse_test!(test_if_le, "(if (@<= x y) c1 c2)");
// parse_test!(test_if_eq, "(if (@= x y) c1 c2)");
parse_test!(test_let_one_prim,    "(let ((a (@id 0))) (halt a))");
// parse_test!(test_let_many_prims,  "(let* ((a (@id 0)) (b (@+ 1 2))) (halt b))");
// parse_test!(test_let_cnt,         "(let* ((c (cnt () (halt 0)))) (c))");
// parse_test!(test_let_fun,         "(let* ((f (fun (r x) (r x)))) (halt b))");
// parse_test!(test_fact_example, "
// (let* ((fact_1
//   (fun (ret-fact x)
//     (let* ((then_1 (cnt () (ret-fact 3)))
//            (else_1
//             (cnt ()
//               (let* ((v_9 (@- x 2))
//                      (rc_1
//                       (cnt (r_2)
//                         (let* ((x_2 (@xor x 1))
//                                (r_3 (@shift-right r_2 1))
//                                (x_1 (@* x_2 r_3))
//                                (v_10 (@xor x_1 1)))
//                           (ret-fact v_10)))))
//                 (fact_1 rc_1 v_9)))))
//       (if (@= 1 x) then_1 else_1))))
//  (t_1 (@byte-read))
//  (t (@shift-left t_1 1))
//  (v (@xor t 1))
//  (then (cnt () (let ((v_8 (@byte-write -54))) (halt 0))))
//  (else
//   (cnt ()
//     (let* ((v_1 (@- v 2))
//            (rc
//             (cnt (r)
//               (let* ((v_6 (@xor v 1))
//                      (r_1 (@shift-right r 1))
//                      (v_5 (@* v_6 r_1))
//                      (v_4 (@xor v_5 1))
//                      (v_3 (@- v_4 110))
//                      (v_2 (@shift-right v_3 1))
//                      (v_7 (@byte-write v_2)))
//                 (halt 0)))))
//       (fact_1 rc v_1)))))
// (if (@= 1 v) then else))
// ");
