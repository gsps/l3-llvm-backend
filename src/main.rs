#[macro_use]
extern crate pest_derive;

mod l3;

fn example<'a>(example_str: &'a str) {
  let program =
    l3::parser::parse_l3cps_program(example_str).unwrap_or_else(|e| panic!("Parsing error: {}", e));
  l3::codegen::compile_and_run_program(&program)
}

fn example_halt() {
  example("(halt 3)");
}

fn example_if_basic() {
  example("(let* ((c1 (cnt () (halt 1))) (c2 (cnt () (halt 2)))) (if (@< 2 1) c1 c2))");
}

fn main() {
  // example_halt();
  example_if_basic();
}
