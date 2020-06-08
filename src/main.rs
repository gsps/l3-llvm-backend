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

fn main() {
  example_halt();
}
