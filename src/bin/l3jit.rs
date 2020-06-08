use ::l3_llvm_backend::l3;

fn run_str<'a>(example_str: &'a str) {
  let program =
    l3::parser::parse_l3cps_program(example_str).unwrap_or_else(|e| panic!("Parsing error: {}", e));
  l3::codegen::compile_and_run_program(&program)
}

fn main() {
  use std::io::{self, Read};
  let mut buffer = String::new();
  io::stdin().read_to_string(&mut buffer).expect("Failed to read program");
  run_str(buffer.as_str());
}
