use ::l3_llvm_backend::l3;

fn run_str<'a>(program_str: &'a str) {
  let program =
    l3::parser::parse_l3cps_program(program_str).unwrap_or_else(|e| panic!("Parsing error: {}", e));
  l3::codegen::compile_and_run_program(&program)
}

fn main() {
  use std::io::Read;
  use std::path::Path;

  let args: Vec<String> = std::env::args().collect();
  let program = if args.len() < 2 {
    let mut buffer = String::new();
    std::io::stdin()
      .read_to_string(&mut buffer)
      .expect("Failed to read program from stdin");
    buffer
  } else if args.len() == 2 {
    std::fs::read_to_string(Path::new(args.last().unwrap()))
      .expect("Failed to read program from file")
  } else {
    eprintln!(
      "Usage: {} [path-to-program]\n  (or pass program on standard input)",
      args.first().unwrap()
    );
    std::process::exit(1);
  };
  run_str(program.as_str());
}
