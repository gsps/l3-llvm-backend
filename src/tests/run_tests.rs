extern crate l3_llvm_runtime;

extern crate assert_cmd;
use assert_cmd::Command;

macro_rules! test_run {
  ($name:ident, $example:expr, $output:expr, $exit:expr) => {
    #[test]
    fn $name() {
      let mut cmd = Command::cargo_bin("l3jit").unwrap();
      let assert = cmd.write_stdin($example).assert().code($exit);
      if let Some::<&'static str>(output) = $output {
        assert.stdout(output);
      }
    }
  };
}

test_run!(test_halt1, "(halt 0)", None, 0);
test_run!(
  test_if_lt,
  "(let* ((c1 (cnt () (halt 1))) (c2 (cnt () (halt 2)))) (if (@< 2 1) c1 c2))",
  None,
  2
);
test_run!(
  test_if_le,
  "(let* ((c1 (cnt () (halt 1))) (c2 (cnt () (halt 2)))) (if (@<= 2 2) c1 c2))",
  None,
  1
);
test_run!(
  test_app_second,
  "(let* ((f (fun (r x y) (r y))) (c (cnt (z) (halt z)))) (f c 1 2))",
  None,
  2
);
