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
  test_app_first,
  "(let* ((f (fun (r x y) (r x))) (c (cnt (z) (halt z)))) (f c 1 2))",
  None,
  1
);
test_run!(
  test_app_second,
  "(let* ((f (fun (r x y) (r y))) (c (cnt (z) (halt z)))) (f c 1 2))",
  None,
  2
);
test_run!(
  test_prim_add,
  "(let* ((x (@+ 1 2))) (halt x))",
  None,
  3
);
test_run!(
  test_prim_bytewrite,
  "(let* ((x (@byte-write 43))) (halt x))",
  Some("+"),
  43
);
test_run!(
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
 (t_1 (@id 5))
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
(if (@= 1 v) then else))",
  Some("A"), // fact(5) - 55 = 65
  0
);
