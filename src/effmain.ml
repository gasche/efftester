open Efftester

let () =
  resetvar ();
  resettypevar ();
  QCheck_runner.run_tests_main [ dep_eq_test_with_logging ]
;;
