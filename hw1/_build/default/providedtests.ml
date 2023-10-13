open Assert
open Hellocaml

(* These tests are provided by you -- they will NOT be graded *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let e4 : exp = Mult(Var "y", Const 0L)
let e5 : exp = Add(e1, Add(e2, Add(Neg(e1), e4)))

let provided_tests : suite = [
  Test ("Student-Provided Tests For Problem 1-3", [
    ("case1", assert_eqf (fun () -> 42) prob3_ans );
    ("case2", assert_eqf (fun () -> 25) (prob3_case2 17) );
    ("case3", assert_eqf (fun () -> prob3_case3) 64);
  ]);
  Test ("Student-provided tests for Problem 4-2", [
    ("case1", assert_eqf (fun() -> string_of e4) "(y * 0)");
    ("case2", assert_eqf (fun() -> string_of e5) "((2 * 3) + ((x + 1) + (-((2 * 3)) + (y * 0))))");
  ]);
  Test ("Student-Provided tests for Problem 4-4", [
    ("case1", assert_eqf (fun() -> (interpret ctxt2 e4)) 0L);
    ("case1", assert_eqf (fun() -> (interpret ctxt2 e5)) 3L);
  ])
  
] 
