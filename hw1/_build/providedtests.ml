open Assert
open Hellocaml

(* These tests are provided by you -- they will NOT be graded *)

(* You should also add additional test cases here to help you   *)
(* debug your program.                                          *)

let ctxt4 = [ ("x", 2L); ("y", 7L); ("z", 0L)]
let ctxt3 = [ ("x", 3L); ("y", 1L); ("z", 5L) ]
let e4 : exp = Mult(Var "y", Const 0L)
let e5 : exp = Add(e1, Add(e2, Add(Neg(e1), e4)))
let e6 : exp = Mult(Var "y", Add(Const 1L, Add(Var "x", Add(Neg(Var "x"), Const 0L))))
let e7 = Mult (e3, Add (Var "z", e3))
let e8 = Add (Const 3L, Mult(Const 0L , Var "x"))

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
    ("case2", assert_eqf (fun() -> (interpret ctxt2 e5)) 3L);
  ]);
  Test ("Student-Provided tests for Problem 4-5", [
    ("case1", assert_eqf (fun() -> (optimize (Neg(Mult(Const 1L, Add(Var "x", Const 0L)))))) (Neg(Var "x")));
    ("case2", assert_eqf (fun() -> (optimize (Add(Var "X", Mult(Var "y", Var "z"))))) (Add(Var "X", Mult(Var "y", Var "z"))));
    ("case3", assert_eqf (fun() -> (optimize e4)) (Const 0L));
    ("case4", assert_eqf (fun() -> (optimize e8)) (Const 3L));
    ("case5", assert_eqf (fun() -> (optimize e6)) (Var "y"));
  ]);
  Test ("Student-Provided tests for Problem 5", [
    ("case1", assert_eqf (fun() -> interpret ctxt3 e1) (run ctxt3 (compile e1)));
    ("case2", assert_eqf (fun() -> interpret ctxt3 e2) (run ctxt3 (compile e2)));
    ("case3", assert_eqf (fun() -> interpret ctxt3 e3) (run ctxt3 (compile e3)));
    ("case4", assert_eqf (fun() -> interpret ctxt3 e4) (run ctxt3 (compile e4)));
    ("case5", assert_eqf (fun() -> interpret ctxt3 e5) (run ctxt3 (compile e5)));
    ("case6", assert_eqf (fun() -> interpret ctxt3 e6) (run ctxt3 (compile e6)));
    ("case7", assert_eqf (fun() -> interpret ctxt3 e7) (run ctxt3 (compile e7)));
    ("case8", assert_eqf (fun() -> interpret ctxt3 e8) (run ctxt3 (compile e8)));
    ("case9", assert_eqf (fun() -> interpret ctxt4 e1) (run ctxt4 (compile e1)));
    ("case10", assert_eqf (fun() -> interpret ctxt4 e2) (run ctxt4 (compile e2)));
    ("case11", assert_eqf (fun() -> interpret ctxt4 e3) (run ctxt4 (compile e3)));
    ("case12", assert_eqf (fun() -> interpret ctxt4 e4) (run ctxt4 (compile e4)));
    ("case13", assert_eqf (fun() -> interpret ctxt4 e5) (run ctxt4 (compile e5)));
    ("case14", assert_eqf (fun() -> interpret ctxt4 e6) (run ctxt4 (compile e6)));
    ("case15", assert_eqf (fun() -> interpret ctxt4 e7) (run ctxt4 (compile e7)));
    ("case16", assert_eqf (fun() -> interpret ctxt4 e8) (run ctxt4 (compile e8)));
  ]);
] 
