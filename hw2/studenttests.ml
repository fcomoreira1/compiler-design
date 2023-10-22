open Assert
open X86
open Simulator
open Xor_test
open Add_test
open Shift_test
open Invalid_test
open Kek
open Sub_test
(* You can use this file for additional test cases to help your *)
(* implementation.                                              *)


let provided_tests : suite = [
  Test ("Debug", [
  ]);
  Test("xor",xor_tests);
  Test("add",add_tests);
  Test("sub",sub_tests);
  Test("shift",shift_tests);
  Test("inv",invalid_tests);
  Test("kek",kek_tests);
] 
