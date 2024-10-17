# Compiler Design

This repo contains the solutions for the Compiler Design course at ETH Zurich. In this course, we built a fully functional compiler from scratch in OCaml. We use a fictional C-like programming language called OAT as a source, LLVMlite as an intermediate representation language, and X86lite. All of these consist of simplified subsets of the languages they are named after.

Here is a non-exhaustive list of what was implemented for each assignment:
1. Introduction to OCaml2.
2. Simulator, Assembler, and Loader for X86lite.
3. Compiler for LLVMlite to X86lite
4. Lexer and Parser. Basic compiler for OAT to LLVMlite with support to basic variable types and functions.
5. Typechecker for OAT. Add support for structs, function pointers, and advanced initialization and casting of variables.
6. Optimizations based on Dataflow analysis. Alias analysis, dead code elimination, constant propagation, and register allocation.

Each assignment has a README explaining how to run and test them. Assignments 5 and 6 have complete compilers.
