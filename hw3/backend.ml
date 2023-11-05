(* ll ir compilation -------------------------------------------------------- *)

open Ll
open X86

(* Overview ----------------------------------------------------------------- *)

(* We suggest that you spend some time understanding this entire file and
   how it fits with the compiler pipeline before making changes.  The suggested
   plan for implementing the compiler is provided on the project web page.
*)

(* helpers ------------------------------------------------------------------ *)

(* Map LL comparison operations to X86 condition codes *)
let compile_cnd = function
  | Ll.Eq -> X86.Eq
  | Ll.Ne -> X86.Neq
  | Ll.Slt -> X86.Lt
  | Ll.Sle -> X86.Le
  | Ll.Sgt -> X86.Gt
  | Ll.Sge -> X86.Ge

(* locals and layout -------------------------------------------------------- *)

(* One key problem in compiling the LLVM IR is how to map its local
   identifiers to X86 abstractions.  For the best performance, one
   would want to use an X86 register for each LLVM %uid.  However,
   since there are an unlimited number of %uids and only 16 registers,
   doing so effectively is quite difficult.  We will see later in the
   course how _register allocation_ algorithms can do a good job at
   this.

   A simpler, but less performant, implementation is to map each %uid
   in the LLVM source to a _stack slot_ (i.e. a region of memory in
   the stack).  Since LLVMlite, unlike real LLVM, permits %uid locals
   to store only 64-bit data, each stack slot is an 8-byte value.

   [ NOTE: For compiling LLVMlite, even i1 data values should be
   represented as a 8-byte quad. This greatly simplifies code
   generation. ]

   We call the datastructure that maps each %uid to its stack slot a
   'stack layout'.  A stack layout maps a uid to an X86 operand for
   accessing its contents.  For this compilation strategy, the operand
   is always an offset from %rbp (in bytes) that represents a storage slot in
   the stack.
*)

type layout = (uid * X86.operand) list

(* A context contains the global type declarations (needed for getelementptr
   calculations) and a stack layout. *)
type ctxt = { tdecls : (tid * ty) list; layout : layout }

(* useful for looking up items in tdecls or layouts *)
let lookup m x = List.assoc x m

(* compiling operands  ------------------------------------------------------ *)

(* LLVM IR instructions support several kinds of operands.

   LL local %uids live in stack slots, whereas global ids live at
   global addresses that must be computed from a label.  Constants are
   immediately available, and the operand Null is the 64-bit 0 value.

     NOTE: two important facts about global identifiers:

     (1) You should use (Platform.mangle gid) to obtain a string
     suitable for naming a global label on your platform (OS X expects
     "_main" while linux expects "main").

     (2) 64-bit assembly labels are not allowed as immediate operands.
     That is, the X86 code: movq _gid %rax which looks like it should
     put the address denoted by _gid into %rax is not allowed.
     Instead, you need to compute an %rip-relative address using the
     leaq instruction:   leaq _gid(%rip).

   One strategy for compiling instruction operands is to use a
   designated register (or registers) for holding the values being
   manipulated by the LLVM IR instruction. You might find it useful to
   implement the following helper function, whose job is to generate
   the X86 instruction that moves an LLVM operand into a designated
   destination (usually a register).
*)
let compile_operand (ctxt : ctxt) (dest : X86.operand) : Ll.operand -> ins =
  function
  | Ll.Null -> (Movq, [ Imm (Lit 0L); dest ])
  | Ll.Const x -> (Movq, [ Imm (Lit x); dest ])
  | Ll.Gid gid -> (Leaq, [ Ind3 (Lbl (Platform.mangle gid), Rip); dest ])
  | Ll.Id uid -> (Movq, [ lookup ctxt.layout uid; dest ])

(* compiling call  ---------------------------------------------------------- *)

(* You will probably find it helpful to implement a helper function that
   generates code for the LLVM IR call instruction.

   The code you generate should follow the x64 System V AMD64 ABI
   calling conventions, which places the first six 64-bit (or smaller)
   values in registers and pushes the rest onto the stack.  Note that,
   since all LLVM IR operands are 64-bit values, the first six
   operands will always be placed in registers.  (See the notes about
   compiling fdecl below.)

   [ NOTE: It is the caller's responsibility to clean up arguments
   pushed onto the stack, so you must free the stack space after the
   call returns. ]

   [ NOTE: Don't forget to preserve caller-save registers (only if
   needed). ]
*)

(* compiling getelementptr (gep)  ------------------------------------------- *)

(* The getelementptr instruction computes an address by indexing into
   a datastructure, following a path of offsets.  It computes the
   address based on the size of the data, which is dictated by the
   data's type.

   To compile getelementptr, you must generate x86 code that performs
   the appropriate arithmetic calculations.
*)

(* [size_ty] maps an LLVMlite type to a size in bytes.
    (needed for getelementptr)

   - the size of a struct is the sum of the sizes of each component
   - the size of an array of t's with n elements is n * the size of t
   - all pointers, I1, and I64 are 8 bytes
   - the size of a named type is the size of its definition

   - Void, i8, and functions have undefined sizes according to LLVMlite.
     Your function should simply return 0 in those cases
*)
let rec size_ty (tdecls : (tid * ty) list) (t : Ll.ty) : int =
  match t with
  | Struct s -> (
      match s with
      | x :: tl -> size_ty tdecls x + size_ty tdecls (Struct tl)
      | _ -> 0)
  | Array (n, a) -> size_ty tdecls a * n
  | I1 | I64 | Ptr _ -> 8
  | I8 | Void | Fun _ -> 0
  | Namedt x -> size_ty tdecls (List.assoc x tdecls)
  | _ -> 0

(* Generates code that computes a pointer value.

   1. op must be of pointer type: t*

   2. the value of op is the base address of the calculation

   3. the first index in the path is treated as the index into an array
     of elements of type t located at the base address

   4. subsequent indices are interpreted according to the type t:

     - if t is a struct, the index must be a constant n and it
       picks out the n'th element of the struct. [ NOTE: the offset
       within the struct of the n'th element is determined by the
       sizes of the types of the previous elements ]

     - if t is an array, the index can be any operand, and its
       value determines the offset within the array.

     - if t is any other type, the path is invalid

   5. if the index is valid, the remainder of the path is computed as
      in (4), but relative to the type f the sub-element picked out
      by the path so far
*)
let compile_gep (ctxt : ctxt) (op : Ll.ty * Ll.operand) (path : Ll.operand list)
    : ins list =
  failwith "compile_gep not implemented"

(* compiling instructions  -------------------------------------------------- *)

(* The result of compiling a single LLVM instruction might be many x86
   instructions.  We have not determined the structure of this code
   for you. Some of the instructions require only a couple of assembly
   instructions, while others require more.  We have suggested that
   you need at least compile_operand, compile_call, and compile_gep
   helpers; you may introduce more as you see fit.

   Here are a few notes:

   - Icmp:  the Setb instruction may be of use.  Depending on how you
     compile Cbr, you may want to ensure that the value produced by
     Icmp is exactly 0 or 1.

   - Load & Store: these need to dereference the pointers. Const and
     Null operands aren't valid pointers.  Don't forget to
     Platform.mangle the global identifier.

   - Alloca: needs to return a pointer into the stack

   - Bitcast: does nothing interesting at the assembly level
*)

let map_bop_opcode (b : bop) : opcode =
  match b with
  | Add -> Addq
  | Sub -> Subq
  | Mul -> Imulq
  | Shl -> Shlq
  | Lshr -> Shrq
  | Ashr -> Sarq
  | And -> Andq
  | Or -> Orq
  | Xor -> Xorq

let compile_icmp (ctxt: ctxt) (uid: uid) (c: Ll.cnd) (t: ty) (op1: Ll.operand) (op2: Ll.operand) = []
  

let compile_insn (ctxt : ctxt) ((uid : uid), (i : Ll.insn)) : X86.ins list =
  match i with
  | Binop (b, t, op1, op2) -> (
      match t with
      | I1 | I8 | I64 ->
          [
            (compile_operand ctxt (Reg Rax)) op1;
            (compile_operand ctxt (Reg Rcx)) op2;
            (map_bop_opcode b, [ Reg Rcx; Reg Rax ]);
            (Movq, [ Reg Rax; lookup ctxt.layout uid ]);
          ]
      | _ -> failwith "Invalid type for Binop")
  | Icmp (c, t, op1, op2) -> compile_icmp ctxt uid c t op1 op2
  | _ -> []

(* compiling terminators  --------------------------------------------------- *)

(* prefix the function name [fn] to a label to ensure that the X86 labels are
   globally unique . *)
let mk_lbl (fn : string) (l : string) = fn ^ "." ^ l

(* Compile block terminators is not too difficult:

   - Ret should properly exit the function: freeing stack space,
     restoring the value of %rbp, and putting the return value (if
     any) in %rax.

   - Br should jump

   - Cbr branch should treat its operand as a boolean conditional

   [fn] - the name of the function containing this terminator
*)
let compile_terminator (fn : string) (ctxt : ctxt) (t : Ll.terminator) :
    ins list =
  match t with
  | Ret (rt, op) ->
      let stack_size = Int64.mul 8L (Int64.of_int (List.length ctxt.layout)) in
      (match rt with
      | I1 | I8 | I64 -> (
          match Option.get op with
          | Const i -> [ (Movq, [ Imm (Lit i); Reg Rax ]) ]
          | Gid id | Id id -> [ (Movq, [ lookup ctxt.layout id; Reg Rax ]) ]
          | _ -> failwith "Expected Non-Null return")
      | _ -> [])
      @ [
          (Addq, [ Imm (Lit stack_size); Reg Rsp ]);
          (Popq, [ Reg Rbp ]);
          (Retq, []);
        ]
  | Br lbl -> [ (Jmp, [ Imm (Lbl (mk_lbl fn lbl)) ]) ]
  | Cbr (op, l1, l2) -> (
      let l1 = mk_lbl fn l1 in
      let l2 = mk_lbl fn l2 in
      match op with
      | Null -> [ (Jmp, [ Imm (Lbl l2) ]) ]
      | Const i ->
          if i <> 0L then [ (Jmp, [ Imm (Lbl l1) ]) ]
          else [ (Jmp, [ Imm (Lbl l2) ]) ]
      | Id id ->
          [
            (Cmpq, [ Imm (Lit 0L); lookup ctxt.layout id ]);
            (J Eq, [ Imm (Lbl l1) ]);
            (Jmp, [ Imm (Lbl l2) ]);
          ]
      | Gid _ ->
          [
            compile_operand ctxt (Reg Rax) op;
            (Cmpq, [ Imm (Lit 0L); Reg Rax ]);
            (J Eq, [ Imm (Lbl l1) ]);
            (Jmp, [ Imm (Lbl l2) ]);
          ])

(* compiling blocks --------------------------------------------------------- *)

(* We have left this helper function here for you to complete.
   [fn] - the name of the function containing this block
   [ctxt] - the current context
   [blk]  - LLVM IR code for the block
*)
let compile_block (fn : string) (ctxt : ctxt) (blk : Ll.block) : ins list =
  let ins_block = List.concat_map (compile_insn ctxt) blk.insns in
  let _, term = blk.term in
  ins_block @ compile_terminator fn ctxt term

let compile_lbl_block fn lbl ctxt blk : elem =
  Asm.text (mk_lbl fn lbl) (compile_block fn ctxt blk)

let compile_all_lbl_blocks (name : string) (f_ctxt : ctxt)
    (lbl_blocks : (lbl * block) list) : elem list =
  let asm_lbl_block (lbl_block : lbl * block) : elem =
    let lbl, blk = lbl_block in
    compile_lbl_block name lbl f_ctxt blk
  in
  List.map asm_lbl_block lbl_blocks

(* compile_fdecl ------------------------------------------------------------ *)

(* This helper function computes the location of the nth incoming
   function argument: either in a register or relative to %rbp,
   according to the calling conventions.  You might find it useful for
   compile_fdecl.

   [ NOTE: the first six arguments are numbered 0 .. 5 ]
*)
let arg_loc (n : int) : operand =
  if n = 0 then Reg Rdi
  else if n = 1 then Reg Rsi
  else if n = 2 then Reg Rdx
  else if n = 3 then Reg Rcx
  else if n = 4 then Reg R08
  else if n = 5 then Reg R09
  else Ind3 (Lit (Int64.of_int ((n - 4) * 8)), Rbp)

(* Allocate all arguments *)
(* let rec args_loc_all (args : uid list) (n : int) : layout =
   match args with
   | h :: tl -> (h, arg_loc n) :: args_loc_all tl (n + 1)
   | _ -> [] *)

(* We suggest that you create a helper function that computes the
   stack layout for a given function declaration.

   - each function argument should be copied into a stack slot
   - in this (inefficient) compilation strategy, each local id
     is also stored as a stack slot.
   - see the discussion about locals
*)

let nth_stack_slot (n : int) : X86.operand =
  Ind3 (Lit (Int64.of_int (-8 * (n + 1))), Rbp)

let rec print_labels_blocks (lbled_blocks : (lbl * block) list) : unit =
  match lbled_blocks with
  | (lbl, _) :: tail ->
      print_endline lbl;
      print_labels_blocks tail
  | [] -> ()

let stack_layout (args : uid list) ((ini_block, lbled_blocks) : cfg) : layout =
  let arg_layout = List.mapi (fun i id -> (id, nth_stack_slot i)) args in
  let rec block_layout ins_list lbl_blocks n =
    match ins_list with
    | (id, ins) :: tl -> (
        match ins with
        | Binop _ | Alloca _ | Load _ | Icmp _ | Bitcast _ | Gep _ ->
            [ (id, nth_stack_slot n) ] @ block_layout tl lbl_blocks (n + 1)
        | Call (t, _, _) ->
            (match t with Void -> [] | _ -> [ (id, nth_stack_slot n) ])
            @ block_layout tl lbl_blocks (n + 1)
        | _ -> [])
    | [] -> (
        match lbl_blocks with
        | (_, bl) :: tail -> block_layout bl.insns tail n
        | _ -> [])
  in
  arg_layout @ block_layout ini_block.insns lbled_blocks (List.length args)

let compile_stack_layout (args : lbl list) (l : layout) : ins list =
  let compile_arg (i : int) (arg : lbl) =
    let op = arg_loc i in
    match op with
    | Reg _ -> [ (Movq, [ op; lookup l arg ]) ]
    | Ind3 _ -> [ (Movq, [ op; Reg Rax ]); (Movq, [ Reg Rax; lookup l arg ]) ]
    | _ -> failwith "Invalid output for arg_loc"
  in
  List.concat (List.mapi compile_arg args)

(* The code for the entry-point of a function must do several things:

   - since our simple compiler maps local %uids to stack slots,
     compiling the control-flow-graph body of an fdecl requires us to
     compute the layout (see the discussion of locals and layout)

   - the function code should also comply with the calling
     conventions, typically by moving arguments out of the parameter
     registers (or stack slots) into local storage space.  For our
     simple compilation strategy, that local storage space should be
     in the stack. (So the function parameters can also be accounted
     for in the layout.)

   - the function entry code should allocate the stack storage needed
     to hold all of the local stack slots.
*)

let compile_fdecl (tdecls : (tid * ty) list) (name : string)
    ({ f_ty; f_param; f_cfg } : fdecl) : prog =
  let main_block, lbl_blocks = f_cfg in
  let f_lay = stack_layout f_param f_cfg in
  let f_ctxt = { tdecls; layout = f_lay } in
  let stack_size = Int64.mul 8L (Int64.of_int (List.length f_ctxt.layout)) in
  let preamble =
    [
      (Pushq, [ Reg Rbp ]);
      (Movq, [ Reg Rsp; Reg Rbp ]);
      (Subq, [ Imm (Lit stack_size); Reg Rsp ]);
    ]
  in
  let asm_cons_layout = compile_stack_layout f_param f_lay in
  let first_block = compile_block name f_ctxt main_block in
  let other_blocks = compile_all_lbl_blocks name f_ctxt lbl_blocks in
  [
    {
      lbl = name;
      global = true;
      asm = Text (preamble @ asm_cons_layout @ first_block);
    };
  ]
  @ other_blocks

(* compile_gdecl ------------------------------------------------------------ *)
(* Compile a global value into an X86 global data declaration and map
   a global uid to its associated X86 label.
*)
let rec compile_ginit : ginit -> X86.data list = function
  | GNull -> [ Quad (Lit 0L) ]
  | GGid gid -> [ Quad (Lbl (Platform.mangle gid)) ]
  | GInt c -> [ Quad (Lit c) ]
  | GString s -> [ Asciz s ]
  | GArray gs | GStruct gs -> List.map compile_gdecl gs |> List.flatten
  | GBitcast (t1, g, t2) -> compile_ginit g

and compile_gdecl (_, g) = compile_ginit g

(* compile_prog ------------------------------------------------------------- *)
let compile_prog { tdecls; gdecls; fdecls } : X86.prog =
  let g (lbl, gdecl) = Asm.data (Platform.mangle lbl) (compile_gdecl gdecl) in
  let f (name, fdecl) = compile_fdecl tdecls name fdecl in
  List.map g gdecls @ (List.map f fdecls |> List.flatten)
