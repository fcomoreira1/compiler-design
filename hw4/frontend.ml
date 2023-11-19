open Ll
open Llutil
open Ast

(* instruction streams ------------------------------------------------------ *)

(* As in the last project, we'll be working with a flattened representation
   of LLVMlite programs to make emitting code easier. This version
   additionally makes it possible to emit elements will be gathered up and
   "hoisted" to specific parts of the constructed CFG
   - G of gid * Ll.gdecl: allows you to output global definitions in the middle
     of the instruction stream. You will find this useful for compiling string
     literals
   - E of uid * insn: allows you to emit an instruction that will be moved up
     to the entry block of the current function. This will be useful for
     compiling local variable declarations
*)

type elt =
  | L of Ll.lbl (* block labels *)
  | I of uid * Ll.insn (* instruction *)
  | T of Ll.terminator (* block terminators *)
  | G of gid * Ll.gdecl (* hoisted globals (usually strings) *)
  | E of uid * Ll.insn (* hoisted entry block instructions *)

type stream = elt list

let ( >@ ) x y = y @ x
let ( >:: ) x y = y :: x
let lift : (uid * insn) list -> stream = List.rev_map (fun (x, i) -> I (x, i))

(* Build a CFG and collection of global variable definitions from a stream *)
let cfg_of_stream (code : stream) : Ll.cfg * (Ll.gid * Ll.gdecl) list =
  let gs, einsns, insns, term_opt, blks =
    List.fold_left
      (fun (gs, einsns, insns, term_opt, blks) e ->
        match e with
        | L l -> (
            match term_opt with
            | None ->
                if List.length insns = 0 then (gs, einsns, [], None, blks)
                else
                  failwith
                  @@ Printf.sprintf
                       "build_cfg: block labeled %s hasno terminator" l
            | Some term -> (gs, einsns, [], None, (l, { insns; term }) :: blks))
        | T t -> (gs, einsns, [], Some (Llutil.Parsing.gensym "tmn", t), blks)
        | I (uid, insn) -> (gs, einsns, (uid, insn) :: insns, term_opt, blks)
        | G (gid, gdecl) -> ((gid, gdecl) :: gs, einsns, insns, term_opt, blks)
        | E (uid, i) -> (gs, (uid, i) :: einsns, insns, term_opt, blks))
      ([], [], [], None, []) code
  in
  match term_opt with
  | None -> failwith "build_cfg: entry block has no terminator"
  | Some term ->
      let insns = einsns @ insns in
      (({ insns; term }, blks), gs)

(* compilation contexts ----------------------------------------------------- *)

(* To compile OAT variables, we maintain a mapping of source identifiers to the
   corresponding LLVMlite operands. Bindings are added for global OAT variables
   and local variables that are in scope. *)

module Ctxt = struct
  type t = (Ast.id * (Ll.ty * Ll.operand)) list

  let empty = []

  (* Add a binding to the context *)
  let add (c : t) (id : id) (bnd : Ll.ty * Ll.operand) : t = (id, bnd) :: c

  (* Lookup a binding in the context *)
  let lookup (id : Ast.id) (c : t) : Ll.ty * Ll.operand = List.assoc id c

  (* Lookup a function, fail otherwise *)
  let lookup_function (id : Ast.id) (c : t) : Ll.ty * Ll.operand =
    match List.assoc id c with
    | Ptr (Fun (args, ret)), g -> (Ptr (Fun (args, ret)), g)
    | _ -> failwith @@ id ^ " not bound to a function"

  let lookup_function_option (id : Ast.id) (c : t) : (Ll.ty * Ll.operand) option
      =
    try Some (lookup_function id c) with _ -> None
end

(* compiling OAT types ------------------------------------------------------ *)

(* The mapping of source types onto LLVMlite is straightforward. Booleans and ints
   are represented as the corresponding integer types. OAT strings are
   pointers to bytes (I8). Arrays are the most interesting type: they are
   represented as pointers to structs where the first component is the number
   of elements in the following array.

   The trickiest part of this project will be satisfying LLVM's rudimentary type
   system. Recall that global arrays in LLVMlite need to be declared with their
   length in the type to statically allocate the right amount of memory. The
   global strings and arrays you emit will therefore have a more specific type
   annotation than the output of cmp_rty. You will have to carefully bitcast
   gids to satisfy the LLVM type checker.
*)

let rec cmp_ty : Ast.ty -> Ll.ty = function
  | Ast.TBool -> I1
  | Ast.TInt -> I64
  | Ast.TRef r -> Ptr (cmp_rty r)

and cmp_rty : Ast.rty -> Ll.ty = function
  | Ast.RString -> I8
  | Ast.RArray u -> Struct [ I64; Array (0, cmp_ty u) ]
  | Ast.RFun (ts, t) ->
      let args, ret = cmp_fty (ts, t) in
      Fun (args, ret)

and cmp_ret_ty : Ast.ret_ty -> Ll.ty = function
  | Ast.RetVoid -> Void
  | Ast.RetVal t -> cmp_ty t

and cmp_fty (ts, r) : Ll.fty = (List.map cmp_ty ts, cmp_ret_ty r)

let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Eq | Neq | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)

let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot -> (TBool, TBool)

(* Compiler Invariants

    The LLVM IR type of a variable (whether global or local) that stores an Oat
    array value (or any other reference type, like "string") will always be a
    double pointer.  In general, any Oat variable of Oat-type t will be
    represented by an LLVM IR value of type Ptr (cmp_ty t).  So the Oat variable
    x : int will be represented by an LLVM IR value of type i64*, y : string will
    be represented by a value of type i8**, and arr : int[] will be represented
    by a value of type {i64, [0 x i64]}**.  Whether the LLVM IR type is a
    "single" or "double" pointer depends on whether t is a reference type.

    We can think of the compiler as paying careful attention to whether a piece
    of Oat syntax denotes the "value" of an expression or a pointer to the
    "storage space associated with it".  This is the distinction between an
    "expression" and the "left-hand-side" of an assignment statement.  Compiling
    an Oat variable identifier as an expression ("value") does the load, so
    cmp_exp called on an Oat variable of type t returns (code that) generates a
    LLVM IR value of type cmp_ty t.  Compiling an identifier as a left-hand-side
    does not do the load, so cmp_lhs called on an Oat variable of type t returns
    and operand of type (cmp_ty t)*.  Extending these invariants to account for
    array accesses: the assignment e1[e2] = e3; treats e1[e2] as a
    left-hand-side, so we compile it as follows: compile e1 as an expression to
    obtain an array value (which is of pointer of type {i64, [0 x s]}* ).
    compile e2 as an expression to obtain an operand of type i64, generate code
    that uses getelementptr to compute the offset from the array value, which is
    a pointer to the "storage space associated with e1[e2]".

    On the other hand, compiling e1[e2] as an expression (to obtain the value of
    the array), we can simply compile e1[e2] as a left-hand-side and then do the
    load.  So cmp_exp and cmp_lhs are mutually recursive.  [[Actually, as I am
    writing this, I think it could make sense to factor the Oat grammar in this
    way, which would make things clearer, I may do that for next time around.]]


    Consider globals7.oat

    /--------------- globals7.oat ------------------
    global arr = int[] null;

    int foo() {
      var x = new int[3];
      arr = x;
      x[2] = 3;
      return arr[2];
    }
    /------------------------------------------------

    The translation (given by cmp_ty) of the type int[] is {i64, [0 x i64}* so
    the corresponding LLVM IR declaration will look like:

    @arr = global { i64, [0 x i64] }* null

    This means that the type of the LLVM IR identifier @arr is {i64, [0 x i64]}**
    which is consistent with the type of a locally-declared array variable.

    The local variable x would be allocated and initialized by (something like)
    the following code snippet.  Here %_x7 is the LLVM IR uid containing the
    pointer to the "storage space" for the Oat variable x.

    %_x7 = alloca { i64, [0 x i64] }*                              ;; (1)
    %_raw_array5 = call i64*  @oat_alloc_array(i64 3)              ;; (2)
    %_array6 = bitcast i64* %_raw_array5 to { i64, [0 x i64] }*    ;; (3)
    store { i64, [0 x i64]}* %_array6, { i64, [0 x i64] }** %_x7   ;; (4)

    (1) note that alloca uses cmp_ty (int[]) to find the type, so %_x7 has
        the same type as @arr

    (2) @oat_alloc_array allocates len+1 i64's

    (3) we have to bitcast the result of @oat_alloc_array so we can store it
         in %_x7

    (4) stores the resulting array value (itself a pointer) into %_x7

   The assignment arr = x; gets compiled to (something like):

   %_x8 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7     ;; (5)
   store {i64, [0 x i64] }* %_x8, { i64, [0 x i64] }** @arr       ;; (6)

   (5) load the array value (a pointer) that is stored in the address pointed
       to by %_x7

   (6) store the array value (a pointer) into @arr

   The assignment x[2] = 3; gets compiled to (something like):

   %_x9 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** %_x7      ;; (7)
   %_index_ptr11 = getelementptr { i64, [0 x  i64] },
                   { i64, [0 x i64] }* %_x9, i32 0, i32 1, i32 2   ;; (8)
   store i64 3, i64* %_index_ptr11                                 ;; (9)

   (7) as above, load the array value that is stored %_x7

   (8) calculate the offset from the array using GEP

   (9) store 3 into the array

   Finally, return arr[2]; gets compiled to (something like) the following.
   Note that the way arr is treated is identical to x.  (Once we set up the
   translation, there is no difference between Oat globals and locals, except
   how their storage space is initially allocated.)

   %_arr12 = load { i64, [0 x i64] }*, { i64, [0 x i64] }** @arr    ;; (10)
   %_index_ptr14 = getelementptr { i64, [0 x i64] },
                  { i64, [0 x i64] }* %_arr12, i32 0, i32 1, i32 2  ;; (11)
   %_index15 = load i64, i64* %_index_ptr14                         ;; (12)
   ret i64 %_index15

   (10) just like for %_x9, load the array value that is stored in @arr

   (11)  calculate the array index offset

   (12) load the array value at the index
*)

(* Global initialized arrays:

   There is another wrinkle: To compile global initialized arrays like in the
   globals4.oat, it is helpful to do a bitcast once at the global scope to
   convert the "precise type" required by the LLVM initializer to the actual
   translation type (which sets the array length to 0).  So for globals4.oat,
   the arr global would compile to (something like):

   @arr = global { i64, [0 x i64] }* bitcast
            ({ i64, [4 x i64] }* @_global_arr5 to { i64, [0 x i64] }* )
   @_global_arr5 = global { i64, [4 x i64] }
                   { i64 4, [4 x i64] [ i64 1, i64 2, i64 3, i64 4 ] }
*)

(* Some useful helper functions *)

(* Generate a fresh temporary identifier. Since OAT identifiers cannot begin
   with an underscore, these should not clash with any source variables *)
let gensym : string -> string =
  let c = ref 0 in
  fun (s : string) ->
    incr c;
    Printf.sprintf "_%s%d" s !c

(* Amount of space an Oat type takes when stored in the satck, in bytes.
   Note that since structured values are manipulated by reference, all
   Oat values take 8 bytes on the stack.
*)
let size_oat_ty (t : Ast.ty) = 8L

(* Generate code to allocate a zero-initialized array of source type TRef (RArray t) of the
   given size. Note "size" is an operand whose value can be computed at
   runtime *)
let oat_alloc_array (t : Ast.ty) (size : Ll.operand) : Ll.ty * operand * stream
    =
  let ans_id, arr_id = (gensym "array", gensym "raw_array") in
  let ans_ty = cmp_ty @@ TRef (RArray t) in
  let arr_ty = Ptr I64 in
  ( ans_ty,
    Id ans_id,
    lift
      [
        (arr_id, Call (arr_ty, Gid "oat_alloc_array", [ (I64, size) ]));
        (ans_id, Bitcast (arr_ty, Id arr_id, ans_ty));
      ] )

(* Compiles an expression exp in context c, outputting the Ll operand that will
   recieve the value of the expression, and the stream of instructions
   implementing the expression.

   Tips:
   - use the provided cmp_ty function!

   - string literals (CStr s) should be hoisted. You'll need to make sure
     either that the resulting gid has type (Ptr I8), or, if the gid has type
     [n x i8] (where n is the length of the string), convert the gid to a
     (Ptr I8), e.g., by using getelementptr.

   - use the provided "oat_alloc_array" function to implement literal arrays
     (CArr) and the (NewArr) expressions
*)

let insn_of_binop (b : binop) (t1 : ty) (rt : ty) (op1 : Ll.operand)
    (op2 : Ll.operand) : insn =
  let t1 = cmp_ty t1 in
  let t = cmp_ty rt in
  match b with
  | Add -> Binop (Add, t, op1, op2)
  | Sub -> Binop (Sub, t, op1, op2)
  | Mul -> Binop (Mul, t, op1, op2)
  | Eq -> Icmp (Eq, t1, op1, op2)
  | Neq -> Icmp (Ne, t1, op1, op2)
  | Lt -> Icmp (Slt, t1, op1, op2)
  | Lte -> Icmp (Sle, t1, op1, op2)
  | Gt -> Icmp (Sgt, t1, op1, op2)
  | Gte -> Icmp (Sge, t1, op1, op2)
  | And -> Binop (And, t, op1, op2)
  | Or -> Binop (Or, t, op1, op2)
  | IAnd -> Binop (And, t, op1, op2)
  | IOr -> Binop (Or, t, op1, op2)
  | Shl -> Binop (Shl, t, op1, op2)
  | Shr -> Binop (Lshr, t, op1, op2)
  | Sar -> Binop (Ashr, t, op1, op2)

let insn_of_unop (u : unop) (t : ty) (op : Ll.operand) : insn =
  let t = cmp_ty t in
  match u with
  | Neg -> Binop (Sub, t, Const 0L, op)
  | Lognot -> Binop (Xor, t, op, Const 1L)
  | Bitnot -> Binop (Xor, t, op, Const (-1L))

let rec cmp_exp (c : Ctxt.t) (exp : Ast.exp node) : Ll.ty * Ll.operand * stream
    =
  match exp.elt with
  | CNull t -> (cmp_rty t, Null, [])
  | CBool b -> (I1, Const (if b then 1L else 0L), [])
  | CInt i -> (I64, Const i, [])
  | CArr (t_el_arr, e_list) ->
      let t_arr, op_arr, str_arr =
        cmp_exp c
          (Ast.no_loc
             (NewArr
                (t_el_arr, Ast.no_loc (CInt (Int64.of_int (List.length e_list))))))
      in
      let str_alloc =
        List.concat
          (List.mapi
             (fun i e : stream ->
               let t_e, op_e, str_e = cmp_exp c e in
               let alloc_aux = gensym "al_aux" in
               let bit_aux = gensym "bit_aux" in
               str_e
               >@ [
                    I
                      ( alloc_aux,
                        Gep (t_arr, op_arr, [ Const (Int64.of_int (i+1)) ]) );
                  ]
               >@ [ I (bit_aux, Bitcast (t_arr, Id alloc_aux, Ptr t_e)) ]
               >@ [ I ("", Store (t_e, op_e, Id bit_aux)) ])
             e_list)
      in
      (t_arr, op_arr, str_arr >@ str_alloc)
  | NewArr (t, e) ->
      let t_e, op_e, str_e = cmp_exp c e in
      let t_array, op_arr, str_arr = oat_alloc_array t op_e in
      (t_array, op_arr, str_e >@ str_arr)
  | Id id -> (
      let t, op = Ctxt.lookup id c in
      let aux_var = gensym "aux" in
      match t with
      | Ptr t -> (t, Id aux_var, [ I (aux_var, Load (Ptr t, op)) ])
      | _ -> failwith "Id should be ptr")
  | Index (e1, e2) -> (
      let t1, op1, str1 = cmp_exp c e1 in
      let t2, op2, str2 = cmp_exp c (Ast.no_loc (Bop(Add, e2, Ast.no_loc (CInt 1L))))in
      let aux_var = gensym "gep_aux" in
      let index_aux = gensym "index_aux" in
      let index_res = gensym "index_res" in
      match t1 with
      | Ptr (Struct [ _; Array (_, t_arr) ]) ->
          ( t_arr,
            Id index_res,
            str1 >@ str2
            >@ [ I (aux_var, Bitcast (t1, op1, Ptr t_arr)) ]
            >@ [ I (index_aux, Gep (Ptr t_arr, Id aux_var, [ op2 ])) ]
            >@ [ I (index_res, Load (Ptr t_arr, Id index_aux)) ] )
      | _ -> failwith "just dont")
  | Call (e, exps) ->
      let f_id =
        match e.elt with Id id -> id | _ -> failwith "Cannot call this var"
      in
      let t, op = Ctxt.lookup_function f_id c in
      let t_ret =
        match t with Ptr (Fun (_, t)) -> t | _ -> failwith "Not a fun"
      in
      let f_args, str_alloc =
        List.fold_left
          (fun (args, str) e ->
            let t, op, str_e = cmp_exp c e in
            ([ (t, op) ] >@ args, str_e >@ str))
          ([], []) exps
      in
      let res = gensym "res" in
      (t_ret, Id res, str_alloc >@ [ I (res, Call (t_ret, op, f_args)) ])
  | Bop (b, e1, e2) ->
      let t1, op1, str1 = cmp_exp c e1 in
      let t2, op2, str2 = cmp_exp c e2 in
      let aux_var = gensym "aux" in
      let bop_t, _, bop_rt = typ_of_binop b in
      ( cmp_ty bop_rt,
        Id aux_var,
        str1 >@ str2 >@ [ I (aux_var, insn_of_binop b bop_t bop_rt op1 op2) ] )
  | Uop (uop, e) ->
      let t, op, str = cmp_exp c e in
      let aux_var = gensym "aux" in
      let _, uop_t = typ_of_unop uop in
      ( cmp_ty uop_t,
        Id aux_var,
        str >@ [ I (aux_var, insn_of_unop uop uop_t op) ] )
  | _ -> failwith "Not Implemented"

(* Compile a statement in context c with return typ rt. Return a new context,
   possibly extended with new local bindings, and the instruction stream
   implementing the statement.

   Left-hand-sides of assignment statements must either be OAT identifiers,
   or an index into some arbitrary expression of array type. Otherwise, the
   program is not well-formed and your compiler may throw an error.

   Tips:
   - for local variable declarau will need to emit Allocas in the
     entry block of the current function using the E() constructor.

   - don't forget to add a league of legenabindings to the context for local variable
     declarations

   - you can avoid some work by translating For loops to the corresponding
     While loop, building the AST and recursively calling cmp_stmt

   - you might find it helpful to reuse the code you wrote for the Call
     expression to implement the SCall statement

   - compiling the left-hand-side of an assignment is almost exactly like
     compiling the Id or Index expression. Instead of loading the resulting
     pointer, you just need to store to it!
*)

let rec cmp_stmt (c : Ctxt.t) (rt : Ll.ty) (stmt : Ast.stmt node) :
    Ctxt.t * stream =
  match stmt.elt with
  | Assn (exp1, exp2) -> (
      let t2, op_rhs, str_rhs = cmp_exp c exp2 in
      match exp1.elt with
      | Id id ->
          let t1, op1 = Ctxt.lookup id c in
          (c, str_rhs >@ [ I ("", Store (t2, op_rhs, op1)) ])
      | Index (e1, e2) ->
          let t1, op1, str1 = cmp_exp c e1 in
          let t2, op2, str2 = cmp_exp c (Ast.no_loc (Bop(Add, e2, Ast.no_loc (CInt 1L))))in
          let aux_var = gensym "gep_aux" in
          let index_aux = gensym "index_aux" in
          let t_arr =
            match t1 with
            | Ptr (Struct [ _; Array (_, t) ]) -> t
            | _ -> failwith "Not a pointer being indexed"
          in
          ( c,
            str_rhs >@ str1 >@ str2
            >@ [ I (aux_var, Gep (t1, op1, [ op2 ])) ]
            >@ [ I (index_aux, Bitcast (t1, Id aux_var, Ptr t_arr)) ]
            >@ [ I ("", Store (t2, op_rhs, Id index_aux)) ] )
      | _ -> failwith "Ill formed LHS")
  | Decl (id, exp) ->
      let t, op, str = cmp_exp c exp in
      let ll_id = gensym id in
      ( Ctxt.add c id (Ptr t, Id ll_id),
        str >@ [ E (ll_id, Alloca t) ] >@ [ I ("", Store (t, op, Id ll_id)) ] )
  | Ret exp -> (
      match exp with
      | None -> (c, [ T (Ret (rt, None)) ])
      | Some e ->
          let _, op, str = cmp_exp c e in
          (c, str >@ [ T (Ret (rt, Option.some op)) ]))
  | SCall (e, exps) ->
      let _, _, str = cmp_exp c (no_loc (Call (e, exps))) in
      (c, str)
  | If (e, st1, st2) ->
      let t, op, str = cmp_exp c e in
      let if_label = gensym "if" in
      let else_label = gensym "else" in
      let fi_label = gensym "fi" in
      let str = str >@ [ T (Cbr (op, if_label, else_label)) ] in
      let rec cmp_stmts c rt stmts =
        match stmts with
        | [] -> (c, [])
        | hd :: tl ->
            let c', s' = cmp_stmt c rt hd in
            let c'', s'' = cmp_stmts c' rt tl in
            (c'', s' >@ s'')
      in
      let c, str_st1 = cmp_stmts c rt st1 in
      let c, str_st2 = cmp_stmts c rt st2 in
      let str_st1_c = [ L if_label ] >@ str_st1 >@ [ T (Br fi_label) ] in
      let str_st2_c = [ L else_label ] >@ str_st2 >@ [ T (Br fi_label) ] in
      (c, str >@ str_st1_c >@ str_st2_c >@ [ L fi_label ])
  | For (v_list, e, st1, st2) ->
      let e = match e with Some e -> e | None -> Ast.no_loc (CInt 1L) in
      let rec cmp_vdecls c (v_list : vdecl list) =
        match v_list with
        | [] -> (c, [])
        | hd :: tl ->
            let c, str = cmp_stmt c rt (Ast.no_loc (Decl hd)) in
            let c', s' = cmp_vdecls c tl in
            (c', str >@ s')
      in
      let c, str_vdecls = cmp_vdecls c v_list in
      let body_stmt = match st1 with Some s -> [ s ] >@ st2 | None -> st2 in
      let c, str_loop = cmp_stmt c rt (Ast.no_loc (While (e, body_stmt))) in
      (c, str_vdecls >@ str_loop)
  | While (e, sts) ->
      let t, op, str = cmp_exp c e in
      let cond_label = gensym "cond" in
      let body_label = gensym "body" in
      let end_label = gensym "end" in
      let cond_str =
        [ L cond_label ] >@ str >@ [ T (Cbr (op, body_label, end_label)) ]
      in
      let rec cmp_stmts c rt stmts =
        match stmts with
        | [] -> (c, [])
        | hd :: tl ->
            let c', s' = cmp_stmt c rt hd in
            let c'', s'' = cmp_stmts c' rt tl in
            (c'', s' >@ s'')
      in
      let c, body_str = cmp_stmts c rt sts in
      let body_str = [ L body_label ] >@ body_str >@ [ T (Br cond_label) ] in
      (c, [ T (Br cond_label) ] >@ cond_str >@ body_str >@ [ L end_label ])

(* Compile a series of statements *)
and cmp_block (c : Ctxt.t) (rt : Ll.ty) (stmts : Ast.block) : Ctxt.t * stream =
  List.fold_left
    (fun (c, code) s ->
      let c, stmt_code = cmp_stmt c rt s in
      (c, code >@ stmt_code))
    (c, []) stmts

(* Adds each function identifer to the context at an
   appropriately translated type.

   NOTE: The Gid of a function is just its source name
*)
let cmp_function_ctxt (c : Ctxt.t) (p : Ast.prog) : Ctxt.t =
  List.fold_left
    (fun c -> function
      | Ast.Gfdecl { elt = { frtyp; fname; args } } ->
          let ft = TRef (RFun (List.map fst args, frtyp)) in
          Ctxt.add c fname (cmp_ty ft, Gid fname)
      | _ -> c)
    c p

(* Populate a context with bindings for global variables
   mapping OAT identifiers to LLVMlite gids and their types.

   Only a small subset of OAT expressions can be used as global initializers
   in well-formed programs. (The constructors starting with C).
*)
let cmp_global_ctxt (c : Ctxt.t) (p : Ast.prog) : Ctxt.t =
  List.fold_left
    (fun c -> function
      | Ast.Gvdecl { elt = { name; init }; _ } ->
          Ctxt.add c name
            (match init.elt with
            | CNull t -> (Ptr (cmp_rty t), Gid name)
            | CBool _ -> (Ptr I1, Gid name)
            | CInt _ -> (Ptr I64, Gid name)
            | CStr s -> (Ptr(Ptr (Array (1 + String.length s, I8))), Gid name)
            | CArr (t, e) ->
                (Ptr (Ptr (Struct [ I64; Array (List.length e, cmp_ty t) ])), Gid name)
            | _ -> failwith "Invalid global initializer")
      | _ -> c)
    c p

(* Compile a function declaration in global context c. Return the LLVMlite cfg
   and a list of global declarations containing the string literals appearing
   in the function.

   You will need to
   1. Allocate stack space for the function parameters using Alloca
   2. Store the function arguments in their corresponding alloca'd stack slot
   3. Extend the context with bindings for function variables
   4. Compile the body of the function using cmp_block
   5. Use cfg_of_stream to produce a LLVMlite cfg from
*)
let rec cmp_fdecl_args (c : Ctxt.t) (args : (ty * id) list) : Ctxt.t * stream =
  match args with
  | [] -> (c, [])
  | (t, id) :: tl ->
      let genid = gensym id in
      (* let _, ll_id = Ctxt.lookup id c in *)
      let alloca = E (genid, Alloca (cmp_ty t)) in
      let store = I ("", Store (cmp_ty t, Id id, Id genid)) in
      let c', str =
        cmp_fdecl_args (Ctxt.add c id (Ptr (cmp_ty t), Id genid)) tl
      in
      (c', [ alloca ] >@ [ store ] >@ str)

let cmp_fdecl (c : Ctxt.t) (f : Ast.fdecl node) :
    Ll.fdecl * (Ll.gid * Ll.gdecl) list =
  let f_rty = cmp_ret_ty f.elt.frtyp in
  let f_ty = List.map (fun (t, _) -> cmp_ty t) f.elt.args in
  let f_param = List.map (fun (_, id) -> id) f.elt.args in
  let f_ctxt, f_args_stream = cmp_fdecl_args c f.elt.args in
  let _, f_body_stream = cmp_block f_ctxt f_rty f.elt.body in
  let f_cfg, l_global = cfg_of_stream (f_args_stream >@ f_body_stream) in
  ({ f_ty = (f_ty, f_rty); f_param; f_cfg }, l_global)

(* Compile a global initializer, returning the resulting LLVMlite global
   declaration, and a list of additional global declarations.

   Tips:
   - Only CNull, CBool, CInt, CStr, and CArr can appear as global initializers
     in well-formed OAT programs. Your compiler may throw an error for the other
     cases

   - OAT arrays are always handled via pointers. A global array of arrays will
     be an array of pointers to arrays emitted as additional global declarations.
*)

let rec cmp_gexp (c : Ctxt.t) (e : Ast.exp node) :
    Ll.gdecl * (Ll.gid * Ll.gdecl) list =
  match e.elt with
  | CNull t -> ((Ptr (cmp_rty t), GNull), [])
  | CBool b -> ((I1, GInt (if b then 1L else 0L)), [])
  | CInt i -> ((I64, GInt i), [])
  | CStr s -> let str_aux = gensym "str_aux" in
    ((Ptr (Array (1 + String.length s, I8)), GGid str_aux), [str_aux ,(Array (1 + String.length s, I8), GString s)])
  | CArr (t, es) ->
      let arr_aux = gensym "arr_aux" in
      let arr_init = List.map (fun (e : exp node) -> fst (cmp_gexp c e)) es in
      let n = List.length arr_init in
      ( (Ptr (Struct [ I64; Array (n, cmp_ty t) ]), GGid arr_aux),
        [
          ( arr_aux,
            ( Struct [ I64; Array (n, cmp_ty t) ],
              GStruct
                [
                  (I64, GInt (Int64.of_int n));
                  (Array (n, cmp_ty t), GArray arr_init);
                ] ) );
        ] )
  | _ ->
      Astlib.print_exp e;
      failwith "Invalid global initializer"

(* Oat internals function context ------------------------------------------- *)
let internals = [ ("oat_alloc_array", Ll.Fun ([ I64 ], Ptr I64)) ]

(* Oat builtin function context --------------------------------------------- *)
let builtins =
  [
    ( "array_of_string",
      cmp_rty @@ RFun ([ TRef RString ], RetVal (TRef (RArray TInt))) );
    ( "string_of_array",
      cmp_rty @@ RFun ([ TRef (RArray TInt) ], RetVal (TRef RString)) );
    ("length_of_string", cmp_rty @@ RFun ([ TRef RString ], RetVal TInt));
    ("string_of_int", cmp_rty @@ RFun ([ TInt ], RetVal (TRef RString)));
    ( "string_cat",
      cmp_rty @@ RFun ([ TRef RString; TRef RString ], RetVal (TRef RString)) );
    ("print_string", cmp_rty @@ RFun ([ TRef RString ], RetVoid));
    ("print_int", cmp_rty @@ RFun ([ TInt ], RetVoid));
    ("print_bool", cmp_rty @@ RFun ([ TBool ], RetVoid));
  ]

(* Compile a OAT program to LLVMlite *)
let cmp_prog (p : Ast.prog) : Ll.prog =
  (* add built-in functions to context *)
  let init_ctxt =
    List.fold_left
      (fun c (i, t) -> Ctxt.add c i (Ll.Ptr t, Gid i))
      Ctxt.empty builtins
  in
  let fc = cmp_function_ctxt init_ctxt p in

  (* build global variable context *)
  let c = cmp_global_ctxt fc p in

  (* let () = List.iter (fun (id, _) -> print_endline id) c in *)

  (* compile functions and global variables *)
  let fdecls, gdecls =
    List.fold_right
      (fun d (fs, gs) ->
        match d with
        | Ast.Gvdecl { elt = gd } ->
            let ll_gd, gs' = cmp_gexp c gd.init in
            (fs, ((gd.name, ll_gd) :: gs') @ gs)
        | Ast.Gfdecl fd ->
            let fdecl, gs' = cmp_fdecl c fd in
            ((fd.elt.fname, fdecl) :: fs, gs' @ gs))
      p ([], [])
  in

  (* gather external declarations *)
  let edecls = internals @ builtins in
  { tdecls = []; gdecls; fdecls; edecls }
