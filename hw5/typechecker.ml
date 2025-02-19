open Ast
open Astlib
open Tctxt

(* Error Reporting ---------------------------------------------------------- *)
(* NOTE: Use type_error to report error messages for ill-typed programs. *)

exception TypeError of string

let type_error (l : 'a node) err =
  let _, (s, e), _ = l.loc in
  raise (TypeError (Printf.sprintf "[%d, %d] %s" s e err))

(* initial context: G0 ------------------------------------------------------ *)
(* The Oat types of the Oat built-in functions *)
let builtins =
  [
    ("array_of_string", ([ TRef RString ], RetVal (TRef (RArray TInt))));
    ("string_of_array", ([ TRef (RArray TInt) ], RetVal (TRef RString)));
    ("length_of_string", ([ TRef RString ], RetVal TInt));
    ("string_of_int", ([ TInt ], RetVal (TRef RString)));
    ("string_cat", ([ TRef RString; TRef RString ], RetVal (TRef RString)));
    ("print_string", ([ TRef RString ], RetVoid));
    ("print_int", ([ TInt ], RetVoid));
    ("print_bool", ([ TBool ], RetVoid));
  ]

(* binary operation types --------------------------------------------------- *)
let typ_of_binop : Ast.binop -> Ast.ty * Ast.ty * Ast.ty = function
  | Add | Mul | Sub | Shl | Shr | Sar | IAnd | IOr -> (TInt, TInt, TInt)
  | Lt | Lte | Gt | Gte -> (TInt, TInt, TBool)
  | And | Or -> (TBool, TBool, TBool)
  | Eq | Neq -> failwith "typ_of_binop called on polymorphic == or !="

(* unary operation types ---------------------------------------------------- *)
let typ_of_unop : Ast.unop -> Ast.ty * Ast.ty = function
  | Neg | Bitnot -> (TInt, TInt)
  | Lognot -> (TBool, TBool)

(* subtyping ---------------------------------------------------------------- *)
(* Decides whether H |- t1 <: t2
    - assumes that H contains the declarations of all the possible struct types

    - you will want to introduce addition (possibly mutually recursive)
      helper functions to implement the different judgments of the subtyping
      relation. We have included a template for subtype_ref to get you started.
      (Don't forget about OCaml's 'and' keyword.)
*)
let rec subtype (c : Tctxt.t) (t1 : Ast.ty) (t2 : Ast.ty) : bool =
  match t1 with
  | TInt -> if t2 = TInt then true else false
  | TBool -> if t2 = TBool then true else false
  | TRef rt1 -> (
      match t2 with
      | TRef rt2 -> subtype_ref c rt1 rt2
      | TNullRef rt2 -> subtype_ref c rt1 rt2
      | _ -> false)
  | TNullRef rt1 -> (
      match t2 with TNullRef rt2 -> subtype_ref c rt1 rt2 | _ -> false)

and subtype_ref_struct (c : Tctxt.t) (id1 : id) (id2 : id) : bool =
  let st1 = lookup_struct id1 c in
  let st2 = lookup_struct id2 c in
  let rec subfields_struct st1 st2 : bool =
    match (st1, st2) with
    | _, [] -> true
    | h1 :: t1, h2 :: t2 ->
        if h1.ftyp = h2.ftyp && h1.fieldName = h2.fieldName then
          subfields_struct t1 t2
        else false
    | _ -> false
  in
  subfields_struct st1 st2

and subtype_ref_func (c : Tctxt.t) (tyl1 : Ast.ty list) (ret1 : Ast.ret_ty)
    (tyl2 : Ast.ty list) (ret2 : Ast.ret_ty) : bool =
  if List.compare_lengths tyl1 tyl2 = 0 then
    if subtype_ret_ty c ret1 ret2 then
      List.for_all2 (fun t1 t2 -> subtype c t2 t1) tyl1 tyl2
    else false
  else false

(* Decides whether H |-r ref1 <: ref2 *)
and subtype_ref (c : Tctxt.t) (t1 : Ast.rty) (t2 : Ast.rty) : bool =
  match t1 with
  | RString -> if t2 = RString then true else false
  | RArray rt1 -> (
      match t2 with
      | RArray rt2 -> if rt1 = rt2 then true else false
      | _ -> false)
  | RStruct id1 -> (
      match t2 with RStruct id2 -> subtype_ref_struct c id1 id2 | _ -> false)
  | RFun (tyl1, ret1) -> (
      match t2 with
      | RFun (tyl2, ret2) -> subtype_ref_func c tyl1 ret1 tyl2 ret2
      | _ -> false)

and subtype_ret_ty (c : Tctxt.t) (t1 : Ast.ret_ty) (t2 : Ast.ret_ty) : bool =
  match t1 with
  | RetVoid -> if t2 = RetVoid then true else false
  | RetVal t1 -> ( match t2 with RetVal t2 -> subtype c t1 t2 | _ -> false)

(* well-formed types -------------------------------------------------------- *)
(* Implement a (set of) functions that check that types are well formed according
   to the H |- t and related inference rules

    - the function should succeed by returning () if the type is well-formed
      according to the rules

    - the function should fail using the "type_error" helper function if the
      type is not well-formed

    - l is just an ast node that provides source location information for
      generating error messages (it's only needed for the type_error generation)

    - tc contains the structure definition context
*)
let rec typecheck_ty (l : 'a Ast.node) (tc : Tctxt.t) (t : Ast.ty) : unit =
  match t with
  | TInt | TBool -> ()
  | TRef rt | TNullRef rt -> typecheck_rty l tc rt

and typecheck_rty (l : 'a Ast.node) (tc : Tctxt.t) (rt : Ast.rty) : unit =
  match rt with
  | RString -> ()
  | RStruct st -> typecheck_struct l tc st
  | RArray t -> typecheck_ty l tc t
  | RFun (arg_t, rt) ->
      typecheck_ret_ty l tc rt;
      List.iter (fun t -> typecheck_ty l tc t) arg_t

and typecheck_struct (l : 'a Ast.node) (tc : Tctxt.t) (st : Ast.id) : unit =
  let str = lookup_struct_option st tc in
  match str with
  | None -> type_error l "Typecheck Struct: Struct not found"
  | Some _ -> ()

(* and typecheck_fun (l : 'a Ast.node) (tc : Tctxt.t) (arg_t : Ast.ty list) : unit =
   List.iter (fun t -> typecheck_ty l tc t) arg_t *)

and typecheck_ret_ty (l : 'a Ast.node) (tc : Tctxt.t) (ret_ty : Ast.ret_ty) :
    unit =
  match ret_ty with RetVoid -> () | RetVal t -> typecheck_ty l tc t

(* typechecking expressions ------------------------------------------------- *)
(* Typechecks an expression in the typing context c, returns the type of the
   expression.  This function should implement the inference rules given in the
   oad.pdf specification.  There, they are written:

       H; G; L |- exp : t

   See tctxt.ml for the implementation of the context c, which represents the
   four typing contexts: H - for structure definitions G - for global
   identifiers L - for local identifiers

   Returns the (most precise) type for the expression, if it is type correct
   according to the inference rules.

   Uses the type_error function to indicate a (useful!) error message if the
   expression is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   Notes: - Structure values permit the programmer to write the fields in any
   order (compared with the structure definition).  This means that, given the
   declaration struct T { a:int; b:int; c:int } The expression new T {b=3; c=4;
   a=1} is well typed.  (You should sort the fields to compare them.)
*)

let rec typecheck_exp (c : Tctxt.t) (e : Ast.exp node) : Ast.ty =
  match e.elt with
  | CNull rt -> TNullRef rt
  | CBool _ -> TBool
  | CInt _ -> TInt
  | CStr _ -> TRef RString
  | Id id -> (
      let id_loc = lookup_local_option id c in
      match id_loc with
      | Some x -> x (*TODO*)
      | None -> (
          let id_g = lookup_global_option id c in
          match id_g with
          | Some x -> x (*TODO*)
          | None -> type_error e ("Exp: Id " ^ id ^ " not found")))
  | CArr (ty, exp_ns) ->
      typecheck_ty e c ty;
      List.iteri
        (fun i exp_node ->
          if subtype c (typecheck_exp c exp_node) ty then ()
          else
            type_error e
              ("Exp: Expression" ^ Int.to_string i ^ "does not match array type"))
        exp_ns;
      TRef (RArray ty)
  | NewArr (ty, exp1, id, exp2) ->
      typecheck_ty e c ty;
      let ty_exp1 = typecheck_exp c exp1 in
      if ty_exp1 <> TInt then type_error e "Exp: Size exp NewArr has to be int"
      else
        let c_arr = add_local c id TInt in
        if subtype c_arr (typecheck_exp c_arr exp2) ty then TRef (RArray ty)
        else type_error e "Exp: Bad NewArr exp2 type"
      (* let ty_exp2 = typecheck_exp c exp2 in
         if match exp1.elt with CInt _ -> true | _ -> false then
           let id_loc = lookup_local_option id c in
           if match id_loc with Some x -> false | _ -> true then TRef (RArray ty)
           else type_error e "Wrong Array" *)
      (*TODO*)
  | Index (exp1, exp2) -> (
      let ty1 = typecheck_exp c exp1 in
      let ty2 = typecheck_exp c exp2 in
      if ty2 <> TInt then type_error e "Exp: Index has to be int"
      else
        match ty1 with
        | TRef (RArray t) -> t
        | _ -> type_error e "Exp: Can only index arrays")
  | Length exp -> (
      let t_arr = typecheck_exp c exp in
      match t_arr with
      | TRef (RArray _) -> TInt
      | _ -> type_error e "Exp: Can't get Length from nonArray")
  | CStruct (id, l) ->
      let str = lookup_struct_option id c in
      (match str with
      | None -> type_error e "Exp: Struct not found"
      | Some str ->
          List.iteri
            (fun i f ->
              let exp1 =
                try Some (List.assoc f.fieldName l) with Not_found -> None
              in
              match exp1 with
              | None ->
                  type_error e
                    ("Exp: Struct field" ^ Int.to_string i ^ "not found")
              | Some exp1 ->
                  let t = typecheck_exp c exp1 in
                  if subtype c t f.ftyp then ()
                  else
                    type_error e
                      ("Exp: Struct field" ^ Int.to_string i ^ "has wrong type"))
            str;
          if List.length str <> List.length l then
            type_error e "Exp: Wrong number of fields for struct");
      TRef (RStruct id)
  | Proj (exp, id_field) -> (
      let ty = typecheck_exp c exp in
      match ty with
      | TRef (RStruct id) -> (
          let str = lookup_struct_option id c in
          match str with
          | None -> type_error e "Exp: Struct for project not found in context"
          | Some str -> (
              let seq_str = List.map (fun x -> (x.fieldName, x.ftyp)) str in
              let t =
                try Some (List.assoc id_field seq_str) with Not_found -> None
              in
              match t with
              | None -> type_error e "Exp: Field not found"
              | Some t -> t))
      | _ -> type_error e "Exp: Can only project structs")
  | Call (e1, es) -> (
      let ty1 = typecheck_exp c e1 in
      match ty1 with
      | TRef (RFun (tyl, ret)) -> (
          if List.length tyl <> List.length es then
            type_error e "Exp: Wrong number of arguments";
          List.iteri
            (fun i e ->
              let t = typecheck_exp c e in
              if subtype c t (List.nth tyl i) then ()
              else
                type_error e
                  ("Exp: Wrong type in call for argument" ^ Int.to_string i))
            es;
          match ret with
          | RetVoid -> type_error e "Exp: Has to return a value"
          | RetVal t -> t)
      | _ -> type_error e "Exp: Can only call functions")
  | Bop (op, exp1, exp2) -> (
      let ty1 = typecheck_exp c exp1 in
      let ty2 = typecheck_exp c exp2 in
      match op with
      | Eq | Neq ->
          if subtype c ty1 ty2 && subtype c ty2 ty1 then TBool
          else type_error e "Exp: Equal have to be same types"
      | _ ->
          let ty_binop1, ty_binop2, ty_binop3 = typ_of_binop op in
          if
            subtype c ty1 ty_binop1 && subtype c ty2 ty_binop2
            && subtype c ty_binop1 ty1 && subtype c ty_binop2 ty2
          then ty_binop3
          else type_error e "Exp: Wrong binop")
  | Uop (op, exp) ->
      let ty_unop1, ty_unop2 = typ_of_unop op in
      let ty = typecheck_exp c exp in
      if ty_unop1 = ty then ty else type_error e "Exp: Wrong uop"
(* statements --------------------------------------------------------------- *)

(* Typecheck a statement
   This function should implement the statement typechecking rules from oat.pdf.

   Inputs:
    - tc: the type context
    - s: the statement node
    - to_ret: the desired return type (from the function declaration)

   Returns:
     - the new type context (which includes newly declared variables in scope
       after this statement
     - A boolean indicating the return behavior of a statement:
        false:  might not return
        true: definitely returns

        in the branching statements, both branches must definitely return

        Intuitively: if one of the two branches of a conditional does not
        contain a return statement, then the entier conditional statement might
        not return.

        looping constructs never definitely return

   Uses the type_error function to indicate a (useful!) error message if the
   statement is not type correct.  The exact wording of the error message is
   not important, but the fact that the error is raised, is important.  (Our
   tests also do not check the location information associated with the error.)

   - You will probably find it convenient to add a helper function that implements the
     block typecheck rules.
*)

let typecheck_vdecl (tc : Tctxt.t) (vd : Ast.vdecl) : Tctxt.t =
  let id, e = vd in
  let t = typecheck_exp tc e in
  let loc = lookup_local_option id tc in
  match loc with
  | Some _ -> type_error e "Id already declared"
  | None -> add_local tc id t

let rec typecheck_block (tc : Tctxt.t) (blk : Ast.block) (to_ret : ret_ty) :
    bool =
  let rec block_aux tc stmts : bool =
    match stmts with
    | stm :: [] ->
        let _, b = typecheck_stmt tc stm to_ret in
        b
    | stm :: tl ->
        let ctxt, b = typecheck_stmt tc stm to_ret in
        if b then type_error stm "Block: Can't return before end of block"
        else block_aux ctxt tl
    | [] -> false
  in
  block_aux tc blk

and typecheck_stmt (tc : Tctxt.t) (s : Ast.stmt node) (to_ret : ret_ty) :
    Tctxt.t * bool =
  match s.elt with
  | Assn (exp1, exp2) -> (
      match exp1.elt with
      | Id id ->
          let loc = lookup_local_option id tc in
          let glob = lookup_global_option id tc in
          (match loc with
          | Some _ -> ()
          | None -> (
              match glob with
              | Some t -> (
                  match t with
                  | TRef (RFun _) ->
                      type_error s "Stmt: Can't assign to functions"
                  | _ -> ())
              | None -> type_error s "Stmt: Id not found"));
          let t1 = typecheck_exp tc exp1 in
          let t2 = typecheck_exp tc exp2 in
          if subtype tc t2 t1 then (tc, false)
          else type_error s "Stmt: Can't assign different types"
      | Proj (exp, field_id) -> (
          let ty = typecheck_exp tc exp in
          match ty with
          | TRef (RStruct str_id) -> (
              let str = lookup_struct_option str_id tc in
              match str with
              | None -> type_error s "Stmt: Struct not found for proj"
              | Some str -> (
                  let seq_str = List.map (fun x -> (x.fieldName, x.ftyp)) str in
                  let t =
                    try Some (List.assoc field_id seq_str)
                    with Not_found -> None
                  in
                  match t with
                  | None -> type_error s "Stmt: Field not found in proj"
                  | Some t ->
                      let t2 = typecheck_exp tc exp2 in
                      if subtype tc t2 t then (tc, false)
                      else type_error s "Stmt: Can't assign different types"))
          | _ -> type_error s "Stmt: Can only assign a field to structs")
      | Index (arr, index_e) -> (
          let ty = typecheck_exp tc arr in
          match ty with
          | TRef (RArray t) ->
              let t_index = typecheck_exp tc index_e in
              if not (subtype tc t_index TInt) then
                type_error s "Stmt: Only int can index array"
              else
                let t2 = typecheck_exp tc exp2 in
                if subtype tc t2 t then (tc, false)
                else
                  type_error s
                    "Stmt: Can't assign different types of array and exp"
          | _ -> type_error s "Stmt: Can only index arrays")
      | _ -> type_error s "Stmt: Can only assign to ids")
  | Decl (id, e) -> (typecheck_vdecl tc (id, e), false)
  | SCall (e1, es) -> (
      let t = typecheck_exp tc e1 in
      match t with
      | TRef (RFun (tyl, ret)) -> (
          List.iteri
            (fun i e ->
              let t = typecheck_exp tc e in
              if subtype tc t (List.nth tyl i) then ()
              else
                type_error s
                  ("Stmt: Wrong type in call for argument" ^ Int.to_string i))
            es;
          match ret with
          | RetVoid -> (tc, false)
          | RetVal _ -> type_error s "Stmt: Call must invoke void function")
      | _ -> type_error s "Stmt: Can only call functions")
  | If (exp, blk1, blk2) ->
      let t = typecheck_exp tc exp in
      if t = TBool then
        let b1 = typecheck_block tc blk1 to_ret in
        let b2 = typecheck_block tc blk2 to_ret in
        (tc, b1 && b2)
      else type_error s "Stmt: If condition must be bool"
  | Cast (rty, id, e, blk1, blk2) ->
      let t = typecheck_exp tc e in
      let rty' =
        match t with
        | TNullRef rt -> rt
        | _ -> type_error s "Stmt: Cast of non TNullRef"
      in
      if subtype_ref tc rty' rty then ()
      else type_error s "Stmt: Cannot cast the two types";
      let ctxt = add_local tc id (TRef rty) in
      let b1 = typecheck_block ctxt blk1 to_ret in
      let b2 = typecheck_block ctxt blk2 to_ret in
      (tc, b1 && b2)
  | While (exp, blk) ->
      let t = typecheck_exp tc exp in
      if t = TBool then
        let _ = typecheck_block tc blk to_ret in
        (tc, false)
      else type_error s "Stmt: While condition must be bool"
  | For (vdecls, exp, stmt, blk) ->
      let for_ctxt = List.fold_left typecheck_vdecl tc vdecls in
      let _ =
        match exp with
        | Some t ->
            if typecheck_exp for_ctxt t <> TBool then
              type_error s "Stmt: For condition must be bool"
            else ()
        | None -> ()
      and _ =
        match stmt with
        | Some t ->
            let _, b = typecheck_stmt for_ctxt t to_ret in
            if b then type_error s "Stmt: For stmt must not return" else ()
        | None -> ()
      and _ = typecheck_block for_ctxt blk to_ret in
      (tc, false)
  | Ret exp -> (
      match exp with
      | Some t ->
          let ty = typecheck_exp tc t in
          if subtype_ret_ty tc (RetVal ty) to_ret then (tc, true)
          else type_error s "Stmt: Return type doesn't match"
      | None ->
          if to_ret = RetVoid then (tc, true)
          else type_error s "Stmt: Returning void for non-void function")
(*TODO Check Cast case*)

(* struct type declarations ------------------------------------------------- *)
(* Here is an example of how to implement the TYP_TDECLOK rule, which is
   is needed elswhere in the type system.
*)

(* Helper function to look for duplicate field names *)
let rec check_dups fs =
  match fs with
  | [] -> false
  | h :: t -> List.exists (fun x -> x.fieldName = h.fieldName) t || check_dups t

let typecheck_tdecl (tc : Tctxt.t) id fs (l : 'a Ast.node) : unit =
  if check_dups fs then type_error l ("Repeated fields in " ^ id)
  else List.iter (fun f -> typecheck_ty l tc f.ftyp) fs

(* function declarations ---------------------------------------------------- *)
(* typecheck a function declaration
    - extends the local context with the types of the formal parameters to the
      function
    - typechecks the body of the function (passing in the expected return type
    - checks that the function actually returns
*)

let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  let updated_tc =
    List.fold_left (fun tc (typ, id) -> Tctxt.add_local tc id typ) tc f.args
  in
  if typecheck_block updated_tc f.body f.frtyp then ()
  else type_error l "No return in function block";
  typecheck_ret_ty l updated_tc f.frtyp

(*let rec fdecl_aux tc f l
  match f.args with
  | ((id,ty)::tl)-> fdecl_aux (add_local tc id ty) tl l
  | []-> tc *)
(* creating the typchecking context ----------------------------------------- *)

(* The following functions correspond to the
   judgments that create the global typechecking context.

   create_struct_ctxt: - adds all the struct types to the struct 'H'
   context (checking to see that there are no duplicate fields

     H |-s prog ==> H'


   create_function_ctxt: - adds the the function identifiers and their
   types to the 'G' context (ensuring that there are no redeclared
   function identifiers)

     H ; G1 |-f prog ==> G2


   create_global_ctxt: - typechecks the global initializers and adds
   their identifiers to the 'G' global context

     H ; G1 |-g prog ==> G2


   NOTE: global initializers may mention function identifiers as
   constants, but can't mention other global values *)
let add_builtins (tc : Tctxt.t) : Tctxt.t =
  let tc =
    add_global tc "string_of_array"
      (TRef (RFun ([ TRef (RArray TInt) ], RetVal (TRef RString))))
  in
  let tc =
    add_global tc "array_of_string"
      (TRef (RFun ([ TRef RString ], RetVal (TRef (RArray TInt)))))
  in
  let tc =
    add_global tc "print_string" (TRef (RFun ([ TRef RString ], RetVoid)))
  in
  let tc = add_global tc "print_int" (TRef (RFun ([ TInt ], RetVoid))) in
  let tc = add_global tc "print_bool" (TRef (RFun ([ TBool ], RetVoid))) in
  tc

let create_struct_ctxt (p : Ast.prog) : Tctxt.t =
  let rec struct_ctxt_aux p ctxt =
    match p with
    | dcl :: tl -> (
        match dcl with
        | Gtdecl g -> (
            let id, fields = g.elt in
            let str = lookup_struct_option id ctxt in
            match str with
            | Some _ -> type_error g "Struct already defined"
            | None ->
                let new_ctxt = add_struct ctxt id fields in
                typecheck_tdecl new_ctxt id fields g;
                struct_ctxt_aux tl new_ctxt)
        | _ -> struct_ctxt_aux tl ctxt)
    | [] -> ctxt
  in
  struct_ctxt_aux p { locals = []; globals = []; structs = [] }

let create_function_ctxt (tc : Tctxt.t) (p : Ast.prog) : Tctxt.t =
  let ctxt =
    List.fold_left
      (fun tc (id, (ty_l, fret)) -> add_global tc id (TRef (RFun (ty_l, fret))))
      tc builtins
  in
  let rec function_ctxt_aux c p =
    match p with
    | h :: tl -> (
        match h with
        | Gfdecl f -> (
            let fty =
              TRef (RFun (List.map (fun (t, _) -> t) f.elt.args, f.elt.frtyp))
            in
            match lookup_global_option f.elt.fname c with
            | Some _ -> type_error f "Function already defined"
            | None ->
                let new_ctxt = add_global c f.elt.fname fty in
                function_ctxt_aux new_ctxt tl)
        | _ -> function_ctxt_aux c tl)
    | [] -> c
  in
  function_ctxt_aux ctxt p

let create_global_ctxt (tc : Tctxt.t) (p : Ast.prog) : Tctxt.t =
  let rec global_aux const_ctxt ctxt p =
    match p with
    | h :: tl -> (
        match h with
        | Gvdecl d -> (
            let id = d.elt.name and init = d.elt.init in
            let ty = typecheck_exp const_ctxt init in
            match lookup_global_option id ctxt with
            | Some _ -> type_error d "Global already defined"
            | None ->
                let new_ctxt = add_global ctxt id ty in
                global_aux const_ctxt new_ctxt tl)
        | _ -> global_aux const_ctxt ctxt tl)
    | [] -> ctxt
  in
  global_aux tc tc p

(* This function implements the |- prog and the H ; G |- prog
   rules of the oat.pdf specification.
*)
let typecheck_program (p : Ast.prog) : unit =
  let sc = create_struct_ctxt p in
  let fc = create_function_ctxt sc p in
  let tc = create_global_ctxt fc p in
  (* print_endline "Globals:";
     List.iter (fun (id, _) -> print_endline id) tc.globals;
     print_endline "Locals:";
     List.iter (fun (id, _) -> print_endline id) tc.locals;
     print_endline "Structs:";
     List.iter (fun (id, _) -> print_endline id) tc.structs; *)
  List.iter
    (fun p ->
      match p with
      | Gfdecl ({ elt = f } as l) -> typecheck_fdecl tc f l
      | Gtdecl ({ elt = id, fs } as l) -> typecheck_tdecl tc id fs l
      | _ -> ())
    p
