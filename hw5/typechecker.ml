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
    | [], _ -> true
    | h1 :: t1, h2 :: t2 ->
        if h1.ftyp = h2.ftyp then subfields_struct t1 t2 else false
    | _ -> false
  in
  subfields_struct st1 st2

and subtype_ref_func (c : Tctxt.t) (tyl1 : Ast.ty list) (ret1 : Ast.ret_ty)
    (tyl2 : Ast.ty list) (ret2 : Ast.ret_ty) : bool =
  if (List.compare_lengths tyl1 tyl2) = 0 then
    if (subtype_ret_ty c ret1 ret2) then
      List.for_all2 (fun t1 t2 -> subtype c t1 t2) tyl1 tyl2
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
      | RFun (tyl2, ret2) ->
          subtype_ref_func c tyl1 ret1 tyl2 ret2
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
  | TRef rt -> typecheck_rty l tc rt 
  | TNullRef rt -> typecheck_rty l tc rt 
   

and typecheck_rty (l : 'a Ast.node) (tc: Tctxt.t) (rt : Ast.rty) : unit =
  match rt with
  |RString -> ()
  |RStruct st -> typecheck_struct l tc st  
  |RArray t -> typecheck_ty l tc t 
  |RFun (t,rt) -> if typecheck_ret_ty l tc rt then typecheck_fun l tc t else  type_error l ("wrong function type")

and typecheck_struct (l : 'a Ast.node) (tc: Tctxt.t) (st : Ast.id) : unit =
  let str = lookup_struct st tc in
  let rec typecheck_struct_aux l tc str =
    match str with 
    | (h::tl)-> begin match h.ftyp with
                |TInt |TBool -> typecheck_struct_aux l tc tl
                |TRef rt |TNullRef rt -> if (typecheck_rty l tc rt = ()) then typecheck_struct_aux l tc tl else type_error l ("struct failure")
  end
  |[]->()
in typecheck_struct_aux l tc str 

and typecheck_fun (l : 'a Ast.node) (tc: Tctxt.t) (tl: Ast.ty list) : unit =
  match tl with
  |(h::t) -> begin match h with 
            | TInt | TBool -> typecheck_fun l tc t 
            | TRef rt | TNullRef rt -> typecheck_rty l tc rt 
            end 
  |_-> ()

and typecheck_ret_ty (l : 'a Ast.node) (tc: Tctxt.t) (ret_ty: Ast.ret_ty) : bool =
  match ret_ty with
  | RetVoid -> true
  | RetVal t -> if typecheck_ty l tc t = () then true else false 
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
  | CBool b -> TBool 
  | CInt i -> TInt 
  | CStr x -> TRef RString 
  | Id id -> let id_loc = lookup_local_option id c in 
              begin match id_loc with
              | Some x -> x (*TODO*)
              | None -> let id_g = lookup_global_option id c in
                         begin match id_g with
                        | Some x -> x (*TODO*)
                        | None -> type_error e ("expression mismatch")
  end 
end 
  | CArr (ty,exp_ns)-> let _ = typecheck_ty e c ty in let _ = List.map (fun exp_node -> subtype c (typecheck_exp c exp_node) ty) exp_ns in TRef (RArray ty)
  | NewArr (ty,exp1,id,epx2) -> let _ = typecheck_ty e c ty in 
                            if (match exp1.elt with |CInt _-> true |_-> false) 
                            then let id_loc = lookup_local_option id c in if (match id_loc with |Some x -> false|_->true) then TRef (RArray ty) else type_error e ("Wrong Array")
                            else type_error e ("Wrong Array initialisation") (*TODO*)
  | Index (exp1,exp2)-> let ty1 =typecheck_exp c exp1 in let ty2 = typecheck_exp c exp2 in if (ty2 = TInt)then match ty1 with |TRef (RArray t) -> typecheck_exp c ({elt = CArr (t,[exp1;exp2]);loc = e.loc})|_-> type_error e ("wrong index") else type_error e ("Wrong indexing")
  | Length exp -> let t_arr= typecheck_exp c exp in begin match t_arr with |TRef (RArray t) -> TInt |_-> type_error e ("Can't get Length from nonArray") end
  | CStruct (id,(ids,exps)::tl) -> type_error e ("Cstruct not implemented")
  | Call (e1, es)-> type_error e ("CAll not implemented")
  | Bop (op,exp1,exp2)->let ty1 = typecheck_exp c exp1 in
                        let ty2 = typecheck_exp c exp2 in
                        begin match op with 
                        |Eq |Neq-> if (subtype c ty1 ty2 && subtype c ty2 ty1) then TBool else type_error e ("Equal have to be same types") 
                        |_-> let (ty_binop1,ty_binop2,ty_binop3)= typ_of_binop op in  
                        if (ty1=ty_binop1 && ty2=ty_binop2)then ty_binop3 else type_error e ("Wrong binop")
                          end
  | Uop (op,exp)-> let (ty_unop1,ty_unop2)=typ_of_unop op in 
                        let ty = typecheck_exp c exp in
                        if (ty_unop1=ty) then ty else type_error e ("Wrong uop")
  | _ -> failwith "Typ Carr and later not implemented"
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
let rec typecheck_stmt (tc : Tctxt.t) (s : Ast.stmt node) (to_ret : ret_ty) :
    Tctxt.t * bool =
  failwith "todo: implement typecheck_stmt"

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
let typecheck_block (tc : Tctxt.t) (f: Ast.block): unit =
  let rec block_aux tc stmt =
    match stmt with 
    |(h::tl)-> begin match h.elt with
              |Decl (id,exp_n)-> let _ = typecheck_exp tc exp_n in ()
              |_-> block_aux tc tl 
  end
    |[]-> ()
in block_aux tc f

let typecheck_fdecl (tc : Tctxt.t) (f : Ast.fdecl) (l : 'a Ast.node) : unit =
  let updated_tc = List.fold_left (fun tc (typ,id) -> Tctxt.add_local tc id typ) tc f.args in
  let _ = typecheck_block updated_tc f.body in 
  let _ = typecheck_ret_ty l updated_tc f.frtyp in
  ()
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
let convert_bnd c l = List.map (fun(id, exp_n)-> {fieldName = id; ftyp = (typecheck_exp c exp_n)}) l 


let rec global_add_aux (c:Tctxt.t)(args : (ty*id) list) : Tctxt.t =
  match args with 
  |((ty,id)::tl)-> global_add_aux (add_global c id ty) tl
  |[]-> c 


let create_struct_ctxt (p : Ast.prog) : Tctxt.t =
    let rec struct_ctxt_aux p ctxt=
      match p with
      |(h::tl)-> begin match h with
                | Gvdecl g -> begin match g.elt.init.elt with
                              | CStruct (id,bnd)-> struct_ctxt_aux tl (add_struct ctxt id (convert_bnd ctxt bnd)) (*TODO*)
                              |_-> struct_ctxt_aux tl ctxt
end
                |_-> struct_ctxt_aux tl ctxt
end 
      |[]-> ctxt
      in struct_ctxt_aux p {locals = []; globals = []; structs = [] }
let create_function_ctxt (tc : Tctxt.t) (p : Ast.prog) : Tctxt.t =
  let rec function_ctxt_aux c p =
    match p with 
    |(h::tl)-> begin match h with
              |Gfdecl f -> function_ctxt_aux (global_add_aux c f.elt.args) tl 
              |_-> function_ctxt_aux c tl
  end 
  |[]-> c 
in function_ctxt_aux tc p 

let rec global_ctxt_add (tc:Tctxt.t) (fl: field list) : Tctxt.t =
  match fl with
  |({fieldName = id;ftyp=ty}::tl)-> global_ctxt_add (add_global tc id ty) tl 
  |[]-> tc 

let create_global_ctxt (tc : Tctxt.t) (p : Ast.prog) : Tctxt.t =
  let rec global_aux tc p =
  match p with 
  |(h::tl)-> begin match h with
            |Gtdecl d -> begin match d.elt with
                        |(id,ts) -> global_aux (global_ctxt_add tc ts) tl
                        
  end
            |_->global_aux tc  tl
end
|[]-> tc 
in global_aux tc p 

(* This function implements the |- prog and the H ; G |- prog
   rules of the oat.pdf specification.
*)
let typecheck_program (p : Ast.prog) : unit =
  let sc = create_struct_ctxt p in
  let fc = create_function_ctxt sc p in
  let tc = create_global_ctxt fc p in
  List.iter
    (fun p ->
      match p with
      | Gfdecl ({ elt = f } as l) -> typecheck_fdecl tc f l
      | Gtdecl ({ elt = id, fs } as l) -> typecheck_tdecl tc id fs l
      | _ -> ())
    p
