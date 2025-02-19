(** Alias Analysis *)

open Ll
open Datastructures

(* The lattice of abstract pointers ----------------------------------------- *)
module SymPtr =
  struct
    type t = MayAlias           (* uid names a pointer that may be aliased *)
           | Unique             (* uid is the unique name for a pointer *)
           | UndefAlias         (* uid is not in scope or not a pointer *)

    let compare : t -> t -> int = Pervasives.compare

    let to_string = function
      | MayAlias -> "MayAlias"
      | Unique -> "Unique"
      | UndefAlias -> "UndefAlias"

  end

(* The analysis computes, at each program point, which UIDs in scope are a unique name
   for a stack slot and which may have aliases *)
type fact = SymPtr.t UidM.t

(* flow function across Ll instructions ------------------------------------- *)
(* TASK: complete the flow function for alias analysis. 

   - After an alloca, the defined UID is the unique name for a stack slot
   - A pointer returned by a load, call, bitcast, or GEP may be aliased
   - A pointer passed as an argument to a call, bitcast, GEP, or store
     may be aliased
   - Other instructions do not define pointers

 *)
let may_alias (op:Ll.operand)(d:fact):fact=
begin match op with 
                    | Gid id -> UidM.update_or SymPtr.MayAlias (fun _-> SymPtr.MayAlias) id d  
                    | _ -> d 
end 


let insn_flow ((u,i):uid * insn) (d:fact) : fact =
  begin match i with
  |Alloca t -> UidM.update_or SymPtr.Unique (fun _-> SymPtr.Unique) u d 
  |Load (_,op) -> may_alias op d 
  |Call (t,op,(ops)) -> List.fold_left (fun d (t,op) -> may_alias op d) d ((t,op)::ops)
  |Bitcast (_,op,_)-> let new_d = UidM.update_or SymPtr.MayAlias (fun _ ->SymPtr.MayAlias) u d in 
    begin match op with 
        | Gid id |Id id -> UidM.update_or SymPtr.MayAlias (fun _-> SymPtr.MayAlias) id new_d  
        | _ -> new_d 
  end
  | Store (_,_,op)->  may_alias op d 
  | Gep (t,op,(ops)) -> let new_d = UidM.update_or SymPtr.MayAlias (fun _-> SymPtr.MayAlias) u d  in 
                        begin match t with
                        |Ptr _ -> begin match op with
                                        |Id id -> UidM.update_or SymPtr.MayAlias (fun _-> SymPtr.MayAlias) id new_d
                                        |_-> new_d
end 
                        |_-> new_d
end
  | _-> d 
end 
(* The flow function across terminators is trivial: they never change alias info *)
let terminator_flow t (d:fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact =
  struct
    type t = fact
    let forwards = true

    let insn_flow = insn_flow
    let terminator_flow = terminator_flow
    
    (* UndefAlias is logically the same as not having a mapping in the fact. To
       compare dataflow facts, we first remove all of these *)
    let normalize : fact -> fact = 
      UidM.filter (fun _ v -> v != SymPtr.UndefAlias)

    let compare (d:fact) (e:fact) : int = 
      UidM.compare SymPtr.compare (normalize d) (normalize e)

    let to_string : fact -> string =
      UidM.to_string (fun _ v -> SymPtr.to_string v)

    (* TASK: complete the "combine" operation for alias analysis.

       The alias analysis should take the join over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful.

       It may be useful to define a helper function that knows how to take the
       join of two SymPtr.t facts.
    *)
    let join (s1:SymPtr.t) (s2:SymPtr.t) : SymPtr.t =
      match s1 with
      |MayAlias -> s1
      |Unique -> begin match s2 with
                |MayAlias -> s2
                |Unique -> s2
                |UndefAlias-> MayAlias
    end
      |UndefAlias -> begin match s2 with
                |UndefAlias -> s1
                |_-> MayAlias
  end
    let combine (ds:fact list) : fact =
      let rec merge_list ds =
        match ds with 
        |[]-> UidM.empty
        |[d]->d
        |(d1::d2::tl)-> merge_list ((UidM.merge (fun str a b ->
          match (a, b) with
          | None, None -> None
          | Some x, None -> Some x
          | None, Some y -> Some y
          | Some x, Some y -> Some (join x y))d1 d2)::tl)
      in merge_list ds 
  end

(* instantiate the general framework ---------------------------------------- *)
module Graph = Cfg.AsGraph (Fact)
module Solver = Solver.Make (Fact) (Graph)

(* expose a top-level analysis operation ------------------------------------ *)
let analyze (g:Cfg.t) : Graph.t =
  (* the analysis starts with every node set to bottom (the map of every uid 
     in the function to UndefAlias *)
  let init l = UidM.empty in

  (* the flow into the entry node should indicate that any pointer parameter 
     to the function may be aliased *)
  let alias_in = 
    List.fold_right 
      (fun (u,t) -> match t with
                    | Ptr _ -> UidM.add u SymPtr.MayAlias
                    | _ -> fun m -> m) 
      g.Cfg.args UidM.empty 
  in
  let fg = Graph.of_cfg init alias_in g in
  Solver.solve fg

