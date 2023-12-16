open Ll
open Datastructures

(* The lattice of symbolic constants ---------------------------------------- *)
module SymConst =
  struct
    type t = NonConst           (* Uid may take on multiple values at runtime *)
           | Const of int64     (* Uid will always evaluate to const i64 or i1 *)
           | UndefConst         (* Uid is not defined at the point *)

    let compare s t =
      match (s, t) with
      | (Const i, Const j) -> Int64.compare i j
      | (NonConst, NonConst) | (UndefConst, UndefConst) -> 0
      | (NonConst, _) | (_, UndefConst) -> 1
      | (UndefConst, _) | (_, NonConst) -> -1

    let to_string : t -> string = function
      | NonConst -> "NonConst"
      | Const i -> Printf.sprintf "Const (%LdL)" i
      | UndefConst -> "UndefConst"

    
  end

(* The analysis computes, at each program point, which UIDs in scope will evaluate 
   to integer constants *)
type fact = SymConst.t UidM.t



(* flow function across Ll instructions ------------------------------------- *)
(* - Uid of a binop or icmp with const arguments is constant-out
   - Uid of a binop or icmp with an UndefConst argument is UndefConst-out
   - Uid of a binop or icmp with an NonConst argument is NonConst-out
   - Uid of stores and void calls are UndefConst-out
   - Uid of all other instructions are NonConst-out
 *)
 (* let print_cnd (c:cnd) : string = 
  match c with
  | Eq -> "eq"
| Ne -> "Ne"
| Slt->"slt"
| Sle->"sle"
| Sgt->"sgt"
| Sge->"sge" *)

 let cnd_const (c1:int64)(c2:int64)(cnd:Ll.cnd)(u:uid)(d:fact)= 
 let cmp_res = (Int64.of_int(Int64.compare c1 c2)) in
 let cmp_bool = (((Int64.compare cmp_res 0L)==0)) in 
 begin match cnd with
 |Ne -> UidM.update_or (SymConst.Const (if cmp_bool then 0L else 1L)) (fun _ -> SymConst.Const (if cmp_bool then 0L else 1L)) u d
 |Eq -> UidM.update_or (SymConst.Const (if cmp_bool then 1L else 0L)) (fun _ -> SymConst.Const (if cmp_bool then 1L else 0L)) u d
 |Slt -> UidM.update_or (SymConst.Const (if ((Int64.compare cmp_res 0L)== -1) then 1L else 0L)) (fun _ -> SymConst.Const (if ((Int64.compare cmp_res 0L)== -1) then 1L else 0L)) u d
 |Sle -> UidM.update_or (SymConst.Const (if ((Int64.compare cmp_res 0L)== 1) then 0L else 1L)) (fun _ -> SymConst.Const (if ((Int64.compare cmp_res 0L)== 1) then 0L else 1L)) u d
 |Sgt ->UidM.update_or (SymConst.Const (if ((Int64.compare cmp_res 0L)== 1) then 1L else 0L)) (fun _ -> SymConst.Const (if ((Int64.compare cmp_res 0L)== 1) then 1L else 0L)) u d
 |Sge ->UidM.update_or (SymConst.Const (if ((Int64.compare cmp_res 0L)== -1) then 0L else 1L)) (fun _ -> SymConst.Const (if ((Int64.compare cmp_res 0L)== -1) then 0L else 1L)) u d
end

 let binop_const (c1 : int64) (c2 : int64) (bop : Ll.bop) (u : uid) (d : fact) : fact =
  match bop with
  | Add -> UidM.update_or (SymConst.Const (Int64.add c1 c2)) (fun _ -> SymConst.Const (Int64.add c1 c2)) u d
  | Sub -> UidM.update_or (SymConst.Const (Int64.sub c1 c2)) (fun _ -> SymConst.Const (Int64.sub c1 c2)) u d
  | Mul -> UidM.update_or (SymConst.Const (Int64.mul c1 c2)) (fun _ -> SymConst.Const (Int64.mul c1 c2)) u d
  | Shl -> UidM.update_or (SymConst.Const (Int64.shift_left c1 (Int64.to_int c2))) (fun _ -> SymConst.Const(Int64.shift_left c1 (Int64.to_int c2))) u d
  | Lshr -> UidM.update_or (SymConst.Const (Int64.shift_right_logical c1 (Int64.to_int c2))) (fun _ -> SymConst.Const(Int64.shift_right_logical c1 (Int64.to_int c2))) u d
  | Ashr -> UidM.update_or (SymConst.Const (Int64.shift_right c1 (Int64.to_int c2))) (fun _ -> SymConst.Const(Int64.shift_right c1 (Int64.to_int c2))) u d
  | And -> UidM.update_or (SymConst.Const (Int64.logand c1 c2)) (fun _ -> SymConst.Const(Int64.logand c1 c2)) u d
  | Or -> UidM.update_or (SymConst.Const (Int64.logor c1 c2)) (fun _ -> SymConst.Const(Int64.logor c1 c2)) u d
  | Xor -> UidM.update_or (SymConst.Const (Int64.logxor c1 c2)) (fun _ -> SymConst.Const(Int64.logxor c1 c2)) u d

let insn_flow (u,i:uid * insn) (d:fact) : fact =
  begin match i with
  |Binop (bop,t,op1,op2) -> begin match op1, op2 with 
        |Const c1, Const c2 -> binop_const c1 c2 bop u d 
        |Const c1, Gid id |Const c1, Id id ->  begin match (UidM.find_or (SymConst.UndefConst) d id)  with
                  |Const c2 ->binop_const c1 c2 bop u d
                  |NonConst -> UidM.update_or (SymConst.NonConst) (fun _-> SymConst.NonConst) u d
                  |UndefConst -> UidM.update_or (SymConst.UndefConst) (fun _-> SymConst.UndefConst) u d  
         end
        |Gid id, Const c2 |Id id, Const c2 -> begin match (UidM.find_or (SymConst.UndefConst) d id) with
                  |Const c1 -> binop_const c1 c2 bop u d
                  |NonConst -> UidM.update_or (SymConst.NonConst) (fun _-> SymConst.NonConst) u d
                  |UndefConst -> UidM.update_or (SymConst.UndefConst) (fun _-> SymConst.UndefConst) u d  
        end
        |Gid i1, Gid i2 |Gid i1, Id i2 | Id i1, Gid i2 |Id i1, Id i2->begin  match (UidM.find_or (SymConst.UndefConst) d i1, UidM.find_or (SymConst.UndefConst) d i2 ) with 
                  |Const c1, Const c2 -> binop_const c1 c2 bop u d
                  |_->UidM.update_or (SymConst.NonConst) (fun _-> SymConst.NonConst) u d
  end 
  |_-> d
end
| Icmp (cnd,_, o1, o2) -> (match o1, o2 with 
    |Const c1, Const c2 ->  cnd_const c1 c2 cnd u d
    |Gid id, Const c2 |Id id, Const c2 -> begin match (UidM.find_or (SymConst.UndefConst) d id) with
          |Const c1 ->  cnd_const c1 c2 cnd u d 
          |_-> UidM.update_or (SymConst.UndefConst) (fun _-> SymConst.NonConst) u d
end
    |Const c1, Gid id |Const c1, Id id  -> begin match (UidM.find_or (SymConst.UndefConst) d id) with
          |Const c2 ->  cnd_const c1 c2 cnd u d
          | _-> UidM.update_or (SymConst.UndefConst) (fun _-> SymConst.NonConst) u d
end
    | Gid i1, Gid i2 |Id i1, Gid i2 | Gid i1, Id i2 |Id i1, Id i2->  UidM.update_or (SymConst.UndefConst) (fun _-> SymConst.NonConst) u d
   |_-> d )
| Store (_,o1,o2)-> d(* UidM.update_or (SymConst.UndefConst) (fun _-> SymConst.UndefConst) u d *)
| _ -> UidM.update_or (SymConst.NonConst) (fun _-> SymConst.NonConst) u d
end 

(* The flow function across terminators is trivial: they never change const info *)
let terminator_flow (t:terminator) (d:fact) : fact = d

(* module for instantiating the generic framework --------------------------- *)
module Fact =
  struct
    type t = fact
    let forwards = true

    let insn_flow = insn_flow
    let terminator_flow = terminator_flow
    
    let normalize : fact -> fact = 
      UidM.filter (fun _ v -> v != SymConst.UndefConst)

    let compare (d:fact) (e:fact) : int  = 
      UidM.compare SymConst.compare (normalize d) (normalize e)

    let to_string : fact -> string =
      UidM.to_string (fun _ v -> SymConst.to_string v)

    (* The constprop analysis should take the meet over predecessors to compute the
       flow into a node. You may find the UidM.merge function useful *)
       let join (s1:SymConst.t) (s2:SymConst.t) : SymConst.t =
        match s1 with
        |Const c1 -> begin match s2 with
                  |Const c2 -> if (c1==c2) then SymConst.Const c1 else SymConst.UndefConst
                  |NonConst -> SymConst.UndefConst
                  |UndefConst-> SymConst.UndefConst
       end
        |UndefConst -> SymConst.UndefConst
      
        |NonConst -> begin match s2 with
                  |UndefConst -> s2
                  |Const _-> SymConst.UndefConst
                  |NonConst -> s2
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
     in the function to UndefConst *)
  let init l = UidM.empty in

  (* the flow into the entry node should indicate that any parameter to the
     function is not a constant *)
  let cp_in = List.fold_right 
    (fun (u,_) -> UidM.add u SymConst.NonConst)
    g.Cfg.args UidM.empty 
  in
  let fg = Graph.of_cfg init cp_in g in
  Solver.solve fg


(* run constant propagation on a cfg given analysis results ----------------- *)
(* HINT: your cp_block implementation will probably rely on several helper 
   functions.                                                                 *)
let run (cg:Graph.t) (cfg:Cfg.t) : Cfg.t =
  let open SymConst in
  

  let cp_block (l:Ll.lbl) (cfg:Cfg.t) : Cfg.t =
    let b = Cfg.block cfg l in
    let cb = Graph.uid_out cg l in
    failwith "Constprop.cp_block unimplemented"
  in

  LblS.fold cp_block (Cfg.nodes cfg) cfg
