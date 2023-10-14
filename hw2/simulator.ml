(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L (* lowest valid address *)
let mem_top = 0x410000L (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17 (* including Rip *)
let ins_size = 8L (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next seven bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte =
  | InsB0 of ins (* 1st byte of an instruction *)
  | InsFrag (* 2nd - 8th bytes of an instruction *)
  | Byte of char (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool; mutable fs : bool; mutable fz : bool }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags; regs : regs; mem : mem }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0
  | Rbx -> 1
  | Rcx -> 2
  | Rdx -> 3
  | Rsi -> 4
  | Rdi -> 5
  | Rbp -> 6
  | Rsp -> 7
  | R08 -> 8
  | R09 -> 9
  | R10 -> 10
  | R11 -> 11
  | R12 -> 12
  | R13 -> 13
  | R14 -> 14
  | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i : int64) : sbyte list =
  let open Char in
  let open Int64 in
  List.map
    (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
    [ 0; 8; 16; 24; 32; 40; 48; 56 ]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs : sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i =
    match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s : string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i] :: acc) (pred i)
  in
  loop [ Byte '\x00' ] @@ (String.length s - 1)

(* Serialize an instruction to sbytes *)
let sbytes_of_ins ((op, args) : ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) ->
        invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | _ -> ()
  in
  List.iter check args;
  [
    InsB0 (op, args);
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
    InsFrag;
  ]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"

(* It might be useful to toggle printing of intermediate states of your
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]
*)
let debug_simulator = ref false

(* Interpret a condition code with respect to the given flags. *)
let interp_cnd { fo; fs; fz } : cnd -> bool =
 fun x ->
  match x with
  | Eq -> fz
  | Neq -> not fz
  | Gt -> fo = fs && not fz
  | Ge -> fo = fs
  | Le -> fo <> fs || fz
  | Lt -> fo <> fs

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr : quad) : int option =
  if addr > mem_top || addr < mem_bot then None
  else
    let dif = Int64.sub addr mem_bot in
    Some (Int64.to_int dif)

let int_map_addr (addr : quad) : int =
  let a = map_addr addr in
  match a with Some x -> x | None -> raise X86lite_segfault

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)

let imm_to_quad (i : imm) : quad =
  match i with Lit a -> a | Lbl _ -> raise X86lite_segfault

let get_from_mem (m : mach) (addr : quad) : quad =
  let add = int_map_addr addr in
  let int64_sbytes =
    [
      m.mem.(add);
      m.mem.(add + 1);
      m.mem.(add + 2);
      m.mem.(add + 3);
      m.mem.(add + 4);
      m.mem.(add + 5);
      m.mem.(add + 6);
      m.mem.(add + 7);
    ]
  in
  int64_of_sbytes int64_sbytes

let store_in_mem (m : mach) (addr : quad) (v : quad) : unit =
  let add = int_map_addr addr in
  let sbytes = sbytes_of_int64 v in
  m.mem.(add) <- List.nth sbytes 0;
  m.mem.(add + 1) <- List.nth sbytes 1;
  m.mem.(add + 2) <- List.nth sbytes 2;
  m.mem.(add + 3) <- List.nth sbytes 3;
  m.mem.(add + 4) <- List.nth sbytes 4;
  m.mem.(add + 5) <- List.nth sbytes 5;
  m.mem.(add + 6) <- List.nth sbytes 6;
  m.mem.(add + 7) <- List.nth sbytes 7

let src_operand (m : mach) (op : operand) : quad =
  match op with
  | Imm im -> imm_to_quad im
  | Reg reg -> m.regs.(rind reg)
  | Ind1 im -> get_from_mem m (imm_to_quad im)
  | Ind2 reg -> get_from_mem m m.regs.(rind reg)
  | Ind3 (im, reg) ->
      get_from_mem m (Int64.add m.regs.(rind reg) (imm_to_quad im))

let dst_operand (m : mach) (op : operand) (v : quad) : unit =
  match op with
  | Imm _ -> failwith "Cannot store data in an immediate value"
  | Reg reg -> m.regs.(rind reg) <- v
  | Ind1 im -> store_in_mem m (imm_to_quad im) v
  | Ind2 reg -> store_in_mem m m.regs.(rind reg) v
  | Ind3 (im, reg) ->
      store_in_mem m (Int64.add m.regs.(rind reg) (imm_to_quad im)) v

open Int64_overflow
let get_op_1 (i : ins) : quad -> t =
  match i with
  | Incq, _ -> succ
  | Decq, _ -> pred
  | Negq, _ -> neg
  | _ -> failwith "Instruction is not equivalent to unary op"

let get_op_2 (i : ins) : quad -> quad -> t =
  match i with
  | Addq, _ -> add
  | Subq, _ -> sub
  | Imulq, _ -> mul
  | _ -> failwith "Instruction is not equivalent to binary op"

let get_log_op (i: ins) = 
  match i with
  | Shlq, _ -> Int64.shift_left
  | Shrq, _ -> Int64.shift_right_logical
  | Sarq, _ -> Int64.shift_right
  | _ -> failwith "Invalid instruction"

let set_flags (m: mach) (res: t) : unit = 
  m.flags.fo <- res.overflow;  
  m.flags.fz <- res.value = 0L;
  m.flags.fs <- Int64.shift_right_logical res.value 63 = 1L

let handle_outcome (m: mach) (res: t) (dst_op: operand) : unit =
    set_flags m res; dst_operand m dst_op res.value
  
let arith_ins (m : mach) (i : ins) : unit =
  match i with 
  | (Addq | Subq | Imulq), [ op1; op2 ] -> 
    handle_outcome m ((get_op_2 i) (src_operand m op1) (src_operand m op2)) op2 
  | (Negq | Incq | Decq), [op] -> 
    handle_outcome m ((get_op_1 i) (src_operand m op)) op
  | _ -> failwith "Non-arithmetic Operation" 

let logic_ins (m : mach) (i : ins) : unit = 
  match i with
  | Xorq, [op1; op2] -> 
    handle_outcome m 
    {value = Int64.logxor (src_operand m op1) (src_operand m op2); overflow = false} op2
  | Orq, [op1; op2] -> 
    handle_outcome m 
    {value = Int64.logor (src_operand m op1) (src_operand m op2); overflow = false} op2
  | Andq, [op1; op2] -> 
    handle_outcome m 
    {value = Int64.logand (src_operand m op1) (src_operand m op2); overflow = false} op2
  | Notq, [op] ->  
    (** Different handling not to set the flags here *)
    dst_operand m op (Int64.lognot (src_operand m op))
  | _ -> failwith "Non-logical Operation"

(** TODO: Have to fix the flags here *)
let bitop_ins (m : mach) (i : ins) : unit =
  match i with
  | (Sarq | Shrq | Shlq), [amt; dst] -> 
    let res = (get_log_op i) (src_operand m amt) (Int64.to_int (src_operand m dst)) in
    dst_operand m dst res
  | (Set cc), [dst] -> let res = (src_operand m dst) in
  if (interp_cnd m.flags cc) then
    (dst_operand m dst (Int64.logor res 1L))
  else
    (dst_operand m dst (Int64.logand res (Int64.lognot 1L)))
  | _ -> failwith "Non-bitwise operation" 

let push (m: mach) (src: operand) : unit = 
    m.regs.(rind Rsp) <- Int64.sub m.regs.(rind Rsp) 8L;
    store_in_mem m m.regs.(rind Rsp) (src_operand m src)

let pop (m: mach) (dst: operand) : unit = 
    dst_operand m dst (get_from_mem m m.regs.(rind Rsp));
    m.regs.(rind Rsp) <- Int64.add m.regs.(rind Rsp) 8L

let datam_ins (m : mach) (i : ins) : unit =
  match i with
  | Pushq, [ op ] -> push m op
  | Popq, [ op ] -> pop m op
  | Movq, [ op1; op2 ] -> dst_operand m op2 (src_operand m op1)
  | Incq, [ op1; op2 ] -> dst_operand m op2 (get_from_mem m (src_operand m op1))
  | _ -> failwith "Invalid data manipulation"

let cflow_ins (m : mach) (i : ins) : unit = 
match i with
  | Jmp, [src] -> m.regs.(rind Rip) <- src_operand m src
  | Callq, [src] -> (push m (Reg Rsp)); m.regs.(rind Rip) <- src_operand m src
  | Retq, [] -> pop m (Reg Rip)
  | J cc, [src] -> if interp_cnd m.flags cc then m.regs.(rind Rip) <- src_operand m src else ()
  | Cmpq, [src1; src2] -> let res = sub (src_operand m src1) (src_operand m src2) in set_flags m res
  | _ -> ()

let handle_instruction (m : mach) (i : ins) : unit =
  let rip = m.regs.(rind Rip) in
  match i with
  | (Addq | Subq | Imulq | Negq | Incq | Decq), _ -> arith_ins m i; m.regs.(rind Rip) <- Int64.add rip 1L
  | (Xorq | Orq | Andq | Notq), _ -> logic_ins m i; m.regs.(rind Rip) <- Int64.add rip 1L
  | (Shlq | Sarq | Shrq | Set _), _ -> bitop_ins m i; m.regs.(rind Rip) <- Int64.add rip 1L
  | (Leaq | Movq | Pushq | Popq), _ -> datam_ins m i; m.regs.(rind Rip) <- Int64.add rip 1L
  | (Jmp | Callq | Retq | J _ | Cmpq), _ -> cflow_ins m i

let step (m : mach) : unit =
  let rip = m.regs.(rind Rip) in
  let inst = m.mem.(int_map_addr rip) in
  match inst with
  | Byte _ | InsFrag -> m.regs.(rind Rip) <- Int64.add rip 1L
  | InsB0 i -> handle_instruction m i 

(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the
   machine halts. *)
let run (m : mach) : int64 =
  while m.regs.(rind Rip) <> exit_addr do
    step m
  done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = {
  entry : quad; (* address of the entry point *)
  text_pos : quad; (* starting address of the code *)
  data_pos : quad; (* starting address of the data *)
  text_seg : sbyte list (* contents of the text segment *);
  data_seg : sbyte list (* contents of the data segment *);
}

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
    - separate the text and data segments
    - compute the size of each segment
       Note: the size of an Asciz string section is (1 + the string length)
             due to the null terminator

    - resolve the labels to concrete addresses and 'patch' the instructions to
      replace Lbl values with the corresponding Imm values.

    - the text segment starts at the lowest address
    - the data segment starts after the text segment

   HINT: List.fold_left and List.fold_right are your friends.
*)
let assemble (p : prog) : exec = failwith "assemble unimplemented"

(* Convert an object file into an executable machine state.
     - allocate the mem array
     - set up the memory state by writing the symbolic bytes to the
       appropriate locations
     - create the inital register state
       - initialize rip to the entry point address
       - initializes rsp to the last word in memory
       - the other registers are initialized to 0
     - the condition code flags start as 'false'

   Hint: The Array.make, Array.blit, and Array.of_list library functions
   may be of use.
*)
let load { entry; text_pos; data_pos; text_seg; data_seg } : mach =
  failwith "load unimplemented"
