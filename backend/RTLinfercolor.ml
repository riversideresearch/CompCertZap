open AST
open BinNums
open Datatypes
open Maps
open Op
open Registers
open RTL
open RTLcolor

(* Union-find version, with liveness bounded quantification and sparse
   colorings (hash tables).

   At a high level, the algorithm builds a set of equality constraints
   between register colors at RTL program points, together with explicit
   constraints to the distinguished colors Red/Green/Blue/White/Pink.

   The state is represented as an array indexed by RTL node number.  Each
   array slot stores a hash table from registers mentioned at that node to
   union-find classes.  Processing an instruction unions together the
   classes forced equal by the coloring discipline for that instruction,
   while liveness limits which unrelated registers must keep the same
   color across control-flow edges.

   Once all constraints have been accumulated, each queried (node, reg)
   pair is mapped to the color represented by its union-find class, with
   Red used as the default for unconstrained pairs.

   This representation is efficient, but it assumes the RTL node numbers
   are dense enough to index the per-node arrays directly. *)

(* This file provides an implementation of the color inference oracle
   declared in Colorcheck.v with the following type: *)
(* Parameter infer_coloring : function -> option (node -> PTree.t color). *)

exception ColorError of string

let rec int_of_positive = function
  | Coq_xI p -> 2 * int_of_positive p + 1
  | Coq_xO p -> 2 * int_of_positive p
  | Coq_xH -> 1

let positive_of_int (i : int) : positive =
  if i < 1 then
    raise (ColorError ("positive_of_int: int must be positive, got "
                       ^ string_of_int i))
  else
    let rec go (j : int) : positive =
      if j == 1 then
        Coq_xH
      else if j mod 2 == 0 then
        Coq_xO (go @@ j / 2)
      else
        Coq_xI (go @@ j / 2)
    in go i

let convert_positive (p : positive) : int = int_of_positive p - 1

let convert_int (i : int) : positive = positive_of_int (i + 1)

let string_of_positive p = string_of_int @@ int_of_positive p

(** Union-find implementation literally copy/pasted from Google AI *)

type uf_node = {
    mutable parent : uf_node;
    mutable rank : int;
  }

(* Creates a new disjoint set for a given value *)
let make () =
  let rec node = { parent = node; rank = 0 } in
  node

(* Finds the representative (root) of the set containing a given node,
   with path compression *)
let rec find node =
  if node.parent == node then
    node
  else begin
      node.parent <- find node.parent; (* Path compression *)
      node.parent
    end

(* Unions two sets by rank *)
let union node1 node2 =
  let root1 = find node1 in
  let root2 = find node2 in
  if root1 != root2 then begin
      if root1.rank < root2.rank then
        root1.parent <- root2
      else if root1.rank > root2.rank then
        root2.parent <- root1
      else begin
          root2.parent <- root1;
          root1.rank <- root1.rank + 1
        end
    end

(** End copy/pasted union-find *)

let eq node1 node2 = find node1 == find node2

let red = make ()
let green = make ()
let blue = make ()
let white = make ()
let pink = make ()

let string_of_uf_node n =
  if eq n red then "R"
  else if eq n green then "G"
  else if eq n blue then "B"
  else if eq n white then "W"
  else if eq n pink then "P"
  else "X"

(* Same as RTL.instruction but with machine integers instead of
   positives. *)
type instruction' =
  | Inop' of int
  | Iop' of operation * int list * int * int
  | Iload' of memory_chunk * addressing * int list * int * int
  | Istore' of memory_chunk * addressing * int list * int * int
  | Icall' of signature * (int, ident) sum * int list * int * int
  | Itailcall' of signature * (int, ident) sum * int list
  | Ibuiltin' of external_function * int builtin_arg list * int builtin_res
                 * int
  | Icond' of condition * int list * int * int
  | Ijumptable' of int * int list
  | Ireturn' of int option

let convert_instr : instruction -> instruction' = function
  | Inop succ -> Inop' (convert_positive succ)
  | Iop (op, args, res, succ) ->
     Iop' (op, List.map convert_positive args, convert_positive res,
           convert_positive succ)
  | Iload (chunk, addr, args, res, succ) ->
     Iload' (chunk, addr, List.map convert_positive args,
             convert_positive res, convert_positive succ)
  | Istore (chunk, addr, args, src, succ) ->
     Istore' (chunk, addr, List.map convert_positive args,
              convert_positive src, convert_positive succ)
  | Icall (sg, fn, args, res, succ) ->
     Icall' (sg, (match fn with
                  | Coq_inl r -> Coq_inl (convert_positive r)
                  | Coq_inr nm -> Coq_inr nm), List.map convert_positive args,
             convert_positive res, convert_positive succ)
  | Itailcall (sg, fn, args) ->
     Itailcall' (sg, (match fn with
                      | Coq_inl r -> Coq_inl (convert_positive r)
                      | Coq_inr nm -> Coq_inr nm), List.map convert_positive args)
  | Ibuiltin (ef, bargs, bres, succ) ->
     Ibuiltin' (ef, List.map (map_builtin_arg convert_positive) bargs,
                map_builtin_res convert_positive bres, convert_positive succ)
  | Icond (cond, args, ifso, ifnot) ->
     Icond' (cond, List.map convert_positive args,
             convert_positive ifso, convert_positive ifnot)
  | Ijumptable (arg, succs) ->
     Ijumptable' (convert_positive arg, List.map convert_positive succs)
  | Ireturn ro -> Ireturn' (match ro with
                            | Some r -> Some (convert_positive r)
                            | None -> None)

let rec regs_of_builtin_res = function
  | BR r -> [r]
  | BR_none -> []
  | BR_splitlong (hi, lo) ->
     app (regs_of_builtin_res hi) (regs_of_builtin_res lo)

let rec regs_of_builtin_arg = function
  | BA r -> r :: []
  | BA_splitlong (hi, lo) ->
     app (regs_of_builtin_arg hi) (regs_of_builtin_arg lo)
  | BA_addptr (a1, a2) -> app (regs_of_builtin_arg a1) (regs_of_builtin_arg a2)
  | _ -> []

let regs_of_function (f : coq_function) : Regset.t =
  List.fold_left (fun acc param -> Regset.add param acc)
    (PTree.fold (fun acc _ instr -> Regset.union acc @@ instr_regs instr)
       f.fn_code Regset.empty) f.fn_params

(* Per-node coloring state. We use one hash table per RTL node,
   mapping registers mentioned at that node to union-find classes. *)
let init_cols (f : coq_function) : (int, uf_node) Hashtbl.t Array.t =
  let num_instrs = List.length (PTree.elements f.fn_code) in
  Array.init num_instrs (fun _ -> Hashtbl.create 100)

let print_col (col : (int, uf_node) Hashtbl.t) : unit =
  Hashtbl.iter (fun r c ->
      print_string @@ "x" ^ string_of_int r ^ "=" ^ string_of_uf_node c ^ ", "
    ) col;
  print_newline ()

let print_cols (f : coq_function) (cols : (int, uf_node) Hashtbl.t Array.t) : unit =
  Array.iteri (fun n col ->
      print_string @@ string_of_int n ^ ": ";
      print_col col
    ) cols

(* Lazily allocate a color class for a register at one node the first
   time some constraint mentions it. *)
let get (col : (int, uf_node) Hashtbl.t) (r : int) : uf_node =
  match Hashtbl.find_opt col r with
  | Some n -> n
  | None -> let n = make () in Hashtbl.add col r n; n

(* Generate all equality/color constraints induced by one instruction.
   [live] is the live-out set for [pc], so registers not mentioned by
   the instruction itself are only related across successors when
   liveness requires it. *)
let instr_constraints
      (cols : (int, uf_node) Hashtbl.t Array.t)
      (live : int list)
      (pc : int) (instr : instruction')
    : unit =
  let col = Array.get cols pc in
  match instr with
  | Inop' succ ->
     let succ_col = Array.get cols succ in
     List.iter (fun r ->
         union (get col r) (get succ_col r)
       ) live
  | Iop' (op, args, res, succ) ->
     let succ_col = Array.get cols succ in
     if is_protectedb op then begin
         List.iter (fun arg -> union (get col arg) white) args;
         union (get succ_col res) white;
         List.iter (fun r ->
             if not (r = res || List.mem r args) then
               union (get col r) (get succ_col r)
           ) live;
       end
     else begin
         let res_color = get succ_col res in
         List.iter (fun arg -> union (get col arg) res_color) args;
         List.iter (fun r ->
             if r <> res then
               union (get col r) (get succ_col r)
           ) live
       end
  | Iload' (_, _, args, res, succ) ->
     let succ_col = Array.get cols succ in
     List.iter (fun arg -> union (get col arg) white) args;
     union (get succ_col res) white;
     List.iter (fun r ->
         if not (r = res || List.mem r args) then
           union (get col r) (get succ_col r)
       ) live
  | Istore' (_, _, args, src, succ) ->
     let succ_col = Array.get cols succ in
     union (get col src) white;
     List.iter (fun arg -> union (get col arg) white) args;
     List.iter (fun r ->
         if not (r = src || List.mem r args) then
           union (get col r) (get succ_col r)
       ) live
  | Icall' (_, fn, args, res, succ) ->
     let succ_col = Array.get cols succ in
     List.iter (fun arg -> union (get col arg) white) args;
     union (get succ_col res) white;
     (match fn with
      | Coq_inl r -> union (get col r) white
      | Coq_inr _ -> ());
     List.iter (fun r ->
         if not (r = res || List.mem r args ||
                   match fn with
                   | Coq_inl r' -> r = r'
                   | Coq_inr _ -> false) then
           union (get col r) (get succ_col r)
       ) live
  | Itailcall' (_, fn, args) ->
     List.iter (fun arg -> union (get col arg) white) args;
     (match fn with
      | Coq_inl r -> union (get col r) white
      | Coq_inr _ -> ())
  | Ibuiltin' (ef, bargs, bres, succ) ->
     let succ_col = Array.get cols succ in
     if is_green_smove_builtinb ef then
       match bargs, bres with
       | [BA arg], BR res ->
          union (get col arg) white;
          union (get succ_col arg) pink;
          union (get succ_col res) green;
          List.iter (fun r ->
              if not (r = arg || r = res) then
                union (get col r) (get succ_col r)
            ) live
       | _ -> ()
     else if is_blue_smove_builtinb ef then
       match bargs, bres with
       | [BA arg], BR res ->
          union (get col arg) pink;
          union (get succ_col arg) red;
          union (get succ_col res) blue;
          List.iter (fun r ->
              if not (r = arg || r = res) then
                union (get col r) (get succ_col r)
            ) live
       | _ -> ()
     else if is_vote_builtinb ef then
       match bargs, bres with
       | [BA arg1; BA arg2; BA arg3], BR res ->
          union (get col arg1) red;
          union (get col arg2) green;
          union (get col arg3) blue;
          union (get succ_col res) white;
          List.iter (fun r ->
              if r <> res then
                union (get col r) (get succ_col r)
            ) live
       | _ -> ()
     else
       let arg_regs = List.concat_map regs_of_builtin_arg bargs in
       let res_regs = regs_of_builtin_res bres in
       List.iter (fun arg ->
           union (get col arg) white
         ) arg_regs;
       List.iter (fun res ->
           union (get succ_col res) white
         ) res_regs;
       List.iter (fun r ->
           if not (List.mem r arg_regs || List.mem r res_regs) then
             union (get col r) (get succ_col r)
         ) live
  | Icond' (_, args, ifso, ifnot) ->
     let ifso_col = Array.get cols ifso in
     let ifnot_col = Array.get cols ifnot in
     List.iter (fun arg -> union (get col arg) white) args;
     List.iter (fun r ->
         if not (List.mem r args) then begin
             union (get col r) (get ifso_col r);
             union (get col r) (get ifnot_col r)
           end
       ) live
  | Ijumptable' (arg, succs) ->
     union (get col arg) white;
     List.iter (fun r ->
         if r <> arg then
           List.iter (fun succ ->
               let succ_col = Array.get cols succ in
               union (get col r) (get succ_col r)
             ) succs
       ) live
  | Ireturn' ro ->
     match ro with
     | Some r -> union (get col r) white
     | None -> ()

(* Seed the entrypoint parameter colors, then accumulate constraints
   for every instruction in the function. *)
let function_constraints
      (f : coq_function)
      (live : int list Array.t)
      (cols : (int, uf_node) Hashtbl.t Array.t)
    : unit =
  (* params *)
  List.iter (fun param ->
      union (get (Array.get cols (convert_positive f.fn_entrypoint))
               (convert_positive param)) white
    ) f.fn_params;
  (* code *)
  PTree.fold (fun acc n instr ->
      let n' = convert_positive n in
      let live_out = Array.get live n' in
      instr_constraints cols live_out n' @@ convert_instr instr
    ) f.fn_code ()

let color_of_uf_node n =
  if eq n red then Red
  else if eq n green then Green
  else if eq n blue then Blue
  else if eq n white then White
  else if eq n pink then Pink
  (* Unconstrained classes default to Red in the exported coloring. *)
  else Red

let ptree_of_uf_node_array (m : uf_node Array.t) : color PTree.t =
  Array.fold_left
    (fun acc (i, n) -> PTree.set (convert_int i) (color_of_uf_node n) acc)
    PTree.Empty
    (Array.mapi (fun i a -> (i, a)) m)

(* Convert liveness information into the array layout expected by
   [function_constraints]. *)
let convert_live_sets (f : coq_function) (live : Regset.t PMap.t) : int list Array.t =
  let num_instrs = List.length (PTree.elements f.fn_code) in
  Array.init num_instrs (fun n ->
      List.map convert_positive @@
        Regset.elements @@ PMap.get (convert_int n) live)

let infer_coloring (f : coq_function) (live : Regset.t PMap.t)
    : (node -> reg -> color) option =
  let start_time = Unix.gettimeofday () in
  let cols = init_cols f in
  function_constraints f (convert_live_sets f live) cols;
  let end_time = Unix.gettimeofday () in
  print_string @@ "# instructions = " ^
                    string_of_int @@ List.length @@
                      PTree.elements f.fn_code;
  print_string @@ ", # registers = " ^
                    string_of_int @@ List.length @@
                      Regset.elements @@ regs_of_function f;
  print_endline @@ ", time = " ^ string_of_float (end_time -. start_time) ^ " s";
  Some (fun n -> let ix = convert_positive n in
                 if ix < Array.length cols then
                   let col = Array.get cols ix in
                   fun r -> match Hashtbl.find_opt col (convert_positive r) with
                            | Some n -> color_of_uf_node n
                            | None -> Red
                 else
                   fun r -> Red)
