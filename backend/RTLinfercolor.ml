open AST
open BinNums
open Datatypes
open Maps
open Op
open Registers
open RTL
open RTLcolor

(* Global unification version, with arrays *)

(* This file provides an implementation of the color inference oracle
   declared in Colorcheck.v with the following type: *)
(* Parameter infer_coloring : function -> option (node -> PTree.t color). *)

exception ColorError of string

(* Tail-recursive list append *)
let[@tail_mod_cons] rec app (l1 : 'a list) (l2 : 'a list) : 'a list =
  match l1 with
  | [] -> l2
  | x :: xs -> x :: (app [@tailcall]) xs l2

(* Tail-recursive list map *)
let[@tail_mod_cons] rec map (f : 'a -> 'b) (l : 'a list) : 'b list =
  match l with
  | [] -> []
  | x :: xs -> f x :: (map [@tailcall]) f xs

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

type color' =
  | Ccolor of color
  | Cvar of int

let string_of_color = function
  | Red -> "R"
  | Green -> "G"
  | Blue -> "B"
  | White -> "W"
  | Pink -> "P"

let string_of_color' = function
  | Ccolor c -> string_of_color c
  | Cvar i -> "" ^ string_of_int i

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
     Iop' (op, map convert_positive args, convert_positive res,
           convert_positive succ)
  | Iload (chunk, addr, args, res, succ) ->
     Iload' (chunk, addr, map convert_positive args,
             convert_positive res, convert_positive succ)
  | Istore (chunk, addr, args, src, succ) ->
     Istore' (chunk, addr, map convert_positive args,
              convert_positive src, convert_positive succ)
  | Icall (sg, fn, args, res, succ) ->
     Icall' (sg, (match fn with
                  | Coq_inl r -> Coq_inl (convert_positive r)
                  | Coq_inr nm -> Coq_inr nm), map convert_positive args,
             convert_positive res, convert_positive succ)
  | Itailcall (sg, fn, args) ->
     Itailcall' (sg, (match fn with
                      | Coq_inl r -> Coq_inl (convert_positive r)
                      | Coq_inr nm -> Coq_inr nm), map convert_positive args)
  | Ibuiltin (ef, bargs, bres, succ) ->
     Ibuiltin' (ef, map (map_builtin_arg convert_positive) bargs,
                map_builtin_res convert_positive bres, convert_positive succ)
  | Icond (cond, args, ifso, ifnot) ->
     Icond' (cond, map convert_positive args,
             convert_positive ifso, convert_positive ifnot)
  | Ijumptable (arg, succs) ->
     Ijumptable' (convert_positive arg, map convert_positive succs)
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

let succs_of_instruction = function
  | Inop' succ -> [succ]
  | Iop' (_, _, _, succ) -> [succ]
  | Iload' (_, _, _, _, succ) -> [succ]
  | Istore' (_, _, _, _, succ) -> [succ]
  | Icall' (_, _, _, _, succ) -> [succ]
  | Ibuiltin' (_, _, _, succ) -> [succ]
  | Icond' (_, _, ifso, ifnot) -> [ifso; ifnot]
  | Ijumptable' (_, succs) -> succs
  | _ -> []

let regs_of_function (f : coq_function) : Regset.t =
  List.fold_left (fun acc param -> Regset.add param acc)
    (PTree.fold (fun acc _ instr -> Regset.union acc @@ instr_regs instr)
       f.fn_code Regset.empty) f.fn_params

let list_max l = List.fold_left max 0 l

let counter = ref 0
let fresh () = let n = !counter in counter := !counter + 1; n
let init_cols (f : coq_function) : color' Array.t Array.t =
  let num_instrs = List.length (PTree.elements f.fn_code) in
  let num_regs = (list_max @@ List.map convert_positive @@
                   Regset.elements @@ regs_of_function f) + 1 in
  (* print_endline @@ "num_instrs = " ^ string_of_int num_instrs; *)
  (* print_endline @@ "num_regs = " ^ string_of_int num_regs; *)
  Array.init num_instrs
    (fun _ -> Array.init num_regs
                (fun _ -> Cvar (fresh ())))

let nodes_in_code (c : code) : node list = map fst (PTree.elements c)

let print_col (col : color' Array.t) : unit =
  Array.iteri (fun r c ->
      print_string @@ "x" ^ string_of_int r ^ "=" ^ string_of_color' c ^ ", "
    ) col;
  print_newline ()

let nodes_in_order (f : coq_function) : int list =
  List.sort (fun x y -> if x < y then 1 else 0) @@
    map convert_positive @@ nodes_in_code f.fn_code

let print_cols (f : coq_function) (cols : color' Array.t Array.t) : unit =
  Array.iteri (fun n col ->
      print_string @@ string_of_int n ^ ": ";
      print_col col
    ) cols

let string_of_instruction : instruction' -> string = function
  | Inop' succ -> "Inop' " ^ string_of_int succ
  | Ibuiltin' (ef, _bargs, _bres, succ) ->
     "Ibuiltin' " ^ string_of_int succ
  | _ -> "TODO"

let ptree_of_intmap (m : 'a Array.t) : 'a PTree.t =
  Array.fold_left
    (fun acc (i, a) -> PTree.set (convert_int i) a acc)
    PTree.Empty
    (Array.mapi (fun i a -> (i, a)) m)

type constraints = (color' * color') list
type tysubst = (color' * int) list

let instr_constraints
      (cols : color' Array.t Array.t)
      (all_regs : int list)
      (pc : int) (instr : instruction')
    : constraints =
  let col = Array.get cols pc in
  match instr with
  | Inop' succ ->
     let succ_col = Array.get cols succ in
     let all_preserved = List.fold_left (fun acc r ->
                             (Array.get col r, Array.get succ_col r) :: acc
                            ) [] all_regs in
     all_preserved
  | Iop' (op, args, res, succ) ->
     let succ_col = Array.get cols succ in
     if is_protectedb op then
       let args_white = map (fun arg -> (Array.get col arg, Ccolor White)) args in
       let res_white = (Array.get succ_col res, Ccolor White) in
       let rest_preserved = List.fold_left (fun acc r ->
                                if r = res || List.mem r args then
                                  acc
                                else
                                  (Array.get col r, Array.get succ_col r) :: acc
                              ) [] all_regs in
       res_white :: app args_white rest_preserved
     else
       let res_color = Array.get succ_col res in
       let args_res =
         map (fun arg -> (Array.get col arg, res_color)) args in
       let rest_preserved =
         List.fold_left (fun acc r ->
             if r = res then
               acc
             else
               (Array.get col r, Array.get succ_col r) :: acc
           ) [] all_regs in
       app args_res rest_preserved
  | Iload' (_, _, args, res, succ) ->
     let succ_col = Array.get cols succ in
     let args_white = map (fun arg -> (Array.get col arg, Ccolor White)) args in
     let res_white = (Array.get succ_col res, Ccolor White) in
     let rest_preserved = List.fold_left (fun acc r ->
                              if r = res || List.mem r args then
                                acc
                              else
                                (Array.get col r, Array.get succ_col r) :: acc
                            ) [] all_regs in
     res_white :: app args_white rest_preserved
  | Istore' (_, _, args, src, succ) ->
     let succ_col = Array.get cols succ in
     let src_white = (Array.get col src, Ccolor White) in
     let args_white = map (fun arg -> (Array.get col arg, Ccolor White)) args in
     let rest_preserved = List.fold_left (fun acc r ->
                              if r = src || List.mem r args then
                                acc
                              else
                                (Array.get col r, Array.get succ_col r) :: acc
                            ) [] all_regs in
     src_white :: app args_white rest_preserved
  | Icall' (_, fn, args, res, succ) ->
     let succ_col = Array.get cols succ in
     let args_white = map (fun arg -> (Array.get col arg, Ccolor White)) args in
     let res_white = (Array.get succ_col res, Ccolor White) in
     let fn_white = match fn with
       | Coq_inl r -> [(Array.get col r, Ccolor White)]
       | Coq_inr _ -> [] in
     let rest_preserved = List.fold_left (fun acc r ->
                              if r = res || List.mem r args ||
                                   (match fn with
                                    | Coq_inl r' -> r = r'
                                    | Coq_inr _ -> false) then
                                acc
                              else
                                (Array.get col r, Array.get succ_col r) :: acc
                            ) [] all_regs in
     res_white :: app fn_white (app args_white rest_preserved)
  | Itailcall' (_, fn, args) ->
     let args_white = map (fun arg -> (Array.get col arg, Ccolor White)) args in
     let fn_white = match fn with
       | Coq_inl r -> [(Array.get col r, Ccolor White)]
       | Coq_inr _ -> [] in
     app fn_white args_white
  | Ibuiltin' (ef, bargs, bres, succ) ->
     let succ_col = Array.get cols succ in
     if is_green_smove_builtinb ef then
       match bargs, bres with
       | [BA arg], BR res ->
          let arg_white = (Array.get col arg, Ccolor White) in
          let arg_pink = (Array.get succ_col arg, Ccolor Pink) in
          let res_green = (Array.get succ_col res, Ccolor Green) in
          let rest_preserved =
            List.fold_left (fun acc r ->
                if r = arg || r = res then
                  acc
                else
                  (Array.get col r, Array.get succ_col r) :: acc
              ) [] all_regs in
          arg_white :: arg_pink :: res_green :: rest_preserved
       | _ -> []
     else if is_blue_smove_builtinb ef then
       match bargs, bres with
       | [BA arg], BR res ->
          let arg_pink = (Array.get col arg, Ccolor Pink) in
          let arg_red = (Array.get succ_col arg, Ccolor Red) in
          let res_blue = (Array.get succ_col res, Ccolor Blue) in
          let rest_preserved =
            List.fold_left (fun acc r ->
                if r = arg || r = res then
                  acc
                else
                  (Array.get col r, Array.get succ_col r) :: acc
              ) [] all_regs in
          arg_pink :: arg_red :: res_blue :: rest_preserved
       | _ -> []
     else if is_vote_builtinb ef then
       match bargs, bres with
       | [BA arg1; BA arg2; BA arg3], BR res ->
          let arg1_red = (Array.get col arg1, Ccolor Red) in
          let arg2_green = (Array.get col arg2, Ccolor Green) in
          let arg3_blue = (Array.get col arg3, Ccolor Blue) in
          let res_white = (Array.get succ_col res, Ccolor White) in
          let rest_preserved =
            List.fold_left (fun acc r ->
                if r = res then
                  acc
                else
                  (Array.get col r, Array.get succ_col r) :: acc
              ) [] all_regs in
          arg1_red :: arg2_green :: arg3_blue :: res_white :: rest_preserved
       | _ -> []
     else
       let arg_regs = List.concat_map regs_of_builtin_arg bargs in
       let res_regs = regs_of_builtin_res bres in
       let args_white = map (fun arg ->
                            (Array.get col arg, Ccolor White)
                          ) arg_regs in
       let res_white = map (fun res ->
                           (Array.get succ_col res, Ccolor White)
                         ) res_regs in
       let rest_preserved =
         List.fold_left (fun acc r ->
             if List.mem r arg_regs || List.mem r res_regs then
               acc
             else
               (Array.get col r, Array.get succ_col r) :: acc
           ) [] all_regs in
       app args_white (app res_white rest_preserved)
  | Icond' (_, args, ifso, ifnot) ->
     let ifso_col = Array.get cols ifso in
     let ifnot_col = Array.get cols ifnot in
     let args_white = map (fun arg -> (Array.get col arg, Ccolor White)) args in
     let rest_preserved = List.fold_left (fun acc r ->
                              if List.mem r args then
                                acc
                              else
                                (Array.get col r, Array.get ifso_col r) ::
                                  (Array.get col r, Array.get ifnot_col r) ::
                                    acc
                            ) [] all_regs in
     app args_white rest_preserved
  | Ijumptable' (arg, succs) ->
     let arg_white = (Array.get col arg, Ccolor White) in
     let rest_preserved =
       List.fold_left (fun acc r ->
           if r = arg then
             acc
           else
             app (map (fun succ ->
                      let succ_col = Array.get cols succ in
                      (Array.get col r, Array.get succ_col r)
                    ) succs) acc
         ) [] all_regs in
     arg_white :: rest_preserved
  | Ireturn' ro ->
     match ro with
     | Some r -> [(Array.get col r, Ccolor White)]
     | None -> []

let gather_constraints
      (f : coq_function) (cols : color' Array.t Array.t)
    : constraints =
  let param_constrs = map (fun param ->
                          (Array.get (Array.get cols (convert_positive f.fn_entrypoint))
                             (convert_positive param),
                           Ccolor White)
                        ) f.fn_params in
  let all_regs = map convert_positive @@ Regset.elements @@ regs_of_function f in
  let code_constrs =
    PTree.fold (fun acc n instr ->
        let constrs = instr_constraints cols all_regs (convert_positive n) @@
                        convert_instr instr in
        (* print_string @@ "constraints for " ^ string_of_positive n ^ ": "; *)
        (* List.iter (fun (s, t) -> *)
        (*     print_string @@ string_of_color' s ^ "=" ^ *)
        (*                       string_of_color' t ^ ", ") constrs; *)
        (* print_newline (); *)
        app acc constrs
      ) f.fn_code [] in
  app param_constrs code_constrs

let subst_color' (s : color') (t : int) : color' -> color' = function
  | Ccolor c -> Ccolor c
  | Cvar i -> if i = t then s else Cvar i

let subst_constr (s : color') (t : int) ((c1, c2) : color' * color') : color' * color' =
  (subst_color' s t c1, subst_color' s t c2)

let subst_constraints (s : color') (t : int) (constrs : constraints) : constraints =
  map (subst_constr s t) constrs

let rec unify : constraints -> tysubst option = function
  | [] -> Some []
  | (s, t) :: constrs ->
     (* print_endline @@ "unifying " ^ string_of_color' s ^ " with " ^ string_of_color' t *)
     if s = t then
       unify constrs
     else
       match s with
       | Cvar x -> begin
           match unify (subst_constraints t x constrs) with
           | Some rest -> Some ((t, x) :: rest)
           | None -> None
         end
       | _ -> begin
           match t with
           | Cvar y -> begin
               match unify (subst_constraints s y constrs) with
               | Some rest -> Some ((s, y) :: rest)
               | None -> None
             end
           | _ -> None
         end

let rec tysubst_color' (subst : tysubst) (c' : color') : color' =
  match subst, c' with
  | [], _ -> c'
  | _, Ccolor _ -> c'
  | (s, t) :: subst', Cvar x ->
     tysubst_color' subst' (if x = t then s else c')

let subst_cols (subst : tysubst) (cols : color' Array.t Array.t)
    : color' Array.t Array.t =
 Array.map (fun col -> Array.map (tysubst_color' subst) col) cols

let finalize_cols (cols : color' Array.t Array.t) : color Array.t Array.t =
  Array.map (fun col ->
      Array.map (fun c' ->
          match c' with
          | Ccolor c -> c
          | Cvar _ -> Red
        ) col
    ) cols

let infer_coloring (f : coq_function) : (node -> color PTree.t) option =
  let start_time = Unix.gettimeofday () in
  (* print_endline "initializing colorings..."; *)
  let cols = init_cols f in
  (* print_cols f cols; *)
  (* print_endline "gathering constraints..."; *)
  let constrs = gather_constraints f cols in
  (* print_endline @@ "generated " ^ string_of_int (List.length constrs) ^ *)
  (*                    " constraints. solving..."; *)
  match unify constrs with
  | Some subst ->
     let end_time = Unix.gettimeofday () in
     print_string @@ "# instructions = " ^
                       string_of_int @@ List.length @@
                         PTree.elements f.fn_code;
     print_string @@ ", # registers = " ^
                       string_of_int @@ List.length @@
                         Regset.elements @@ regs_of_function f;
     print_endline @@ ", time = " ^ string_of_float (end_time -. start_time) ^ " s";
     let m = subst_cols subst cols in
     (* print_cols f m; *)
     let final_cols = Array.map ptree_of_intmap @@ finalize_cols m in
     (* Some (fun n -> Option.value ~default:PTree.Empty @@ *)
  (*                  Intmap.find_opt (convert_positive n) final_cols) *)
     Some (fun n -> let ix = convert_positive n in
                    if ix < Array.length final_cols then
                      Array.get final_cols ix
                    else
                      PTree.Empty)
  | None -> print_endline "color inference failed!";
            None
