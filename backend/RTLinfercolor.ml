open AST
open BinNums
open Datatypes
open Maps
open Op
open Registers
open RTL
open RTLcolor

(* Faster version that uses OCaml's Map module and machine integer
   keys instead of PTree and PMap with positive keys. *)

(* This file provides an implementation of the color inference oracle
   declared in Colorcheck.v with the following type: *)
(* Parameter infer_coloring : function -> option (node -> PTree.t color). *)

exception ColorError of string

module Intmap = Map.Make(Int)

let rec int_of_positive = function
  | Coq_xI p -> 2 * int_of_positive p + 1
  | Coq_xO p -> 2 * int_of_positive p
  | Coq_xH -> 1

let string_of_positive p = string_of_int @@ int_of_positive p

(* let string_of_color = function *)
(*   | Red -> "Red" *)
(*   | Green -> "Green" *)
(*   | Blue -> "Blue" *)
(*   | White -> "White" *)
(*   | Pink -> "Pink" *)

let string_of_color = function
  | Red -> "R"
  | Green -> "G"
  | Blue -> "B"
  | White -> "W"
  | Pink -> "P"

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
  | Inop succ -> Inop' (int_of_positive succ)
  | Iop (op, args, res, succ) ->
     Iop' (op, List.map int_of_positive args, int_of_positive res,
           int_of_positive succ)
  | Iload (chunk, addr, args, res, succ) ->
     Iload' (chunk, addr, List.map int_of_positive args,
             int_of_positive res, int_of_positive succ)
  | Istore (chunk, addr, args, src, succ) ->
     Istore' (chunk, addr, List.map int_of_positive args,
              int_of_positive src, int_of_positive succ)
  | Icall (sg, fn, args, res, succ) ->
     Icall' (sg, (match fn with
                  | Coq_inl r -> Coq_inl (int_of_positive r)
                  | Coq_inr nm -> Coq_inr nm), List.map int_of_positive args,
             int_of_positive res, int_of_positive succ)
  | Itailcall (sg, fn, args) ->
     Itailcall' (sg, (match fn with
                      | Coq_inl r -> Coq_inl (int_of_positive r)
                      | Coq_inr nm -> Coq_inr nm), List.map int_of_positive args)
  | Ibuiltin (ef, bargs, bres, succ) ->
     Ibuiltin' (ef, List.map (map_builtin_arg int_of_positive) bargs,
                map_builtin_res int_of_positive bres, int_of_positive succ)
  | Icond (cond, args, ifso, ifnot) ->
     Icond' (cond, List.map int_of_positive args,
             int_of_positive ifso, int_of_positive ifnot)
  | Ijumptable (arg, succs) ->
     Ijumptable' (int_of_positive arg, List.map int_of_positive succs)
  | Ireturn ro -> Ireturn' (match ro with
                            | Some r -> Some (int_of_positive r)
                            | None -> None)

let union (pc : int) (t1 : color Intmap.t) (t2 : color Intmap.t)
    : color Intmap.t option =
  Intmap.fold (fun n c topt ->
      match topt with
      | Some t -> begin
          match Intmap.find_opt n t with
          | Some c' ->
             if c = c' then Some t else
               (print_endline @@
                  string_of_int pc ^ ": " ^
                    string_of_color c ^ "<>" ^ string_of_color c';
                None)
          | None -> Some (Intmap.add n c t)
        end
      | None -> None) t1 (Some t2)

let rec regs_of_builtin_res = function
  | BR r -> [r]
  | BR_none -> []
  | BR_splitlong (hi, lo) ->
     regs_of_builtin_res hi @ regs_of_builtin_res lo

(* Can/should we fuse replication followed immediately by voting?
   E.g., when you have two unsafe ops in a row, the white result from
   the first could be fed directly into the argument of the
   second. This would be equivalent wrt. fault tolerance to
   replicating the result and then voting on it, but more
   efficient. The only difference I guess is if that result is then
   used elsewhere; maybe we do that only when the result is dead after
   the following instruction. *)

let rec regs_of_builtin_arg = function
| BA r -> r :: []
| BA_splitlong (hi, lo) ->
  app (regs_of_builtin_arg hi) (regs_of_builtin_arg lo)
| BA_addptr (a1, a2) -> app (regs_of_builtin_arg a1) (regs_of_builtin_arg a2)
| _ -> []

let transfer (instr : instruction') (col : color Intmap.t) : color Intmap.t =
  match instr with
  | Inop' _ -> col
  | Iop' (op, args, res, _) ->
     if is_unsafeb op then
       Intmap.add res White
         (List.fold_left (fun acc arg -> Intmap.remove arg acc) col args)
     else
       (* Don't worry about the 'is_basic' constraint here. The color
          checker will check that. Same for equality of colors of
          arguments. We could do a pass in this module at the end to
          check those constraints for debugging purposes. *)
       List.fold_left (fun acc arg -> match Intmap.find_opt arg col with
                                      | Some c -> Intmap.add res c acc
                                      | None -> acc) col args
  | Iload' (_, _, args, res, _) ->
     Intmap.add res White
       (List.fold_left (fun acc arg -> Intmap.remove arg acc) col args)
  | Istore' (_, _, args, dst, _) ->
     Intmap.remove dst
       (List.fold_left (fun acc arg -> Intmap.remove arg acc) col args)
  | Icall' (_, fn, args, res, _) -> begin
      let col' =
        Intmap.add res White
          (List.fold_left (fun acc arg -> Intmap.remove arg acc) col args) in
      match fn with
      | Coq_inl r -> Intmap.remove r col'
      | Coq_inr _ -> col'
    end
  | Itailcall' (_, fn, args) -> begin
      let col' =
        List.fold_left (fun acc arg -> Intmap.remove arg acc) col args in
      match fn with
      | Coq_inl r -> Intmap.remove r col'
      | Coq_inr _ -> col'
    end
  | Ibuiltin' (ef, bargs, bres, _) ->
     if is_smove_builtinb ef then
       match bargs, bres with
       | [BA arg], BR res -> begin
           match Intmap.find_opt arg col with
           | Some White ->
              Intmap.add arg Pink @@ Intmap.add res Green col
           | Some Pink ->
              Intmap.add arg Red @@ Intmap.add res Blue col
           | Some _ -> raise (ColorError "smove arg not White or Pink")
           | None -> col
         end
       | _, _ -> raise (ColorError "invalid argument(s) or res of smove builtin")
     else if is_vote_builtinb ef then
       match bargs, bres with
       | [BA arg1; BA arg2; BA arg3], BR res ->
          (* Intmap.add res White *)
          (*   (List.fold_left (fun acc arg -> Intmap.remove arg acc) *)
          (*      col [arg1; arg2; arg3]) *)
          Intmap.add res White col
       | _, _ -> raise (ColorError "invalid argument(s) or res of vote builtin")
     else
       let arg_regs = List.concat_map regs_of_builtin_arg bargs in
       let res_regs = regs_of_builtin_res bres in
       List.fold_left (fun acc r -> Intmap.add r White acc)
         (List.fold_left (fun acc arg -> Intmap.remove arg acc) col arg_regs)
         res_regs
  | Icond' (_, args, _, _) ->
     List.fold_left (fun acc arg -> Intmap.remove arg acc) col args
  | Ijumptable' (arg, _) ->
     Intmap.remove arg col
  | Ireturn' ro -> match ro with
                  | Some r -> Intmap.remove r col
                  | None -> col

(* (\** Check constraints for debugging purposes (the verified checker *)
(*     will catch any errors so this is not strictly necessary). *\) *)
(* let check_code (c : code) (cols : color PTree.t PMap.t) : unit = *)
(*   let check_instr = function *)
(*     | Inop' _ -> () *)
(*     | _ -> () in *)
(*   print_endline "checking code..."; *)
(*   PTree.fold (fun _ _ -> check_instr) c () *)

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

let build_pred_map (c : code) : (int * instruction') list Intmap.t =
  PTree.fold (fun acc n instr ->
      let n' = int_of_positive n in
      let instr' = convert_instr instr in
      List.fold_left (fun acc2 succ ->
          Intmap.add succ ((n', instr') ::
                             (Option.value ~default:[] @@ Intmap.find_opt succ acc2)) acc2
        ) acc @@ succs_of_instruction instr'
    ) c Intmap.empty

(* let update *)
(*       (nodes_instrs : (int * instruction') list) *)
(*       (pred_map : (int * instruction') list Intmap.t) *)
(*       (cols : color Intmap.t Intmap.t) *)
(*     : (color Intmap.t Intmap.t) option = *)
(*   (\* For each instruction  *\) *)
(*   List.fold_left (fun acc (n, instr) -> *)
(*       let preds = Option.value ~default:[] @@ Intmap.find_opt n pred_map in *)
(*       let preds_col = *)
(*         List.fold_left (fun acc2 (pred_node, pred_instr) -> *)
(*             match acc2 with *)
(*             | Some m -> *)
(*                union n m (transfer pred_instr @@ *)
(*                             Option.value ~default:Intmap.empty @@ *)
(*                               Intmap.find_opt pred_node cols) *)
(*             | None -> None *)
(*           ) (Some Intmap.empty) preds in *)
(*       match acc, preds_col with *)
(*       | Some m1, Some m2 -> begin *)
(*           match union n (Option.value ~default:Intmap.empty @@ *)
(*                            Intmap.find_opt n cols) m2 with *)
(*           | Some col' -> Some (Intmap.add n col' m1) *)
(*           | None -> None *)
(*         end *)
(*       | _, _ -> None *)
(*     ) (Some cols) nodes_instrs *)

let update
      (nodes_instrs : (int * instruction') list)
      (pred_map : (int * instruction') list Intmap.t)
      (cols : color Intmap.t Intmap.t)
    : (color Intmap.t Intmap.t) option =
  (* let start_time = Unix.gettimeofday () in *)
  (* For each instruction  *)
  let res =
    List.fold_left (fun acc (n, instr) ->
        match acc with
        | Some m1 -> begin
            let preds = Option.value ~default:[] @@ Intmap.find_opt n pred_map in
            let preds_col =
              List.fold_left (fun acc2 (pred_node, pred_instr) ->
                  match acc2 with
                  | Some m ->
                     union n m (transfer pred_instr @@
                                  Option.value ~default:Intmap.empty @@
                                    Intmap.find_opt pred_node m1)
                  | None -> None
                ) (Some Intmap.empty) preds in
            match preds_col with
            | Some m2 -> begin
                match union n (Option.value ~default:Intmap.empty @@
                                 Intmap.find_opt n m1) m2 with
                | Some col' -> Some (Intmap.add n col' m1)
                | None -> None
              end
            | _ -> None
          end
        | None -> None
      ) (Some cols) nodes_instrs in
  (* let end_time = Unix.gettimeofday () in *)
  (* print_endline @@ "update: " ^ string_of_float (end_time -. start_time) ^ "s"; *)
  res

(** Old version of update that is probably equivalent to the above but
    more confusing. *)  
(* let update (c : code) (cols : color PTree.t PMap.t) *)
(*     : (color PTree.t PMap.t) option = *)
(*   (\* For each instruction  *\) *)
(*   PTree.fold (fun acc n instr -> *)
(*       match acc with *)
(*       | Some m0 -> *)
(*          (\* Compute out-coloring via transfer function *\) *)
(*          let col = transfer instr (Option.value ~default:[] @@ Intmap.find_opt n m0) in *)
(*          (\* For each successor of the instruction *\) *)
(*          List.fold_left (fun acc2 succ -> *)
(*              match acc2 with *)
(*              | Some m -> begin *)
(*                  (\* Compute union of successor's previous coloring *)
(*                     with newly computed out-coloring *\) *)
(*                  match union col (Option.value ~default:[] @@ Intmap.find_opt succ m) with *)
(*                  (\* If successful, update successor's coloring to *)
(*                     the union *\) *)
(*                  | Some col' -> Some (Intmap.add succ col' m) *)
(*                  (\* Else inference failure *\) *)
(*                  | _ -> None *)
(*                end *)
(*              | None -> None *)
(*            ) (Some m0) (succs_of_instruction instr) *)
(*       | None -> None *)
(*     ) c (Some cols) *)

(** t minus bindings in l *)
let minus (t : 'a Intmap.t) (l : int list) : 'a Intmap.t =
  List.fold_left (fun acc n -> Intmap.remove n acc) t l

let ignored_registers : instruction' -> int list = function
  | Iop' (op, args, res, _) when is_unsafeb op -> res :: args
  | Iload' (_, _, args, res, _) -> res :: args
  | Istore' (_, _, args, src, _) -> src :: args
  | Icall' (_, fn, args, res, _) -> begin
      match fn with
      | Coq_inl r -> r :: res :: args
      | Coq_inr _ -> res :: args
    end
  | Itailcall' (_, fn, args) -> begin
      match fn with
      | Coq_inl r -> r :: args
      | Coq_inr _ -> args
    end
  | Ibuiltin' (ef, bargs, bres, _) ->
     let args = List.concat_map regs_of_builtin_arg bargs in
     let ress = regs_of_builtin_res bres in
     args @ ress
  | Icond' (_, args, _, _) -> args
  | Ijumptable' (arg, _) -> [arg]
  | Ireturn' (Some arg) -> [arg]
  | _ -> []

(* let update2 *)
(*       (nodes_instrs : (int * instruction') list) *)
(*       (cols : color Intmap.t Intmap.t) *)
(*     : (color Intmap.t Intmap.t) option = *)
(*   List.fold_left (fun acc (n, instr) -> *)
(*       let ignored_regs = ignored_registers instr in *)
(*       let succs_col = *)
(*         List.fold_left (fun acc2 succ -> *)
(*             match acc2 with *)
(*             | Some m -> union n m (minus (Option.value ~default:Intmap.empty @@ *)
(*                                             Intmap.find_opt succ cols) ignored_regs) *)
(*             | None -> None *)
(*           ) (Some Intmap.empty) @@ succs_of_instruction instr in *)
(*       match acc, succs_col with *)
(*       | Some m, Some col -> begin *)
(*           match union n (Option.value ~default:Intmap.empty @@ *)
(*                            Intmap.find_opt n cols) col with *)
(*           | Some col' -> begin *)
(*               match instr with *)
(*               (\* For safe Iops, if successor assigns a color to the *)
(*                  result then propagate that to the arguments. *\) *)
(*               | Iop' (op, args, res, _) when not (is_unsafeb op) -> begin *)
(*                   match Intmap.find_opt res col with *)
(*                   | Some c -> begin *)
(*                       let arg_cols = *)
(*                         List.fold_left (fun acc3 arg -> *)
(*                             Intmap.add arg c acc3 *)
(*                           ) Intmap.empty args in *)
(*                       match union n col' arg_cols with *)
(*                       | Some final_col -> *)
(*                          Some (Intmap.add n final_col m) *)
(*                       | None -> None *)
(*                     end *)
(*                   | None -> Some (Intmap.add n col' m) *)
(*                 end *)
(*               | _ -> Some (Intmap.add n col' m) *)
(*             end *)
(*           | None -> None *)
(*         end *)
(*       | _, _ -> None *)
(*     ) (Some cols) nodes_instrs *)

let update2
      (nodes_instrs : (int * instruction') list)
      (cols : color Intmap.t Intmap.t)
    : (color Intmap.t Intmap.t) option =
  (* let start_time = Unix.gettimeofday () in *)
  let res =
    List.fold_left (fun acc (n, instr) ->
        let ignored_regs = ignored_registers instr in
        let succs_col =
          List.fold_left (fun acc2 succ ->
              match acc2 with
              | Some m -> union n m (minus (Option.value ~default:Intmap.empty @@
                                              Intmap.find_opt succ cols) ignored_regs)
              | None -> None
            ) (Some Intmap.empty) @@ succs_of_instruction instr in
        match acc, succs_col with
        | Some m, Some col -> begin
            match union n (Option.value ~default:Intmap.empty @@
                             Intmap.find_opt n m) col with
            | Some col' -> begin
                match instr with
                (* For safe Iops, if successor assigns a color to the
                   result then propagate that to the arguments. *)
                | Iop' (op, args, res, _) when not (is_unsafeb op) -> begin
                    match Intmap.find_opt res col with
                    | Some c -> begin
                        let arg_cols =
                          List.fold_left (fun acc3 arg ->
                              Intmap.add arg c acc3
                            ) Intmap.empty args in
                        match union n col' arg_cols with
                        | Some final_col ->
                           Some (Intmap.add n final_col m)
                        | None -> None
                      end
                    | None -> Some (Intmap.add n col' m)
                  end
                | _ -> Some (Intmap.add n col' m)
              end
            | None -> None
          end
        | _, _ -> None
      ) (Some cols) nodes_instrs in
  (* let end_time = Unix.gettimeofday () in *)
  (* print_endline @@ "update2: " ^ string_of_float (end_time -. start_time) ^ "s"; *)
  res

(* let update3 *)
(*       (nodes_instrs : (int * instruction') list) *)
(*       (cols : color Intmap.t Intmap.t) *)
(*     : color Intmap.t Intmap.t = *)
(*   List.fold_left (fun acc (n, instr) -> *)
(*       match instr with *)
(*       (\* For smoves, if the successor assigns a color to the argument *)
(*          then infer the corresponding color for it here (if red at *)
(*          successor then pink here, or if pink at successor then white *)
(*          here). *\) *)
(*       | Ibuiltin' (ef, [BA arg], BR res, succ) when is_smove_builtinb ef -> *)
(*          begin *)
(*            match Intmap.find_opt arg (Option.value ~default:Intmap.empty @@ *)
(*                                         Intmap.find_opt succ cols) with *)
(*            | Some c -> *)
(*               let arg_c = if c = Red then Pink else White in *)
(*               Intmap.add n (Intmap.add arg arg_c @@ *)
(*                               Option.value ~default:Intmap.empty @@ *)
(*                                 Intmap.find_opt n acc) acc *)
(*            | None -> acc *)
(*          end *)
(*       | _ -> acc *)
(*     ) cols nodes_instrs *)

let update3
      (nodes_instrs : (int * instruction') list)
      (cols : color Intmap.t Intmap.t)
    : color Intmap.t Intmap.t =
  (* let start_time = Unix.gettimeofday () in *)
  let res =
    List.fold_left (fun acc (n, instr) ->
        match instr with
        (* For smoves, if the successor assigns a color to the argument
           then infer the corresponding color for it here (if red at
           successor then pink here, or if pink at successor then white
           here). *)
        | Ibuiltin' (ef, [BA arg], BR res, succ) when is_smove_builtinb ef ->
           begin
             match Intmap.find_opt arg (Option.value ~default:Intmap.empty @@
                                          Intmap.find_opt succ cols) with
             | Some c ->
                let arg_c = if c = Red then Pink else White in
                Intmap.add n (Intmap.add arg arg_c @@
                                Option.value ~default:Intmap.empty @@
                                  Intmap.find_opt n acc) acc
             | None -> acc
           end
        | _ -> acc
      ) cols nodes_instrs in
  (* let end_time = Unix.gettimeofday () in *)
  (* print_endline @@ "update3: " ^ string_of_float (end_time -. start_time) ^ "s"; *)
  res

(** Initialize nodes' colorings. The entry point assigns White to the
    function's parameters. Unsafe instructions assign White to their
    arguments. Votes assign Red, Green, and Blue to their
    arguments. Smove argument colors are left unspecified, to be
    inferred by the dataflow analysis. *)
let init_cols (f : coq_function) : color Intmap.t Intmap.t =
  let init_col = function
    | Inop' _ -> Intmap.empty
    | Iop' (op, args, _, _) ->
       if is_unsafeb op then
         List.fold_left (fun acc arg -> Intmap.add arg White acc) Intmap.empty args
       else
         Intmap.empty
    | Iload' (_, _, args, _, _) ->
       List.fold_left (fun acc arg -> Intmap.add arg White acc) Intmap.empty args
    | Istore' (_, _, args, src, _) ->
       Intmap.add src White @@
         List.fold_left (fun acc arg -> Intmap.add arg White acc) Intmap.empty args
    | Icall' (_, fn, args, _, _) -> begin
        let col = List.fold_left (fun acc arg -> Intmap.add arg White acc)
                    Intmap.empty args in
        match fn with
        | Coq_inl r -> Intmap.add r White col
        | Coq_inr _ -> col
      end
    | Itailcall' (_, fn, args) -> begin
        let col = List.fold_left (fun acc arg -> Intmap.add arg White acc)
                    Intmap.empty args in
        match fn with
        | Coq_inl r -> Intmap.add r White col
        | Coq_inr _ -> col
      end
    | Ibuiltin' (ef, bargs, bres, _) ->
       if is_smove_builtinb ef then
         Intmap.empty
       else if is_vote_builtinb ef then
         match bargs with
         | [BA arg1; BA arg2; BA arg3] ->
            Intmap.add arg1 Red @@
              Intmap.add arg2 Green @@
                Intmap.add arg3 Blue
                  Intmap.empty
         | _ -> raise (ColorError "Invalid arguments to vote builtin")
       else
         let regs = List.concat_map regs_of_builtin_arg bargs in
         List.fold_left (fun acc r -> Intmap.add r White acc) Intmap.empty regs
    | Icond' (_, args, _, _) ->
       List.fold_left (fun acc arg -> Intmap.add arg White acc) Intmap.empty args
    | Ijumptable' (arg, _) ->
       Intmap.add arg White Intmap.empty
    | Ireturn' ro -> match ro with
                    | Some r -> Intmap.add r White Intmap.empty
                    | None -> Intmap.empty
  in
  (* Initial colorings for all nodes *)
  let cols = PTree.fold (fun acc n instr ->
                 Intmap.add (int_of_positive n)
                   (init_col @@ convert_instr instr) acc)
               f.fn_code Intmap.empty in
  (* Set params to White at entry point *)
  Intmap.add (int_of_positive f.fn_entrypoint)
    (List.fold_left
       (fun t param -> Intmap.add (int_of_positive param) White t)
       Intmap.empty
       f.fn_params)
    cols

let nodes_in_code (c : code) : node list = List.map fst (PTree.elements c)

let print_col (col : color Intmap.t) : unit =
  List.iter (fun (r, c) ->
      print_string @@ "x" ^ string_of_int r ^ "=" ^ string_of_color c ^ ", "
    ) @@ Intmap.bindings col;
  print_newline ()

let nodes_in_order (f : coq_function) : int list =
  (* List.sort (fun x y -> if BinPos.Pos.leb y x then 0 else 1) @@ *)
  (*   nodes_in_code f.fn_code *)
  List.sort (fun x y -> if x < y then 1 else 0) @@
    List.map int_of_positive @@ nodes_in_code f.fn_code

let print_cols (f : coq_function) (cols : color Intmap.t Intmap.t) : unit =
  List.iter (fun n -> print_string @@ string_of_int n ^ ": ";
                      print_col (Option.value ~default:Intmap.empty @@
                                   Intmap.find_opt n cols)) @@ nodes_in_order f

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

let string_of_instruction : instruction' -> string = function
  | Inop' succ -> "Inop' " ^ string_of_int succ
  | Ibuiltin' (ef, _bargs, _bres, succ) ->
     "Ibuiltin' " ^ string_of_int succ
  | _ -> "TODO"

let ptree_of_intmap (m : 'a Intmap.t) : 'a PTree.t =
  Intmap.fold (fun n c acc -> PTree.set (positive_of_int n) c acc) m PTree.Empty

(* let pmap_of_intmap (def : 'a) (m : 'a Intmap.t) : 'a PMap.t = *)
(*   Intmap.fold (fun n c acc -> PMap.set (positive_of_int n) c acc) m (PMap.init def) *)

(* module OrdPos = struct *)
(*   type t = positive *)
(*   let compare a b = *)
(*     if a = b then 0 else *)
(*     if BinPos.Pos.leb a b then -1 else 1 *)
(* end *)
(* module Intset = Set.Make(OrdPos) *)

let regs_of_function (f : coq_function) : Regset.t =
  List.fold_left (fun acc param -> Regset.add param acc)
    (PTree.fold (fun acc _ instr -> Regset.union acc @@ instr_regs instr)
       f.fn_code Regset.empty) f.fn_params

let infer_coloring (f : coq_function) : (node -> color PTree.t) option =
  (* if (List.length @@ PTree.elements f.fn_code) > 1000 then None else begin *)
  (* print_endline @@ "function size = " ^ *)
  (*                    string_of_int @@ List.length @@ PTree.elements f.fn_code; *)
  (* print_endline @@ "entrypoint = " ^ string_of_positive @@ f.fn_entrypoint; *)
  (* print_endline @@ "# params = " ^ string_of_int @@ List.length f.fn_params; *)
  (* List.iter (fun param -> print_endline @@ string_of_positive param) f.fn_params; *)
  (* (match Intmap.find_opt (positive_of_int 36) f.fn_code with *)
  (* | Some instr -> print_endline @@ string_of_instruction instr *)
  (* | None -> ()); *)
  let pred_map = build_pred_map f.fn_code in
  let nodes_instrs =
    List.map (fun n -> (n, convert_instr @@ Option.get @@
                             PTree.get (positive_of_int n) f.fn_code)) @@
      nodes_in_order f in
  let nodes_instrs_rev = List.rev nodes_instrs in
  let rec go (cols : color Intmap.t Intmap.t) : color Intmap.t Intmap.t option =
    (* print_cols f cols; *)
    (* print_newline (); *)
    (* print_endline "update"; *)
    match update nodes_instrs pred_map cols with
    | Some cols' -> begin
        (* print_endline "update2"; *)
        match update2 nodes_instrs_rev cols' with
        | Some cols'' ->
           (* print_endline "update3"; *)
           let cols''' = update3 nodes_instrs_rev cols'' in
           if cols = cols''' then Some cols''' else go cols'''
        | None -> None
      end
    | None -> None
  in
  let start_time = Unix.gettimeofday () in
  match go (init_cols f) with
  | Some m ->
     (* check_code f.fn_code m; *)
     (* print_endline "color inference succeeded!"; *)
     let end_time = Unix.gettimeofday () in
     print_string @@ "# instructions = " ^
                       string_of_int @@ List.length @@
                         PTree.elements f.fn_code;
     print_string @@ ", # registers = " ^
                       string_of_int @@ List.length @@
                         Regset.elements @@ regs_of_function f;
     print_endline @@ ", time = " ^ string_of_float (end_time -. start_time) ^ " s";
     let final_cols = Intmap.map ptree_of_intmap m in
     Some (fun n -> Option.value ~default:PTree.Empty @@
                      Intmap.find_opt (int_of_positive n) final_cols)
  | None -> print_endline "color inference failed!";
            None
