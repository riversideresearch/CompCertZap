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

let string_of_color' = function
  | Some c -> string_of_color c
  | None -> "X"

let print_col (col : color option Array.t) : unit =
  Array.iteri (fun r c ->
      print_string @@ "x" ^ string_of_int (r + 1) ^
                        "=" ^ string_of_color' c ^ ", "
    ) col;
  print_newline ()

let print_cols (cols : color option Array.t Array.t) : unit =
  Array.iteri (fun n col ->
      print_string @@ string_of_int (n + 1) ^ ": ";
      print_col col
    ) cols

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

(* let union (pc : int) (t1 : color Array.t) (t2 : color Array.t) *)
(*     : color Array.t option = *)
(*   Intmap.fold (fun n c topt -> *)
(*       match topt with *)
(*       | Some t -> begin *)
(*           match Intmap.find_opt n t with *)
(*           | Some c' -> *)
(*              if c = c' then Some t else *)
(*                (print_endline @@ *)
(*                   string_of_int pc ^ ": " ^ *)
(*                     string_of_color c ^ "<>" ^ string_of_color c'; *)
(*                 None) *)
(*           | None -> Some (Intmap.add n c t) *)
(*         end *)
(*       | None -> None) t1 (Some t2) *)

let rec regs_of_builtin_res = function
  | BR r -> [r]
  | BR_none -> []
  | BR_splitlong (hi, lo) ->
     regs_of_builtin_res hi @ regs_of_builtin_res lo

(* Can/should we fuse replication followed immediately by voting?
   E.g., when you have two protected ops in a row, the white result
   from the first could be fed directly into the argument of the
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

let if_some (o : 'a option) (f : 'a -> unit) : unit =
  match o with
  | Some x -> f x
  | None -> ()

(* TODO: the use of if_some here is wrong. It should only block uses
   of [c], but not hardcoded colors like White. *)
let transfer (instr : instruction')
      (src : color option Array.t)
      (dst : color option Array.t) : unit =
  match instr with
  | Inop' _ -> Array.iteri (fun i co ->
                   if_some co @@ fun c ->
                     Array.set dst i (Some c)
                 ) src
  | Iop' (op, args, res, _) ->
     if is_protectedb op then
       Array.iteri (fun i co ->
           if_some co @@ fun c ->
              if i = res then
                Array.set dst i (Some White)
              else if not @@ List.mem i args then
                Array.set dst i (Some c)
         ) src
     else begin
         (* Don't worry about the 'is_basic' constraint here. The color
            checker will check that. Same for equality of colors of
            arguments. We could do a pass in this module at the end to
            check those constraints for debugging purposes. *)
         match args with
         | arg :: _ -> begin
            match Array.get src arg with
            | Some args_c ->
               Array.iteri (fun i co ->
                   if_some co @@ fun c ->
                     Array.set dst i (if i = res then Some args_c else Some c)
                 ) src
            | None -> ()
           end
         | _ -> ()
       end
  | Iload' (_, _, args, res, _) ->
     Array.iteri (fun i co ->
         if_some co @@ fun c ->
         if i = res then
           Array.set dst i (Some White)
         else if not @@ List.mem i args then
           Array.set dst i (Some c)
       ) src
  | Istore' (_, _, args, rdst, _) ->
     Array.iteri (fun i co ->
         if_some co @@ fun c ->
         if i <> rdst && not @@ List.mem i args then
           Array.set dst i (Some c)
       ) src
  | Icall' (_, fn, args, res, _) -> begin
      match fn with
      | Coq_inl r ->
         Array.iteri (fun i co ->
             if_some co @@ fun c ->
             if i = res then
               Array.set dst i (Some White)
             else if i <> r && not @@ List.mem i args then
               Array.set dst i (Some c)
           ) src
      | Coq_inr _ ->
         Array.iteri (fun i co ->
             if_some co @@ fun c ->
             if i = res then
               Array.set dst i (Some White)
             else if not @@ List.mem i args then
               Array.set dst i (Some c)
           ) src
    end
  | Itailcall' (_, fn, args) -> begin
      match fn with
      | Coq_inl r ->
         Array.iteri (fun i co ->
             if_some co @@ fun c ->
             if i <> r && not @@ List.mem i args then
               Array.set dst i (Some c)
           ) src
      | Coq_inr _ ->
         Array.iteri (fun i co ->
             if_some co @@ fun c ->
             if not @@ List.mem i args then
               Array.set dst i (Some c)
           ) src
    end
  | Ibuiltin' (ef, bargs, bres, _) ->
     if is_smove_builtinb ef then
       match bargs, bres with
       | [BA arg], BR res -> begin
           match Array.get src arg with
           | Some White ->
              Array.iteri (fun i co ->
                  if_some co @@ fun c ->
                  Array.set dst i @@ Some (
                    if i = arg then Pink else if i = res then Green else c)
                ) src
           | Some Pink ->
              Array.iteri (fun i co ->
                  if_some co @@ fun c ->
                  Array.set dst i @@ Some(
                    if i = arg then Red else if i = res then Blue else c)
                ) src
           | Some _ -> raise (ColorError "smove arg not White or Pink") 
           | None -> ()
         end
       | _, _ -> raise (ColorError "invalid argument(s) or res of smove builtin")
     else if is_vote_builtinb ef then
       match bargs, bres with
       | [BA arg1; BA arg2; BA arg3], BR res ->
          Array.iteri (fun i co ->
              if_some co @@ fun c ->
              Array.set dst i @@ Some (
                if i = res then White else c)
            ) src
       | _, _ -> raise (ColorError "invalid argument(s) or res of vote builtin")
     else
       let arg_regs = List.concat_map regs_of_builtin_arg bargs in
       let res_regs = regs_of_builtin_res bres in
       Array.iteri (fun i co ->
           if List.mem i res_regs then
             Array.set dst i (Some White)
           else if not @@ List.mem i arg_regs then
             if_some co @@ fun c ->
             Array.set dst i (Some c)
         ) src
  | Icond' (_, args, _, _) ->
     Array.iteri (fun i co ->
         if_some co @@ fun c ->
         if not @@ List.mem i args then
           Array.set dst i (Some c)
       ) src
  | Ijumptable' (arg, _) ->
     Array.iteri (fun i co ->
         if_some co @@ fun c ->
         if i <> arg then Array.set dst i (Some c)
       ) src
  | Ireturn' ro -> match ro with
                   | Some r ->
                      Array.iteri (fun i co ->
                          if_some co @@ fun c ->
                          if i <> r then Array.set dst i (Some c)
                        ) src
                   | None ->
                      ()

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

let list_max l = List.fold_left max 0 l

(* let build_pred_map (c : code) : (int * instruction') list Array.t = *)
(*   let num_nodes = *)
(*     list_max @@ List.map (fun (p, _) -> int_of_positive p) @@ *)
(*       PTree.elements c in *)
(*   let pred_map = Array.init num_nodes (fun _ -> []) in *)
(*   PTree.fold (fun () n instr -> *)
(*       let n' = convert_positive n in *)
(*       let instr' = convert_instr instr in *)
(*       List.iter (fun succ -> *)
(*           Array.set pred_map succ ((n', instr') :: Array.get pred_map succ) *)
(*         ) @@ succs_of_instruction instr' *)
(*     ) c (); *)
(*   pred_map *)

(* Not sure but there may be risk of infinite looping this update rule
   (i.e., it may not be monotone) on mal-formed programs. If true,
   then we need to make the transfer function detect failure and exit
   when writing to an incompatible color. *)
let update
      (code : (int * instruction') list)
      (cols : color option Array.t Array.t)
    : unit =
  List.iter (fun (n, instr) ->
      (* print_endline @@ "update1 instruction " ^ string_of_int (n + 1); *)
      (* List.iter (fun succ -> print_endline @@ string_of_int (succ + 1)) @@ *)
      (*   succs_of_instruction instr; *)
      (* print_cols cols; print_newline (); *)
      List.iter (fun succ ->
          transfer instr cols.(n) cols.(succ)) @@
        succs_of_instruction instr
    ) @@ code

let ignored_registers : instruction' -> int list = function
  | Iop' (op, args, res, _) when is_protectedb op -> res :: args
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

(* l1 \ l2 *)
let rec list_minus (l1 : 'a list) (l2 : 'a list) : 'a list =
  match l1 with
  | [] -> []
  | x :: xs ->
     if List.mem x l2 then
       list_minus xs l2
     else
       x :: list_minus xs l2

let update2
      (all_regs : int list)
      (code : (int * instruction') list)
      (cols : color option Array.t Array.t)
    : unit =
  List.iter (fun (i, instr) ->
      let col = Array.get cols i in
      let ignored_regs = ignored_registers instr in
      let unignored_regs = list_minus all_regs ignored_regs in
      List.iter (fun succ ->
          let succ_col = Array.get cols succ in
          List.iter (fun r ->
              match Array.get succ_col r with
              | Some c ->
                 Array.set col r (Some c)
              | None -> ()
            ) unignored_regs
        ) @@ succs_of_instruction instr;
      match instr with
      (* For unprotected Iops, if successor assigns a color to the
         result then propagate that to the arguments. *)
      | Iop' (op, args, res, succ) when not (is_protectedb op) -> begin
          let succ_col = Array.get cols succ in
          match Array.get succ_col res with
          | Some res_c ->
             List.iter (fun arg -> Array.set col arg (Some res_c)) args
          | None -> ()
        end
      | _ -> ()
    ) code

let update3
      (code : (int * instruction') list)
      (cols : color option Array.t Array.t)
    : unit =
  List.iter (fun (i, instr) ->
      let col = Array.get cols i in
      match instr with
      | Ibuiltin' (ef, [BA arg], _, succ) when is_smove_builtinb ef ->
         begin
           let succ_col = Array.get cols succ in
           match Array.get succ_col arg with
           | Some c ->
              if c = Red then
                Array.set col arg (Some Pink)
              else if c = Pink then
                Array.set col arg (Some White)
              else
                raise (ColorError "update3")
           | None -> ()
         end
      | _ -> ()
    ) code

let regs_of_function (f : coq_function) : Regset.t =
  List.fold_left (fun acc param -> Regset.add param acc)
    (PTree.fold (fun acc _ instr -> Regset.union acc @@ instr_regs instr)
       f.fn_code Regset.empty) f.fn_params

(** Initialize nodes' colorings. The entry point assigns White to the
    function's parameters. Unsafe instructions assign White to their
    arguments. Votes assign Red, Green, and Blue to their
    arguments. Smove argument colors are left unspecified, to be
    inferred by the dataflow analysis. *)
let init_cols (f : coq_function) : color option Array.t Array.t =
  let instrs = List.map (fun (p, instr) ->
                   (convert_positive p, convert_instr instr)
                 ) @@ PTree.elements f.fn_code in
  let num_instrs = List.length instrs in
  let num_regs = (list_max @@ List.map convert_positive @@
                   Regset.elements @@ regs_of_function f) + 1 in
  (* print_endline @@ "num_instrs = " ^ string_of_int num_instrs; *)
  (* print_endline @@ "num_regs = " ^ string_of_int num_regs; *)
  let cols = Array.init num_instrs
               (fun _ -> Array.init num_regs
                           (fun _ -> None)) in
  let entrypoint_col = Array.get cols @@ convert_positive f.fn_entrypoint in
  List.iter (fun param ->
      Array.set entrypoint_col (convert_positive param) (Some White)
    ) f.fn_params;
  List.iter (fun (n, instr) ->
      let col = Array.get cols n in
      match instr with
      | Inop' _ -> ()
      | Iop' (op, args, _, _) ->
         if is_protectedb op then
           List.iter (fun arg -> Array.set col arg (Some White)) args
      | Iload' (_, _, args, _, _) ->
         List.iter (fun arg -> Array.set col arg (Some White)) args
      | Istore' (_, _, args, src, _) ->
         List.iter (fun arg -> Array.set col arg (Some White)) args;
         Array.set col src (Some White)
      | Icall' (_, fn, args, _, _) -> begin
          List.iter (fun arg -> Array.set col arg (Some White)) args;
          match fn with
          | Coq_inl r -> Array.set col r (Some White)
          | Coq_inr _ -> ()
        end
      | Itailcall' (_, fn, args) -> begin
          List.iter (fun arg -> Array.set col arg (Some White)) args;
          match fn with
          | Coq_inl r -> Array.set col r (Some White)
          | Coq_inr _ -> ()
        end
      | Ibuiltin' (ef, bargs, bres, _) ->
         if is_smove_builtinb ef then
           ()
         else if is_vote_builtinb ef then
           match bargs with
           | [BA arg1; BA arg2; BA arg3] ->
              Array.set col arg1 (Some Red);
              Array.set col arg2 (Some Green);
              Array.set col arg3 (Some Blue)
           | _ ->
              raise (ColorError "Invalid arguments to vote builtin")
         else
           let regs = List.concat_map regs_of_builtin_arg bargs in
           List.iter (fun r -> Array.set col r (Some White)) regs;
           Array.set col res (Some White)
      | Icond' (_, args, _, _) ->
         List.iter (fun arg -> Array.set col arg (Some White)) args
      | Ijumptable' (arg, _) ->
         Array.set col arg (Some White)
      | Ireturn' ro -> match ro with
                       | Some r -> Array.set col r (Some White)
                       | None -> ()
    ) instrs;
  cols

let nodes_in_code (c : code) : node list = List.map fst (PTree.elements c)

let nodes_in_order (f : coq_function) : int list =
  List.sort (fun x y -> if x > y then 1 else 0) @@
    List.map convert_positive @@ nodes_in_code f.fn_code

let string_of_instruction : instruction' -> string = function
  | Inop' succ -> "Inop' " ^ string_of_int succ
  | Ibuiltin' (ef, _bargs, _bres, succ) ->
     "Ibuiltin' " ^ string_of_int succ
  | _ -> "TODO"

let ptree_of_array (m : 'a option Array.t) : 'a PTree.t =
  Array.fold_left
    (fun acc (i, o) -> match o with
                       | Some a ->
                          PTree.set (convert_int i) a acc
                       | None -> acc)
    PTree.Empty
    (Array.mapi (fun i a -> (i, a)) m)

let copy (cols : 'a Array.t Array.t) : 'a Array.t Array.t =
  Array.init (Array.length cols) (fun i -> Array.copy cols.(i))

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
  (* let pred_map = build_pred_map f.fn_code in *)
  (* let nodes_instrs = *)
  (*   List.map (fun n -> (n, convert_instr @@ Option.get @@ *)
  (*                            PTree.get (positive_of_int n) f.fn_code)) @@ *)
  (*     nodes_in_order f in *)
  (* let nodes_instrs_rev = List.rev nodes_instrs in *)
  List.iter (fun n -> print_endline @@ string_of_int n) @@ nodes_in_order f;
  let code = List.map (fun n ->
                 (n, convert_instr @@ Option.get @@
                       PTree.get (convert_int n) f.fn_code)
               ) @@ nodes_in_order f in
  let code_rev = List.rev code in
  let all_regs = List.map convert_positive @@
                   Regset.elements @@ regs_of_function f in
  (* List.iter (fun r -> print_string @@ string_of_int r ^ " ") all_regs; *)
  (* print_newline (); *)
  let rec go (cols : color option Array.t Array.t) : color option Array.t Array.t =
    let new_cols = copy cols in
    print_cols new_cols; print_newline ();
    print_endline "update1";
    update code new_cols;
    print_cols new_cols; print_newline ();
    print_endline "update2";
    update2 all_regs code_rev new_cols;
    print_cols new_cols; print_newline ();
    print_endline "update3";
    update3 code_rev new_cols;
    print_cols new_cols; print_newline ();
    if new_cols = cols then new_cols else go new_cols
  in
  let start_time = Unix.gettimeofday () in
  let init = init_cols f in
  (* print_cols f init; print_newline (); *)
  let m = go init in
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
  let final_cols = Array.map ptree_of_array m in
  Some (fun n -> let ix = convert_positive n in
                 if ix < Array.length final_cols then
                   Array.get final_cols ix
                 else
                   PTree.Empty)
  (*    Some (fun n -> Option.value ~default:PTree.Empty @@ *)
  (*                     Intmap.find_opt (int_of_positive n) final_cols) *)
  (* | None -> print_endline "color inference failed!"; *)
  (*           None *)
