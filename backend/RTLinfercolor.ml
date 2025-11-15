open AST
open Datatypes
open Maps
open RTL
open RTLcolor

(* Parameter infer_coloring : function -> option (node -> PTree.t color). *)

exception ColorError of string

let union (t1 : color PTree.t) (t2 : color PTree.t) : color PTree.t option =
  PTree.fold (fun topt n c ->
      match topt with
      | Some t -> begin
         match PTree.get n t with
         | Some c' -> if c = c' then Some t else None
         | None -> Some (PTree.set n c t)
        end
      | None -> None) t1 (Some t2)

(* let union' (topt1 : color PTree.t option) (topt2 : color PTree.t option) *)
(*     : color PTree.t option = *)
(*   match topt1, topt1 with *)
(*   | Some t1, None -> Some t1 *)
(*   | None, Some t2 -> Some t2 *)
(*   | Some t1, Some t2 -> union t1 t2 *)
(*   | None, None -> None *)

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

let transfer (instr : instruction) (col : color PTree.t) : color PTree.t =
  match instr with
  | Inop _ -> col
  | Iop (op, args, res, _) ->
     if is_unsafeb op then
       PTree.set res White
         (List.fold_left (fun acc arg -> PTree.remove arg acc) col args)
     else
       (* Don't worry about the 'is_basic' constraint here. The color
          checker will check that. Same for equality of colors of
          arguments. We could do a pass in this module at the end to
          check those constraints for debugging purposes. *)
       List.fold_left (fun acc arg -> match PTree.get arg col with
                                      | Some c -> PTree.set res c acc
                                      | None -> acc) col args
  | Iload (_, _, args, res, _) ->
     PTree.set res White
       (List.fold_left (fun acc arg -> PTree.remove arg acc) col args)
  | Istore (_, _, args, dst, _) ->
     PTree.remove dst
       (List.fold_left (fun acc arg -> PTree.remove arg acc) col args)
  | Icall (_, fn, args, res, _) -> begin
      let col' =
        PTree.set res White
          (List.fold_left (fun acc arg -> PTree.remove arg acc) col args) in
      match fn with
      | Coq_inl r -> PTree.remove r col'
      | Coq_inr _ -> col'
    end
  | Itailcall (_, fn, args) -> begin
      let col' =
        List.fold_left (fun acc arg -> PTree.remove arg acc) col args in
      match fn with
      | Coq_inl r -> PTree.remove r col'
      | Coq_inr _ -> col'
    end
  | Ibuiltin (ef, args, res, _) ->
     if is_smove_builtinb ef then
       match args, res with
       | [BA arg], BR res' -> begin
           let col' = PTree.set res' Green (PTree.remove arg col) in
           match PTree.get arg col with
           | Some White -> PTree.set arg Pink col'
           | Some Pink -> PTree.set arg Red col'
           | Some _ -> raise (ColorError "smove arg not White or Pink")
           | None -> col
         end
       | _, _ -> raise (ColorError "invalid argument(s) or res of smove builtin")
     else if is_vote_builtinb ef then
       match args, res with
       | [BA arg1; BA arg2; BA arg3], BR res' ->
          PTree.set res' White
            (List.fold_left (fun acc arg -> PTree.remove arg acc)
               col [arg1; arg2; arg3])
       | _, _ -> raise (ColorError "invalid argument(s) or res of vote builtin")
     else
       let arg_regs = List.concat_map regs_of_builtin_arg args in
       let res_regs = regs_of_builtin_res res in
       List.fold_left (fun acc r -> PTree.set r White acc)
         (List.fold_left (fun acc arg -> PTree.remove arg acc) col arg_regs)
         res_regs
  | Icond (_, args, _, _) ->
     List.fold_left (fun acc arg -> PTree.remove arg acc) col args
  | Ijumptable (arg, _) ->
     PTree.remove arg col
  | Ireturn ro -> match ro with
                  | Some r -> PTree.remove r col
                  | None -> col

(** Check constraints for debugging purposes (the verified checker
    will catch any errors so this is not strictly necessary). *)
let check_code (c : code) (cols : color PTree.t PMap.t) : unit =
  let check_instr = function
    | Inop _ -> ()
    | _ -> () in
  print_endline "checking code...";
  PTree.fold (fun _ _ -> check_instr) c ()

(* let nodes_in_code (c : code) : node list = List.map fst (PTree.elements c) *)

(* let update (c : code) (cols : node -> color PTree.t) *)
(*     : (node -> color PTree.t) option = *)
(*   PTree.fold (fun acc n instr -> *)
(*       match acc, succ_of_instruction instr with *)
(*       | Some f, Some succ -> *)
(*          let col = transfer instr (cols n) in begin *)
(*              match union col (cols succ) with *)
(*              | Some col' -> Some (fun m -> if m = succ then col' else f m) *)
(*              | None -> None *)
(*            end *)
(*       | _, _ -> acc *)
(*     ) c (Some cols) *)

let succs_of_instruction = function
  | Iop (_, _, _, succ) -> [succ]
  | Iload (_, _, _, _, succ) -> [succ]
  | Istore (_, _, _, _, succ) -> [succ]
  | Icall (_, _, _, _, succ) -> [succ]
  | Ibuiltin (_, _, _, succ) -> [succ]
  | Icond (_, _, ifso, ifnot) -> [ifso; ifnot]
  | Ijumptable (_, succs) -> succs
  | _ -> []
  
let update (c : code) (cols : color PTree.t PMap.t)
    : (color PTree.t PMap.t) option =
  (* For each instruction  *)
  PTree.fold (fun acc n instr ->
      match acc with
      | Some m ->
         (* Compute out-coloring via transfer function *)
         let col = transfer instr (PMap.get n cols) in begin
             (* For each successor of the instruction *)
             List.fold_left (fun acc2 succ ->
                 match acc2 with
                 | Some m' -> begin
                     (* Compute union of successor's previous coloring
                        with newly computed out-coloring *)
                     match union col (PMap.get succ cols) with
                     (* If successful, update successor's coloring to
                        the union *)
                     | Some col' ->
                        Some (PMap.set succ col' m')
                     (* Else inference failure *)
                     | _ -> None
                   end
                 | None -> None
               ) (Some m) (succs_of_instruction instr)
                            (* match union col (PMap.get succ cols) with *)
                            (* | Some col' -> Some (PMap.set succ col' m) *)
                            (* | None -> None *)
           end
      | None -> None
    ) c (Some cols)

(* type code = instruction PTree.t *)

(* type coq_function = { fn_sig : signature; fn_params : reg list; *)
(*                       fn_stacksize : coq_Z; fn_code : code; *)
(*                       fn_entrypoint : node } *)

(** Initialize nodes' colorings. The entry point assigns White to the
    function's parameters. Unsafe instructions assign White to their
    arguments. Votes assign Red, Green, and Blue to their
    arguments. Smove argument colors are left unspecified, to be
    inferred by the dataflow analysis. *)
let init_cols (f : coq_function) : color PTree.t PMap.t =
  let init_col = function
    | Inop _ -> PTree.Empty
    | _ -> PTree.Empty (* TODO *)
  in
  (* Initial colorings for all nodes *)
  let cols = PTree.fold (fun acc n instr -> PMap.set n (init_col instr) acc)
               f.fn_code (PMap.init PTree.Empty) in
  (* Set params to White at entry point *)
  PMap.set f.fn_entrypoint
    (List.fold_left
       (fun t param -> PTree.set param White t)
       PTree.Empty
       f.fn_params)
    cols

let infer_coloring (f : coq_function) : (node -> color PTree.t) option =
  let rec go (cols : color PTree.t PMap.t) : color PTree.t PMap.t option =
    match update f.fn_code cols with
    | Some cols' -> if cols = cols' then Some cols' else go cols'
    | None -> None
  in
  match go (init_cols f) with
  | Some m -> check_code f.fn_code m;
              Some (fun n -> PMap.get n m)
  | None -> None
