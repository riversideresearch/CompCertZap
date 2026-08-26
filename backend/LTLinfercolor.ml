(* open AST *)
open BinNums
open Datatypes
open FaultPolicy
open SharedFaultPolicy
open Maps

(* open Op *)
(* open Registers *)
open LTL

(* open LTLcolor *)
open Locations
open Machregs
open AST
open Conventions1
(* open Op *)

exception ColorError of string

(* type instruction = *)
(* | Lop of operation * mreg list * mreg *)
(* | Lload of memory_chunk * addressing * mreg list * mreg *)
(* | Lgetstack of slot * coq_Z * typ * mreg *)
(* | Lsetstack of mreg * slot * coq_Z * typ *)
(* | Lstore of memory_chunk * addressing * mreg list * mreg *)
(* | Lcall of signature * (mreg, ident) sum *)
(* | Ltailcall of signature * (mreg, ident) sum *)
(* | Lbuiltin of external_function * loc builtin_arg list * mreg builtin_res *)
(* | Lbranch of node *)
(* | Lcond of condition * mreg list * node * node *)
(* | Ljumptable of mreg * node list *)
(* | Lreturn *)

let rec int_of_nat = function
  | Datatypes.O -> 0
  | Datatypes.S n -> 1 + int_of_nat n

type loc = R' of mreg | S' of slot * int * typ

let rec int_of_positive = function
  | Coq_xI p -> (2 * int_of_positive p) + 1
  | Coq_xO p -> 2 * int_of_positive p
  | Coq_xH -> 1

let positive_of_int (i : int) : positive =
  if i < 1 then
    raise
      (ColorError
         ("positive_of_int: int must be positive, got " ^ string_of_int i))
  else
    let rec go (j : int) : positive =
      if j == 1 then Coq_xH
      else if j mod 2 == 0 then Coq_xO (go @@ (j / 2))
      else Coq_xI (go @@ (j / 2))
    in
    go i

let convert_positive (p : positive) : int = int_of_positive p - 1
let convert_int (i : int) : positive = positive_of_int (i + 1)

type uf_node = { mutable parent : uf_node; mutable rank : int }
(** Union-find implementation literally copy/pasted from Google AI *)

(* Create a new disjoint set for a given value *)
let make () =
  let rec node = { parent = node; rank = 0 } in
  node

(* Find the representative (root) of the set containiing of given node,
   with path compression *)
let rec find node =
  if node.parent == node then node
  else begin
    node.parent <- find node.parent;
    (* Path compression *)
    node.parent
  end

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

let union node1 node2 =
  let root1 = find node1 in
  let root2 = find node2 in
  if root1 != root2 then begin
    let is_red r = r == find red
    and is_green r = r == find green
    and is_blue r = r == find blue
    and is_white r = r == find white
    and is_pink r = r == find pink in
    let is_base r =
      is_red r || is_green r || is_blue r || is_white r || is_pink r
    in
    if is_base root1 && is_base root2 then
      Printf.printf "MERGE: root1=%s root2=%s\n%!" (string_of_uf_node root1)
        (string_of_uf_node root2);
    if root1.rank < root2.rank then root1.parent <- root2
    else if root1.rank > root2.rank then root2.parent <- root1
    else begin
      root2.parent <- root1;
      root1.rank <- root1.rank + 1
    end
  end

let loc_name = function
  | Locations.R r -> (
      match Machregsnames.name_of_register r with Some s -> s | None -> "?")
  | Locations.S _ -> "stack"

(* union_labeled (lbl "vote arg1->red") (loc_name arg1) (get col arg1) red; *)

let union_labeled label loc_str node1 node2 =
  let r1_before = find node1 and r2_before = find node2 in
  union node1 node2;
  if r1_before != r2_before then
    Printf.printf "  ^ triggered by: %s [loc=%s]\n%!" label (loc_name loc_str)

(* Unions two sets by rank *)
(* let union node1 node2 =  *)
(*     let root1 = find node1 in  *)
(*     let root2 = find node2 in  *)
(*     if root1 != root2 then begin *)
(*         if root1.rank < root2.rank then *)
(*             root1.parent <- root2 *)
(*         else if root1.rank > root2.rank then *)
(*             root2.parent <- root1 *)
(*         else begin *)
(*             root2.parent <- root1; *)
(*             root1.rank <- root1.rank + 1 *)
(*         end *)
(*     end *)

(** End copy/pasted union-find *)

(* let eq node1 node2 = find node1 == find node2 *)
(**)
(* let red = make () *)
(* let green = make () *)
(* let blue = make () *)
(* let white = make () *)
(* let pink = make () *)
(**)
(* let string_of_uf_node n =  *)
(*     if eq n red then "R" *)
(*     else if eq n green then "G" *)
(*     else if eq n blue then "B" *)
(*     else if eq n white then "W" *)
(*     else if eq n pink then "P" *)
(*     else "X" *)

(* Array of array of hashtables *)
let init_cols (f : coq_function) (live : (nat * Locset.t) List.t PMap.t) :
    (Locations.loc, uf_node) Hashtbl.t Array.t Array.t =
  let num_bb = List.length (PTree.elements f.fn_code) in
  Array.init num_bb (fun n ->
      let inl = List.length (PMap.get (convert_int n) live) in
      Array.init inl (fun _ -> Hashtbl.create 100))

let print_instr (instr : instruction) =
  match instr with
  | Lop _ -> print_endline "Lop"
  | Lload _ -> print_endline "Lload"
  | Lsmove _ -> print_endline "Lsmove"
  | Lstore _ -> print_endline "Lstore"
  | Lcall _ -> print_endline "Lcall"
  | Ltailcall _ -> print_endline "Ltailcall"
  | Lbuiltin _ -> print_endline "Lbuiltin"
  | Lcond _ -> print_endline "Lcond"
  | Ljumptable _ -> print_endline "Ljumptable"
  | Lreturn -> print_endline "Lreturn"
  | Lgetstack _ -> print_endline "Lgetstack"
  | Lsetstack _ -> print_endline "Lsetstack"
  | Lbranch _ -> print_endline "Lbranch"

let print_pc (f : coq_function) : unit =
  List.iter
    (fun (pc, bb) ->
      Printf.printf "Instrucion label: %d\n" (int_of_positive pc);
      List.iter (fun instr -> print_instr instr) bb)
    (PTree.elements f.fn_code)

(* visited set *)
let get (col : (Locations.loc, uf_node) Hashtbl.t) (r : Locations.loc) : uf_node
    =
  match Hashtbl.find_opt col r with
  | Some n -> n
  | None ->
      let n = make () in
      Hashtbl.add col r n;
      n

let process_loc (l : Locations.loc) (col : (Locations.loc, uf_node) Hashtbl.t) :
    unit =
  match l with
  | Locations.R r -> union (get col (Locations.R r)) white
  | Locations.S (sl, ofs, ty) as s -> union (get col s) white

let process_args (rp : 'a rpair List.t) : Locations.loc List.t =
  List.fold_left
    (fun acc x ->
      match x with One l -> l :: acc | Twolong (l, l') -> l :: l' :: acc)
    [] rp

let rec regs_of_builtin_res = function
  | BR r -> [ r ]
  | BR_none -> []
  | BR_splitlong (hi, lo) ->
      app (regs_of_builtin_res hi) (regs_of_builtin_res lo)

let rec regs_of_builtin_arg = function
  | BA r -> r :: []
  | BA_splitlong (hi, lo) ->
      app (regs_of_builtin_arg hi) (regs_of_builtin_arg lo)
  | BA_addptr (a1, a2) -> app (regs_of_builtin_arg a1) (regs_of_builtin_arg a2)
  | _ -> []

let instr_constraints (instr : instruction) (bb : instruction list)
    (live : Locations.loc List.t)
    (cols : (Locations.loc, uf_node) Hashtbl.t Array.t Array.t) (pc : int)
    (index : int) : unit =
  let col = Array.get (Array.get cols pc) index in

  let lbl s = Printf.sprintf "%s @ pc=%d idx=%d" s pc index in
  match instr with
  | Lop (op, args, res) ->
      let succ_col = Array.get (Array.get cols pc) (index + 1) in
      if is_protectedb op then begin
        List.iter
          (fun arg ->
            union_labeled
              (lbl "Lop-protected arg->white")
              (Locations.R arg)
              (get col (Locations.R arg))
              white)
          args;
        union_labeled
          (lbl "Lop-protected res->white")
          (Locations.R res)
          (get succ_col (Locations.R res))
          white;
        List.iter
          (fun r ->
            match r with
            | Locations.R reg ->
                if not (reg = res || List.mem reg args) then
                  union (get col r) (get succ_col r)
            | Locations.S _ -> union (get col r) (get succ_col r))
          live
      end
      else begin
        let res_color = get succ_col (Locations.R res) in
        List.iter (fun arg -> union (get col (Locations.R arg)) res_color) args;
        List.iter
          (fun r ->
            match r with
            | Locations.R reg ->
                if reg <> res then union (get col r) (get succ_col r)
            | Locations.S _ -> union (get col r) (get succ_col r))
          live
      end
  | Lload (chunk, addr, args, dst) ->
      let succ_col = Array.get (Array.get cols pc) (index + 1) in
      List.iter
        (fun arg ->
          union_labeled (lbl "Lload arg->white") (Locations.R arg)
            (get col (Locations.R arg))
            white)
        args;
      union_labeled (lbl "Lload dst->white") (Locations.R dst)
        (get succ_col (Locations.R dst))
        white;
      List.iter
        (fun r ->
          match r with
          | Locations.R reg ->
              if not (reg = dst || List.mem reg args) then
                union (get col r) (get succ_col r)
          | Locations.S _ -> union (get col r) (get succ_col r))
        live
  | Lsmove (scol, src, dst) ->
      let succ_col = Array.get (Array.get cols pc) (index + 1) in
      if scol = LTL.Green then (
        union_labeled (lbl "Lsmove-green src->white") src (get col src) white;
        union_labeled
          (lbl "Lsmove-green src'->pink")
          src (get succ_col src) pink;
        union_labeled
          (lbl "Lsmove-green dst->green")
          dst (get succ_col dst) green;

        List.iter
          (fun r ->
            if not (r = src || r = dst) then union (get col r) (get succ_col r))
          live)
      else if scol = LTL.Blue then (
        union_labeled (lbl "Lsmove-blue src->pink") src (get col src) pink;
        union_labeled (lbl "Lsmove-blue src'->red") src (get succ_col src) red;
        union_labeled (lbl "Lsmove-blue dst->blue") dst (get succ_col dst) blue;
        List.iter
          (fun r ->
            if not (r = src || r = dst) then union (get col r) (get succ_col r))
          live)
      else if scol = LTL.White then (
        union_labeled (lbl "Lsmove-white src->white") src (get col src) white;
        union_labeled
          (lbl "Lsmove-white dst->white [col, NOT succ_col]")
          dst (get succ_col dst) white;

        List.iter
          (fun r ->
            if not (r = dst || r = src) then union (get col r) (get succ_col r))
          live)
      else ()
  | Lgetstack (sl, ofs, ty, dst) ->
      let succ_col = Array.get (Array.get cols pc) (index + 1) in
      let s = Locations.S (sl, ofs, ty) in
      if sl = Locations.Local then
        union
          (get succ_col (Locations.R dst))
          (get col (Locations.S (sl, ofs, ty)))
      else if sl = Locations.Incoming then
        union_labeled
          (lbl "Lgetstack-incoming dst->white")
          (Locations.R dst)
          (get succ_col (Locations.R dst))
          white
      else ();

      List.iter
        (fun r ->
          match r with
          | Locations.R reg ->
              if not (Locations.R reg = Locations.R dst) then
                union (get col r) (get succ_col r)
          | Locations.S (sl, ofs, ty) as s' ->
              if not (s = s') then union (get col r) (get succ_col r))
        live
  | Lsetstack (src, sl, ofs, ty) ->
      let succ_col = Array.get (Array.get cols pc) (index + 1) in
      let s = Locations.S (sl, ofs, ty) in
      if sl = Locations.Local then
        union
          (get succ_col (Locations.S (sl, ofs, ty)))
          (get col (Locations.R src))
      else if sl = Locations.Outgoing then
        union_labeled
          (lbl "Lsetstack-outgoing slot->white")
          (Locations.S (sl, ofs, ty))
          (get succ_col (Locations.S (sl, ofs, ty)))
          white
      else ();

      List.iter
        (fun r ->
          match r with
          | Locations.R reg ->
              if not (Locations.R reg = Locations.R src) then
                union (get col r) (get succ_col r)
          | Locations.S (sl, ofs, ty) as s' ->
              if not (s = s') then union (get col r) (get succ_col r))
        live
  | Lstore (chunk, addr, args, src) ->
      let succ_col = Array.get (Array.get cols pc) (index + 1) in
      union_labeled (lbl "Lstore src->white") (Locations.R src)
        (get col (Locations.R src))
        white;

      List.iter
        (fun arg ->
          union_labeled (lbl "Lstore arg->white") (Locations.R arg)
            (get col (Locations.R arg))
            white)
        args;
      List.iter
        (fun r ->
          match r with
          | Locations.R reg ->
              if not (reg = src || List.mem reg args) then
                union (get col r) (get succ_col r)
          | Locations.S _ -> union (get col r) (get succ_col r))
        live
  | Lcall (sg, ros) ->
      let succ_col = Array.get (Array.get cols pc) (index + 1) in
      let args = process_args (loc_arguments sg) in
      let res = loc_result sg in
      List.iter (fun lp -> process_loc lp col) args;
      (match res with
      | One l ->
          union_labeled (lbl "Lcall res->white") (Locations.R l)
            (get succ_col (Locations.R l))
            white
      | Twolong (l, l') ->
          union_labeled
            (lbl "Lcall res(hi)->white")
            (Locations.R l)
            (get succ_col (Locations.R l))
            white;
          union_labeled
            (lbl "Lcall res(lo)->white")
            (Locations.R l')
            (get succ_col (Locations.R l'))
            white);

      (match ros with
      | Coq_inl r ->
          union_labeled (lbl "Lcall ros->white") (Locations.R r)
            (get col (Locations.R r)) white
      | Coq_inr _ -> ());
      List.iter
        (fun r ->
          match r with
          | Locations.R reg ->
              if
                not
                  (match res with
                  | One l -> reg = l
                  | Twolong (l, l') -> (
                      reg = l || reg = l'
                      || List.mem (Locations.R reg) args
                      ||
                      match ros with
                      | Coq_inl reg' -> reg = reg'
                      | Coq_inr _ -> false))
              then union (get col r) (get succ_col r)
          | Locations.S (sl, ofs, ty) as s ->
              if not (List.mem s args) then union (get col r) (get succ_col r))
        live
  | Ltailcall (sg, ros) -> (
      let args = process_args (loc_arguments sg) in
      List.iter
        (fun arg ->
          union_labeled (lbl "Ltailcall arg->white") arg (get col arg) white)
        args;
      match ros with
      | Coq_inl r ->
          union_labeled
            (lbl "Ltailcall ros->white")
            (Locations.R r) (get col (Locations.R r)) white
      | Coq_inr _ -> ())
  | Lbuiltin (ef, args, res) ->
      let succ_col = Array.get (Array.get cols pc) (index + 1) in
      if is_vote_builtinb ef then
        match (args, res) with
        | [ BA arg1; BA arg2; BA arg3 ], BR res ->
            union_labeled (lbl "vote arg1->red") arg1 (get col arg1) red;
            union_labeled (lbl "vote arg2->green") arg2 (get col arg2) green;
            union_labeled (lbl "vote arg3->blue") arg3 (get col arg3) blue;
            union_labeled (lbl "vote res->white") (Locations.R res)
              (get succ_col (Locations.R res))
              white;
            List.iter
              (fun r ->
                if r <> Locations.R res then union (get col r) (get succ_col r))
              live
        | _ -> ()
      else if builtin_can_replicate ef then (
        match res with
        | BR res' ->
            let res_color = get succ_col (Locations.R res') in
            let arg_regs = List.concat_map regs_of_builtin_arg args in
            List.iter (fun arg -> union (get col arg) res_color) arg_regs;
            List.iter
              (fun r ->
                if r <> Locations.R res' then union (get col r) (get succ_col r))
              live
        | _ ->
            let arg_regs = List.concat_map regs_of_builtin_arg args in
            let res_regs = regs_of_builtin_res res in
            List.iter
              (fun arg ->
                union_labeled
                  (lbl "builtin-replicate arg->white")
                  arg (get col arg) white)
              arg_regs;
            List.iter
              (fun res ->
                union_labeled
                  (lbl "builtin-replicate res->white")
                  (Locations.R res)
                  (get succ_col (Locations.R res))
                  white)
              res_regs;

            List.iter
              (fun r ->
                match r with
                | Locations.R reg ->
                    if not (List.mem r arg_regs || List.mem reg res_regs) then
                      union (get col r) (get succ_col r)
                | Locations.S (sl, ofs, ty) as s ->
                    if not (List.mem s arg_regs) then
                      union (get col r) (get succ_col r))
              live)
      else
        let arg_regs = List.concat_map regs_of_builtin_arg args in
        let res_regs = regs_of_builtin_res res in
        List.iter
          (fun arg ->
            union_labeled (lbl "builtin arg->white") arg (get col arg) white)
          arg_regs;
        List.iter
          (fun res ->
            union_labeled (lbl "builtin res->white") (Locations.R res)
              (get succ_col (Locations.R res))
              white)
          res_regs;
        List.iter
          (fun r ->
            match r with
            | Locations.R reg ->
                if not (List.mem r arg_regs || List.mem reg res_regs) then
                  union (get col r) (get succ_col r)
            | Locations.S (sl, ofs, ty) as s ->
                if not (List.mem s arg_regs) then
                  union (get col r) (get succ_col r))
          live
  | Lcond (cond, args, s1, s2) ->
      let ifso_col = Array.get (Array.get cols (convert_positive s1)) 0 in
      let ifnot_col = Array.get (Array.get cols (convert_positive s2)) 0 in
      List.iter
        (fun arg ->
          union_labeled (lbl "Lcond arg->white") (Locations.R arg)
            (get col (Locations.R arg))
            white)
        args;
      List.iter
        (fun r ->
          match r with
          | Locations.R reg ->
              if not (List.mem reg args) then begin
                union (get col r) (get ifso_col r);
                union (get col r) (get ifnot_col r)
              end
          | Locations.S _ ->
              union (get col r) (get ifso_col r);
              union (get col r) (get ifnot_col r))
        live
  | Ljumptable (arg, tbl) ->
      union_labeled
        (lbl "Ljumptable arg->white")
        (Locations.R arg)
        (get col (Locations.R arg))
        white;

      List.iter
        (fun r ->
          match r with
          | Locations.R reg ->
              if reg <> arg then
                List.iter
                  (fun succ ->
                    let succ_col =
                      Array.get (Array.get cols (convert_positive succ)) 0
                    in
                    union (get col r) (get succ_col r))
                  tbl
          | Locations.S _ -> ())
        live
  | Lbranch node ->
      let succ_col = Array.get (Array.get cols (convert_positive node)) 0 in

      List.iter (fun r -> union (get col r) (get succ_col r)) live
  | Lreturn -> ()

let transf_instr_constraints (bb : instruction List.t)
    (llive : (nat * Locset.t) List.t PMap.t)
    (cols : (Locations.loc, uf_node) Hashtbl.t Array.t Array.t) (pc : positive)
    : unit =
  List.iteri
    (fun i instr ->
      let pc' = convert_positive pc in
      instr_constraints instr bb
        (Locset.elements (snd (List.nth (PMap.get pc llive) i)))
        cols pc' i)
    bb

let function_constraints (f : coq_function)
    (llive : (nat * Locset.t) List.t PMap.t)
    (cols : (Locations.loc, uf_node) Hashtbl.t Array.t Array.t) : unit =
  (* params *)
  (* An extra cases check on the stack locations to check if its an incoming slot
    * before setting to white... but might not be loc_arguments should return args needed
    * based on the convention (assumption)
     *)
  let params = process_args (loc_arguments f.fn_sig) in
  List.iter
    (fun param ->
      union
        (get
           (Array.get (Array.get cols (convert_positive f.fn_entrypoint)) 0)
           param)
        white)
    params;

  (* code *)
  PTree.fold
    (fun acc n bb ->
      (* let n' = convert_positive n in *)
      transf_instr_constraints bb llive cols n)
    f.fn_code ()

let color_of_uf_node n =
  if eq n red then Red
  else if eq n green then Green
  else if eq n blue then Blue
  else if eq n white then White
  else if eq n pink then Pink
  (* Unconstrained classes default to Red in the exported coloring. *)
    else Red

let infer_coloring (f : coq_function) (live : (nat * Locset.t) List.t PMap.t) :
    (node -> nat -> Locations.loc -> color) option =
  let start_time = Unix.gettimeofday () in
  (* let cols = init_cols f in *)

  let cols = init_cols f live in
  function_constraints f live cols;

  (* --- debug: check whether the five base colors have collapsed --- *)
  Printf.printf "red=green: %b\n" (eq red green);
  Printf.printf "red=blue: %b\n" (eq red blue);
  Printf.printf "red=white: %b\n" (eq red white);
  Printf.printf "red=pink: %b\n" (eq red pink);
  Printf.printf "green=blue: %b\n" (eq green blue);
  Printf.printf "green=white: %b\n" (eq green white);
  Printf.printf "green=pink: %b\n" (eq green pink);
  Printf.printf "blue=white: %b\n" (eq blue white);
  Printf.printf "blue=pink: %b\n" (eq blue pink);
  Printf.printf "white=pink: %b\n" (eq white pink);
  (* --- end debug --- *)
  (* let _ = print_pc f in *)
  let end_time = Unix.gettimeofday () in
  print_endline @@ "  Time = " ^ string_of_float (end_time -. start_time) ^ " s";
  Printf.printf "***************************\n";

  Some
    (fun p i ->
      let px = convert_positive p in
      let ix = int_of_nat i in

      let b_cols = Array.length (Array.get cols px) in
      (* Printf.printf "index val: %d\n" ix; *)
      let i_col = Array.get (Array.get cols px) (ix - 1) in
      if ix - 1 < b_cols then fun r ->
        match Hashtbl.find_opt i_col r with
        | Some n ->
            (* Printf.printf "pc %d; instr index: %d\n" (px + 1) (ix - 1); *)
            (* Printf.printf "uf_node returned: %s\n" (string_of_uf_node n); *)
            color_of_uf_node n
        | None ->
            (* Printf.printf "pc %d; instr index: %d\n" (px + 1) (ix - 1); *)
            (* Printf.printf "uf_node returned: Red-> unconstrained\n"; *)
            Red
      else fun r -> Red)
