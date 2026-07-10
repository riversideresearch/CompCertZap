(* open AST *)
open BinNums
(* open Datatypes *)
open FaultPolicy
(* open SharedFaultPolicy *)
open Maps
(* open Op *)
open Registers
open LTL
open RTLcolor
open Locations
open Machregs
open AST
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



type loc =
    | R' of mreg
    | S' of slot * int * typ

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

(** Union-find implementation literally copy/pasted from Google AI *)
type uf_node = {
    mutable parent : uf_node;
    mutable rank : int;
}

(* Create a new disjoint set for a given value *)
let make () = 
    let rec node = { parent = node; rank = 0 } in
    node

(* Find the representative (root) of the set containiing of given node,
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



(* Array of array of hashtables *)
let init_cols (f : coq_function) (live : Locset.t List.t PMap.t) : (Locations.loc, uf_node) Hashtbl.t Array.t Array.t =
    let num_bb = List.length (PTree.elements f.fn_code) in
    Array.init num_bb (fun n ->
        let inl = List.length (PMap.get (convert_int n) live) in
        Array.init inl (fun _ -> Hashtbl.create 100)
    )


let print_instr (instr : instruction) =
  match instr with
  | Lop _ -> print_endline "Iop"
  | Lload _ -> print_endline "Iload"
  | Lstore _ -> print_endline "Istore"
  | Lcall _ -> print_endline "Icall"
  | Ltailcall _ -> print_endline "Itailcall"
  | Lbuiltin _ -> print_endline "Ibuiltin"
  | Lcond _ -> print_endline "Icond"
  | Ljumptable _ -> print_endline "Ijumptable"
  | Lreturn -> print_endline "Ireturn"
  | Lgetstack _ -> print_endline "Igetstack"
  | Lsetstack _ -> print_endline "Isetstack"
  | Lbranch _ -> print_endline "Ibranch"

let print_pc (f : coq_function) : unit =
    List.iter
        (fun (pc, bb) ->
            Printf.printf "Instrucion label: %d\n" (int_of_positive pc)
            (* List.iter  *)
                (* (fun ( instr) ->  *)
                (*     print_instr instr) bb *)
            )
        (PTree.elements f.fn_code)

(* visited set *)
let get (col : (Locations.loc, uf_node) Hashtbl.t) (r : Locations.loc) : uf_node =
    match Hashtbl.find_opt col r with
    | Some n -> n
    | None -> let n = make () in Hashtbl.add col r n; n



let instr_constraints 
        (instr : instruction) (live : Locations.loc List.t)
        (cols : (Locations.loc, uf_node) Hashtbl.t Array.t Array.t) (pc : int) (index : int) : unit =
    let col = Array.get (Array.get cols pc) index in
    match instr with
    | Lop (op, args, res) ->
        let succ_col = Array.get (Array.get cols pc) (index + 1) in
        if is_protectedb op then begin
            List.iter (fun arg -> union (get col (Locations.R arg)) white) args;
            union (get succ_col (Locations.R res)) white;
            List.iter (fun  r ->
                match r with
                | Locations.R reg ->
                    if not (reg = res || List.mem reg args) then
                        union (get col r) (get succ_col r)
                | Locations.S _ ->
                        union (get col r) (get succ_col r)
            ) live;
        end
        else begin
            let res_color = get succ_col (Locations.R res) in
            List.iter (fun arg -> union (get col (Locations.R arg)) res_color) args;
            List.iter (fun r ->
                match r with
                | Locations.R reg ->
                    if reg <> res then
                        union (get col r) (get succ_col r)
                | Locations.S _ ->
                        union (get col r) (get succ_col r)
            ) live
        end
    | Lload (chunk, addr, args, dst) ->
        let succ_col = Array.get (Array.get cols pc) (index + 1) in
        List.iter (fun arg -> union (get col (Locations.R arg)) white) args;
        union (get succ_col (Locations.R dst)) white;
        List.iter (fun r ->
            match r with
            | Locations.R reg ->
                if not (reg = dst || List.mem reg args) then
                    union (get col r) (get succ_col r)
            | Locations.S _ ->
                    union (get col r) (get succ_col r)

        ) live
    | _ -> ()

    (* | Lload (chunk, addr, args, dst) -> *)
    (*     let succ_col = Array.get (Array.get cols (convert_positive pc)) (index + 1) in *)
    (* | Lgetstack (sl, ofs, ty, dst) -> *)
    (* | Lsetstack (src, sl, ofs, ty) -> *)
    (* | Lstore (chunk, addr, args, src) -> *)
    (* | Lcall (sg, ros) -> *)
    (* | Ltailcall (sg, ros) -> *)
    (* | Lbuiltin (ef, args, res) -> *)
    (* | Lbranch (s) -> *)
    (* | Lcond (cond, args, s1, s2) -> *)
    (* | Ljumptable (arg, tbl) -> *)
    (* | Lreturn *)



let transf_instr_constraints 
        (bb : instruction List.t) (llive : Locset.t List.t PMap.t)
        (cols : (Locations.loc, uf_node) Hashtbl.t Array.t Array.t) (pc : positive) : unit =
    List.iteri (fun i instr ->
        let pc' = convert_positive pc in
        instr_constraints instr (Locset.elements (List.nth (PMap.get pc llive) i)) cols pc' i
    ) bb


        

let function_constraints 
        (f : coq_function) (llive : Locset.t List.t PMap.t) 
        (cols : (Locations.loc, uf_node) Hashtbl.t Array.t Array.t) : unit =
    PTree.fold (fun acc n bb ->
        (* let n' = convert_positive n in *)
        transf_instr_constraints bb llive cols n
    ) f.fn_code ()



let infer_coloring (f : coq_function) (live : Locset.t List.t PMap.t)
    : (node -> reg -> color) option =

        (* let start_time = Unix.gettimeofday () in *)
        (* let cols = init_cols f in *)

        let cols = init_cols f live in
        function_constraints f live cols;
        let _ = print_pc f in

        Some (fun n r -> Red)
