This document assumes knowledge of the TMR pass (votes and smoves) and its soundness proof.

The implementation described here is in the `fault-tolerance-backward-sim2-union-find` branch of our CompCert fork.

# Fault Tolerance

A program is fault tolerant if it behaves the same under a faulty semantics as under the usual non-faulty semantics. Or in other words, faults will not manifest as errors. Our current "faulty semantics" implements a single-fault model in which the destination register of some instructions can be "zapped" nondeterministically to have its contents replaced by an arbitrary value. We prove that programs compiled by ccomp with the `-tmr` flag are fault tolerant wrt this fault model.

# Proving Fault Tolerance

Our strategy for proving fault tolerance of compiled programs is to decompose the property into two smaller properties: agreement and separation. Intuitively, agreement means that the arguments to majority votes are equal, and separation means that they are produced by independent computations. Together, these two properties imply fault tolerance.

agreement /\ separation => fault tolerance

For proving agreement and separation, we use a different strategy for each:
1) agreement is guaranteed by construction by soundness of the TMR replication pass
2) separation is established a posteriori by a verified checker for a color system. Well-colored programs are those whose computations and votes do not mix colors.

# RTL Proof of Concept

The current development is a proof of concept in which fault tolerance is proved at the level of the RTL intermediate representation, prior to register allocation. Essentially we are proving "if you use a truncated version of ccomp that just outputs RTL, if the RTL output passes the color checker then when you run it in a faulty RTL machine it will behave correctly despite the presence of faults". Extension to the level of asm is possible; it is mostly a matter of implementing a color checker for the backend of choice. See ref:TODO.

The CompCert compiler is a function `transf_c_program` (defined in `driver/Compiler.v`) that transforms a CompCert C program into an assembly program. We define a truncated version of this function called `transf_c_program_to_rtl` that stops right before register allocation, producing an RTL program.

We include two extra passes at the end of the usual RTL pipeline: 1) a "Novotes" pass that checks that the program contains no vote builtins to begin with (rejecting the program if it does), and 2) the TMR replication pass that inserts redundant computations and votes for combining them.

Currently the color checker is not included formally in the pipeline. It is inserted as a check in `driver/Driver.ml` on the intermediate RTL before final conversion to assembly.

## Fault model

The faulty semantics is
1) a state wrapper type that augments RTL.state with a fault bit representing whether a fault has occured yet, and
2) an inductive step relation that wraps the usual RTL.step relation. CallStates and ReturnStates step as normal without changing the fault bit. Normal (function internal) states may have their result register zapped.

```coq
Record fstate : Type :=
  mkfstate { fs_state : RTL.state
           ; fault : bool }.

Inductive fstep : fstate -> trace -> fstate -> Prop :=
| fstep_step_State : forall stk f sp pc rs m t s' s'' b b'
    (STEP: RTL.step ge (State stk f sp pc rs m) t s')
    (ZAP: maybe_zap f pc s' b s'' b'),
    fstep
      {| fs_state := State stk f sp pc rs m; fault := b |}
      t
      {| fs_state := s''; fault := b' |}
| fstep_step_other :
    (* allow other states to step normally without changing fault bit *)
```

`maybe_zap` encodes the nonderministic possibility of zapping the result register, resulting in a new RTL state and fault bit recording that the fault occured. Only some instructions are allowed to have their results zapped; this is how we encode the limitations of the fault protection. If a fault were to occur on a disallowed, our inserted redundancy may not prevent it from manifesting as an error.

```coq
(* Technically we could/should allow faults (and not vote on) on most builtins, just not external function calls or votes themselves. *)
Definition zap_allowed (i : instruction) : Prop :=
  match i with
  | Iop op _ _ _ => ~ is_protected op
  | Iload _ _ _ _ _ => False
  | Istore _ _ _ _ _ => False
  | Icall _ _ _ _ _ => False
  | Itailcall _ _ _ => False
  | Ibuiltin _ _ _ _ => False
  | _ => True
  end.

Inductive maybe_zap (f : function) (pc : node)
  : RTL.state -> bool -> RTL.state -> bool -> Prop :=
| maybe_zap_refl : forall s b, maybe_zap f pc s b s b
| maybe_zap_reg : forall stk sp pc' rs m i r v,
    val_compat (rs # r) v ->
    f.(fn_code) ! pc = Some i ->
    zap_allowed i ->
    res_of_instruction i = Some r ->
    maybe_zap f pc
      (State stk f sp pc' rs m) false
      (State stk f sp pc' (rs # r <- v) m) true.
```

`val_compat` asserts that two values are "compatible", i.e., built using the same constructor (or Vundef on the LHS). It is similar to `Val.lessdef` except it doesn't require defined values to be equal.
```coq
Inductive val_compat : val -> val -> Prop :=
| val_compat_undef : forall v, val_compat Vundef v
| val_compat_int : forall i j, val_compat (Vint i) (Vint j)
| val_compat_long : forall i j, val_compat (Vlong i) (Vlong j)
| val_compat_float : forall x y, val_compat (Vfloat x) (Vfloat y)
| val_compat_single : forall x y, val_compat (Vsingle x) (Vsingle y)
| val_compat_ptr : forall b1 b2 ofs1 ofs2, val_compat (Vptr b1 ofs1) (Vptr b2 ofs2).
```

## 2- and 3-voting

We have two versions of each majority vote primitive: 2-vote and 3-vote. 2-voting has the usual semantics: as long as two arguments are equal, the result is equal to them, otherwise the result is undefined. 3-voting is more strict: it requires that all three arguments be equal for the result to be defined.

3-voting was introduced as a technical device for the faulty simulation proof (see ref:TODO). It does incur a cost: the language semantics of every intermediate representation is parameterized by vote type which can be either `Two` or `Three`. The only place it makes a difference is in the semantics of vote builtins, where either 2-voting or 3-voting semantics is chosen depending on the vote type parameter. We use a VoteSemantics typeclass to avoid explicit passing of the vote type parameter, so in the end we just have to wrap all the semantics definitions in a Section like:
```coq
Section VOTE.
Context {VT: Builtins2.vote_type} {vsem: Builtins2.VoteSemantics VT}.
(* original definitions/code *)
End VOTE.
```

The typeclass and its instances for vote types `Two` and `Three` are defined as follows:
```coq
Record vote_sems : Type :=
  { vote_sem_int : builtin_sem Xint
  ; vote_sem_long : builtin_sem Xlong
  ; vote_sem_single : builtin_sem Xsingle
  ; vote_sem_float : builtin_sem Xfloat
  }.

Inductive vote_type : Type :=
| Two
| Three.

Definition vote_type_sem (vty: vote_type) : vote_sems :=
  match vty with
  | Two   => (* ... *)
  | Three => (* ... *)
  end.

(* When all three arguments are equal, the output is equal to them. *)
Definition vote_sem_ok {tret: xtype} (sem : builtin_sem tret) : Prop :=
  forall a, Val.has_rettype a tret -> sem.(bs_sem _) [a; a; a] = Some a.

Class VoteSemantics (vty : vote_type) : Prop :=
  { vote_sem_int_ok : vote_sem_ok (vote_type_sem vty).(vote_sem_int)
  ; vote_sem_long_ok : vote_sem_ok (vote_type_sem vty).(vote_sem_long)
  ; vote_sem_single_ok : vote_sem_ok (vote_type_sem vty).(vote_sem_single)
  ; vote_sem_float_ok : vote_sem_ok (vote_type_sem vty).(vote_sem_float)
  }.

Program Instance VoteSemantics_Two : VoteSemantics Two.
(* ... *)
Program Instance VoteSemantics_Three : VoteSemantics Three.
(* ... *)
```

The faulty semantics described in the previous section is not parameterized by vote type; it is hardcoded to 2-vote semantics.

# Refinement and Semantic Preservation

## Refinement
In general, a program `p2` in language `L2` refines the semantics of program `p1` in language `L1` if for every behavior `beh2` of `p2`, there exists a behavior `beh1` of `p1` that is improved by `beh2`. A bit more formally:
```coq
forall beh2,
  program_behaves (L2.semantics p2) beh2 ->
  exists beh1, program_behaves (L1.semantics p1) beh1 /\ behavior_improves beh1 beh2.
```

A translation function `f` is semantics preserving if for any program `p`, the translation `f p` refines `p`.

Refinement is implied by backward simulation. Both refinement and backward simulation are existing notions in CompCert, and the main high-level compiler correctness theorem of CompCert is expressed as semantic preservation of `transf_c_program` (see Theorem `transf_c_program_preservation` in `driver/Complements.v`).

## Semantic Preservation Under Faults

Our main fault tolerance theorem is a modified preservation theorem that targets the faulty semantics. Roughly:
```
forall p beh2,
  well_colored p ->
  program_behaves (RTL.faulty_semantics (compile p)) beh2 ->
  exists beh1, program_behaves (RTL.semantics p) beh1 /\ behavior_improves beh1 beh2.
```

See `transf_c_program_to_rtl_preservation_faulty` in `driver/Complements.v` for the real thing.

We prove this theorem by composition of refinements. See ref:TODO for details.

# Agreement

Intuitively, "agreement" means that the argument values to every vote instruction are always equal. We could express this as something like: for every initial state `s0` and state `s` such that the program star-steps from `s0` to `s` and in `s` the current instruction is a vote with argument registers `r1` `r2` and `r3`, the values of those registers in the register state of `s` are equal.

However, this characterization of agreement is not preserved by refinement. So while we can obtain it by construction immediately post-TMR pass (and thus use it in the RTL-level fault tolerance proof), we can't transport it down to asm through CompCert's existing refinement proofs.

Fortunately, it also turns out to be stronger than necessary, and there is a weaker notion of agreement that is sufficient for our purposes:
```coq
Definition rtl_weak_agreement :=
    forall beh,
      program_behaves rtl_sem2 beh ->
      program_behaves rtl_sem3 beh.
```
where rtl_sem2 is the usual RTL semantics with 2-voting, and rtl_sem3 is the same with 3-voting. This notion of agreement is strictly weaker because it allows for vote arguments to be unequal if the results of those votes don't affect observable behavior (e.g., are ignored or masked in some way). Thus we call it "weak agreement" and the former stronger variant "strong agreement".

Weak agreement is preserved by forward simulation (see `forward_simulation_preserves_weak_agreement` in `x86/Asmagreement.v` for a proof of this fact wrt. refinement from RTL to X86). However, we don't need to use this fact directly because we can express it more conveniently as a refinement property:

```coq
Definition rtl_weak_agreement' :=
  forall beh3, program_behaves rtl_sem3 beh3 ->
    exists beh2, program_behaves rtl_sem2 beh2 /\ behavior_improves beh2 beh3.
```

This is the form used in the proofs, because it plugs in naturally to the composition of refinements that make up the overall semantic preservation proof.

# Color System

A "coloring" of a function is an assignment of colors to registers at each point in the function. More concretely: for an RTL function, a coloring `col : node -> reg -> option color` maps each instruction label (`node`) to a partial map from registers to colors.

The well-colored judgment (i.e., the property checked by the color checker) asserts that a program is well-colored wrt a given coloring The coloring is assumed to be provided. The declarative/relational specification of the well-colored judgment is defined in `backend/RTLcolor.v`.

There are five distinct colors:
```coq
Inductive color : Type :=
| Red
| Green
| Blue
| White
| Pink.
```

Red, green, and blue are the basic colors used to distinguish and separate redundant computations. White is in one sense the color of the results of majority votes, but more generally it means "not protected against faults". The immediate result of a majority vote is colored White because if that vote instruction were to be faulted causing its result value to be corrupted, the program would not be able to recover because the result is not protected by TMR. This is true not only for votes, but all function calls in general (for now at least since we aren't replicating function parameters); the result of a function call is White until its value has been propagated to shadow copies by smoves.

The color rule for majority votes is approximately:
```
col pc arg1 = Red /\
col pc arg2 = Green /\
col pc arg3 = Blue /\
col succ res = White
____________________________________________  C-vote
pc |-> (res := vote(arg1, arg2, arg3), succ)
```
where `col pc arg1 = Red` means that the color of register `arg1` at instruction label `pc` is Red. `pc |-> (res := vote(arg1, arg2, arg3), succ)` means that the instruction at label `pc` is the vote instruction with successor label `succ`. 

A typical majority vote generated by the TMR pass has the form `r1 := vote(r1, r2, r3)` where the result register is the same as the first argument. `r1` is expected to be Red at `pc`, and White at `succ`. Similarly, arguments to functions are expected to be White (as they are the results of majority votes) temporarily and may become Red again after the function call.

Pink is an intermediate shade between White and Red. When the result of a function call is stored in a white registers, it must be copied by smove instructions to its shadow copies. This happens in two steps:
1) smove from white result to green copy, and change the result register from white to pink,
2) smove from pink result to blue copy, and change the result register from pink to red.

Thus there are two different smove instructions (white smoves and pink smoves), and their color rules are approximately:
```
col pc arg = White /\
col succ arg = Pink /\
col succ res = Green
______________________________________  C-smove-white
pc |-> (res := smove_white(arg), succ)

col pc arg = Pink /\
col succ arg = Red /\
col succ res = Blue
______________________________________  C-smove-pink
pc |-> (res := smove_white(arg), succ)
``` 

## Color Checker

A Boolean decider for the well-colored judgment (i.e., the color checker) is defined in `backend/RTLcolorcheck.v`. It is proved sound wrt the relational judgment:
```coq
Lemma check_program_sound (p : program) :
  check_program p = true -> wc_program p.
```

`check_program` just runs `check_function` on every function of the program, which is where the real work happens:
```coq
Definition check_function (f : function) : bool :=
  match infer_coloring f with
  | None => false
  | Some col => check_col_function col f
  end.
```

`check_function` begins by attempting to synthesize a coloring for the function via `infer_coloring`. If that step succeeds, it proceeds to check well-coloredness wrt the synthesized coloring. `infer_coloring` is not implemented in Coq nor proved correct; it is declared as an axiom in Coq and wired up to an an unverified OCaml implementation in the extracted OCaml code. This is acceptable because we don't actually depend on the correctness of `infer_coloring`; invalid colorings are rejected by the color checker.

## Color Inference

The color inference oracle is implemented in `backend/RTLinfercolor.ml`. It uses a union-find data structure to assign colors to registers, which allows us to efficient compute unions of sets (of registers) and check membership in these sets. Roughly, the algorithm works as follows:
1) Create representative singletons for Red, Blue, Green, White and Pink.
2) Assign unique singletons to every register at every instruction label.
3) Walk the function, unioning registers based on color equality constraints imposed by the instruction coloring rules.

In the end, every register will either have been unioned with one of the representative colors, or be unconstrained (assigned Red by default). If any of the representative colors end up in the same set, the function is not colorable.

This algorithm has good performance even on very large functions. But there is one problem: the assignment of colors to every register at every instruction label in step 2 requires a dense table whose size is roughly quadratic in the size of the function (# instructions, which tends to be in linear proportion to the number of pseudo registers used). This table can be very large for large functions, resulting in prohibitively high memory usage.

### Color Inference Optimization

One may ask: "why do we need to assign colors to every register (that appears in the function), not just the registers that appear in the instruction?". The answer is that there are some additional constraints on the coloring rules that enforce consistency constraints along successor edges (see `wc_instruction` in `backend/RTLcolor.v` for all the coloring rules). Roughly speaking, we require that the colors of all registers other than the arguments or result of an instruction are preserved along the edge to its successor(s), which is necessary to preserve an important invariant in the faulty simulation proof (see ref:TODO).

However, strictly speaking we needn't care about preserving the colors of *all* registers in the function, but only those that are live along the successor edge (i.e., live-out at the current instruction). The invariant used in the faulty simulation proof is thus overly coarse (due to quantifying over all registers in the function) and could be constrained via liveness information. Then we could use a sparse table in the color inference oracle to dramatically reduce memory usage on large functions. The `fault-tolerance-backward-sim2-union-find-liveness` branch of our CompCert fork implements this optimization in the color inference oracle and color checker, but the corresponding changes to the faulty simulation proof are not done yet.

# Faulty Simulation

Given a well-colored program `prog`, we prove a backward simulation from the non-faulty 3-voting semantics of prog (source) to its faulty 2-voting semantics (target):
```coq
Theorem faulty_backward_simulation :
    backward_simulation
      (@RTL.semantics Builtins2.Three VoteSemantics_Three prog)
      (faulty_semantics prog).
```

The proof is lengthy but mostly straightforward, except that the match relation between register states of the two executions uses `Val.lessdef` rather than equality. I.e., we maintain the invariant that for every register `r`, the value of `r` in the non-faulty execution is either undefined or equal to the value `r` in the faulty execution. This is because 2-voting is more permissive than 3-voting in general; when just two arguments are equal, the 3-vote result is undefined but the 2-vote result is defined. And results of such votes can be assigned to registers and propagate throughout the computation arbitarily, so we must allow undefined values to appear anywhere on the 3-voting side.

Since backward simulation implies behavior refinement, we obtain from this theorem the fact that the faulty semantics of well-colored programs refines their non-faulty 3-voting semantics.
```
3-voting non-faulty RTL >= 2-voting faulty RTL
```

# Putting it all together

We prove the main fault tolerance semantic preservation theorem via composition of refinements. To facilitate this, we factor the compiler function `transf_c_program_to_rtl` into two parts:
- `transf_c_program_to_rtl' : Csyntax -> RTL`
  + stops after "Novotes" check
- `transf_rtl_program_to_rtl' : RTL -> RTL`
  + DMR/TMR

This gives us an intermediate RTL program sitting between the Novotes check and TMR insertion, allowing us to bridge the gap between 2-voting and 3-voting that is incurred by the faulty simulation at the end.

2-voting C program >= 2-voting RTL program with no votes                         (1)
                   >= 3-voting RTL program with no votes                         (2)
                   >= 3-voting final RTL program with TMR                        (3)
                   >= 2-voting final RTL program with TMR under faulty semantics (4)

(1) follows from the standard backward simulation up to this point in the pipeline.
(2) follows trivially from weak agreement, which is implied trivially by no_votes.
(3) follows from the standard backward simulation (which we proved separately for the TMR pass)
(4) follows from the faulty simulation, assuming that the program is well-colored

# Extending to asm

Extension to an asm backend is possible due to weak agreement (i.e., refinement of 2-voting semantics by 3-voting semantics) being preserved by CompCert's standard refinement proofs. Thus we get agreement for free, even at the level of asm.

The hard part is extending separation to asm. This will require the color system, color inference/checker, and faulty simulation proofs to be reimplemented for each target backend.

# Catalogue of changes (from notes.md)

- improve/generalize vote builtin definitions in `backend/Builtins2.v`
- prove that RTL semantics is determinate
- vote on 'unsafe' Iops (division, mod, and a couple bit shift ops)
- avoid redundant votes on registers that appear multiple times in argument list
- parameterize all semantics definitions by vote_type (instantiated with either Two or Three, see `backend/Builtins2.v`)
- Alternate compiler pipeline defined in `driver/Compiler.v` that stops after DMR/TMR and renumbering, yielding RTL as output
- Fault tolerance theorem in `driver/Complements.v` wrt. the RTL compiler
- `driver/Driver.v`: run color checker on intermediate RTL before compiling it down to asm
- `extraction/Extraction.v`: add extraction directive to instantiate `RTLcolorcheck.infer_coloring` with `RTLinfercolor.infer_coloring`
  + also tell Coq to extract `RTLcolorcheck.check_program` and `Compiler.transf_c_program_to_rtl` so they can be used in `driver/Driver.v`

- New files
  + `backend/RTLfault.v`: faulty RTL semantics
  + `backend/RTLcolor.v`: declarative specification of RTL color system
  + `backend/RTLcolorcheck.v`: Boolean checker for RTL color system. Assumes oracle for inferring function coloring (map from CFG node to partial map from register to color). Sound but not necessarily complete because nothing is not assumed of the inference oracle (except that it is a pure deterministic function, which is implicitly assumed but we don't actually exploit anyway)
  + `backend/RTLtolerant.v`: proof of backward simulation from 3-voting non-faulty semantics (source) to 2-voting faulty semantics (target). See `Theorem faulty_backward_simulation`
  + `backend/RTLinfercolor.ml`: unverified OCaml code for inferring function colorings. Hodgepodge dataflow analysis with three update functions, one forward and two backward. Probably could be redesigned to use a single unification pass followed by a single forward propagation pass.
  + `backend/RTLagreement.v`: definition of 'weak agreement' for RTL
  + `x86/Asmagreement.v`: definition of 'weak agreement' for x86 asm, and proof that weak agreement is preserved from RTL to asm by forward simulation for safe programs
  + `backend/Novotes.v`: checker for establishing no_votes property on RTL programs.
  + `backend/Novotesproof.v`: definition of no_votes property, and proofs that the no_votes checker is sound wrt. it and that it trivially satisfies a forward simulation (as it doesn't change the program).
