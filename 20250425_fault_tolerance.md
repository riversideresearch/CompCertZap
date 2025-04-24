***This is too simplistic.***

A. To prove that if a fault checker succeeds on a program, then that program is fault tolerant, we will likely need a stronger rule for majority votes than we get simply from assigning colors.

B. The abstract state for a register file (colors, replication maps, whatever) must be PC-relative.
At the assembler level, registers serve different purposes at different program points.




# Overview

We intend to use translation validation to prove [fault tolerance](./riscV/Tolerant.v) for programs produced with our replication pass.

These notes sketch two decision procedures:

- Given an internal function and an assignment of colors to registers for that function, does the function's code respect that assignment?

- Given an internal function, infer a suitable color assignment.

We can lift these from functions to programs.
Ultimately we intend to prove that if a program is "OK" according to these decision procedures, then it is fault tolerant.

***Two or one?***
We describe two decision procedures for clarity, but we can likely get by with just one.
The implementation should do whatever simplifies the fault tolerance proof the most.



# Typing, not Dataflow

We cannot readily use CompCert's dataflow analyses for assembler code.
At the assembler level, we have `code := list instruction`.
Kildall's algorithm assumes a CFG, i.e., `code := PTree.t instruction`.

This isn't really a blocker.
We could presumably build a CFG with a prepass over a function's code.

We _can_ type check the code.


# Spilled registers

We may eventually want to address the following TODO (from [our fault model](./riscV/Fault.v#88)).

> Stores to stack slots that arise from spilling a temporary probably
> tolerate faults. They don't show up in the trace. Modulo assumptions
> about coalescing stack slots, they are unique per redundant
> computation.

To address it, we could probably color not just registers but also stack slots.





# Declarative typing rules


Judgments

- `r : c` means that register `r` has color `c`.
(The other judgments are parametric in an assignment of colors to registers.
A register may have at most one color in a typing derivation.)

- `i OK` means that instruction `i` is well-formed.

- `code OK` means that the instruction sequence `code` is well-formed.




***Per-function color assignments.***
To keep [color inference](#colorinference) efficient, we want to infer colors for one function body at a time.
Therefore, our type system covers only the code _inside_ an internal function and we have to worry seperately about "calling conventions".
It would be catastrophic, for example, if we allowed function A to call function B passing it an argument register `r` where A assumes register r is green while B assumes r is red.
Our type system should be sound for function calls because of its rules for conditional and computed branch instructions, Pallocframe, and Pfreeframe.
(Roughly, registers that inform control flow and activation records must be red.)
Those rules deserve careful scrutiny.



## Registers

To account for registers, we need two kinds of axioms:

1. <a name="safe"></a>Registers considered by replication (e.g., general purpose integer registers) can be assigned any color.

2. <a name="unsafe"></a>Registers not considered by replication must be red (e.g., the frame pointer and PC).

Each internal function has an (inferred) assignment of colors to registers, i.e., a finite map satisfying [(1)](#safe), [(2)](#unsafe).

Typing rules for instructions and code are parametric in a color assignment.


***Type-preserving compilation.***
Notice that (1) could be strengthened.
A function's argument registers, for example, are red while their replicas must be blue or green.
If we had a replication map on hand, we could use it to "read off" a color assignment roughly as follows.
```
	Fixpoint colormap_of_replmap (rm : replmap) (dom : list reg) (acc : colormap) : colormap :=
		match dom with
		| [] => acc
		| r1 :: dom =>
			let '(r2, r3) := rm#r1 in
			let acc := colormap_of_replmap rm dom acc in
			let acc := Colormap.set r1 red acc in
			let acc := Colormap.set r2 green acc in
			let acc := Colormap.set r3 blue acc in
			acc
		end.
```





## Code

To account for code we need only one rule:
```
	Forall (fun i => i OK) code
	----
	code OK
```
It says that every instruction in the code is compatible with the ambient color assignment.





## Instructions

For most instructions, we can define typing rules based on the instruction's [`tolerance`](./riscV/Fault.v#103) as assigned by our fault model.

The exceptions are instructions that mediate "color boundaries"---smoves and majority votes.

Roughly, we want:
```
	src : red
	dest : c
	c != red	(optional)
	--- smove
	smove(src, dest)

	r1 : red
	r2 : green
	r3 : blue
	dest : c
	c = red	(optional)
	--- maj_vote
	maj_vote(r1, r2, r3, dest)
```

The actual rules will be a bit uglier due to how things are represented.
Examples:
```
	lookup_builtin_function name sg = BI_replicate BI_smove_long
	src : red
	dest : c
	----- 64-bit integer smove
	Pbuiltin (EF_runtime name sg) [BA src] (BR dest) OK

	lookup_builtin_function name sg = BI_replicate BI_vote_long
	r1 : red
	r2 : green
	r3 : blue
	dest : c
	----- 64-bit integer majority vote
	Pbuiltin (EF_runtime name sg) [BA r1; BA r2; BA r3] (BR dest) OK
```

This rule for `smove(src, dest)` happens to agree with the rule we'd get by "reading off" a rule based on the instruction's tolerance `IntolerantOn [src]`.
Treating smove specially alongside majority vote matters only for clarity.





### Tolerant instructions

The typing rules for `Tolerant` instructions insist that all argument and result registers have the same color, but they do not constrain that color.

Examples:
```
	Forall (fun r => r : c) (res :: args)
	----- Tolerant Instruction Tempalte
	instr args, res OK


	dest : c
	src : c
	----- 64-bit integer additon
	Paddil dest src imm OK

```




### Intolerant instructions

The typing rules for `Intolerant` instructions insist that all argument and result registers are `red`.

This covers standard builtins and external functions and is forced by CompCert traces.

Examples:
```
	Forall (fun r => r : red) (res :: args)
	----- Intolerant Instruction Template
	instr args, res OK


	bargs = BA <$> args
	bdest = BR dest
	Forall (fun r => r : red) (dest :: args)
	--- External function calls
	Pbuiltin (EF_external _ _) bargs bdest OK
```




### IntolerantOn instructions

The typing rules for `IntolerantOn (regs : list reg)` instructions insist that registers in `regs` are red and that all other argument and result registers agree on some color.

This covers some conditional branches, indirect jumps, stores, Pallocframe (which fiddles with function parameter registers), and Pbtbl (which hides an indirect jump).

Examples:
```
	Forall (fun r => r : red) regs
	Forall (fun r => r : c) ((res :: args) \ regs)
	----- `IntolerantOn regs` Instruction Template
	instr args, res OK


	r : red
	--- Indirect jump
	Pj_r r _ : OK
```




# <a name="colorinference"></a>Color inference

Given an internal function, we want to infer an assignment of colors to registers that's consistent with [(1)](#safe), [(2)](#unsafe).

It's probably simplest to use a variation on the declarative typing rules, leaving existential color choices to unification.
It looks like we can use CompCert's [unification constraint solver](./common/Unityping.v).
