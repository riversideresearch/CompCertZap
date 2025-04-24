***WIP.***
Dave is still working on this draft.
In addition to a few TODOs below, he wants to think more about equations between values and join points.
(We may need something more heavy handed than dataflow analyses.)

The older, flawed draft is [20250425_fault_tolerance.md](./20250425_fault_tolerance.md).




We aim to check some invariants:

- (EnoughReplication, informally) All computations for a color depend only on
shared state (outside our fault model) and on values of that color.
This ensures that there's enough redundnacy, i.e., that a fault in one
color's computation does not impact any other color's computation.

- (ObserveVotes, informally) Majority votes guard any values flowing into control
flow instructions and stores to (volatile) shared memory. (Stores to
spilled stack slots need not be guarded by majority votes.) This helps
ensure that despite faults, we preserve behavior.

- (ValueAgreement, informally) The values flowing into majory votes agree modulo
at most one fault. This helps ensure that despite faults, we preserve
behavior.





# Replication Maps

To support our invariants, we aim to construct a PC-relative
replication map of the form `location -fin-> location * location`
where `location` accounts for (1) stack slots and (2) registers
covered by replication:
```
Variant location : Type :=
| R (_ : mreg)
| S (_ : ptrofs) (_ : typ).
```

The following registers are shared resources and occur neither in the
domain nor the codomain of a replication map.

- X0 always reads zero.

- PC, RA (link register), SP, GP (global pointer), TP (thread pointer)
are shared resources.

- FP (frame pointer) is a shared resource that may house junk. Any
color can initialize it to non-junk (a pointer into the caller's
activation record).

- TMP (CompCert temporary) is a shared resource that may be used by at
most one color at a time.

Unlike the rest, FP is an `mreg` and could conceivably be relevant to the replication pass, followed by register allocation.
The register allocator and Mach semantics treat it specially.



# Using replication maps to check invariants


With a PC-relative replication map in hand, we can refine our invariants:

(EnoughReplication) From a replication map, we can read off the color
of any location used or defined at a given PC and check that all
"computation" instructions use only shared state and locations of a
single color and define only locations of that color.

(ObserveVotes) This is orthogonal. (In fact majory votes help us to infer
replication maps.)

(ValueAgreement, very rough) If `rm # r = (g, b)`, then

- If we have not faulted, `!r = !g = !b`

- If we have faulted, `!r = !g` or `!r = !b` or `!g = !b`

If it helps, we could imagine switching from a majority vote primitive
to a `sync r, g, b` primitive with post-condition `!r = !g = !b`.


**TODO:**
One plausible approach to value agreement:
Use a dataflow analysis to define a set of equations between values (more likely: symbolic expressions) that must hold at each program point.

- Necula's work on symbolic evaluation seems relevant (see his translation validation paper and PhD dissertation).
- So do the "static expressions" tied to value typing in the FT TAL paper.
- Keywords for other potentially related work include common subexpression elimination (CSE) and global value numbering (GVN).
	We could perhaps reuse setup in CompCert's CSE, dead code elimination, or constant propagation passes.






# Abstract syntax for dataflow analysis


We aim to define replication maps using a dataflow analysis over an abstract syntax for an internal function's code.
The intent is to "read off" the abstract syntax by pattern matching on the code.

We list some constructors for our `abstract_instruction` type.
For now, even ostensibly trivial, non-branching constructors carry a successor `s : node` representing the next instruction in the control flow graph.



Required:

- Simplify stack access instruction sequences.

	The aim is to reverse [Asmgen](./riscV/Asmgen.v)'s translations of stack loads and stores, recovering a location-based interface analogous to [Mach](./backend/Mach.v)'s:

	```
	(*
	Callee's activation record: Load or store from offset [ofs * 4]
	relative to SP.
	*)
	| Agetstack (ofs : ptrofs) (ty : typ) (dst : mreg) (_ : node)
	| Asetstack (src : mreg) (ofs : ptrofs) (ty : typ) (_ : node)

	(*
	Caller's activation record: Load from offset [ofs * 4] relative to
	the pointer at function-specific offset `f_link_ofs` from SP.
	(This encapsulates most uses of FP.)
	*)
	| Agetparam (ofs : ptrofs) (ty : typ) (dst : mreg) (_ : node)
	```


- Simplify Smoves and majoriy votes.

	The aim is to hide our encodings of these operations as type-specific builtins:

	```
	| Asmove (ty : typ) (r dest : mreg) (_ : node)
	| Amaj_vote (ty : typ) (r g b dest : mreg) (_ : node)
	```


Probably optional:

- Speak in terms of locations (and machine registers `mreg`) to
highlight state impacted by the replication pass




# Building a replication map


Key ideas:

- A few registers are invisible to the RTL-level replication pass.
These are shared state (= limitations of fault tolerance). Examples:
SP, FP, TMP.

- All other registers have at most one color at a time and their
PC-relative color must be inferred.

- Stack slots have colors that are invariant throughout the function's
code but that generally must be inferred.\
**TODO:** This presupposes the register allocator does not coalesce stack slots.


We expect to track constraints on values and constraints on the replication map.
We can express constraints on colors in terms of contraints on the replication map:
A replication map `rm` makes a locaton red, green, or blue according to `rm # red = (green, blue)`.


Inference is informed by:

- A load from the caller's activation record `Agetparam ofs ty dst s` constrains values `!S ofs ty = !R dst` and the replication map `color(S ofs ty) = red = color(R dst)`.

- A store to the callee's activation record `Asetstack src ofs ty s` constrains values `!R src = !S src ofs ty` and the replication map `color(R src) = color(S ofs ty)`.

- A load from the callee's activation record `Agetstack ofs ty dst s` constrains values `!S ofs ty = !R dst` and the replication map `color(S ofs ty) = color(R dst)`.

- A function's parameter register `r` constrains the replication map at the function's entry point `color(R r) = red`.


- A majority vote `Amaj_vote ty r g b dest s` constrains the replication map `color(R r) = red`, `color(R g) = green`, `color(R b) = blue`.
	It also constrains values, but the equations are complicated.

	**TODO:**
	The `sync r g b` primitive might be nicer here in part because it dispenses with the `dest` register.
	We could learn after `sync` that `!r = !g = !b` rather than a disjunction of value equations.
	Before sync, either there has been no fault and the same equations hold
	or there has been a fault and we have the disjunction `!r = !g = !b \/ !r = !g \/ !r = !b \/ !g = !b`.

- An smove `Asmove ty r dest s` constrains the replication map `color(R r) = red`, `color(R dest) \in {blue, green}` and values `!r = !dest`.

	**TODO:**
	Either `smove r g b` (writing to both `g` and `b`)
	or `smove_{G+B} r, dest` (writing to `dest` while specifying its color)
	might be nicer here to avoid the disjunction.







# Background on the stack



[LTL](./backend/LTL.v) extends load/store ops with stack slots:
```
Inductive instruction: Type :=
	| Lgetstack (sl: slot) (ofs: Z) (ty: typ) (dst: mreg)
	| Lsetstack (src: mreg) (sl: slot) (ofs: Z) (ty: typ)
Definition bblock := list instruction.
Definition code: Type := PTree.t bblock.
```

The triples in these instructions correspond to data carried by stack _locations_ (cf [Locations](./backend/Locations.v)):
```
Inductive slot: Type := Local | Incoming | Outgoing.
Inductive loc : Type := R (r: mreg) | S (sl: slot) (pos: Z) (ty: typ).
```



[Linear](./backend/Linear.v) drops CFGs in favor of labels and operations like `Lgoto`, preserving LTL's treatment of the stack.
```
Inductive instruction: Type :=
	| Lgetstack: slot -> Z -> typ -> mreg -> instruction
	| Lsetstack: mreg -> slot -> Z -> typ -> instruction
Definition code: Type := list instruction.
```




[Mach](./backend/Mach.v) switches to memory-based stack operations:
```
Inductive instruction: Type :=
	(*
	Callee's activation record: Load or store from offset [ofs * 4]
	relative to the stack pointer.
	*)
	| Mgetstack (ofs : ptrofs) (ty : typ) (dst : mreg)
	| Msetstack (src : mreg) (ofs : ptrofs) (ty : typ)

	(*
	Caller's activation record: Load from offset [ofs * 4] relative to
	the pointer at function-specific offset `f_link_ofs` from the stack
	pointer.
	*)
	| Mgetparam (ofs : ptrofs) (ty : typ) (dst : mreg)
Definition code := list instruction.
```


RISC-V [Asm](./riscV/Asm.v), of course, has only loads and stores.
The translation from Mach to Asm, [Asmgen](./riscV/Asmgen.v), tracks statically whether the frame pointer is definitely valid.
When the frame pointer is valid, it caches the caller's stack pointer (at offset `fn_link_ofs` from the stack pointer).
The translation of `Mgetparam` uses this validity bit (`ep`) to emit code that sets FP if necessary, and loads relative to FP.
```
Definition transl_instr (f: Mach.function) (i: Mach.instruction)
		(ep: bool) (k: code) : res (list instruction) :=
	match i with
	| Mgetstack ofs ty dst => loadind SP ofs ty dst k
	| Msetstack src ofs ty => storeind src SP ofs ty k
	| Mgetparam ofs ty dst =>
			(* load via the frame pointer if it is valid *)
			do c <- loadind X30 ofs ty dst k;
			OK (
				if ep then c
				else loadind_ptr SP f.(fn_link_ofs) X30 c
			)
```
Both `loadind` and `storeind` boil down to several possible instruction sequences depending on the type and the size of the offset.
`loadind_ptr` is similar but "knows" the type is either a 64- or 32-bit integer.
