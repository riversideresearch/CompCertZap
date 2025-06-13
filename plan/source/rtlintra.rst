================================
RTL intra-function control flow
================================

.. See ../../backend/RTL.v
	and ../../backend/Replicate.v

**Recap.**
Symbolic evaluation for RTL comprises an RTL interpeter working with symbolic state.
A symbolic *state* comprises (among other things for RTL) a symbolic register file and a symbolic memory (expression).
A symbolic *register file* is a finite partial function sending RTL temporaries to symbolic (value) expressions.
Symbolic value and memory *expressions* syntactically denote, respectively, CompCert values and memories as well as operations over those types.

Interpreting RTL using state built up from symbolic values and memories effectively tracks the "history" of a computation syntactically.
This enables, e.g., deciding if the concurrent red, green, and blue threads of a replicated function computed, at each :math:`\vote(r,g,b)` instruction, equal symbolic value expressions in registers :math:`r`, :math:`g`, and :math:`b` (up to a possible fault in one color).
The metatheory for symbolic evaluation will then lift this decidable equality to equality on the values that arise under the faulty and non-faulty semantics.

Branching instructions present a challenge.
Most publications on symbolic evaluation assume annotations in the form of *preconditions* on branch targets.
These are simple FOL assertions defined over symbolic state used to decide if the concrete symbolic state before a branch instruction justifies the branch.

Our aim here is to *infer* suitable preconditions for use by the fault checker.
We sketch only the main ideas.
Separately, we will consider how to reflect those ideas at the level of RISC-V assembler.

**RTL Syntax.**

.. code-block:: coq

	(* backend/RTL.v *)
	Definition node := positive.
	Inductive instruction: Type := (*...*).
	Definition code: Type := PTree.t instruction.

	Definition instr_uses (i: instruction) : list reg.
	Definition instr_defs (i: instruction) : option reg.
	Definition successors_instr (i: instruction) : list node.

	(* backend/Replicate.v *)
	Definition replmap : Type := Regmap.t (reg * reg).


**Register groups.**
Let ``group ::= Rep0 (r : reg) | Rep2 (r g b : reg)`` be the syntactic category of *register groups*.
Group ``Rep0 r`` denotes an unreplicated red register ``r``.
Group ``Rep2 r g b`` denotes a fully replicated triple comprising red register ``r``, green register ``g``, and blue register ``b``.

A register's *contents* start unreplicated.
Special moves set up redundant computation.

.. code-block:: coq

	Variant group : Type :=
	| Rep0 (r : reg)
	| Rep1 (r : reg) (c : color) (x : reg)
	| Rep2 (r g b : reg).

	(*
	Groups must always be compatible with the ambient replication map.
	*)
	Definition group_compat (rm : replmap) (g : group) : Prop :=
		match g with
		| Rep0 r => exists p, rm#r = p
		| Rep1 r G g => exists p, rm#r = p /\ p.1 = g
		| Rep1 r B b => exists p, rm#r = p /\ p.2 = b
		| Rep2 r g b => rm#r = (g, b)
		end.

	Definition fully_replicated_color (x : reg) (g : group) : option color :=
		match g with
		| Rep2 r g b =>
			if reg_eq x r then Some R
			else if reg_eq x g then Some G
			else if reg_eq x b then Some B
			else None
		| Rep0 _ | Rep1 _ _ _ => None
		end.
	(* More liberal variant *)
	Definition replicated_color (x : reg) (g : group) : option color :=
		match g with
		| Rep0 r => if reg_eq x r then Some R
		| Rep1 r c y =>
			if reg_eq x r then Some R
			else if reg_eq x c then Some c
			else None
		| Rep2 r g b =>
			if reg_eq x r then Some R
			else if reg_eq x g then Some G
			else if reg_eq x b then Some B
			else None
		end.

A *grouping* :math:`G` is a finite map from temporaries to their current (compatible) groups.
For dataflow, :math:`\dom G` is the set of registers which have a definite group.
(To forget about a register, we remove it from :math:`G`.)

- The initial grouping for a function sends every temporary :math:`r` in its parameters ``params`` and possibly uninitialized registers ``uregs`` to the unreplicated group ``Rep0 r``.

- :math:`d \gets \smove r`

	- If :math:`r \not\in \dom G`, fail with grouping :math:`\top`
	- If :math:`d \in \dom G`, fail with grouping :math:`\top`
	- If :math:`G(r)` is ``Rep0 r``,

		- Pick the color ``c`` assigned to ``d`` by the replication map's entry for ``r`` (or fail with grouping :math:`\top`)
		- Let ``g := Rep1 r c d``
		- Continue with grouping ``G; r <- g; d <- g``

	- If :math:`G(r)` is ``Rep1 r c_x x``,

		- Pick the color ``c_d`` assigned to ``d`` by the replication map's entry for ``r`` (or fail with grouping :math:`\top`)
		- If :math:`c_x = c_d`, fail with grouping :math:`\top`
		- Let ``(g, b)`` be ``(x,d)`` or ``(d, x)`` according to ``c_x``, ``c_d``
		- Let ``gr := Rep2 r g b``
		- Continue with grouping ``G; r <- gr; g <- gr; b <- gr``

	- If :math:`G(r)` is ``Rep _ _ _``

		- Fail with grouping :math:`\top` (disallow "extra" :math:`\smove`'s)

- :math:`d \gets \vote(r, g, b)`

	- Let ``g_0 := Rep r g b``
	- Fail with grouping :math:`\top` unless :math:`G(r) = G(g) = G(b) = g_0`
	- Let ``g := Rep0 d``
	- Continue with grouping ``G; del r; del g; del b; d <- g``

	.. note::
		In practice, :math:`d = r` but we don't rely on that.

		We transition :math:`r` to the unreplicated group ``Rep0 r`` to ease precondition inference.
		Roughly, a basic block's precondition accounts the *groups* used but not defined in the  block (rather than the registers).
		For each group :math:`g`, we will

		- Assumes :math:`g` is either unreplicated ``Rep0`` or fully replicates ``Rep``
		- Quantifies over a symbolic value :math:`v`
		- Assumes :math:`g \mapsto v`

		We drop :math:`g`, :math:`b` to keep the grouping consistent (feeding the side-condition on :math:`\smove`).


- ``Iop op args dest succ``

	- Fail with grouping :math:`\top` unless there exists a color :math:`c` s.t. ``Forall (fun x : reg => (gr <- G x; fully_replicated_color x gr) = Some c) (dest :: args)``

	.. note::
		This restricts computations to the case that all of ``args`` and ``dest`` are fully replicated and share a color.

		If necessary due to code motion interleaving special moves and computations, we could generalize ``fully_replicated_color`` to ``replicated_color``.

		One can imagine a more aggressive replication pass that emits ``Iop``  to *initialize* replicas (i.e., no prior :math:`\smove`).
		This could presumably be supported with color unification.

-----------

.. note:: Some thoughts.

	- Divide groupings into

		- *global groupings* :math:`G` (``Rep0``, ``Rep2``) which may appear at the boundaries of basic blocks and
		- *local groupings* :math:`L` (``Rep1``) which may appear within a basic block during special moves

	- We defined global groupings in order to succinctly express pre- and post-conditions for basic blocks.
		Next steps:

		- Define ``block_defs`` and ``block_uses`` sending blocks to (global) groupings.

		- Define preconditions in terms of uses.

		- Decide if this apporach scales down to the RISC-V level.
