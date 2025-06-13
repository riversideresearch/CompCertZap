============================
Intra-function control flow
============================

.. attention::
	For every replicated location *used* by a basic block:

	- Quantify over a single value
	- Assume all replicas agree on that value (modulo any fault)

	For every shard location *used* by a basic block:

	- Quantify over a single value
	- Remember: The location may be spilled and restored from the stack, but no computation can rely on the value until the location has been replicated with ``smove``

Locally, the fault checker must check that all registers relevant to a branch are either shared (like X0) or red (due to a vote).
This is trivial.

Non-locally, the fault checker must *infer* preconditions for the labels serving as branch targets.
This inference may involve proof search and unification.

- Our RTL replication pass votes on data relevant to *paths* through an internal function's CFG.
	If we're going to branch based on some value :math:`v` stored in some register :math:`d`, then the fault checker may require that we've calculated :math:`v`  using :math:`d \gets \vote(r, g, b)` for some registers :math:`r`, :math:`g`, and :math:`b`.

- All boring computational steps within a basic block have been replicated by our RTL pass.
	These replicated steps have been obscured (through register allocation, etc) but must remain.

- A basic block has a location footprint.
	Each instruction in a basic block *uses* some locations (= inputs) and *defines* some locations (= outputs) and *kills* some locations (= trashed).
	Only *input* locations matter for a basic block's precondition.

- Labels are join points, and we might proceed as in a dataflow analysis.
	For this, we would need to (1) define a join operation on logical state and separately (2) read a precondition off a logical state.
	(This seems easy for symbolic execution.)




.. code-block:: coq

	(* riscV/Asm.v *)
	Inductive instruction : Type :=
	| ⋯
	| Pj_l    (l: label)                              (**r jump to label *)
	| ⋯
	(* Conditional branches, 32-bit comparisons *)
	| Pbeqw   (rs1 rs2: ireg0) (l: label)             (**r branch-if-equal *)
	| Pbnew   (rs1 rs2: ireg0) (l: label)             (**r branch-if-not-equal signed *)
	| Pbltw   (rs1 rs2: ireg0) (l: label)             (**r branch-if-less signed *)
	| Pbltuw  (rs1 rs2: ireg0) (l: label)             (**r branch-if-less unsigned *)
	| Pbgew   (rs1 rs2: ireg0) (l: label)             (**r branch-if-greater-or-equal signed *)
	| Pbgeuw  (rs1 rs2: ireg0) (l: label)             (**r branch-if-greater-or-equal unsigned *)

	(* Conditional branches, 64-bit comparisons *)
	| Pbeql   (rs1 rs2: ireg0) (l: label)             (**r branch-if-equal *)
	| Pbnel   (rs1 rs2: ireg0) (l: label)             (**r branch-if-not-equal signed *)
	| Pbltl   (rs1 rs2: ireg0) (l: label)             (**r branch-if-less signed *)
	| Pbltul  (rs1 rs2: ireg0) (l: label)             (**r branch-if-less unsigned *)
	| Pbgel   (rs1 rs2: ireg0) (l: label)             (**r branch-if-greater-or-equal signed *)
	| Pbgeul  (rs1 rs2: ireg0) (l: label)             (**r branch-if-greater-or-equal unsigned *)







----------------------


CompCert more or less follows the RISC-V ABI.
(There is an exception related to passing FP arguments to variadic functions.
See riscV/Conventions1.v.)

For calling conventions, CompCert
.. math::
	\sp(r \gets E) s := \cdots

We want citations to work, *e.g.,* :cite:`necula2000tv`.


We aim to prove that at each majority vote

.. math::
	d \gets \vote(r,g,b)

the contents of locations :math:`r`, :math:`g`, :math:`b` are identical modulo any fault.


We use *symbolic execution* to build up, between majority votes, a history of each color's computations.

Now we can link to :ref:`signature`.
