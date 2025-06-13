=========================
Inter-function control flow
=========================

An internal function's *signature* records its argument and result types as well as details relevant to calling it (such as varargs and whether it returns a struct).

Given a function's signature, we aim to compute its precondition and postcondition.
This enables us to

- **Check functions.**
	To check an internal function, the fault checker may assume the function's precondition and must ensure that if the function returns, it establishes its postcondition.
- **Check inter-function control flow instructions.**
	When checking internal function call instructions, the fault checker must ensure that the current symbolic state implies that function's precondition and can assume the function's postcondition.


CompCert tracks function signatures for us.
In its model of RISC-V assembly, for example, the indirect call instruction instructions ``Pj_r`` and ``Pjal_r`` carry a signature:

.. _call_instructions:
.. code-block:: coq

	(* riscV/Asm.v *)
	Inductive instruction : Type :=
	| ⋯
	| Pj_s    (symb: ident) (sg: signature)           (**r jump to symbol *)
	| Pj_r    (r: ireg)     (sg: signature)           (**r jump register *)
	| Pjal_s  (symb: ident) (sg: signature)           (**r jump-and-link symbol *)
	| Pjal_r  (r: ireg)     (sg: signature)           (**r jump-and-link register *)


.. _conventions:
Calling conventions
====================

Signatures determine *calling conventions* which specify the architecture- and ABI-specific locations (stack slots and machine registers) used during internal function calls.

We summarize CompCert's (implicit) interface for calling conventions.
Concrete conventions (e.g., riscV/Conventions1.v or x86/Conventions1.v) follow the interface.
Generic definitions and lemmas building on the interface start in backend/Conventions.v.

The interface depends on a few auxiliary types:

- Machine registers ``mreg`` are those registers targeted by register allocation (ruling out reserved registers like PC, SP, and TMP).
- Register pairs ``rpair A`` comprise either a single register of type A or a pair of high and low registers.
- Locations ``loc`` comprise either a machine register or a stack slot.



.. _loc_arguments:
Argument locations
-------------------

The stack slots here are from a *caller's* point of view.

.. code-block:: coq

	(** [loc_arguments s] returns the list of locations where to store arguments
		when calling a function with signature [s].  *)
	Definition loc_arguments (s: signature) : list (rpair loc).

	(** Argument locations are either non-temporary registers or [Outgoing]
		stack slots at nonnegative offsets. *)
	Definition loc_argument_acceptable (l: loc) : Prop :=
		match l with
		| R r => is_callee_save r = false
		| S Outgoing ofs ty => ofs >= 0 /\ (typealign ty | ofs)
		| _ => False
		end.

	Lemma loc_arguments_acceptable:
		forall (s: signature) (p: rpair loc),
		In p (loc_arguments s) -> forall_rpair loc_argument_acceptable p.

	Lemma loc_arguments_main:
		loc_arguments signature_main = nil.

.. loc_result:
Result locations
-----------------

.. code-block:: coq

	(** Location of function result *)
	Definition loc_result (s: signature) : rpair mreg.

	(** The result registers have types compatible with that given in the signature. *)
	Lemma loc_result_type:
		forall sig,
		subtype (proj_sig_res sig) (typ_rpair mreg_type (loc_result sig)) = true.

	(** The result locations are caller-save registers *)
	Lemma loc_result_caller_save:
		forall (s: signature),
		forall_rpair (fun r => is_callee_save r = false) (loc_result s).

	(** If the result is in a pair of registers, those registers are distinct and have type [Tint] at least. *)
	Lemma loc_result_pair:
		forall sg,
		match loc_result sg with
		| One _ => True
		| Twolong r1 r2 =>
				 r1 <> r2 /\ proj_sig_res sg = Tlong
			/\ subtype Tint (mreg_type r1) = true /\ subtype Tint (mreg_type r2) = true
			/\ Archi.ptr64 = false
		end.

	(** The location of the result depends only on the result part of the signature *)
	Lemma loc_result_exten:
		forall s1 s2, s1.(sig_res) = s2.(sig_res) -> loc_result s1 = loc_result s2.

Normalization
--------------

ABIs like x86 use *partial* registers.
CompCert's *normalization* extends these to full registers.

.. code-block:: coq

	Definition parameter_needs_normalization (t: xtype) : bool.
	Definition return_value_needs_normalization (t: xtype) : bool.

Preconditions
==============

To build the precondition for a function signature ``s``, we use :ref:`loc_arguments`:

- Quantify over a symbolic state :math:`\state` comprising a symbolic memory :math:`\mem`, a symbolic register file :math:`\rs`, and a symbolic color assignment :math:`\color`.

- Fold over the argument locations :math:`\loc` in ``loc_arguments s`` (accumulating a predicate ``pred``)

	- Assume :math:`\color[\loc] = \red` (see the following note)

	- If :math:`\loc` has the form ``S Outgoing i t`` (= caller argument slot :math:`i` of type :math:`t`),

		- Quantify over a value :math:`v`
		- Assume :math:`v : t` (reflecting ``Val.has_type v t`` in the logic)
		- Assume :math:`\mem_t[\rs[\SP] + a + 4i] = v` where :math:`a` is ``fe_ofs_arg``

	- if :math:`\loc` has the form ``R mr`` (= a machine register)

		- Let :math:`r` be ``preg_of mr``
		- Quantify over a value :math:`v`
		- Assume :math:`\rs[r] = v`

	- If :math:`\loc` has any other form (impossible, see ``loc_argument_acceptable`` in :ref:`conventions`),

		- Assume :math:`\bot`


.. note::
	- We do not need to sanity check :math:`r` in the register case.
		Machine registers exclude reserved registers like PC and SP.

	- We only need to color machine registers.
		The replication pass does not "see" other registers, and cannot protect them.

	- We only need to color *local* stack slots.
		We presently use CompCert's calling convention.
		Incoming and outgoing slots are aways red.

Postconditions
===============


.. attention::
	Post-conditions matter for JAL instructions.
	They are also relevant to external function and builtin calls.
	The judgment, ``external_call`` produces a *new* memory.
	(The RISC-V assembler semantics takes care of side-effects on the register file.)
	Presumably the theory of ``external_call`` spells out some nice properties relating the memories before and after the call.

	The caller needs to know that

	- The caller's outgoing and local stack slots have been preserved.

	- For every result location in ``loc_result s``, the location (1) is red and (2) contains an existentially quantified value.

	- The register file has been preserved, modulo

		- registers in ``loc_result s``,

		- for builtins, registers destroyed by the builtin (now ``Vundef``), and

		- for external calls, all caller save registers (now ``Vundef``).

	On RISC-V, "returns" are jumps to the link register RA.
	Suppose we have a post-condition :math:`Q`.
	A function's precondition will involve

		- Quantifying over a predicate :math:`\Psi` on abstract states
		- Quantifying over a value :math:`v`
		- Assuming :math:`v : \text{Tptr}`
		- Assuming :math:`\rs[\RA] = v`
		- Assuming :math:`\forall s, Q s \to \Psi s`


Internal, builtin, and external functions
==========================================

Flesh out the fault checking rules for

- :ref:`call instructions<call_instructions>`,
- builtin functions, and
- external functions.

The latter two have dedicated rules in the operational semantics.
