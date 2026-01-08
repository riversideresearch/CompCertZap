# Changes in this branch
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
  + `backend/Novotes.v`: checker for establishing no_votes property on RTL programs. Not yet implemented
  + `backend/Novotesproof.v`: definition of no_votes property, and proofs that the no_votes checker is sound wrt. it and that it trivially satisfies a forward simulation (as it doesn't change the program). Not yet done

# Notes
- We shouldn't need to actually use preservation of weak agreement directly (thus we shouldn't need to assume safety of the source program) if we just compose behavioral refinement at the right places (from source to right after novotes, where weak agreement can be trivially obtained and thus a behavioral refinement of 2-voting with 3-voting, then compose with behavioral refinement wrt. 3-voting from that point (obtained via forward simulation as usual) to asm.
