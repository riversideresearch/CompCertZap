# Milestones

## v1.0 Liveness-Bounded Fault Tolerance Proof (Shipped: 2026-03-05)

**Phases completed:** 4 phases, 4 plans, 8 tasks
**Timeline:** 2025-11-27 → 2026-03-04
**Lines changed:** +1,509 / -842 across 6 files

**Key accomplishments:**
- Created ProofLiveness.v: conservative backward liveness analysis (Kildall solver) that always includes Iop/Iload args
- Swapped RTLcolor.v and RTLcolorcheck.v from Liveness.analyze to ProofLiveness.analyze; completed all 14 check_col_instr_sound proof cases
- Fully proved faulty_backward_simulation in RTLtolerant.v with liveness-bounded match relation — zero Admitted
- End-to-end validated: Complements.vo compiles, zero Admitted across all files, ccomp binary compiles C with -tmr flag

---

