/-
  Axiom audit for the HMCFA mechanization.

  Run with:  `lake env lean DMCFA/AxiomAudit.lean`

  For each top-level theorem, `#print axioms` reports the complete set of
  axioms it transitively depends on. The expected output is, for every
  theorem, ONLY:

    - `propext`, `Classical.choice`, `Quot.sound`  — Lean 4's three standard
      foundational axioms (the basis of the entire Lean/Mathlib ecosystem); and
    - `exists_fresh` / `LN.exists_fresh`  — "for any finitely-supported store
      over the infinite address space, a fresh address exists" (manifestly
      sound).

  In particular NO `barendregt_fresh_env` / `barendregt_var_ne` appears: the
  concrete B&P <-> ANF equivalence is now proved in a fully locally-nameless
  representation (`DMCFA.LN.*`), which removes those two axioms entirely.
-/
import DMCFA

open DMCFA

/-! Concrete equivalence (Bauer-Pretnar <-> concrete ANF machine),
    locally-nameless — the result the reviewers asked us to make axiom-free. -/
#print axioms DMCFA.LN.soundness               -- concrete ANF eval -> B&P eval
#print axioms DMCFA.LN.completeness_combined    -- B&P eval -> concrete ANF eval

/-! Concrete -> Fresh-Guarded -> Timestamped -> Abstract chain. -/
#print axioms DMCFA.simulation                       -- concrete -> fresh-guarded
#print axioms DMCFA.naive_to_strict_from_empty       -- address freshness (paper Thm 3)
#print axioms DMCFA.fresh_to_concrete_from_empty     -- fresh-guarded -> timestamped (soundness)
#print axioms DMCFA.concrete_to_fresh_from_empty     -- timestamped -> fresh-guarded (completeness)
#print axioms DMCFA.abstract_soundness               -- timestamped -> abstract (soundness)
