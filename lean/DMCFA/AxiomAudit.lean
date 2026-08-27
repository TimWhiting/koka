/-
  Axiom audit for the HMCFA mechanization.

  Run with:  `lake env lean DMCFA/AxiomAudit.lean`

  For each top-level theorem, `#print axioms` reports the complete set of
  axioms it transitively depends on. Inspect the output for project-specific
  assumptions such as `exists_fresh` / `LN.exists_fresh` and for any classical
  axioms. The concrete B&P <-> ANF equivalence is
  proved in a fully locally-nameless representation (`DMCFA.LN.*`).
-/
import DMCFA

open DMCFA

/-! Concrete equivalence (Bauer-Pretnar <-> concrete ANF machine),
    locally-nameless — the result the reviewers asked us to make axiom-free. -/
#print axioms DMCFA.LN.soundness               -- concrete ANF eval -> B&P eval
#print axioms DMCFA.LN.completeness_combined    -- B&P eval -> concrete ANF eval

/-! Concrete-LN <-> Concrete-named bridge: connects the locally-nameless concrete
    machine (left of the chain) to the named concrete machine (right of the
    chain), so the whole B&P -> Abstract story composes through one concrete
    semantics. Holds for well-formed source programs (`WFExp`). -/
#print axioms DMCFA.Bridge.sim_forward               -- named concrete eval -> LN concrete eval (of the translation)
#print axioms DMCFA.Bridge.sim_backward              -- LN concrete eval (of the translation) -> named concrete eval

/-! Concrete -> Fresh-Guarded -> Timestamped -> Abstract chain. -/
#print axioms DMCFA.simulation                       -- concrete -> fresh-guarded
#print axioms DMCFA.naive_to_strict_from_empty       -- address freshness (paper Thm 3)
#print axioms DMCFA.fresh_to_concrete_from_empty     -- fresh-guarded -> timestamped (soundness)
#print axioms DMCFA.concrete_to_fresh_from_empty     -- timestamped -> fresh-guarded (completeness)
#print axioms DMCFA.abstract_soundness               -- timestamped -> abstract (soundness)
