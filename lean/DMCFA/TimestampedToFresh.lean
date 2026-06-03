/-
  T ↔ TFresh equivalence and corollaries.

  - TFresh → T: trivial (drop freshness premises), in TStrictOfNaive.lean
  - T → TFresh: the Freshness proof (Freshness.lean)

  Key corollary: for well-labeled programs starting from a FreshInvariant store,
  every timestamped derivation is also a fresh-guarded derivation, and the output
  store satisfies FreshInvariant.
-/

import DMCFA.FreshToTimestamped
import DMCFA.FreshnessSimulation

namespace DMCFA

/-! ## FreshInvariant for empty store -/

theorem FreshInvariant.empty : FreshInvariant TStore.empty where
  names := by intro a₁ a₂ _ _ h; simp [TStore.empty] at h
  konts := by intro k₁ k₂ _ _ _ h; simp [TStore.empty] at h
  wf_store := by intro a; simp [TStore.empty]
  chain_wf := by intro a; simp [TStore.empty]

/-! ## T → TFresh corollaries (parameterized by isHandlerLabel) -/

/-- Any timestamped expression derivation from a FreshInvariant store with
    WellFormedProgram is also a fresh-guarded derivation. -/
theorem naive_implies_strict_exp
    (isHandlerLabel : Label → Prop)
    (h_hl_consistent : ∀ (h : Handler), ∀ l ∈ h.handlerLabels, isHandlerLabel l)
    (h_hl_sound : ∀ l, isHandlerLabel l →
      ∀ (e : Exp), WellLabeledProgram e → l ∈ e.allLabels → l ∈ e.handlerLabels)
    {e : Exp} {ρ : TEnv} {σ : TStore} {t : Time} {v : TValue} {σ' : TStore}
    (h_eval : TEvalExp e ρ σ t v σ')
    (h_wf : WellFormedProgram e)
    (h_fi : FreshInvariant σ)
    (h_var : ∀ x ∈ e.topAllocVars, σ (.val ⟨x, t⟩) = none)
    (h_kont : ∀ l ∈ e.allLabels, ∀ k : TKAddr,
      k.frame.time = t → k.frame.label = l → σ (.kont k) = none)
    (h_cdf : ∀ l ∈ e.allLabels, CallDescFresh σ t l)
    (h_hdf : ∀ l ∈ e.handlerLabels, HandlerDescFresh σ t l) :
    TFreshEvalExp e ρ σ t v σ' ∧ FreshInvariant σ' ∧
    WriteBound σ σ' t e.topAllocVars e.allLabels e.allLabels e.allLabels := by
  obtain ⟨n, hn⟩ := tneval_exp_to_N h_eval
  have h_result :=
    (_root_.DMCFA.simulation isHandlerLabel h_hl_consistent h_hl_sound n).1
      e ρ σ t v σ' hn h_wf h_fi h_var h_kont h_cdf h_hdf
  exact ⟨teval_expN_to h_result.1, h_result.2.2.1, h_result.2.2.2.1⟩

/-- Any timestamped cexp derivation from a FreshInvariant store is also fresh-guarded. -/
theorem naive_implies_strict_cexp
    (isHandlerLabel : Label → Prop)
    (h_hl_consistent : ∀ (h : Handler), ∀ l ∈ h.handlerLabels, isHandlerLabel l)
    (h_hl_sound : ∀ l, isHandlerLabel l →
      ∀ (e : Exp), WellLabeledProgram e → l ∈ e.allLabels → l ∈ e.handlerLabels)
    {ce : CExp} {ρ : TEnv} {σ : TStore} {t : Time} {l_enc : Label}
    {v : TValue} {σ' : TStore}
    (h_eval : TEvalCExp ce ρ σ t l_enc v σ')
    (h_wl : WellLabeledSubCExp ce) (h_wn : WellNamedSubCExp ce)
    (h_fi : FreshInvariant σ)
    (h_var : ∀ x ∈ ce.topAllocVars, σ (.val ⟨x, t⟩) = none)
    (h_kont_enc : ∀ k : TKAddr, k.frame.time = t → k.frame.label = l_enc → σ (.kont k) = none)
    (h_kont : ∀ l ∈ ce.allLabels, ∀ k : TKAddr,
      k.frame.time = t → k.frame.label = l → σ (.kont k) = none)
    (h_disj : l_enc ∉ ce.allLabels)
    (h_cdf : ∀ l ∈ ce.allLabels, CallDescFresh σ t l)
    (h_cdf_enc : CallDescFresh σ t l_enc)
    (h_hdf_enc : ce.isHandlerCExp → HandlerDescFresh σ t l_enc)
    (h_hdf : ∀ l ∈ ce.handlerLabels, HandlerDescFresh σ t l)
    (h_label_kind : isHandlerLabel l_enc → ce.isHandlerCExp = true) :
    TFreshEvalCExp ce ρ σ t l_enc v σ' ∧ FreshInvariant σ' ∧
    WriteBound σ σ' t ce.topAllocVars ce.allLabels ({l_enc} ∪ ce.allLabels)
      ({l_enc} ∪ ce.allLabels) := by
  obtain ⟨n, hn⟩ := tneval_cexp_to_N h_eval
  have h_result :=
    (_root_.DMCFA.simulation isHandlerLabel h_hl_consistent h_hl_sound n).2.1
      ce ρ σ t l_enc v σ' hn h_wl h_wn h_fi h_var h_kont_enc h_kont h_disj
      h_cdf h_cdf_enc h_hdf_enc h_hdf h_label_kind
  exact ⟨teval_cexpN_to h_result.1, h_result.2.2.1, h_result.2.2.2.1⟩

/-! ## All freshness conditions hold for empty store -/

theorem empty_callDescFresh (t : Time) (l : Label) : CallDescFresh TStore.empty t l :=
  fun _ _ => rfl

theorem empty_handlerDescFresh (t : Time) (l : Label) : HandlerDescFresh TStore.empty t l :=
  fun _ _ _ => rfl

/-- Address Freshness from empty store (Corollary of Theorem 3):
    (e, ρ, ∅, t) ⇓et (v, σ') ⟹ (e, ρ, ∅, t) ⇓et_f (v, σ')
    Every timestamped derivation from an empty store is fresh-guarded. -/
theorem naive_to_strict_from_empty
    (isHandlerLabel : Label → Prop)
    (h_hl_consistent : ∀ (h : Handler), ∀ l ∈ h.handlerLabels, isHandlerLabel l)
    (h_hl_sound : ∀ l, isHandlerLabel l →
      ∀ (e : Exp), WellLabeledProgram e → l ∈ e.allLabels → l ∈ e.handlerLabels)
    {e : Exp} {ρ : TEnv} {t : Time} {v : TValue} {σ' : TStore}
    (h_eval : TEvalExp e ρ TStore.empty t v σ')
    (h_wf : WellFormedProgram e) :
    TFreshEvalExp e ρ TStore.empty t v σ' ∧ FreshInvariant σ' := by
  obtain ⟨h1, h2, _⟩ := naive_implies_strict_exp isHandlerLabel h_hl_consistent h_hl_sound
    h_eval h_wf FreshInvariant.empty
    (fun _ _ => rfl) (fun _ _ _ _ _ => rfl)
    (fun l _ => empty_callDescFresh t l)
    (fun l _ => empty_handlerDescFresh t l)
  exact ⟨h1, h2⟩

end DMCFA
