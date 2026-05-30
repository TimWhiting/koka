/-
  Tmk Preservation: Naive evaluation only modifies store addresses
  whose tmk has the evaluation's tmk as a suffix.

  Key theorem: tn_eval_preserves_non_suffix (and mutual variants)

  This is a purely semantic property — it doesn't require freshness/WellLabeled.
-/

import DMCFA.NaiveSemantics

namespace DMCFA

/-! ## Helper lemmas -/

/-- If l₁ is NOT a suffix of l₂, then (x :: l₁) is NOT a suffix of l₂ -/
theorem not_isSuffix_of_cons_not_isSuffix {α : Type*} {l₁ l₂ : List α} {x : α}
    (h : ¬ l₁ <:+ l₂) : ¬ (x :: l₁) <:+ l₂ := by
  intro ⟨t, ht⟩
  apply h
  exact ⟨t ++ [x], by rw [List.append_assoc]; simpa using ht⟩

/-- Helper: extend at an address whose tmk has `tmk` as suffix preserves non-suffix addresses -/
private theorem extend_preserves {σ : TStore} {addr : TAddr} {s : TStorable}
    {a : TAddr} {tmk : MKTime}
    (h_not_suffix : ¬ tmk <:+ a.time.tmk)
    (h_addr_tmk : addr.time.tmk = a.time.tmk → tmk <:+ a.time.tmk) :
    (σ.extend addr s) a = σ a := by
  apply TStore.extend_ne
  intro heq
  exact h_not_suffix (h_addr_tmk (heq ▸ rfl))

/-- Helper: extend at val address with time t preserves addresses not at tmk-suffix -/
private theorem extend_val_preserves {σ : TStore} {x : Var} {t : Time} {s : TStorable}
    {a : TAddr} (h_not_suffix : ¬ t.tmk <:+ a.time.tmk) :
    (σ.extend (.val ⟨x, t⟩) s) a = σ a := by
  apply TStore.extend_ne
  intro heq; exact h_not_suffix (heq ▸ List.suffix_refl _)

/-- Helper: extend at kont address preserves addresses not at tmk-suffix -/
private theorem extend_kont_preserves {σ : TStore} {k : TKAddr} {s : TStorable}
    {a : TAddr} (h_not_suffix : ¬ k.frame.time.tmk <:+ a.time.tmk) :
    (σ.extend (.kont k) s) a = σ a := by
  apply TStore.extend_ne
  intro heq; exact h_not_suffix (heq ▸ List.suffix_refl _)

/-- foldl of store extensions preserves addresses with non-matching tmk -/
theorem foldl_extend_preserves_non_suffix (σ : TStore) (pairs : List (Var × TDenotable))
    (t_alloc : Time)
    (a : TAddr) (h_a : ¬ t_alloc.tmk <:+ a.time.tmk) :
    (pairs.foldl (fun s (x, d) => s.extend (.val ⟨x, t_alloc⟩) (.denotable d)) σ) a = σ a := by
  induction pairs generalizing σ with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rw [ih]
    exact extend_val_preserves h_a

/-! ## Main mutual preservation theorem -/

mutual

/-- Naive exp evaluation only modifies addresses at tmk-suffix timestamps -/
theorem tn_eval_exp_preserves_non_suffix
    (h : TEvalExpN n e ρ σ t v σ') :
    ∀ a, ¬ t.tmk <:+ a.time.tmk → σ' a = σ a := by
  intro a h_not_suffix
  match h with
  | .eval_let h_ce h_cont =>
    have h1 := tn_eval_cexp_preserves_non_suffix h_ce a h_not_suffix
    have h2 := tn_continue_frame_preserves_non_suffix h_cont a h_not_suffix
    rw [h2, h1]
  | .eval_tail h_ce =>
    exact tn_eval_cexp_preserves_non_suffix h_ce a h_not_suffix

/-- Naive cexp evaluation only modifies addresses at tmk-suffix timestamps -/
theorem tn_eval_cexp_preserves_non_suffix
    (h : TEvalCExpN n ce ρ σ t l v σ') :
    ∀ a, ¬ t.tmk <:+ a.time.tmk → σ' a = σ a := by
  intro a h_not_suffix
  match h with
  | .eval_atomic _ => rfl
  | .eval_funApp_clos _ _ _ h_tnew h_σnew h_ρnew h_body =>
    subst h_tnew; subst h_σnew; subst h_ρnew
    -- t_new.tmk = t.tmk, so h_not_suffix still applies
    have h_body_pres := tn_eval_exp_preserves_non_suffix h_body a h_not_suffix
    rw [h_body_pres]
    exact foldl_extend_preserves_non_suffix σ _ ⟨l :: t.tk, t.tmk⟩ a h_not_suffix
  | .eval_opApp _ => rfl
  | .eval_funApp_kont h_f h_ae h_tmk h_apply h_teq h_handle =>
    subst h_tmk; subst h_teq
    have h1 := tn_apply_kont_preserves_non_suffix h_apply a
      (not_isSuffix_of_cons_not_isSuffix h_not_suffix)
    have h2 := tn_handle_value_preserves_non_suffix h_handle a h_not_suffix
    rw [h2, h1]
  | .eval_fun h_av _ _ h_σ' =>
    subst h_av; subst h_σ'
    exact extend_val_preserves h_not_suffix
  | .eval_match _ _ _ _ h_body =>
    exact tn_eval_exp_preserves_non_suffix h_body a h_not_suffix
  | .eval_match_succ _ _ _ _ h_afresh h_σnew h_ρnew h_body =>
    subst h_afresh; subst h_σnew; subst h_ρnew
    have h1 := tn_eval_exp_preserves_non_suffix h_body a h_not_suffix
    rw [h1]
    exact extend_val_preserves h_not_suffix
  | .eval_handler h_tb h_body h_handle =>
    subst h_tb
    have h1 := tn_eval_exp_preserves_non_suffix h_body a
      (not_isSuffix_of_cons_not_isSuffix h_not_suffix)
    have h2 := tn_handle_value_preserves_non_suffix h_handle a h_not_suffix
    rw [h2, h1]

/-- Naive continue frame only modifies addresses at tmk-suffix timestamps -/
theorem tn_continue_frame_preserves_non_suffix
    (h : TContinueFrameN n l fc t v σ v' σ') :
    ∀ a, ¬ t.tmk <:+ a.time.tmk → σ' a = σ a := by
  intro a h_not_suffix
  match h with
  | .continue_let h_eq h_body =>
    subst h_eq
    have h1 := tn_eval_exp_preserves_non_suffix h_body a h_not_suffix
    rw [h1]
    exact extend_val_preserves h_not_suffix
  | .continue_op h_ψ h_aκ h_σ' =>
    subst h_ψ; subst h_aκ; subst h_σ'
    exact extend_kont_preserves h_not_suffix

/-- Naive handle value only modifies addresses at tmk-suffix timestamps -/
theorem tn_handle_value_preserves_non_suffix
    (h : THandleValueN n l hdl ρ v σ t v' σ') :
    ∀ a, ¬ t.tmk <:+ a.time.tmk → σ' a = σ a := by
  intro a h_not_suffix
  match h with
  | .handle_return _ h_anew h_body =>
    subst h_anew
    have h1 := tn_eval_exp_preserves_non_suffix h_body a h_not_suffix
    rw [h1]
    exact extend_val_preserves h_not_suffix
  | .handle_op _ h_ax h_ares _ _ h_dkont h_σop h_body =>
    subst h_ax; subst h_ares; subst h_dkont; subst h_σop
    have h1 := tn_eval_exp_preserves_non_suffix h_body a h_not_suffix
    rw [h1]
    -- σ_op = (σ.extend (.val a_x) _).extend (.val a_resume) _
    rw [extend_val_preserves h_not_suffix, extend_val_preserves h_not_suffix]
  | .handle_capture_op _ h_ψ h_aκ h_σ' =>
    subst h_ψ; subst h_aκ; subst h_σ'
    exact extend_kont_preserves h_not_suffix

/-- Naive apply kont only modifies addresses at tmk-suffix timestamps -/
theorem tn_apply_kont_preserves_non_suffix
    (h : TApplyKontN n oa_κ d σ tmk v σ') :
    ∀ a, ¬ tmk <:+ a.time.tmk → σ' a = σ a := by
  intro a h_not_suffix
  match h with
  | .apply_continue => rfl
  | .apply_restore _ _ h_apply h_eq h_cont =>
    subst h_eq
    have h1 := tn_apply_kont_preserves_non_suffix h_apply a h_not_suffix
    have h2 := tn_continue_frame_preserves_non_suffix h_cont a h_not_suffix
    rw [h2, h1]
  | .apply_restore_handle h_lookup h_content h_eq h_apply h_eq2 h_handle =>
    subst h_eq; subst h_eq2
    have h1 := tn_apply_kont_preserves_non_suffix h_apply a
      (not_isSuffix_of_cons_not_isSuffix (x := (_, _)) h_not_suffix)
    have h2 := tn_handle_value_preserves_non_suffix h_handle a h_not_suffix
    rw [h2, h1]

end

end DMCFA
