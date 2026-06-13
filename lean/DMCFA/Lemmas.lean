/-
  Concrete-machine utility lemmas (shared by the timestamped/abstract chain)

  - Fresh address existence (axiom `exists_fresh`)
  - Store monotonicity (`Store.extend_comm`, `Env.extend_comm`)
  - Evaluation store monotonicity (`eval_store_mono` & friends)

  The concrete Bauer-Pretnar <-> ANF equivalence is now proved in the
  locally-nameless development (`DMCFA.LN.*`); the old named-variable
  substitution-correspondence lemmas have been removed.
-/

import DMCFA.Semantics

namespace DMCFA

/-! ## Fresh address existence -/

/-- Axiom: for any store, there exists a fresh address -/
axiom exists_fresh (σ : Store) : ∃ a : VAddr, σ a = none

private theorem Forall₂_left_mem {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) (a : α) (ha : a ∈ l₁) : ∃ b ∈ l₂, R a b := by
  induction h with
  | nil => simp at ha
  | @cons a' b' l1 l2 hab _ ih =>
    cases ha with
    | head => exact ⟨b', List.Mem.head _, hab⟩
    | tail _ h => obtain ⟨b, hb, hr⟩ := ih h; exact ⟨b, List.Mem.tail _ hb, hr⟩

/-! ## Store monotonicity -/

/-- Store monotonicity: extending store preserves existing mappings -/
@[simp] theorem Store.extend_preserves (σ : Store) (a : VAddr) (d : Denotable)
    (a' : VAddr) (h : a' ≠ a) : (σ.extend a d) a' = σ a' := by grind

/-- Store.extend commutes when addresses differ -/
theorem Store.extend_comm {σ : Store} {a1 a2 : VAddr} {d1 d2 : Denotable} (h : a1 ≠ a2) :
    (σ.extend a1 d1).extend a2 d2 = (σ.extend a2 d2).extend a1 d1 := by grind

/-- Env.extend commutes when variables differ -/
theorem Env.extend_comm {ρ : Env} {x1 x2 : Var} {a1 a2 : VAddr} (h : x1 ≠ x2) :
    (ρ.extend x1 a1).extend x2 a2 = (ρ.extend x2 a2).extend x1 a1 := by
  funext x; simp [Env.extend]; grind

/-- Freshness through extend with different address -/
@[simp] theorem Store.fresh_extend_of_fresh {σ : Store} {a1 a2 : VAddr} {d : Denotable}
    (h_fresh : σ a1 = none) (h_ne : a1 ≠ a2) :
    (σ.extend a2 d) a1 = none := by grind

/-! ## foldl extend preserves old mappings -/

private theorem foldl_extend_preserves
    (pairs : List (VAddr × Denotable)) (σ : Store)
    (a : VAddr) (d : Denotable) (h_in : σ a = some d)
    (h_ne : ∀ p ∈ pairs, p.1 ≠ a) :
    (pairs.foldl (fun s (p : VAddr × Denotable) => s.extend p.1 p.2) σ) a = some d := by
  induction pairs generalizing σ with
  | nil => exact h_in
  | cons p ps ih =>
    simp only [List.foldl]
    apply ih
    · simp only [Store.extend]
      have := (h_ne p (by simp)).symm
      rw [if_neg this]; exact h_in
    · intro q hq; exact h_ne q (by simp [hq])

/-! ## Evaluation store monotonicity -/

mutual

/-- Evaluation only extends the store: old mappings are preserved -/
theorem eval_store_mono
    (h : EvalExp e ρ σ v σ') :
    ∀ a d, σ a = some d → σ' a = some d :=
  match h with
  | .eval_let h_cexp h_cont =>
    fun a d h_in =>
      eval_continue_store_mono h_cont a d (eval_cexp_store_mono h_cexp a d h_in)
  | .eval_tail h_cexp =>
    fun a d h_in => eval_cexp_store_mono h_cexp a d h_in

theorem eval_cexp_store_mono
    (h : EvalCExp ce ρ σ v σ') :
    ∀ a d, σ a = some d → σ' a = some d :=
  match h with
  | .eval_atomic _ => fun _ _ h_in => h_in
  | .eval_funApp_clos _ _ _ h_fresh _ _ h_σ h_ρ h_eval =>
    fun a d h_in => by
      rename_i ds as_v _ _ _ _ _ _ _
      apply eval_store_mono h_eval; subst h_σ
      have h_ne : ∀ p ∈ as_v.zip ds, p.1 ≠ a := by
        intro ⟨a', d'⟩ h_mem h_eq; subst h_eq
        exact absurd ((List.forall₂_iff_zip.mp h_fresh).2 h_mem) (by simp [h_in])
      exact foldl_extend_preserves _ _ _ _ h_in h_ne
  | .eval_opApp _ => fun _ _ h_in => h_in
  | .eval_funApp_kont _ _ h_apply h_handle =>
    fun a d h_in =>
      eval_handle_store_mono h_handle a d (eval_apply_store_mono h_apply a d h_in)
  | .eval_fun h_fresh _ _ h_σ' =>
    fun a d h_in => by subst h_σ'; grind
  | .eval_match _ _ _ _ h_eval =>
    fun a d h_in => eval_store_mono h_eval a d h_in
  | .eval_match_succ _ _ _ h_fresh h_σ _ h_eval =>
    fun a d h_in => by apply eval_store_mono h_eval; subst h_σ; grind
  | .eval_handler h_eval h_handle =>
    fun a d h_in =>
      eval_handle_store_mono h_handle a d (eval_store_mono h_eval a d h_in)

theorem eval_continue_store_mono
    (h : ContinueFrame f v σ v' σ') :
    ∀ a d, σ a = some d → σ' a = some d :=
  match h with
  | .continue_let h_fresh h_σ h_eval =>
    fun a d h_in => by apply eval_store_mono h_eval; subst h_σ; grind
  | .continue_op => fun _ _ h_in => h_in

theorem eval_handle_store_mono
    (h : HandleValue hh ρ v σ v' σ') :
    ∀ a d, σ a = some d → σ' a = some d :=
  match h with
  | .handle_return _ h_fresh h_σ h_eval =>
    fun a d h_in => by apply eval_store_mono h_eval; subst h_σ; grind
  | .handle_op _ h_fresh_vk h_fresh_v _ _ h_σ h_eval =>
    fun a d h_in => by apply eval_store_mono h_eval; subst h_σ; grind
  | .handle_capture_op _ _ => fun _ _ h_in => h_in

theorem eval_apply_store_mono
    (h : ApplyKont κ dd σ v σ') :
    ∀ a d, σ a = some d → σ' a = some d :=
  match h with
  | .apply_continue => fun _ _ h_in => h_in
  | .apply_restore h_apply h_cont =>
    fun a d h_in =>
      eval_continue_store_mono h_cont a d (eval_apply_store_mono h_apply a d h_in)
  | .apply_restore_handle h_apply h_handle =>
    fun a d h_in =>
      eval_handle_store_mono h_handle a d (eval_apply_store_mono h_apply a d h_in)

end -- mutual eval store mono

end DMCFA
