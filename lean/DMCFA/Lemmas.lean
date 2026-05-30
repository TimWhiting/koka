/-
  Key lemmas for the equivalence proof

  - Store monotonicity
  - Substitution-environment correspondence
  - Weakening
  - Fresh address existence (axiom)
  - B&P closedness preservation
-/

import DMCFA.Equivalence
import DMCFA.BPSemantics
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

/-! ## FVS decomposition lemmas for B&P -/

@[grind ->] private theorem append_eq_nil {l1 l2 : List α} (h : l1 ++ l2 = []) : l1 = [] ∧ l2 = [] := by
  constructor
  · cases l1 with
    | nil => rfl
    | cons _ _ => simp at h
  · cases l1 with
    | nil => exact h
    | cons _ _ => simp at h

@[grind ->] theorem filter_eq_nil_mem {l : List α} {p : α → Bool} :
    l.filter p = [] → ∀ v, v ∈ l → p v = false := by simp

@[grind ->] theorem bp_letIn_fvs_c1 {x : BP.Var} {c1 c2 : BP.Comp} :
    (BP.Comp.letIn x c1 c2).fvs = [] → c1.fvs = [] := by simp; grind

@[grind ->] theorem bp_letIn_fvs_c2 {x : BP.Var} {c1 c2 : BP.Comp} :
    (BP.Comp.letIn x c1 c2).fvs = [] →
    ∀ v, v ∈ c2.fvs → v = x := by simp

@[grind ->] theorem bp_if_fvs_scrutinee {e : BP.Expr} {c1 c2 : BP.Comp} :
    (BP.Comp.ifThenElse e c1 c2).fvs = [] → e.fvs = [] := by simp; grind

@[grind ->] theorem bp_if_fvs_c1 {e : BP.Expr} {c1 c2 : BP.Comp} :
    (BP.Comp.ifThenElse e c1 c2).fvs = [] → c1.fvs = [] := by simp; grind

@[grind ->] theorem bp_if_fvs_c2 {e : BP.Expr} {c1 c2 : BP.Comp} :
    (BP.Comp.ifThenElse e c1 c2).fvs = [] → c2.fvs = [] := by simp

@[grind ->] theorem bp_matchNat_fvs_scrutinee {e : BP.Expr} {c1 : BP.Comp} {x : BP.Var} {c2 : BP.Comp} :
    (BP.Comp.matchNat e c1 x c2).fvs = [] → e.fvs = [] := by simp; grind

@[grind ->] theorem bp_matchNat_fvs_c1 {e : BP.Expr} {c1 : BP.Comp} {x : BP.Var} {c2 : BP.Comp} :
    (BP.Comp.matchNat e c1 x c2).fvs = [] → c1.fvs = [] := by simp; grind

@[grind ->] theorem bp_matchNat_fvs_c2 {e : BP.Expr} {c1 : BP.Comp} {x : BP.Var} {c2 : BP.Comp} :
    (BP.Comp.matchNat e c1 x c2).fvs = [] →
    ∀ v, v ∈ c2.fvs → v = x := by simp

/-! ## evalAtomic correspondence -/

/-- ExprEquiv + closed implies evalAtomic succeeds with corresponding value -/
theorem expr_equiv_eval_atomic :
    ExprEquiv σ ρ e_bp ae →
    e_bp.fvs = [] →
    ∃ d, evalAtomic ae ρ σ = some d ∧ ValueEquiv σ e_bp d := by
  intro h_equiv h_closed
  cases h_equiv with
  | var => simp [BP.Expr.fvs_var] at h_closed
  | true_ => exact ⟨_, rfl, ValueEquiv.con_true⟩
  | false_ => exact ⟨_, rfl, ValueEquiv.con_false⟩
  | unit => exact ⟨_, rfl, ValueEquiv.con_unit⟩
  | zero => exact ⟨_, rfl, ValueEquiv.con_zero⟩
  | lam h_body => exact ⟨_, rfl, ValueEquiv.lambda h_body⟩
  | var_subst h_rho h_store h_val _ =>
    refine ⟨_, ?_, h_val⟩
    simp [evalAtomic, h_rho, h_store]
  | succ h_inner =>
    rename_i e_inner _
    have h_inner_closed : e_inner.fvs = [] := by
      simp [BP.Expr.fvs_succ] at h_closed; exact h_closed
    cases h_inner with
    | var => simp [BP.Expr.fvs_var] at h_inner_closed
    | var_subst h_rho h_store h_val _ =>
      refine ⟨_, ?_, ValueEquiv.succ h_store h_val⟩
      simp [evalAtomic, h_rho, h_store]

/-! ## General store monotonicity for equivalences -/

mutual

/-- ValueEquiv is monotone in the store -/
theorem value_equiv_store_mono
    (h : ValueEquiv σ e_bp d)
    (mono : ∀ a d, σ a = some d → σ' a = some d) :
    ValueEquiv σ' e_bp d :=
  match h with
  | .con_true => .con_true
  | .con_false => .con_false
  | .con_unit => .con_unit
  | .con_zero => .con_zero
  | .succ h_store h_val =>
    .succ (mono _ _ h_store) (value_equiv_store_mono h_val mono)
  | .lambda h_body =>
    .lambda (comp_equiv_store_mono h_body mono)
  | .rec_lambda h_body h_store =>
    .rec_lambda (comp_equiv_store_mono h_body mono) (mono _ _ h_store)
  | .kont h_hdl h_kont h_fresh =>
    .kont (handler_equiv_store_mono h_hdl mono) (kont_equiv_store_mono h_kont mono) h_fresh

/-- ExprEquiv is monotone in the store -/
theorem expr_equiv_store_mono
    (h : ExprEquiv σ ρ e_bp ae)
    (mono : ∀ a d, σ a = some d → σ' a = some d) :
    ExprEquiv σ' ρ e_bp ae :=
  match h with
  | .var => .var
  | .true_ => .true_
  | .false_ => .false_
  | .unit => .unit
  | .zero => .zero
  | .succ h_inner => .succ (expr_equiv_store_mono h_inner mono)
  | .lam h_body => .lam (comp_equiv_store_mono h_body mono)
  | .var_subst h_rho h_store h_val h_closed =>
    .var_subst h_rho (mono _ _ h_store) (value_equiv_store_mono h_val mono) h_closed

/-- CompEquiv is monotone in the store -/
theorem comp_equiv_store_mono
    (h : CompEquiv σ ρ c e)
    (mono : ∀ a d, σ a = some d → σ' a = some d) :
    CompEquiv σ' ρ c e :=
  match h with
  | .tail h_cexp => .tail (comp_equiv_cexp_store_mono h_cexp mono)
  | .letE h_cexp h_c2 =>
    .letE (comp_equiv_cexp_store_mono h_cexp mono) (comp_equiv_store_mono h_c2 mono)
  | .letRec h_c1 h_c2 =>
    .letRec (comp_equiv_store_mono h_c1 mono) (comp_equiv_store_mono h_c2 mono)

/-- CompEquivCExp is monotone in the store -/
theorem comp_equiv_cexp_store_mono
    (h : CompEquivCExp σ ρ c ce)
    (mono : ∀ a d, σ a = some d → σ' a = some d) :
    CompEquivCExp σ' ρ c ce :=
  match h with
  | .atomic h_expr => .atomic (expr_equiv_store_mono h_expr mono)
  | .funApp h_e1 h_e2 =>
    .funApp (expr_equiv_store_mono h_e1 mono) (expr_equiv_store_mono h_e2 mono)
  | .ifE h_expr h_c1 h_c2 =>
    .ifE (expr_equiv_store_mono h_expr mono) (comp_equiv_store_mono h_c1 mono) (comp_equiv_store_mono h_c2 mono)
  | .matchNat h_expr h_c1 h_c2 =>
    .matchNat (expr_equiv_store_mono h_expr mono) (comp_equiv_store_mono h_c1 mono) (comp_equiv_store_mono h_c2 mono)
  | .opApp h_expr => .opApp (expr_equiv_store_mono h_expr mono)
  | .handler h_hdl h_c =>
    .handler (handler_equiv_store_mono h_hdl mono) (comp_equiv_store_mono h_c mono)

/-- OpClausesEquiv is monotone in the store -/
theorem op_clauses_equiv_store_mono
    (h : OpClausesEquiv σ ρ bp_ops anf_ops)
    (mono : ∀ a d, σ a = some d → σ' a = some d) :
    OpClausesEquiv σ' ρ bp_ops anf_ops :=
  match h with
  | .nil => .nil
  | .cons h_comp h_rest =>
    .cons (comp_equiv_store_mono h_comp mono) (op_clauses_equiv_store_mono h_rest mono)

/-- HandlerEquiv is monotone in the store -/
theorem handler_equiv_store_mono
    (h : HandlerEquiv σ ρ hh h_anf)
    (mono : ∀ a d, σ a = some d → σ' a = some d) :
    HandlerEquiv σ' ρ hh h_anf :=
  match h with
  | .mk h_ret h_ops =>
    .mk (comp_equiv_store_mono h_ret mono) (op_clauses_equiv_store_mono h_ops mono)

/-- KontEquiv is monotone in the store -/
theorem kont_equiv_store_mono
    (h : KontEquiv σ x_c c κ)
    (mono : ∀ a d, σ a = some d → σ' a = some d) :
    KontEquiv σ' x_c c κ :=
  match h with
  | .kont_end => .kont_end
  | .kont_let h_inner h_c2 h_fresh =>
    .kont_let (kont_equiv_store_mono h_inner mono) (comp_equiv_store_mono h_c2 mono) h_fresh
  | .kont_handle h_inner h_hdl h_fresh =>
    .kont_handle (kont_equiv_store_mono h_inner mono) (handler_equiv_store_mono h_hdl mono) h_fresh

end -- mutual store monotonicity

/-! ## Equivalence extend-store lemmas -/

@[grind <-] private theorem store_extend_preserves_of_fresh (σ : Store) (a_new : VAddr) (d_new : Denotable)
    (h_fresh : σ a_new = none) :
    ∀ a d, σ a = some d → (Store.extend σ a_new d_new) a = some d := by grind

theorem value_equiv_extend_store :
    ValueEquiv σ e_bp d →
    σ a_new = none →
    ValueEquiv (Store.extend σ a_new d_new) e_bp d := by
  intro h hf; exact value_equiv_store_mono h (store_extend_preserves_of_fresh σ a_new d_new hf)

theorem expr_equiv_extend_store :
    ExprEquiv σ ρ e_bp ae →
    σ a_new = none →
    ExprEquiv (Store.extend σ a_new d_new) ρ e_bp ae := by
  intro h hf; exact expr_equiv_store_mono h (store_extend_preserves_of_fresh σ a_new d_new hf)

theorem comp_equiv_extend_store :
    CompEquiv σ ρ c e →
    σ a_new = none →
    CompEquiv (Store.extend σ a_new d_new) ρ c e := by
  intro h hf; exact comp_equiv_store_mono h (store_extend_preserves_of_fresh σ a_new d_new hf)

theorem comp_equiv_cexp_extend_store :
    CompEquivCExp σ ρ c ce →
    σ a_new = none →
    CompEquivCExp (Store.extend σ a_new d_new) ρ c ce := by
  intro h hf; exact comp_equiv_cexp_store_mono h (store_extend_preserves_of_fresh σ a_new d_new hf)

theorem handler_equiv_extend_store :
    HandlerEquiv σ ρ hh h_anf →
    σ a_new = none →
    HandlerEquiv (Store.extend σ a_new d_new) ρ hh h_anf := by
  intro h hf; exact handler_equiv_store_mono h (store_extend_preserves_of_fresh σ a_new d_new hf)

theorem result_equiv_extend_store :
    ResultEquiv σ r v →
    σ a_new = none →
    ResultEquiv (Store.extend σ a_new d_new) r v := by
  intro h hf
  cases h with
  | value h_val => exact .value (value_equiv_extend_store h_val hf)
  | op h_store h_val h_kont =>
    exact .op (store_extend_preserves_of_fresh σ a_new d_new hf _ _ h_store)
      (value_equiv_extend_store h_val hf)
      (kont_equiv_store_mono h_kont (store_extend_preserves_of_fresh σ a_new d_new hf))

theorem kont_equiv_extend_store :
    KontEquiv σ x_c c κ →
    σ a_new = none →
    KontEquiv (Store.extend σ a_new d_new) x_c c κ := by
  intro h hf; exact kont_equiv_store_mono h (store_extend_preserves_of_fresh σ a_new d_new hf)

/-- If `σ.extend a1 d` maps `a2` to `none`, then `σ a2 = none`. -/
@[simp, grind ->] theorem Store.fresh_of_fresh_extend {σ : Store} {a1 a2 : VAddr} {d : Denotable}
    (h_fresh_ext : (σ.extend a1 d) a2 = none) :
    σ a2 = none := by grind

/-- If `σ.extend a1 d` maps `a2` to `none`, then `a1 ≠ a2`. -/
@[simp, grind ->] theorem Store.ne_of_fresh_extend {σ : Store} {a1 a2 : VAddr} {d : Denotable}
    (h_fresh_ext : (σ.extend a1 d) a2 = none) :
    a1 ≠ a2 := by grind

/-! ## Substitution-environment correspondence (THE key lemma) -/

-- Substitution on B&P side ↔ env/store extension on ANF side.
-- If `CompEquiv σ ρ c e` and `ValueEquiv σ e_bp d` and `a` is fresh,
-- then `CompEquiv (σ.extend a d) (ρ.extend x a) (c.subst x e_bp) e`.

/-- Barendregt convention: binder variables are fresh in the environment.
    This is an assumption we need at call sites where B&P substitution
    corresponds to ANF env/store extension. -/
axiom barendregt_fresh_env
    (ρ : Env) (x : Var) : ρ x = none
/-- Barendregt convention: distinct binder variables in the same scope are different. -/
axiom barendregt_var_ne
    (x y : Var) : x ≠ y

mutual

theorem expr_equiv_subst_binding (x : Var)
    (h : ExprEquiv σ ρ e_expr ae)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = [])
    (h_fresh : σ a = none)
    (h_fresh_env : ρ x = none) :
    ExprEquiv (Store.extend σ a d) (Env.extend ρ x a) (e_expr.subst x e_bp) ae :=
  match h with
  | .var => by
      rename_i y
      by_cases h_eq : y = x
      · subst h_eq
        simp [BP.Expr.subst_var_self]
        exact ExprEquiv.var_subst
          (show (Env.extend ρ y a) y = some a by simp [Env.extend])
          (show (Store.extend σ a d) a = some d by simp [Store.extend])
          (value_equiv_extend_store h_val h_fresh)
          h_closed
      · rw [BP.Expr.subst_var_ne h_eq]
        exact .var
  | .true_ => by simp [BP.Expr.subst_true]; exact .true_
  | .false_ => by simp [BP.Expr.subst_false]; exact .false_
  | .unit => by simp [BP.Expr.subst_unit]; exact .unit
  | .zero => by simp [BP.Expr.subst_zero]; exact .zero
  | .succ h_inner => by
      simp [BP.Expr.subst_succ]
      exact .succ (expr_equiv_subst_binding x h_inner h_val h_closed h_fresh h_fresh_env)
  | .lam h_body => by
      rename_i _ _ z
      by_cases h_eq : z = x
      · rw [h_eq, BP.Expr.subst_lam_self]
        exact .lam (comp_equiv_weaken x h_body h_fresh h_fresh_env)
      · rw [BP.Expr.subst_lam_ne h_eq]
        exact .lam (comp_equiv_subst_binding x h_body h_val h_closed h_fresh h_fresh_env)
  | .var_subst h_rho h_store h_val_inner h_closed_inner => by
      rw [BP.Expr.subst_of_fvs_nil h_closed_inner]
      rename_i a' d' y
      have h_ne_addr : a' ≠ a := by grind
      have h_yx : y ≠ x := by grind
      exact ExprEquiv.var_subst
        (show (Env.extend ρ x a) y = some a' by simp [Env.extend, h_yx]; exact h_rho)
        (show (Store.extend σ a d) a' = some d' by simp [Store.extend, h_ne_addr]; exact h_store)
        (value_equiv_extend_store h_val_inner h_fresh)
        h_closed_inner

theorem comp_equiv_subst_binding (x : Var)
    (h : CompEquiv σ ρ c e)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = [])
    (h_fresh : σ a = none)
    (h_fresh_env : ρ x = none) :
    CompEquiv (Store.extend σ a d) (Env.extend ρ x a) (c.subst x e_bp) e :=
  match h with
  | .tail h_cexp =>
    .tail (comp_equiv_cexp_subst_binding x h_cexp h_val h_closed h_fresh h_fresh_env)
  | .letE h_cexp h_c2 => by
      rename_i _ _ _ y _
      by_cases h_eq : y = x
      · rw [h_eq, BP.Comp.subst_letIn_self]
        exact .letE (comp_equiv_cexp_subst_binding x h_cexp h_val h_closed h_fresh h_fresh_env)
          (comp_equiv_weaken x h_c2 h_fresh h_fresh_env)
      · rw [BP.Comp.subst_letIn_ne h_eq]
        exact .letE (comp_equiv_cexp_subst_binding x h_cexp h_val h_closed h_fresh h_fresh_env)
          (comp_equiv_subst_binding x h_c2 h_val h_closed h_fresh h_fresh_env)
  | .letRec h_c1 h_c2 => by
      rename_i _ _ _ _ f_rec x_rec _
      by_cases hf : x = f_rec
      · subst hf
        rw [BP.Comp.subst_letRec_self_f]
        exact .letRec (comp_equiv_weaken x h_c1 h_fresh h_fresh_env)
          (comp_equiv_weaken x h_c2 h_fresh h_fresh_env)
      · by_cases hy : x = x_rec
        · subst hy
          rw [BP.Comp.subst_letRec_self_y hf]
          exact .letRec (comp_equiv_weaken x h_c1 h_fresh h_fresh_env)
            (comp_equiv_subst_binding x h_c2 h_val h_closed h_fresh h_fresh_env)
        · rw [BP.Comp.subst_letRec_ne hf hy]
          exact .letRec (comp_equiv_subst_binding x h_c1 h_val h_closed h_fresh h_fresh_env)
            (comp_equiv_subst_binding x h_c2 h_val h_closed h_fresh h_fresh_env)

theorem comp_equiv_cexp_subst_binding (x : Var)
    (h : CompEquivCExp σ ρ c ce)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = [])
    (h_fresh : σ a = none)
    (h_fresh_env : ρ x = none) :
    CompEquivCExp (Store.extend σ a d) (Env.extend ρ x a) (c.subst x e_bp) ce :=
  match h with
  | .atomic h_expr => by
      simp [BP.Comp.subst_val]
      exact .atomic (expr_equiv_subst_binding x h_expr h_val h_closed h_fresh h_fresh_env)
  | .funApp h_e1 h_e2 => by
      simp [BP.Comp.subst_app]
      exact .funApp (expr_equiv_subst_binding x h_e1 h_val h_closed h_fresh h_fresh_env)
        (expr_equiv_subst_binding x h_e2 h_val h_closed h_fresh h_fresh_env)
  | .ifE h_expr h_c1 h_c2 => by
      simp [BP.Comp.subst_ifThenElse]
      exact .ifE (expr_equiv_subst_binding x h_expr h_val h_closed h_fresh h_fresh_env)
        (comp_equiv_subst_binding x h_c1 h_val h_closed h_fresh h_fresh_env)
        (comp_equiv_subst_binding x h_c2 h_val h_closed h_fresh h_fresh_env)
  | .matchNat h_expr h_c1 h_c2 => by
      rename_i _ _ _ _ y
      by_cases h_eq : y = x
      · rw [h_eq, BP.Comp.subst_matchNat_self]
        exact .matchNat (expr_equiv_subst_binding x h_expr h_val h_closed h_fresh h_fresh_env)
          (comp_equiv_subst_binding x h_c1 h_val h_closed h_fresh h_fresh_env)
          (comp_equiv_weaken x h_c2 h_fresh h_fresh_env)
      · rw [BP.Comp.subst_matchNat_ne h_eq]
        exact .matchNat (expr_equiv_subst_binding x h_expr h_val h_closed h_fresh h_fresh_env)
          (comp_equiv_subst_binding x h_c1 h_val h_closed h_fresh h_fresh_env)
          (comp_equiv_subst_binding x h_c2 h_val h_closed h_fresh h_fresh_env)
  | .opApp h_expr => by
      simp [BP.Comp.subst_opCall]
      exact .opApp (expr_equiv_subst_binding x h_expr h_val h_closed h_fresh h_fresh_env)
  | .handler h_hdl h_c => by
      simp [BP.Comp.subst_withHandle]
      exact .handler (handler_equiv_subst_binding x h_hdl h_val h_closed h_fresh h_fresh_env)
        (comp_equiv_subst_binding x h_c h_val h_closed h_fresh h_fresh_env)

theorem handler_equiv_subst_binding (x : Var)
    (h : HandlerEquiv σ ρ hh h_anf)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = [])
    (h_fresh : σ a = none)
    (h_fresh_env : ρ x = none) :
    HandlerEquiv (Store.extend σ a d) (Env.extend ρ x a) (hh.subst x e_bp) h_anf :=
  match h with
  | .mk h_ret h_ops => by
    simp only [BP.BPHandler.subst]
    split
    · exact .mk (comp_equiv_weaken x h_ret h_fresh h_fresh_env)
        (op_clauses_equiv_subst_binding x h_ops h_val h_closed h_fresh h_fresh_env)
    · exact .mk (comp_equiv_subst_binding x h_ret h_val h_closed h_fresh h_fresh_env)
        (op_clauses_equiv_subst_binding x h_ops h_val h_closed h_fresh h_fresh_env)

theorem op_clauses_equiv_subst_binding (x : Var)
    (h : OpClausesEquiv σ ρ bp_ops anf_ops)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = [])
    (h_fresh : σ a = none)
    (h_fresh_env : ρ x = none) :
    OpClausesEquiv (Store.extend σ a d) (Env.extend ρ x a)
      (bp_ops.map fun p => (p.1, p.2.1, if p.2.1 = x || "resume" = x then p.2.2 else p.2.2.subst x e_bp))
      anf_ops :=
  match h with
  | .nil => .nil
  | .cons h_comp h_rest => by
    simp only [List.map]
    split
    · exact .cons (comp_equiv_weaken x h_comp h_fresh h_fresh_env)
        (op_clauses_equiv_subst_binding x h_rest h_val h_closed h_fresh h_fresh_env)
    · exact .cons (comp_equiv_subst_binding x h_comp h_val h_closed h_fresh h_fresh_env)
        (op_clauses_equiv_subst_binding x h_rest h_val h_closed h_fresh h_fresh_env)

/-- Weakening: extending env with a fresh binding preserves CompEquiv -/
theorem comp_equiv_weaken (x : Var)
    (h : CompEquiv σ ρ c e)
    (h_fresh : σ a = none)
    (h_fresh_env : ρ x = none) :
    CompEquiv (Store.extend σ a d) (Env.extend ρ x a) c e :=
  match h with
  | .tail h_cexp =>
    .tail (comp_equiv_cexp_weaken x h_cexp h_fresh h_fresh_env)
  | .letE h_cexp h_c2 =>
    .letE (comp_equiv_cexp_weaken x h_cexp h_fresh h_fresh_env) (comp_equiv_weaken x h_c2 h_fresh h_fresh_env)
  | .letRec h_c1 h_c2 =>
    .letRec (comp_equiv_weaken x h_c1 h_fresh h_fresh_env) (comp_equiv_weaken x h_c2 h_fresh h_fresh_env)

theorem comp_equiv_cexp_weaken (x : Var)
    (h : CompEquivCExp σ ρ c ce)
    (h_fresh : σ a = none)
    (h_fresh_env : ρ x = none) :
    CompEquivCExp (Store.extend σ a d) (Env.extend ρ x a) c ce :=
  match h with
  | .atomic h_expr =>
    .atomic (expr_equiv_weaken x h_expr h_fresh h_fresh_env)
  | .funApp h_e1 h_e2 =>
    .funApp (expr_equiv_weaken x h_e1 h_fresh h_fresh_env) (expr_equiv_weaken x h_e2 h_fresh h_fresh_env)
  | .ifE h_expr h_c1 h_c2 =>
    .ifE (expr_equiv_weaken x h_expr h_fresh h_fresh_env) (comp_equiv_weaken x h_c1 h_fresh h_fresh_env) (comp_equiv_weaken x h_c2 h_fresh h_fresh_env)
  | .matchNat h_expr h_c1 h_c2 =>
    .matchNat (expr_equiv_weaken x h_expr h_fresh h_fresh_env) (comp_equiv_weaken x h_c1 h_fresh h_fresh_env) (comp_equiv_weaken x h_c2 h_fresh h_fresh_env)
  | .opApp h_expr =>
    .opApp (expr_equiv_weaken x h_expr h_fresh h_fresh_env)
  | .handler h_hdl h_c =>
    .handler (handler_equiv_weaken x h_hdl h_fresh h_fresh_env) (comp_equiv_weaken x h_c h_fresh h_fresh_env)

theorem expr_equiv_weaken (x : Var)
    (h : ExprEquiv σ ρ e_expr ae)
    (h_fresh : σ a = none)
    (h_fresh_env : ρ x = none) :
    ExprEquiv (Store.extend σ a d) (Env.extend ρ x a) e_expr ae :=
  match h with
  | .var => .var
  | .true_ => .true_
  | .false_ => .false_
  | .unit => .unit
  | .zero => .zero
  | .succ h_inner => .succ (expr_equiv_weaken x h_inner h_fresh h_fresh_env)
  | .lam h_body => .lam (comp_equiv_weaken x h_body h_fresh h_fresh_env)
  | .var_subst h_rho h_store h_val h_closed => by
      rename_i a' d' y
      have h_ne_addr : a' ≠ a := by grind
      have h_yx : y ≠ x := by grind
      exact ExprEquiv.var_subst
        (show (Env.extend ρ x a) y = some a' by simp [Env.extend, h_yx]; exact h_rho)
        (show (Store.extend σ a d) a' = some d' by simp [Store.extend, h_ne_addr]; exact h_store)
        (value_equiv_extend_store h_val h_fresh)
        h_closed

theorem handler_equiv_weaken (x : Var)
    (h : HandlerEquiv σ ρ hh h_anf)
    (h_fresh : σ a = none)
    (h_fresh_env : ρ x = none) :
    HandlerEquiv (Store.extend σ a d) (Env.extend ρ x a) hh h_anf :=
  match h with
  | .mk h_ret h_ops =>
    .mk (comp_equiv_weaken x h_ret h_fresh h_fresh_env) (op_clauses_equiv_weaken x h_ops h_fresh h_fresh_env)

theorem op_clauses_equiv_weaken (x : Var)
    (h : OpClausesEquiv σ ρ bp_ops anf_ops)
    (h_fresh : σ a = none)
    (h_fresh_env : ρ x = none) :
    OpClausesEquiv (Store.extend σ a d) (Env.extend ρ x a) bp_ops anf_ops :=
  match h with
  | .nil => .nil
  | .cons h_comp h_rest =>
    .cons (comp_equiv_weaken x h_comp h_fresh h_fresh_env) (op_clauses_equiv_weaken x h_rest h_fresh h_fresh_env)

end -- mutual subst_binding / weaken

/-! ## Redundant substitution lemma

  If variable x is already bound in ρ to address a, and σ(a) = d,
  and e_bp is value-equivalent to d, then substituting e_bp for x
  on the B&P side is a no-op from the ANF equivalence perspective. -/

mutual

theorem expr_equiv_redundant_subst (x : Var)
    (h : ExprEquiv σ ρ e_expr ae)
    (h_bound : ρ x = some a)
    (h_store : σ a = some d)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = []) :
    ExprEquiv σ ρ (e_expr.subst x e_bp) ae :=
  match h with
  | .var => by
      rename_i y
      by_cases h_eq : y = x
      · subst h_eq
        simp [BP.Expr.subst_var_self]
        exact ExprEquiv.var_subst h_bound h_store h_val h_closed
      · rw [BP.Expr.subst_var_ne h_eq]; exact .var
  | .true_ => by simp [BP.Expr.subst_true]; exact .true_
  | .false_ => by simp [BP.Expr.subst_false]; exact .false_
  | .unit => by simp [BP.Expr.subst_unit]; exact .unit
  | .zero => by simp [BP.Expr.subst_zero]; exact .zero
  | .succ h_inner => by
      simp [BP.Expr.subst_succ]
      exact .succ (expr_equiv_redundant_subst x h_inner h_bound h_store h_val h_closed)
  | .lam h_body => by
      rename_i _ _ z
      by_cases h_eq : z = x
      · rw [h_eq, BP.Expr.subst_lam_self]; exact .lam h_body
      · rw [BP.Expr.subst_lam_ne h_eq]
        exact .lam (comp_equiv_redundant_subst x h_body h_bound h_store h_val h_closed)
  | .var_subst h_rho h_store' h_val' h_closed' => by
      rw [BP.Expr.subst_of_fvs_nil h_closed']
      exact .var_subst h_rho h_store' h_val' h_closed'

theorem comp_equiv_redundant_subst (x : Var)
    (h : CompEquiv σ ρ c e)
    (h_bound : ρ x = some a)
    (h_store : σ a = some d)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = []) :
    CompEquiv σ ρ (c.subst x e_bp) e :=
  match h with
  | .tail h_cexp =>
    .tail (comp_equiv_cexp_redundant_subst x h_cexp h_bound h_store h_val h_closed)
  | .letE h_cexp h_c2 => by
      rename_i _ _ _ y _
      by_cases h_eq : y = x
      · rw [h_eq, BP.Comp.subst_letIn_self]
        exact .letE (comp_equiv_cexp_redundant_subst x h_cexp h_bound h_store h_val h_closed) h_c2
      · rw [BP.Comp.subst_letIn_ne h_eq]
        exact .letE (comp_equiv_cexp_redundant_subst x h_cexp h_bound h_store h_val h_closed)
          (comp_equiv_redundant_subst x h_c2 h_bound h_store h_val h_closed)
  | .letRec h_c1 h_c2 => by
      rename_i _ _ _ _ f_rec x_rec _
      by_cases hf : x = f_rec
      · subst hf; rw [BP.Comp.subst_letRec_self_f]; exact .letRec h_c1 h_c2
      · by_cases hy : x = x_rec
        · subst hy; rw [BP.Comp.subst_letRec_self_y hf]
          exact .letRec h_c1 (comp_equiv_redundant_subst x h_c2 h_bound h_store h_val h_closed)
        · rw [BP.Comp.subst_letRec_ne hf hy]
          exact .letRec (comp_equiv_redundant_subst x h_c1 h_bound h_store h_val h_closed)
            (comp_equiv_redundant_subst x h_c2 h_bound h_store h_val h_closed)

theorem comp_equiv_cexp_redundant_subst (x : Var)
    (h : CompEquivCExp σ ρ c ce)
    (h_bound : ρ x = some a)
    (h_store : σ a = some d)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = []) :
    CompEquivCExp σ ρ (c.subst x e_bp) ce :=
  match h with
  | .atomic h_expr => by
      simp [BP.Comp.subst_val]
      exact .atomic (expr_equiv_redundant_subst x h_expr h_bound h_store h_val h_closed)
  | .funApp h_e1 h_e2 => by
      simp [BP.Comp.subst_app]
      exact .funApp (expr_equiv_redundant_subst x h_e1 h_bound h_store h_val h_closed)
        (expr_equiv_redundant_subst x h_e2 h_bound h_store h_val h_closed)
  | .ifE h_expr h_c1 h_c2 => by
      simp [BP.Comp.subst_ifThenElse]
      exact .ifE (expr_equiv_redundant_subst x h_expr h_bound h_store h_val h_closed)
        (comp_equiv_redundant_subst x h_c1 h_bound h_store h_val h_closed)
        (comp_equiv_redundant_subst x h_c2 h_bound h_store h_val h_closed)
  | .matchNat h_expr h_c1 h_c2 => by
      rename_i _ _ _ _ y
      by_cases h_eq : y = x
      · rw [h_eq, BP.Comp.subst_matchNat_self]
        exact .matchNat (expr_equiv_redundant_subst x h_expr h_bound h_store h_val h_closed)
          (comp_equiv_redundant_subst x h_c1 h_bound h_store h_val h_closed) h_c2
      · rw [BP.Comp.subst_matchNat_ne h_eq]
        exact .matchNat (expr_equiv_redundant_subst x h_expr h_bound h_store h_val h_closed)
          (comp_equiv_redundant_subst x h_c1 h_bound h_store h_val h_closed)
          (comp_equiv_redundant_subst x h_c2 h_bound h_store h_val h_closed)
  | .opApp h_expr => by
      simp [BP.Comp.subst_opCall]
      exact .opApp (expr_equiv_redundant_subst x h_expr h_bound h_store h_val h_closed)
  | .handler h_hdl h_c => by
      simp [BP.Comp.subst_withHandle]
      exact .handler (handler_equiv_redundant_subst x h_hdl h_bound h_store h_val h_closed)
        (comp_equiv_redundant_subst x h_c h_bound h_store h_val h_closed)

theorem handler_equiv_redundant_subst (x : Var)
    (h : HandlerEquiv σ ρ hh h_anf)
    (h_bound : ρ x = some a)
    (h_store : σ a = some d)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = []) :
    HandlerEquiv σ ρ (hh.subst x e_bp) h_anf :=
  match h with
  | .mk h_ret h_ops => by
    simp only [BP.BPHandler.subst]
    split
    · exact .mk h_ret (op_clauses_equiv_redundant_subst x h_ops h_bound h_store h_val h_closed)
    · exact .mk (comp_equiv_redundant_subst x h_ret h_bound h_store h_val h_closed)
        (op_clauses_equiv_redundant_subst x h_ops h_bound h_store h_val h_closed)

theorem op_clauses_equiv_redundant_subst (x : Var)
    (h : OpClausesEquiv σ ρ bp_ops anf_ops)
    (h_bound : ρ x = some a)
    (h_store : σ a = some d)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = []) :
    OpClausesEquiv σ ρ
      (bp_ops.map fun p => (p.1, p.2.1, if p.2.1 = x || "resume" = x then p.2.2 else p.2.2.subst x e_bp))
      anf_ops :=
  match h with
  | .nil => .nil
  | .cons h_comp h_rest => by
    simp only [List.map]
    split
    · exact .cons h_comp (op_clauses_equiv_redundant_subst x h_rest h_bound h_store h_val h_closed)
    · exact .cons (comp_equiv_redundant_subst x h_comp h_bound h_store h_val h_closed)
        (op_clauses_equiv_redundant_subst x h_rest h_bound h_store h_val h_closed)

end -- mutual redundant_subst

/-! ## Environment extension preserves equivalence -/

mutual

theorem expr_equiv_extend_env
    (h : ExprEquiv σ ρ e_bp ae) (x : Var) (a : VAddr)
    (h_none : ρ x = none) :
    ExprEquiv σ (ρ.extend x a) e_bp ae :=
  match h with
  | .var => .var
  | .true_ => .true_
  | .false_ => .false_
  | .unit => .unit
  | .zero => .zero
  | .succ h_inner => .succ (expr_equiv_extend_env h_inner x a h_none)
  | .lam h_body => .lam (comp_equiv_extend_env h_body x a h_none)
  | .var_subst (y := y) h_rho h_store h_val h_fvs =>
    have h_ne : y ≠ x := by grind
    have : (ρ.extend x a) y = (ρ y) := by simp [Env.extend, h_ne]
    .var_subst (this ▸ h_rho) h_store h_val h_fvs

theorem comp_equiv_extend_env
    (h : CompEquiv σ ρ c e) (x : Var) (a : VAddr)
    (h_none : ρ x = none) :
    CompEquiv σ (ρ.extend x a) c e :=
  match h with
  | .tail h_cexp => .tail (comp_equiv_cexp_extend_env h_cexp x a h_none)
  | .letE h_cexp h_c2 =>
    .letE (comp_equiv_cexp_extend_env h_cexp x a h_none)
          (comp_equiv_extend_env h_c2 x a h_none)
  | .letRec h_c1 h_c2 =>
    .letRec (comp_equiv_extend_env h_c1 x a h_none)
            (comp_equiv_extend_env h_c2 x a h_none)

theorem comp_equiv_cexp_extend_env
    (h : CompEquivCExp σ ρ c ce) (x : Var) (a : VAddr)
    (h_none : ρ x = none) :
    CompEquivCExp σ (ρ.extend x a) c ce :=
  match h with
  | .atomic h_expr => .atomic (expr_equiv_extend_env h_expr x a h_none)
  | .funApp h_e1 h_e2 =>
    .funApp (expr_equiv_extend_env h_e1 x a h_none)
            (expr_equiv_extend_env h_e2 x a h_none)
  | .ifE h_expr h_c1 h_c2 =>
    .ifE (expr_equiv_extend_env h_expr x a h_none)
         (comp_equiv_extend_env h_c1 x a h_none)
         (comp_equiv_extend_env h_c2 x a h_none)
  | .matchNat h_expr h_c1 h_c2 =>
    .matchNat (expr_equiv_extend_env h_expr x a h_none)
              (comp_equiv_extend_env h_c1 x a h_none)
              (comp_equiv_extend_env h_c2 x a h_none)
  | .opApp h_expr => .opApp (expr_equiv_extend_env h_expr x a h_none)
  | .handler h_hdl h_c =>
    .handler (handler_equiv_extend_env h_hdl x a h_none)
             (comp_equiv_extend_env h_c x a h_none)

theorem handler_equiv_extend_env
    (h : HandlerEquiv σ ρ h_bp h_anf) (x : Var) (a : VAddr)
    (h_none : ρ x = none) :
    HandlerEquiv σ (ρ.extend x a) h_bp h_anf :=
  match h with
  | .mk h_ret h_ops =>
    .mk (comp_equiv_extend_env h_ret x a h_none)
        (op_clauses_equiv_extend_env h_ops x a h_none)

theorem op_clauses_equiv_extend_env
    (h : OpClausesEquiv σ ρ ops ops') (x : Var) (a : VAddr)
    (h_none : ρ x = none) :
    OpClausesEquiv σ (ρ.extend x a) ops ops' :=
  match h with
  | .nil => .nil
  | .cons h_c h_rest =>
    .cons (comp_equiv_extend_env h_c x a h_none)
          (op_clauses_equiv_extend_env h_rest x a h_none)

end -- mutual extend_env

/-! ## findBranch computation -/

@[simp, grind =] theorem findBranch_true (e1 e2 : Exp) :
    findBranch [Branch.branch ConLabel.true_ [] e1,
                Branch.branch ConLabel.false_ [] e2] ConLabel.true_ = some ([], e1) := by simp

@[simp, grind =] theorem findBranch_false (e1 e2 : Exp) :
    findBranch [Branch.branch ConLabel.true_ [] e1,
                Branch.branch ConLabel.false_ [] e2] ConLabel.false_ = some ([], e2) := by simp

@[simp, grind =] theorem findBranch_zero (e1 : Exp) (xs : List Var) (e2 : Exp) :
    findBranch [Branch.branch ConLabel.zero [] e1,
                Branch.branch ConLabel.succ xs e2] ConLabel.zero = some ([], e1) := by simp

@[simp, grind =] theorem findBranch_succ (e1 : Exp) (xs : List Var) (e2 : Exp) :
    findBranch [Branch.branch ConLabel.zero [] e1,
                Branch.branch ConLabel.succ xs e2] ConLabel.succ = some (xs, e2) := by simp
/-! ## ValueEquiv inversion helpers -/

@[simp, grind ->] theorem value_equiv_true_inv :
    ValueEquiv σ BP.Expr.true_ d → d = Denotable.conLabel ConLabel.true_ := by
  intro h; cases h; rfl

@[simp, grind ->]theorem value_equiv_false_inv :
    ValueEquiv σ BP.Expr.false_ d → d = Denotable.conLabel ConLabel.false_ := by
  intro h; cases h; rfl

@[simp, grind ->] theorem value_equiv_zero_inv :
    ValueEquiv σ BP.Expr.zero d → d = Denotable.conLabel ConLabel.zero := by
  intro h; cases h; rfl

@[simp, grind ->] theorem value_equiv_succ_inv :
    ValueEquiv σ (BP.Expr.succ e') d →
    ∃ a d', d = Denotable.succVal a ∧ σ a = some d' ∧ ValueEquiv σ e' d' := by
  intro h; cases h with
  | succ h_store h_val => exact ⟨_, _, rfl, h_store, h_val⟩

/-! ## ResultEquiv inversion helpers -/

@[simp, grind ->] theorem result_equiv_value_inv :
    ResultEquiv σ (BP.Result.value e') v →
    ∃ d, v = Value.den d ∧ ValueEquiv σ e' d := by
  intro h; cases h with
  | value h_val => exact ⟨_, rfl, h_val⟩

@[simp, grind ->] theorem result_equiv_op_inv :
    ResultEquiv σ (BP.Result.op op e_op x_c c_op) v →
    ∃ a d κ, v = Value.suspended op [a] κ ∧ σ a = some d ∧
      ValueEquiv σ e_op d ∧ KontEquiv σ x_c c_op κ := by
  intro h; cases h with
  | op h_store h_val h_kont => exact ⟨_, _, _, rfl, h_store, h_val, h_kont⟩

/-! ## Handler hasOp correspondence -/

@[simp] theorem op_clauses_any_equiv
    (h : OpClausesEquiv σ ρ bp_ops anf_ops) :
    bp_ops.any (fun (op', _, _) => op' == op) = anf_ops.any (fun (op', _, _) => op' == op) :=
  match h with
  | .nil => rfl
  | .cons _ h_rest => by simp only [List.any_cons]; congr 1; exact op_clauses_any_equiv h_rest

@[simp] theorem handler_hasOp_equiv :
    HandlerEquiv σ ρ h_bp h_anf →
    h_bp.hasOp op = h_anf.hasOp op := by
  intro h
  cases h with
  | mk _ h_ops =>
    simp only [BP.BPHandler.hasOp, Handler.hasOp]
    exact op_clauses_any_equiv h_ops

/-! ## Handler extraction helpers -/

/-- Extract the ANF handler from a HandlerEquiv proof -/
def HandlerEquiv.getAnf : HandlerEquiv σ ρ h_bp h_anf → Handler := fun _ => h_anf

/-! ## Handler findOp correspondence -/

@[simp] theorem op_clauses_findOp_equiv
    (h : OpClausesEquiv σ ρ bp_ops anf_ops)
    (h_find : bp_ops.findSome? (fun p => if p.1 = op then some (p.2.1, p.2.2) else none) = some (x_op, c_bp)) :
    ∃ e_anf, anf_ops.findSome? (fun p => if p.1 = op then some (p.2.1, p.2.2) else none) = some (x_op, e_anf) ∧
      CompEquiv σ ρ c_bp e_anf :=
  match h with
  | .nil => by simp [List.findSome?] at h_find
  | .cons h_comp h_rest => by
    rename_i _ _ op_hd x_hd
    simp only [List.findSome?] at h_find ⊢
    by_cases h_eq : op_hd = op
    · simp [h_eq] at h_find ⊢
      obtain ⟨rfl, rfl⟩ := h_find
      exact And.intro rfl h_comp
    · simp [h_eq] at h_find ⊢
      exact op_clauses_findOp_equiv h_rest h_find

@[simp] theorem handler_findOp_equiv
    (h : HandlerEquiv σ ρ h_bp h_anf)
    (h_find : h_bp.findOp op = some (x_op, c_bp)) :
    ∃ e_anf, h_anf.findOp op = some (x_op, e_anf) ∧ CompEquiv σ ρ c_bp e_anf := by
  cases h with
  | mk _ h_ops =>
    simp only [BP.BPHandler.findOp, Handler.findOp] at h_find ⊢
    exact op_clauses_findOp_equiv h_ops h_find

/-! ## Closedness for B&P subst -/

/-- Closed comp whose only free var is x, after subst with closed expr, is closed -/
theorem bp_comp_subst_closed_of_fvs_sub {c : BP.Comp} {x : BP.Var} {e : BP.Expr} :
    (∀ v, v ∈ c.fvs → v = x) →
    e.fvs = [] →
    (c.subst x e).fvs = [] :=
  BP.Comp.fvs_subst_closed

/-- After subst, remaining fvs are the non-x fvs of original -/
theorem bp_comp_subst_fvs_sub {c : BP.Comp} {x : BP.Var} {e : BP.Expr} :
    (∀ v, v ∈ c.fvs → v = x ∨ v = y) →
    e.fvs = [] →
    ∀ v, v ∈ (c.subst x e).fvs → v = y := by
  intro h_fvs h_e_closed v hv
  rcases BP.Comp.fvs_subst_sub hv with ⟨hc, hne⟩ | he
  · rcases h_fvs v hc with rfl | rfl
    · exact absurd rfl hne
    · rfl
  · rw [h_e_closed] at he; simp at he

/-! ## Additional FVS decomposition -/

@[grind ->] theorem bp_opCall_fvs {op : BP.OpName} {e : BP.Expr} :
    (BP.Comp.opCall op e).fvs = [] → e.fvs = [] := by simp

@[grind ->] theorem bp_val_fvs {e : BP.Expr} :
    (BP.Comp.val e).fvs = [] → e.fvs = [] := by simp

@[grind ->] theorem bp_app_fvs_e1 {e1 e2 : BP.Expr} :
    (BP.Comp.app e1 e2).fvs = [] → e1.fvs = [] := by simp; grind

@[grind ->] theorem bp_app_fvs_e2 {e1 e2 : BP.Expr} :
    (BP.Comp.app e1 e2).fvs = [] → e2.fvs = [] := by simp

private theorem opsFvs_eq_flatMap (ops : List (BP.OpName × BP.Var × BP.Comp)) :
    BP.opsFvs ops = ops.flatMap (fun p => (BP.Comp.fvs p.2.2).filter (fun v => v ≠ p.2.1 && v ≠ "resume")) := by
  induction ops with
  | nil => simp [BP.opsFvs]
  | cons hd tl ih =>
    unfold BP.opsFvs
    rw [List.flatMap_cons, ih]
    simp only [BP.Comp.fvs]

@[grind ->] theorem bp_withHandle_fvs_hdl {h : BP.BPHandler} {c : BP.Comp} :
    (BP.Comp.withHandle h c).fvs = [] → h.fvs = [] := by
  rw [BP.Comp.fvs_withHandle]; intro h_fvs
  have h1 := (append_eq_nil h_fvs).1
  simp only [BP.BPHandler.fvs]
  rw [← opsFvs_eq_flatMap]
  exact h1

theorem not_mem_withHandle_hdl_fvs {h : BP.BPHandler} {c : BP.Comp} {x : Var}
    (h_closed : (BP.Comp.withHandle h c).fvs = []) : x ∉ h.fvs := by
  rw [bp_withHandle_fvs_hdl h_closed]; exact nofun

@[grind ->] theorem bp_withHandle_fvs_c {h : BP.BPHandler} {c : BP.Comp} :
    (BP.Comp.withHandle h c).fvs = [] → c.fvs = [] := by
  rw [BP.Comp.fvs_withHandle]; intro h_fvs
  exact (append_eq_nil h_fvs).2

@[grind ->] theorem bp_letRec_fvs {f x : BP.Var} {c1 c2 : BP.Comp} :
    (BP.Comp.letRec f x c1 c2).fvs = [] →
    (∀ v, v ∈ c1.fvs → v = f ∨ v = x) ∧ (∀ v, v ∈ c2.fvs → v = f) := by
  rw [BP.Comp.fvs_letRec]; intro h
  have ⟨h1, h2⟩ := append_eq_nil h
  constructor
  · intro v hv
    have := filter_eq_nil_mem h1 v hv
    simp at this
    grind
  · intro v hv
    have := filter_eq_nil_mem h2 v hv
    simp at this
    exact this

@[grind ->] theorem bp_withHandle_ret_fvs {x_ret : BP.Var} {c_ret : BP.Comp} {ops : List (BP.OpName × BP.Var × BP.Comp)} {c : BP.Comp} :
    (BP.Comp.withHandle ⟨(x_ret, c_ret), ops⟩ c).fvs = [] →
    ∀ v, v ∈ c_ret.fvs → v = x_ret := by
  rw [BP.Comp.fvs_withHandle]; intro h_fvs v hv
  have ⟨h_hdl, _⟩ := append_eq_nil h_fvs
  simp only at h_hdl
  have ⟨h_ret, _⟩ := append_eq_nil h_hdl
  have := filter_eq_nil_mem h_ret v hv; simp at this; exact this

@[grind ->] theorem bp_withHandle_ops_fvs {x_ret : BP.Var} {c_ret : BP.Comp} {ops : List (BP.OpName × BP.Var × BP.Comp)} {c : BP.Comp} :
    (BP.Comp.withHandle ⟨(x_ret, c_ret), ops⟩ c).fvs = [] →
    BP.opsFvs ops = [] := by
  rw [BP.Comp.fvs_withHandle]; intro h_fvs
  have ⟨h_hdl, _⟩ := append_eq_nil h_fvs
  simp only at h_hdl
  exact (append_eq_nil h_hdl).2

private theorem bp_opsFvs_findOp_fvs :
    BP.opsFvs ops = [] →
    ops.findSome? (fun p => if p.1 = op then some (p.2.1, p.2.2) else none) = some (x, c_h) →
    ∀ v, v ∈ c_h.fvs → v = x ∨ v = "resume" := by
  intro h_ops h_find v hv
  induction ops with
  | nil => simp [List.findSome?] at h_find
  | cons hd tl ih =>
    obtain ⟨op', y, c'⟩ := hd
    simp only [List.findSome?] at h_find
    simp only [BP.opsFvs] at h_ops
    have ⟨h_fvs_hd, h_fvs_tl⟩ := append_eq_nil h_ops
    by_cases h_eq : op' = op
    · simp [h_eq] at h_find
      obtain ⟨rfl, rfl⟩ := h_find
      have := filter_eq_nil_mem h_fvs_hd v hv
      simp [decide_eq_false_iff_not] at this
      grind
    · simp [h_eq] at h_find
      exact ih h_fvs_tl h_find

theorem bp_findOp_fvs {h : BP.BPHandler} {op : BP.OpName} :
    (BP.Comp.withHandle h c).fvs = [] →
    h.findOp op = some (x, c_h) →
    ∀ v, v ∈ c_h.fvs → v = x ∨ v = "resume" := by
  intro h_closed h_find
  obtain ⟨⟨x_ret, c_ret⟩, ops⟩ := h
  have h_ops := bp_withHandle_ops_fvs h_closed
  simp [BP.BPHandler.findOp] at h_find
  exact bp_opsFvs_findOp_fvs h_ops h_find

/-! ## B&P closedness lemmas -/

/-- B&P evaluation of closed terms produces closed results (general) -/
@[grind ->] theorem bp_eval_closed :
    BP.Eval c r → c.fvs = [] →
    match r with
    | BP.Result.value e' => e'.fvs = []
    | BP.Result.op _ e_op x_c c_op => e_op.fvs = [] ∧ (∀ v, v ∈ c_op.fvs → v = x_c) := by
  intro h_eval h_closed
  induction h_eval with
  | val => grind
  | if_true _ ih => exact ih (bp_if_fvs_c1 h_closed)
  | if_false _ ih => exact ih (bp_if_fvs_c2 h_closed)
  | match_zero _ ih => exact ih (bp_matchNat_fvs_c1 h_closed)
  | match_succ _ ih =>
    have h_fvs_scrut := bp_matchNat_fvs_scrutinee h_closed
    simp [BP.Expr.fvs_succ] at h_fvs_scrut
    exact ih (bp_comp_subst_closed_of_fvs_sub (bp_matchNat_fvs_c2 h_closed) h_fvs_scrut)
  | let_val _ _ ih1 ih2 =>
    have h_e'_closed := ih1 (bp_letIn_fvs_c1 h_closed)
    exact ih2 (bp_comp_subst_closed_of_fvs_sub (bp_letIn_fvs_c2 h_closed) h_e'_closed)
  | let_op _ ih =>
    have ⟨h_eop, h_cop⟩ := ih (bp_letIn_fvs_c1 h_closed)
    refine ⟨h_eop, fun v hv => ?_⟩
    rw [BP.Comp.fvs_letIn] at hv
    rcases List.mem_append.mp hv with h1 | h2
    · exact h_cop v h1
    · grind
  | op_call =>
    simp [BP.Comp.fvs_opCall] at h_closed
    exact ⟨h_closed, fun v hv => by simp [BP.Comp.fvs_val, BP.Expr.fvs_var] at hv; exact hv⟩
  | app_lam _ ih =>
    rename_i x_lam c_body e_arg _
    have h_fvs_e2 := bp_app_fvs_e2 h_closed
    have h_fvs_e1 := bp_app_fvs_e1 h_closed
    have h_body_fvs : ∀ v, v ∈ c_body.fvs → v = x_lam := by
      intro v hv
      have h_filt := BP.Expr.fvs_lam ▸ h_fvs_e1
      have := filter_eq_nil_mem h_filt v hv
      simp at this; exact this
    exact ih (bp_comp_subst_closed_of_fvs_sub h_body_fvs h_fvs_e2)
  | let_rec _ ih =>
    rename_i f_rec x_rec c1_bp c2_bp _
    have ⟨h_c1_fvs, h_c2_fvs⟩ := bp_letRec_fvs h_closed
    have h_lam_closed : (BP.Expr.lam x_rec (BP.Comp.letRec f_rec x_rec c1_bp c1_bp)).fvs = [] := by
      rw [BP.Expr.fvs_lam, BP.Comp.fvs_letRec, List.filter_append]
      suffices h : (c1_bp.fvs.filter (fun v => decide (v ≠ f_rec) && decide (v ≠ x_rec))).filter (fun v => decide (v ≠ x_rec)) = [] ∧
          (c1_bp.fvs.filter (fun v => decide (v ≠ f_rec))).filter (fun v => decide (v ≠ x_rec)) = [] by
        rw [h.1, h.2]; rfl
      refine ⟨?_, ?_⟩ <;> {
        apply List.filter_eq_nil_iff.mpr; intro v hv
        have hv' := (List.mem_filter.mp hv).1
        have hv_pred := (List.mem_filter.mp hv).2
        rcases h_c1_fvs v hv' with rfl | rfl <;> simp_all
      }
    exact ih (bp_comp_subst_closed_of_fvs_sub h_c2_fvs h_lam_closed)
  | handle_val _ h_eq _ ih1 ih2 =>
    have h_c_closed := bp_withHandle_fvs_c h_closed
    have h_e'_closed : BP.Expr.fvs _ = [] := ih1 h_c_closed
    -- Extract return clause fvs from handler closedness
    have h_hdl_fvs := h_closed
    rw [BP.Comp.fvs_withHandle] at h_hdl_fvs
    have ⟨h_ret_fvs, _⟩ := append_eq_nil h_hdl_fvs
    have ⟨h_ret_fvs', _⟩ := append_eq_nil h_ret_fvs
    -- h_eq : (x_ret, c_ret) = h.returnClause, so h.returnClause.1 = x_ret, .2 = c_ret
    rw [← h_eq] at h_ret_fvs'
    simp at h_ret_fvs'
    exact ih2 (bp_comp_subst_closed_of_fvs_sub h_ret_fvs' h_e'_closed)
  | handle_op _ h_findOp _ ih1 ih2 =>
    rename_i c_bp op_bp e_op_bp x_c_bp c_op_bp x_bp c_h_bp r_bp h_bp _ _
    have h_c_closed := bp_withHandle_fvs_c h_closed
    obtain ⟨h_eop_closed, h_cop_fvs⟩ := ih1 h_c_closed
    have h_ch_fvs := bp_findOp_fvs h_closed h_findOp
    -- Handler fvs are empty from the original withHandle closedness
    have h_wh := h_closed; rw [BP.Comp.fvs_withHandle] at h_wh
    have ⟨h_hdl_empty, _⟩ := append_eq_nil h_wh
    have ⟨h_ret_empty, h_ops_empty⟩ := append_eq_nil h_hdl_empty
    -- Build closedness of kont lambda
    have h_kont_closed : (BP.Expr.lam x_c_bp (BP.Comp.withHandle h_bp c_op_bp)).fvs = [] := by
      simp only [BP.Expr.fvs_lam, BP.Comp.fvs_withHandle]
      rw [h_ret_empty, h_ops_empty]
      simp only [List.nil_append, List.append_nil]
      apply List.filter_eq_nil_iff.mpr; intro v hv
      have := h_cop_fvs v hv; grind
    have h_subst1_fvs := bp_comp_subst_fvs_sub h_ch_fvs h_eop_closed
    have h_subst2_closed := bp_comp_subst_closed_of_fvs_sub h_subst1_fvs h_kont_closed
    exact ih2 h_subst2_closed
  | handle_forward _ _ ih => grind

/-- B&P evaluation of closed terms produces closed value results -/
theorem bp_eval_value_closed :
    BP.Eval c (BP.Result.value e') → c.fvs = [] → e'.fvs = [] := by
  intro h_eval h_closed; exact bp_eval_closed h_eval h_closed

/-- B&P evaluation of closed terms produces closed op results -/
theorem bp_eval_op_closed :
    BP.Eval c (BP.Result.op op e_op x_c c_op) → c.fvs = [] →
    e_op.fvs = [] ∧ (∀ v, v ∈ c_op.fvs → v = x_c) := by
  intro h_eval h_closed; exact bp_eval_closed h_eval h_closed

/-- The kont lambda (fun x_c => with h handle c_op) is closed
    when the original withHandle h c is closed and c ⇓ #op e_op x_c c_op -/
theorem bp_kont_lam_closed
    (h_eval : BP.Eval c (BP.Result.op op e_op x_c c_op))
    (h_wh_closed : (BP.Comp.withHandle h c).fvs = []) :
    (BP.Expr.lam x_c (BP.Comp.withHandle h c_op)).fvs = [] := by
  have h_c_closed := bp_withHandle_fvs_c h_wh_closed
  have ⟨_, h_cop_fvs⟩ := bp_eval_op_closed h_eval h_c_closed
  have h_wh := h_wh_closed; rw [BP.Comp.fvs_withHandle] at h_wh
  have ⟨h_hdl_empty, _⟩ := append_eq_nil h_wh
  have ⟨h_ret_empty, h_ops_empty⟩ := append_eq_nil h_hdl_empty
  simp only [BP.Expr.fvs_lam, BP.Comp.fvs_withHandle]
  rw [h_ret_empty, h_ops_empty]
  simp only [List.nil_append, List.append_nil]
  apply List.filter_eq_nil_iff.mpr; intro v hv
  have := h_cop_fvs v hv; grind

end DMCFA
