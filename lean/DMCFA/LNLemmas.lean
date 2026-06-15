/-
  Key lemmas for the equivalence proof (locally nameless, full ANF-LN rewrite)

  - Store monotonicity
  - Local-closedness invariants
  - `evalAtomic` correspondence
  - Open-binding (THE key substitution-environment correspondence lemma)
  - Fresh address existence (axiom)
  - B&P closedness preservation
-/

import DMCFA.LNEquivalence
import DMCFA.LNBPSemantics
import DMCFA.LNSemantics

namespace DMCFA.LN

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

/-- Extending a store with the value it already holds at `a` is a no-op. -/
theorem Store.extend_self {σ : Store} {a : VAddr} {d : Denotable} (h : σ a = some d) :
    Store.extend σ a d = σ := by
  funext a'
  by_cases he : a' = a
  · subst he; simp [Store.extend, h]
  · simp [Store.extend, he]

/-- Store.extend commutes when addresses differ -/
theorem Store.extend_comm {σ : Store} {a1 a2 : VAddr} {d1 d2 : Denotable} (h : a1 ≠ a2) :
    (σ.extend a1 d1).extend a2 d2 = (σ.extend a2 d2).extend a1 d1 := by grind

/-- Freshness through extend with different address -/
@[simp] theorem Store.fresh_extend_of_fresh {σ : Store} {a1 a2 : VAddr} {d : Denotable}
    (h_fresh : σ a1 = none) (h_ne : a1 ≠ a2) :
    (σ.extend a2 d) a1 = none := by grind

/-! ## Env.push lookup helpers

Pushing onto `Env`'s address stack resolves `bvar 0` to the new address and
shifts all other indices down by one (`bvar (i+1)` resolves as `bvar i` did
before the push). Since pushing never overwrites an existing entry, there is
no "freshness in `ρ`'s domain" side-condition anywhere. -/

@[simp] theorem Env.lookup_push_zero (ρ : Env) (a : VAddr) : (ρ.push a).lookup 0 = some a := by
  simp [Env.lookup, Env.push]

@[simp] theorem Env.lookup_push_succ (ρ : Env) (a : VAddr) (i : Nat) :
    (ρ.push a).lookup (i + 1) = ρ.lookup i := by
  simp [Env.lookup, Env.push]

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
  | .eval_funApp_clos _ _ _ h_fresh _ _ h_σ _ h_eval =>
    fun a d h_in => by
      apply eval_store_mono h_eval; subst h_σ
      rename_i ds as_v _ _ _ _ _ _ _
      have h_ne : ∀ p ∈ as_v.zip ds, p.1 ≠ a := by
        intro ⟨a', d'⟩ h_mem h_eq; subst h_eq
        exact absurd ((List.forall₂_iff_zip.mp h_fresh).2 h_mem) (by simp [h_in])
      exact foldl_extend_preserves _ _ _ _ h_in h_ne
  | .eval_opApp _ => fun _ _ h_in => h_in
  | .eval_funApp_kont _ _ h_apply h_handle =>
    fun a d h_in =>
      eval_handle_store_mono h_handle a d (eval_apply_store_mono h_apply a d h_in)
  | .eval_fun h_fresh _ h_σ' =>
    fun a d h_in => by subst h_σ'; grind
  | .eval_match _ _ _ h_eval =>
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

@[grind ->] theorem bp_letIn_fvs_c1 {c1 c2 : BPLN.Comp} :
    (BPLN.Comp.letIn c1 c2).fvs = [] → c1.fvs = [] := by simp; grind

/-- In locally-nameless form, `c2`'s own binder is `bvar 0`, never an `fvar`,
    so closedness of the whole `letIn` makes `c2` itself closed outright. -/
@[grind ->] theorem bp_letIn_fvs_c2 {c1 c2 : BPLN.Comp} :
    (BPLN.Comp.letIn c1 c2).fvs = [] → c2.fvs = [] := by simp

@[grind ->] theorem bp_if_fvs_scrutinee {e : BPLN.Expr} {c1 c2 : BPLN.Comp} :
    (BPLN.Comp.ifThenElse e c1 c2).fvs = [] → e.fvs = [] := by simp; grind

@[grind ->] theorem bp_if_fvs_c1 {e : BPLN.Expr} {c1 c2 : BPLN.Comp} :
    (BPLN.Comp.ifThenElse e c1 c2).fvs = [] → c1.fvs = [] := by simp; grind

@[grind ->] theorem bp_if_fvs_c2 {e : BPLN.Expr} {c1 c2 : BPLN.Comp} :
    (BPLN.Comp.ifThenElse e c1 c2).fvs = [] → c2.fvs = [] := by simp

@[grind ->] theorem bp_matchNat_fvs_scrutinee {e : BPLN.Expr} {c1 c2 : BPLN.Comp} :
    (BPLN.Comp.matchNat e c1 c2).fvs = [] → e.fvs = [] := by simp; grind

@[grind ->] theorem bp_matchNat_fvs_c1 {e : BPLN.Expr} {c1 c2 : BPLN.Comp} :
    (BPLN.Comp.matchNat e c1 c2).fvs = [] → c1.fvs = [] := by simp; grind

/-- `c2`'s binder (`bvar 0`) is never an `fvar`, so closedness of the whole
    `matchNat` makes `c2` itself closed outright. -/
@[grind ->] theorem bp_matchNat_fvs_c2 {e : BPLN.Expr} {c1 c2 : BPLN.Comp} :
    (BPLN.Comp.matchNat e c1 c2).fvs = [] → c2.fvs = [] := by simp

@[grind ->] theorem bp_letRec_fvs_c1 {c1 c2 : BPLN.Comp} :
    (BPLN.Comp.letRec c1 c2).fvs = [] → c1.fvs = [] := by simp; grind

@[grind ->] theorem bp_letRec_fvs_c2 {c1 c2 : BPLN.Comp} :
    (BPLN.Comp.letRec c1 c2).fvs = [] → c2.fvs = [] := by simp

/-! ## Local-closedness invariants for the equivalence relations

These mirror the depth counter `n` on the B&P side: every relation that
relates a B&P term `t` to an ANF term at depth `n` guarantees `t` has no
loose bound variables beyond `n`. The `ValueEquiv`/`KontEquiv` cases (which
carry no `n`) are fully closed (`lc`) resp. 1-open (`compLcAt 1`, matching the
"resume slot" `bvar 0`). This is what lets the open-binding lemma below treat
`var_subst`'s inlined value as a no-op under `exprOpenRec`/`compOpenRec`. -/

/-- `compLcAt`'s `withHandle` equation, stated for an opaque handler `h`
    (the raw equation pattern-matches on `h`'s fields, which doesn't fire by
    `simp` against an opaque variable). -/
private theorem compLcAt_withHandle (n : Nat) (h : BPLN.BPHandler) (c : BPLN.Comp) :
    BPLN.compLcAt n (BPLN.Comp.withHandle h c) ↔
      BPLN.compLcAt (n+1) h.returnClause ∧ BPLN.opsLcAt (n+2) h.opClauses ∧ BPLN.compLcAt n c := by
  cases h with
  | mk c_ret ops => simp [BPLN.compLcAt]

mutual

theorem value_equiv_lc (h : ValueEquiv σ e_bp d) : e_bp.lc :=
  match h with
  | .con_true => by simp [BPLN.Expr.lc, BPLN.exprLcAt]
  | .con_false => by simp [BPLN.Expr.lc, BPLN.exprLcAt]
  | .con_unit => by simp [BPLN.Expr.lc, BPLN.exprLcAt]
  | .con_zero => by simp [BPLN.Expr.lc, BPLN.exprLcAt]
  | .succ _ h_val => by simp only [BPLN.Expr.lc, BPLN.exprLcAt]; exact value_equiv_lc h_val
  | .lambda h_body => by
    simp only [BPLN.Expr.lc, BPLN.exprLcAt]
    exact comp_equiv_lcAt h_body
  | .rec_lambda h_body _ => by
    simp only [BPLN.Expr.lc, BPLN.exprLcAt, BPLN.compLcAt]
    exact ⟨BPLN.compLcAt_mono _ 2 3 (comp_equiv_lcAt h_body) (by omega), comp_equiv_lcAt h_body⟩
  | .kont h_hdl h_kont => by
    simp only [BPLN.Expr.lc, BPLN.exprLcAt, compLcAt_withHandle]
    exact ⟨BPLN.compLcAt_mono _ 1 2 (handler_equiv_lcAt_ret h_hdl) (by omega),
     BPLN.opsLcAt_mono _ 2 3 (handler_equiv_lcAt_ops h_hdl) (by omega),
     kont_equiv_lcAt h_kont⟩

theorem expr_equiv_lcAt {n : Nat} (h : ExprEquiv σ ρ n e ae) : BPLN.exprLcAt n e :=
  match h with
  | .var_bound h_lt => by simp only [BPLN.exprLcAt]; exact h_lt
  | .true_ => by simp [BPLN.exprLcAt]
  | .false_ => by simp [BPLN.exprLcAt]
  | .unit => by simp [BPLN.exprLcAt]
  | .zero => by simp [BPLN.exprLcAt]
  | .succ h_inner => by simp only [BPLN.exprLcAt]; exact expr_equiv_lcAt h_inner
  | .lam h_body => by
    simp only [BPLN.exprLcAt]
    exact comp_equiv_lcAt h_body
  | .var_subst _ _ _ h_val _ => BPLN.exprLcAt_mono _ 0 _ (value_equiv_lc h_val) (Nat.zero_le _)

theorem comp_equiv_lcAt {n : Nat} (h : CompEquiv σ ρ n c e) : BPLN.compLcAt n c :=
  match h with
  | .tail h_cexp => comp_equiv_cexp_lcAt h_cexp
  | .letE h_cexp h_c2 => by
    simp only [BPLN.compLcAt]
    exact ⟨comp_equiv_cexp_lcAt h_cexp, comp_equiv_lcAt h_c2⟩
  | .letRec h_c1 h_c2 => by
    simp only [BPLN.compLcAt]
    exact ⟨comp_equiv_lcAt h_c1, comp_equiv_lcAt h_c2⟩

theorem comp_equiv_cexp_lcAt {n : Nat} (h : CompEquivCExp σ ρ n c ce) : BPLN.compLcAt n c :=
  match h with
  | .atomic h_expr => by simp only [BPLN.compLcAt]; exact expr_equiv_lcAt h_expr
  | .funApp h_e1 h_e2 => by
    simp only [BPLN.compLcAt]
    exact ⟨expr_equiv_lcAt h_e1, expr_equiv_lcAt h_e2⟩
  | .ifE h_expr h_c1 h_c2 => by
    simp only [BPLN.compLcAt]
    exact ⟨expr_equiv_lcAt h_expr, comp_equiv_lcAt h_c1, comp_equiv_lcAt h_c2⟩
  | .matchNat h_expr h_c1 h_c2 => by
    simp only [BPLN.compLcAt]
    exact ⟨expr_equiv_lcAt h_expr, comp_equiv_lcAt h_c1, comp_equiv_lcAt h_c2⟩
  | .opApp_bvar h_expr => by simp only [BPLN.compLcAt]; exact expr_equiv_lcAt h_expr
  | .handler h_hdl h_c => by
    simp only [compLcAt_withHandle]
    exact ⟨handler_equiv_lcAt_ret h_hdl, handler_equiv_lcAt_ops h_hdl, comp_equiv_lcAt h_c⟩

theorem op_clauses_equiv_lcAt {n : Nat}
    (h : OpClausesEquiv σ ρ n bp_ops anf_ops) : BPLN.opsLcAt (n + 2) bp_ops :=
  match h with
  | .nil => by simp [BPLN.opsLcAt]
  | .cons h_c h_rest => by
    simp only [BPLN.opsLcAt]
    exact ⟨comp_equiv_lcAt h_c, op_clauses_equiv_lcAt h_rest⟩

theorem handler_equiv_lcAt_ret {n : Nat}
    (h : HandlerEquiv σ ρ n hh h_anf) : BPLN.compLcAt (n + 1) hh.returnClause :=
  match h with
  | .mk h_ret _ => comp_equiv_lcAt h_ret

theorem handler_equiv_lcAt_ops {n : Nat}
    (h : HandlerEquiv σ ρ n hh h_anf) : BPLN.opsLcAt (n + 2) hh.opClauses :=
  match h with
  | .mk _ h_ops => op_clauses_equiv_lcAt h_ops

theorem kont_equiv_lcAt (h : KontEquiv σ c κ) : BPLN.compLcAt 1 c :=
  match h with
  | .kont_end => by simp only [BPLN.compLcAt, BPLN.exprLcAt]; omega
  | .kont_let h_inner h_c2 => by
    simp only [BPLN.compLcAt]
    exact ⟨kont_equiv_lcAt h_inner, BPLN.compLcAt_mono _ 1 2 (comp_equiv_lcAt h_c2) (by omega)⟩
  | .kont_handle h_inner h_hdl => by
    simp only [compLcAt_withHandle]
    exact ⟨BPLN.compLcAt_mono _ 1 2 (handler_equiv_lcAt_ret h_hdl) (by omega),
     BPLN.opsLcAt_mono _ 2 3 (handler_equiv_lcAt_ops h_hdl) (by omega),
     kont_equiv_lcAt h_inner⟩

end -- mutual lcAt invariants

/-! ## evalAtomic correspondence -/

/-- ExprEquiv + closed implies evalAtomic succeeds with corresponding value.
    At the top level `n = 0`, so `var_bound` (which needs `i < n`) is
    vacuous, and `resume` is impossible (`fvar "resume"` is never closed). -/
theorem expr_equiv_eval_atomic :
    ExprEquiv σ ρ 0 e_bp ae →
    e_bp.fvs = [] →
    ∃ d, evalAtomic ae ρ σ = some d ∧ ValueEquiv σ e_bp d := by
  intro h_equiv h_closed
  cases h_equiv with
  | var_bound h_lt => exact absurd h_lt (Nat.not_lt_zero _)
  | true_ => exact ⟨_, rfl, ValueEquiv.con_true⟩
  | false_ => exact ⟨_, rfl, ValueEquiv.con_false⟩
  | unit => exact ⟨_, rfl, ValueEquiv.con_unit⟩
  | zero => exact ⟨_, rfl, ValueEquiv.con_zero⟩
  | lam h_body => exact ⟨_, rfl, ValueEquiv.lambda h_body⟩
  | var_subst h_le h_rho h_store h_val _ =>
    refine ⟨_, ?_, h_val⟩
    simp only [Nat.sub_zero] at h_rho
    simp [evalAtomic, h_rho, h_store]
  | succ h_inner =>
    rename_i e_inner i
    have h_inner_closed : e_inner.fvs = [] := by
      simp [BPLN.Expr.fvs_succ] at h_closed; exact h_closed
    cases h_inner with
    | var_bound h_lt => exact absurd h_lt (Nat.not_lt_zero _)
    | var_subst h_le h_rho h_store h_val _ =>
      refine ⟨_, ?_, ValueEquiv.succ h_store h_val⟩
      simp only [Nat.sub_zero] at h_rho
      simp [evalAtomic, evalAddr, h_rho, h_store]

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
  | .kont h_hdl h_kont =>
    .kont (handler_equiv_store_mono h_hdl mono) (kont_equiv_store_mono h_kont mono)

/-- ExprEquiv is monotone in the store -/
theorem expr_equiv_store_mono
    (h : ExprEquiv σ ρ n e_bp ae)
    (mono : ∀ a d, σ a = some d → σ' a = some d) :
    ExprEquiv σ' ρ n e_bp ae :=
  match h with
  | .var_bound h_lt => .var_bound h_lt
  | .true_ => .true_
  | .false_ => .false_
  | .unit => .unit
  | .zero => .zero
  | .succ h_inner => .succ (expr_equiv_store_mono h_inner mono)
  | .lam h_body => .lam (comp_equiv_store_mono h_body mono)
  | .var_subst h_le h_rho h_store h_val h_closed =>
    .var_subst h_le h_rho (mono _ _ h_store) (value_equiv_store_mono h_val mono) h_closed

/-- CompEquiv is monotone in the store -/
theorem comp_equiv_store_mono
    (h : CompEquiv σ ρ n c e)
    (mono : ∀ a d, σ a = some d → σ' a = some d) :
    CompEquiv σ' ρ n c e :=
  match h with
  | .tail h_cexp => .tail (comp_equiv_cexp_store_mono h_cexp mono)
  | .letE h_cexp h_c2 =>
    .letE (comp_equiv_cexp_store_mono h_cexp mono) (comp_equiv_store_mono h_c2 mono)
  | .letRec h_c1 h_c2 =>
    .letRec (comp_equiv_store_mono h_c1 mono) (comp_equiv_store_mono h_c2 mono)

/-- CompEquivCExp is monotone in the store -/
theorem comp_equiv_cexp_store_mono
    (h : CompEquivCExp σ ρ n c ce)
    (mono : ∀ a d, σ a = some d → σ' a = some d) :
    CompEquivCExp σ' ρ n c ce :=
  match h with
  | .atomic h_expr => .atomic (expr_equiv_store_mono h_expr mono)
  | .funApp h_e1 h_e2 =>
    .funApp (expr_equiv_store_mono h_e1 mono) (expr_equiv_store_mono h_e2 mono)
  | .ifE h_expr h_c1 h_c2 =>
    .ifE (expr_equiv_store_mono h_expr mono) (comp_equiv_store_mono h_c1 mono) (comp_equiv_store_mono h_c2 mono)
  | .matchNat h_expr h_c1 h_c2 =>
    .matchNat (expr_equiv_store_mono h_expr mono) (comp_equiv_store_mono h_c1 mono) (comp_equiv_store_mono h_c2 mono)
  | .opApp_bvar h_expr => .opApp_bvar (expr_equiv_store_mono h_expr mono)
  | .handler h_hdl h_c =>
    .handler (handler_equiv_store_mono h_hdl mono) (comp_equiv_store_mono h_c mono)

/-- OpClausesEquiv is monotone in the store -/
theorem op_clauses_equiv_store_mono
    (h : OpClausesEquiv σ ρ n bp_ops anf_ops)
    (mono : ∀ a d, σ a = some d → σ' a = some d) :
    OpClausesEquiv σ' ρ n bp_ops anf_ops :=
  match h with
  | .nil => .nil
  | .cons h_comp h_rest =>
    .cons (comp_equiv_store_mono h_comp mono) (op_clauses_equiv_store_mono h_rest mono)

/-- HandlerEquiv is monotone in the store -/
theorem handler_equiv_store_mono
    (h : HandlerEquiv σ ρ n hh h_anf)
    (mono : ∀ a d, σ a = some d → σ' a = some d) :
    HandlerEquiv σ' ρ n hh h_anf :=
  match h with
  | .mk h_ret h_ops =>
    .mk (comp_equiv_store_mono h_ret mono) (op_clauses_equiv_store_mono h_ops mono)

/-- KontEquiv is monotone in the store -/
theorem kont_equiv_store_mono
    (h : KontEquiv σ c κ)
    (mono : ∀ a d, σ a = some d → σ' a = some d) :
    KontEquiv σ' c κ :=
  match h with
  | .kont_end => .kont_end
  | .kont_let h_inner h_c2 =>
    .kont_let (kont_equiv_store_mono h_inner mono) (comp_equiv_store_mono h_c2 mono)
  | .kont_handle h_inner h_hdl =>
    .kont_handle (kont_equiv_store_mono h_inner mono) (handler_equiv_store_mono h_hdl mono)

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

/-- Re-extending a store at an address `a` with the value it already holds
there is a no-op, so any `ValueEquiv σ` survives unchanged. -/
theorem value_equiv_extend_store_self {σ : Store} {a : VAddr} {d dx : Denotable} {e_bp : BPLN.Expr}
    (h_val : ValueEquiv σ e_bp dx) (h_store : σ a = some d) :
    ValueEquiv (Store.extend σ a d) e_bp dx := by
  rw [Store.extend_self h_store]; exact h_val

theorem expr_equiv_extend_store {n : Nat} :
    ExprEquiv σ ρ n e_bp ae →
    σ a_new = none →
    ExprEquiv (Store.extend σ a_new d_new) ρ n e_bp ae := by
  intro h hf; exact expr_equiv_store_mono h (store_extend_preserves_of_fresh σ a_new d_new hf)

theorem comp_equiv_extend_store {n : Nat} :
    CompEquiv σ ρ n c e →
    σ a_new = none →
    CompEquiv (Store.extend σ a_new d_new) ρ n c e := by
  intro h hf; exact comp_equiv_store_mono h (store_extend_preserves_of_fresh σ a_new d_new hf)

theorem comp_equiv_cexp_extend_store {n : Nat} :
    CompEquivCExp σ ρ n c ce →
    σ a_new = none →
    CompEquivCExp (Store.extend σ a_new d_new) ρ n c ce := by
  intro h hf; exact comp_equiv_cexp_store_mono h (store_extend_preserves_of_fresh σ a_new d_new hf)

theorem handler_equiv_extend_store {n : Nat} :
    HandlerEquiv σ ρ n hh h_anf →
    σ a_new = none →
    HandlerEquiv (Store.extend σ a_new d_new) ρ n hh h_anf := by
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
    KontEquiv σ c κ →
    σ a_new = none →
    KontEquiv (Store.extend σ a_new d_new) c κ := by
  intro h hf; exact kont_equiv_store_mono h (store_extend_preserves_of_fresh σ a_new d_new hf)

/-- If `σ.extend a1 d` maps `a2` to `none`, then `σ a2 = none`. -/
@[grind ->] theorem Store.fresh_of_fresh_extend {σ : Store} {a1 a2 : VAddr} {d : Denotable}
    (h_fresh_ext : (σ.extend a1 d) a2 = none) :
    σ a2 = none := by grind

/-- If `σ.extend a1 d` maps `a2` to `none`, then `a1 ≠ a2`. -/
@[simp, grind ->] theorem Store.ne_of_fresh_extend {σ : Store} {a1 a2 : VAddr} {d : Denotable}
    (h_fresh_ext : (σ.extend a1 d) a2 = none) :
    a1 ≠ a2 := by grind

/-! ## Open-binding (THE key lemma)

Opening the outermost open index `n` of a `(n+1)`-deep equivalence with a
fresh binding `a ↦ d` corresponds to B&P's `compOpenRec n e_bp _` /
`exprOpenRec n e_bp _`, and to the ANF side pushing `a` onto `ρ`'s address
stack (`Env.push`) while the ANF term itself stays syntactically unchanged.

The only freshness side condition is `σ a = none` (a real
store-address-allocation obligation, discharged via `exists_fresh`). There is
NO `ρ`-domain-freshness condition: `Env.push` never overwrites an existing
entry, so no Barendregt-style naming convention is needed. -/

mutual

theorem expr_equiv_open_binding {n : Nat}
    (h : ExprEquiv σ ρ (n + 1) e_expr ae)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = [])
    (h_fresh : σ a = none) :
    ExprEquiv (Store.extend σ a d) (ρ.push a) n (BPLN.exprOpenRec n e_bp e_expr) ae :=
  match h with
  | @ExprEquiv.var_bound i _ _ _ h_lt => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp h_lt with hi | hi
      · simp only [BPLN.Expr.open_bvar, if_neg (Nat.ne_of_lt hi)]
        exact .var_bound hi
      · subst hi
        simp only [BPLN.Expr.open_bvar]
        exact ExprEquiv.var_subst (a := a) (Nat.le_refl _)
          (by simp [Env.lookup_push_zero])
          (by simp [Store.extend])
          (value_equiv_extend_store h_val h_fresh)
          h_closed
  | .true_ => by simp only [BPLN.Expr.open_true]; exact .true_
  | .false_ => by simp only [BPLN.Expr.open_false]; exact .false_
  | .unit => by simp only [BPLN.Expr.open_unit]; exact .unit
  | .zero => by simp only [BPLN.Expr.open_zero]; exact .zero
  | .succ h_inner => by
      simp only [BPLN.Expr.open_succ]
      exact .succ (expr_equiv_open_binding h_inner h_val h_closed h_fresh)
  | .lam h_body => by
      simp only [BPLN.Expr.open_lam]
      exact .lam (comp_equiv_open_binding (n := n + 1) h_body h_val h_closed h_fresh)
  | .var_subst h_le h_rho h_store h_val_inner h_closed_inner => by
      rename_i i a' d'
      rw [BPLN.Expr.open_of_lc (value_equiv_lc h_val_inner) n e_bp]
      have h_an : n + 1 ≤ i := by omega
      have h_ax : a' ≠ a := by
        intro h_eq; subst h_eq
        rw [h_store] at h_fresh; exact absurd h_fresh (by simp)
      refine ExprEquiv.var_subst (a := a') (by omega) ?_ ?_
        (value_equiv_extend_store h_val_inner h_fresh) h_closed_inner
      · have h_eq : i - n = (i - (n + 1)) + 1 := by omega
        rw [h_eq, Env.lookup_push_succ, h_rho]
      · simp only [Store.extend_preserves _ _ _ _ h_ax, h_store]

theorem comp_equiv_open_binding {n : Nat}
    (h : CompEquiv σ ρ (n + 1) c e)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = [])
    (h_fresh : σ a = none) :
    CompEquiv (Store.extend σ a d) (ρ.push a) n (BPLN.compOpenRec n e_bp c) e :=
  match h with
  | .tail h_cexp =>
    .tail (comp_equiv_cexp_open_binding h_cexp h_val h_closed h_fresh)
  | .letE h_cexp h_c2 => by
      simp only [BPLN.Comp.open_letIn]
      exact .letE (comp_equiv_cexp_open_binding h_cexp h_val h_closed h_fresh)
        (comp_equiv_open_binding (n := n + 1) h_c2 h_val h_closed h_fresh)
  | .letRec h_c1 h_c2 => by
      simp only [BPLN.Comp.open_letRec]
      exact .letRec
        (comp_equiv_open_binding (n := n + 2) h_c1 h_val h_closed h_fresh)
        (comp_equiv_open_binding (n := n + 1) h_c2 h_val h_closed h_fresh)

theorem comp_equiv_cexp_open_binding {n : Nat}
    (h : CompEquivCExp σ ρ (n + 1) c ce)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = [])
    (h_fresh : σ a = none) :
    CompEquivCExp (Store.extend σ a d) (ρ.push a) n (BPLN.compOpenRec n e_bp c) ce :=
  match h with
  | .atomic h_expr => by
      simp only [BPLN.Comp.open_val]
      exact .atomic (expr_equiv_open_binding h_expr h_val h_closed h_fresh)
  | .funApp h_e1 h_e2 => by
      simp only [BPLN.Comp.open_app]
      exact .funApp (expr_equiv_open_binding h_e1 h_val h_closed h_fresh)
        (expr_equiv_open_binding h_e2 h_val h_closed h_fresh)
  | .ifE h_expr h_c1 h_c2 => by
      simp only [BPLN.Comp.open_ifThenElse]
      exact .ifE (expr_equiv_open_binding h_expr h_val h_closed h_fresh)
        (comp_equiv_open_binding h_c1 h_val h_closed h_fresh)
        (comp_equiv_open_binding h_c2 h_val h_closed h_fresh)
  | .matchNat h_expr h_c1 h_c2 => by
      simp only [BPLN.Comp.open_matchNat]
      exact .matchNat (expr_equiv_open_binding h_expr h_val h_closed h_fresh)
        (comp_equiv_open_binding h_c1 h_val h_closed h_fresh)
        (comp_equiv_open_binding (n := n + 1) h_c2 h_val h_closed h_fresh)
  | .opApp_bvar h_expr => by
      simp only [BPLN.Comp.open_opCall]
      exact .opApp_bvar (expr_equiv_open_binding h_expr h_val h_closed h_fresh)
  | .handler h_hdl h_c => by
      simp only [BPLN.Comp.open_withHandle]
      exact .handler (handler_equiv_open_binding h_hdl h_val h_closed h_fresh)
        (comp_equiv_open_binding h_c h_val h_closed h_fresh)

theorem handler_equiv_open_binding {n : Nat}
    (h : HandlerEquiv σ ρ (n + 1) hh h_anf)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = [])
    (h_fresh : σ a = none) :
    HandlerEquiv (Store.extend σ a d) (ρ.push a) n
      ⟨BPLN.compOpenRec (n + 1) e_bp hh.returnClause,
       BPLN.opsOpenRec (n + 2) e_bp hh.opClauses⟩ h_anf :=
  match h with
  | .mk h_ret h_ops =>
    .mk (comp_equiv_open_binding (n := n + 1) h_ret h_val h_closed h_fresh)
      (op_clauses_equiv_open_binding h_ops h_val h_closed h_fresh)

theorem op_clauses_equiv_open_binding {n : Nat}
    (h : OpClausesEquiv σ ρ (n + 1) bp_ops anf_ops)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = [])
    (h_fresh : σ a = none) :
    OpClausesEquiv (Store.extend σ a d) (ρ.push a) n
      (BPLN.opsOpenRec (n + 2) e_bp bp_ops) anf_ops :=
  match h with
  | .nil => by simp only [BPLN.opsOpenRec_nil]; exact .nil
  | .cons h_c h_rest => by
      simp only [BPLN.opsOpenRec_cons]
      exact .cons (comp_equiv_open_binding (n := n + 2) h_c h_val h_closed h_fresh)
        (op_clauses_equiv_open_binding h_rest h_val h_closed h_fresh)

end -- mutual open_binding

/-! ## Open-binding with address reuse

A variant of `comp_equiv_open_binding` for opening a binder with a value
`(e_bp, d)` that is *already* stored at address `a` (`σ a = some d`), rather
than a fresh address. Since `Store.extend σ a d = σ` in this case
(`Store.extend_self`), the store is unchanged by opening -- only `ρ` gains
`a` and the B&P term is opened. This is the variant needed when a recursive
closure's own (already-allocated) address is substituted for its `self`
binder. -/

mutual

theorem expr_equiv_open_binding_addr {n : Nat}
    (h : ExprEquiv σ ρ (n + 1) e_expr ae)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = [])
    (h_store : σ a = some d) :
    ExprEquiv σ (ρ.push a) n (BPLN.exprOpenRec n e_bp e_expr) ae :=
  match h with
  | @ExprEquiv.var_bound i _ _ _ h_lt => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp h_lt with hi | hi
      · simp only [BPLN.Expr.open_bvar, if_neg (Nat.ne_of_lt hi)]
        exact .var_bound hi
      · subst hi
        simp only [BPLN.Expr.open_bvar]
        exact ExprEquiv.var_subst (a := a) (Nat.le_refl _)
          (by simp [Env.lookup_push_zero])
          h_store
          h_val
          h_closed
  | .true_ => by simp only [BPLN.Expr.open_true]; exact .true_
  | .false_ => by simp only [BPLN.Expr.open_false]; exact .false_
  | .unit => by simp only [BPLN.Expr.open_unit]; exact .unit
  | .zero => by simp only [BPLN.Expr.open_zero]; exact .zero
  | .succ h_inner => by
      simp only [BPLN.Expr.open_succ]
      exact .succ (expr_equiv_open_binding_addr h_inner h_val h_closed h_store)
  | .lam h_body => by
      simp only [BPLN.Expr.open_lam]
      exact .lam (comp_equiv_open_binding_addr (n := n + 1) h_body h_val h_closed h_store)
  | .var_subst h_le h_rho h_store_av h_val_inner h_closed_inner => by
      rename_i i a' d'
      rw [BPLN.Expr.open_of_lc (value_equiv_lc h_val_inner) n e_bp]
      refine ExprEquiv.var_subst (a := a') (by omega) ?_ h_store_av h_val_inner h_closed_inner
      have h_eq : i - n = (i - (n + 1)) + 1 := by omega
      rw [h_eq, Env.lookup_push_succ, h_rho]

theorem comp_equiv_open_binding_addr {n : Nat}
    (h : CompEquiv σ ρ (n + 1) c e)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = [])
    (h_store : σ a = some d) :
    CompEquiv σ (ρ.push a) n (BPLN.compOpenRec n e_bp c) e :=
  match h with
  | .tail h_cexp =>
    .tail (comp_equiv_cexp_open_binding_addr h_cexp h_val h_closed h_store)
  | .letE h_cexp h_c2 => by
      simp only [BPLN.Comp.open_letIn]
      exact .letE (comp_equiv_cexp_open_binding_addr h_cexp h_val h_closed h_store)
        (comp_equiv_open_binding_addr (n := n + 1) h_c2 h_val h_closed h_store)
  | .letRec h_c1 h_c2 => by
      simp only [BPLN.Comp.open_letRec]
      exact .letRec
        (comp_equiv_open_binding_addr (n := n + 2) h_c1 h_val h_closed h_store)
        (comp_equiv_open_binding_addr (n := n + 1) h_c2 h_val h_closed h_store)

theorem comp_equiv_cexp_open_binding_addr {n : Nat}
    (h : CompEquivCExp σ ρ (n + 1) c ce)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = [])
    (h_store : σ a = some d) :
    CompEquivCExp σ (ρ.push a) n (BPLN.compOpenRec n e_bp c) ce :=
  match h with
  | .atomic h_expr => by
      simp only [BPLN.Comp.open_val]
      exact .atomic (expr_equiv_open_binding_addr h_expr h_val h_closed h_store)
  | .funApp h_e1 h_e2 => by
      simp only [BPLN.Comp.open_app]
      exact .funApp (expr_equiv_open_binding_addr h_e1 h_val h_closed h_store)
        (expr_equiv_open_binding_addr h_e2 h_val h_closed h_store)
  | .ifE h_expr h_c1 h_c2 => by
      simp only [BPLN.Comp.open_ifThenElse]
      exact .ifE (expr_equiv_open_binding_addr h_expr h_val h_closed h_store)
        (comp_equiv_open_binding_addr h_c1 h_val h_closed h_store)
        (comp_equiv_open_binding_addr h_c2 h_val h_closed h_store)
  | .matchNat h_expr h_c1 h_c2 => by
      simp only [BPLN.Comp.open_matchNat]
      exact .matchNat (expr_equiv_open_binding_addr h_expr h_val h_closed h_store)
        (comp_equiv_open_binding_addr h_c1 h_val h_closed h_store)
        (comp_equiv_open_binding_addr (n := n + 1) h_c2 h_val h_closed h_store)
  | .opApp_bvar h_expr => by
      simp only [BPLN.Comp.open_opCall]
      exact .opApp_bvar (expr_equiv_open_binding_addr h_expr h_val h_closed h_store)
  | .handler h_hdl h_c => by
      simp only [BPLN.Comp.open_withHandle]
      exact .handler (handler_equiv_open_binding_addr h_hdl h_val h_closed h_store)
        (comp_equiv_open_binding_addr h_c h_val h_closed h_store)

theorem handler_equiv_open_binding_addr {n : Nat}
    (h : HandlerEquiv σ ρ (n + 1) hh h_anf)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = [])
    (h_store : σ a = some d) :
    HandlerEquiv σ (ρ.push a) n
      ⟨BPLN.compOpenRec (n + 1) e_bp hh.returnClause,
       BPLN.opsOpenRec (n + 2) e_bp hh.opClauses⟩ h_anf :=
  match h with
  | .mk h_ret h_ops =>
    .mk (comp_equiv_open_binding_addr (n := n + 1) h_ret h_val h_closed h_store)
      (op_clauses_equiv_open_binding_addr h_ops h_val h_closed h_store)

theorem op_clauses_equiv_open_binding_addr {n : Nat}
    (h : OpClausesEquiv σ ρ (n + 1) bp_ops anf_ops)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = [])
    (h_store : σ a = some d) :
    OpClausesEquiv σ (ρ.push a) n
      (BPLN.opsOpenRec (n + 2) e_bp bp_ops) anf_ops :=
  match h with
  | .nil => by simp only [BPLN.opsOpenRec_nil]; exact .nil
  | .cons h_c h_rest => by
      simp only [BPLN.opsOpenRec_cons]
      exact .cons (comp_equiv_open_binding_addr (n := n + 2) h_c h_val h_closed h_store)
        (op_clauses_equiv_open_binding_addr h_rest h_val h_closed h_store)

end -- mutual open_binding_addr


/-! ## findBranch computation -/

@[simp, grind =] theorem findBranch_true (e1 e2 : Exp) :
    findBranch [Branch.branch ConLabel.true_ e1,
                Branch.branch ConLabel.false_ e2] ConLabel.true_ = some e1 := by
  simp [findBranch]

@[simp, grind =] theorem findBranch_false (e1 e2 : Exp) :
    findBranch [Branch.branch ConLabel.true_ e1,
                Branch.branch ConLabel.false_ e2] ConLabel.false_ = some e2 := by
  simp [findBranch]

@[simp, grind =] theorem findBranch_zero (e1 e2 : Exp) :
    findBranch [Branch.branch ConLabel.zero e1,
                Branch.branch ConLabel.succ e2] ConLabel.zero = some e1 := by
  simp [findBranch]

@[simp, grind =] theorem findBranch_succ (e1 e2 : Exp) :
    findBranch [Branch.branch ConLabel.zero e1,
                Branch.branch ConLabel.succ e2] ConLabel.succ = some e2 := by
  simp [findBranch]

/-! ## ValueEquiv inversion helpers -/

@[grind ->] theorem value_equiv_true_inv :
    ValueEquiv σ BPLN.Expr.true_ d → d = Denotable.conLabel ConLabel.true_ := by
  intro h; cases h; rfl

@[grind ->] theorem value_equiv_false_inv :
    ValueEquiv σ BPLN.Expr.false_ d → d = Denotable.conLabel ConLabel.false_ := by
  intro h; cases h; rfl

@[grind ->] theorem value_equiv_zero_inv :
    ValueEquiv σ BPLN.Expr.zero d → d = Denotable.conLabel ConLabel.zero := by
  intro h; cases h; rfl

@[simp, grind ->] theorem value_equiv_succ_inv :
    ValueEquiv σ (BPLN.Expr.succ e') d →
    ∃ a d', d = Denotable.succVal a ∧ σ a = some d' ∧ ValueEquiv σ e' d' := by
  intro h; cases h with
  | succ h_store h_val => exact ⟨_, _, rfl, h_store, h_val⟩

/-! ## ResultEquiv inversion helpers -/

@[simp, grind ->] theorem result_equiv_value_inv :
    ResultEquiv σ (BPLN.Result.value e') v →
    ∃ d, v = Value.den d ∧ ValueEquiv σ e' d := by
  intro h; cases h with
  | value h_val => exact ⟨_, rfl, h_val⟩

@[simp, grind ->] theorem result_equiv_op_inv :
    ResultEquiv σ (BPLN.Result.op op e_op c_op) v →
    ∃ a d κ, v = Value.suspended op [a] κ ∧ σ a = some d ∧
      ValueEquiv σ e_op d ∧ KontEquiv σ c_op κ := by
  intro h; cases h with
  | op h_store h_val h_kont => exact ⟨_, _, _, rfl, h_store, h_val, h_kont⟩

/-! ## Handler hasOp correspondence -/

@[simp] theorem op_clauses_any_equiv {n : Nat}
    (h : OpClausesEquiv σ ρ n bp_ops anf_ops) :
    bp_ops.any (fun (op', _) => op' == op) = anf_ops.any (fun (op', _) => op' == op) :=
  match h with
  | .nil => rfl
  | .cons _ h_rest => by simp only [List.any_cons]; congr 1; exact op_clauses_any_equiv h_rest

@[simp] theorem handler_hasOp_equiv {n : Nat} :
    HandlerEquiv σ ρ n h_bp h_anf →
    h_bp.hasOp op = h_anf.hasOp op := by
  intro h
  cases h with
  | mk _ h_ops =>
    simp only [BPLN.BPHandler.hasOp, Handler.hasOp]
    exact op_clauses_any_equiv h_ops

/-! ## Handler extraction helpers -/

/-- Extract the ANF handler from a HandlerEquiv proof -/
def HandlerEquiv.getAnf {n : Nat} : HandlerEquiv σ ρ n h_bp h_anf → Handler := fun _ => h_anf

/-! ## Handler findOp correspondence -/

@[simp] theorem op_clauses_findOp_equiv {n : Nat}
    (h : OpClausesEquiv σ ρ n bp_ops anf_ops)
    (h_find : bp_ops.findSome? (fun p => if p.1 = op then some p.2 else none) = some c_bp) :
    ∃ e_anf, anf_ops.findSome? (fun p => if p.1 = op then some p.2 else none) = some e_anf ∧
      CompEquiv σ ρ (n + 2) c_bp e_anf :=
  match h, h_find with
  | .nil, h_find => by simp [List.findSome?] at h_find
  | .cons h_comp h_rest, h_find => by
    rename_i _ _ _ _ op_hd
    simp only [List.findSome?] at h_find ⊢
    by_cases h_eq : op_hd = op
    · simp [h_eq] at h_find ⊢
      obtain rfl := h_find
      exact h_comp
    · simp [h_eq] at h_find ⊢
      exact op_clauses_findOp_equiv h_rest h_find

@[simp] theorem handler_findOp_equiv {n : Nat}
    (h : HandlerEquiv σ ρ n h_bp h_anf)
    (h_find : h_bp.findOp op = some c_bp) :
    ∃ e_anf, h_anf.findOp op = some e_anf ∧ CompEquiv σ ρ (n + 2) c_bp e_anf := by
  cases h with
  | mk _ h_ops =>
    simp only [BPLN.BPHandler.findOp, Handler.findOp] at h_find ⊢
    exact op_clauses_findOp_equiv h_ops h_find

/-! ## Additional FVS decomposition -/

@[grind ->] theorem bp_opCall_fvs {op : BPLN.OpName} {e : BPLN.Expr} :
    (BPLN.Comp.opCall op e).fvs = [] → e.fvs = [] := by simp

@[grind ->] theorem bp_val_fvs {e : BPLN.Expr} :
    (BPLN.Comp.val e).fvs = [] → e.fvs = [] := by simp

@[grind ->] theorem bp_app_fvs_e1 {e1 e2 : BPLN.Expr} :
    (BPLN.Comp.app e1 e2).fvs = [] → e1.fvs = [] := by simp; grind

@[grind ->] theorem bp_app_fvs_e2 {e1 e2 : BPLN.Expr} :
    (BPLN.Comp.app e1 e2).fvs = [] → e2.fvs = [] := by simp

@[grind ->] theorem bp_withHandle_fvs_hdl {h : BPLN.BPHandler} {c : BPLN.Comp} :
    (BPLN.Comp.withHandle h c).fvs = [] → h.fvs = [] := by
  rw [BPLN.Comp.fvs_withHandle]; intro h_fvs
  exact (append_eq_nil h_fvs).1

theorem not_mem_withHandle_hdl_fvs {h : BPLN.BPHandler} {c : BPLN.Comp} {x : BPLN.Var}
    (h_closed : (BPLN.Comp.withHandle h c).fvs = []) : x ∉ h.fvs := by
  rw [bp_withHandle_fvs_hdl h_closed]; exact nofun

@[grind ->] theorem bp_withHandle_fvs_c {h : BPLN.BPHandler} {c : BPLN.Comp} :
    (BPLN.Comp.withHandle h c).fvs = [] → c.fvs = [] := by
  rw [BPLN.Comp.fvs_withHandle]; intro h_fvs
  exact (append_eq_nil h_fvs).2

@[grind ->] theorem bp_withHandle_ret_fvs {h : BPLN.BPHandler} {c : BPLN.Comp} :
    (BPLN.Comp.withHandle h c).fvs = [] → h.returnClause.fvs = [] := by
  rw [BPLN.Comp.fvs_withHandle]; intro h_fvs
  exact (append_eq_nil (append_eq_nil h_fvs).1).1

@[grind ->] theorem bp_withHandle_ops_fvs {h : BPLN.BPHandler} {c : BPLN.Comp} :
    (BPLN.Comp.withHandle h c).fvs = [] → BPLN.opClauses_fvs h.opClauses = [] := by
  rw [BPLN.Comp.fvs_withHandle]; intro h_fvs
  exact (append_eq_nil (append_eq_nil h_fvs).1).2

/-- An op clause body found by `findOp` is closed (its binders -- the argument
    `bvar 0` and the continuation `resume` `bvar 1` -- contribute nothing to
    `fvs`, and the enclosing handler is closed). -/
private theorem bp_opsFvs_findOp_closed :
    BPLN.opClauses_fvs ops = [] →
    ops.findSome? (fun p => if p.1 = op then some p.2 else none) = some c_h →
    c_h.fvs = [] := by
  intro h_ops h_find
  induction ops with
  | nil => simp [List.findSome?] at h_find
  | cons hd tl ih =>
    obtain ⟨op', c'⟩ := hd
    simp only [List.findSome?] at h_find
    simp only [BPLN.opClauses_fvs_cons] at h_ops
    have ⟨h_fvs_hd, h_fvs_tl⟩ := append_eq_nil h_ops
    by_cases h_eq : op' = op
    · simp [h_eq] at h_find; obtain rfl := h_find; exact h_fvs_hd
    · simp [h_eq] at h_find; exact ih h_fvs_tl h_find

/-- An op clause body found by `findOp` (in a closed handler) is closed. -/
theorem bp_findOp_fvs {h : BPLN.BPHandler} {op : BPLN.OpName} {c : BPLN.Comp} :
    (BPLN.Comp.withHandle h c).fvs = [] →
    h.findOp op = some c_h →
    c_h.fvs = [] := by
  intro h_closed h_find
  have h_ops := bp_withHandle_ops_fvs h_closed
  simp only [BPLN.BPHandler.findOp] at h_find
  exact bp_opsFvs_findOp_closed h_ops h_find

/-! ## B&P closedness lemmas -/

/-- B&P evaluation of closed terms produces closed results (general) -/
@[grind ->] theorem bp_eval_closed :
    BPLN.Eval c r → c.fvs = [] →
    match r with
    | BPLN.Result.value e' => e'.fvs = []
    | BPLN.Result.op _ e_op c_op => e_op.fvs = [] ∧ c_op.fvs = [] := by
  intro h_eval h_closed
  induction h_eval with
  | val => simpa [BPLN.Comp.fvs_val] using h_closed
  | if_true _ ih => exact ih (bp_if_fvs_c1 h_closed)
  | if_false _ ih => exact ih (bp_if_fvs_c2 h_closed)
  | match_zero _ ih => exact ih (bp_matchNat_fvs_c1 h_closed)
  | match_succ _ ih =>
    have h_fvs_scrut := bp_matchNat_fvs_scrutinee h_closed
    simp only [BPLN.Expr.fvs_succ] at h_fvs_scrut
    exact ih (BPLN.Comp.fvs_open_closed (bp_matchNat_fvs_c2 h_closed) h_fvs_scrut)
  | let_val _ _ ih1 ih2 =>
    have h_e'_closed := ih1 (bp_letIn_fvs_c1 h_closed)
    exact ih2 (BPLN.Comp.fvs_open_closed (bp_letIn_fvs_c2 h_closed) h_e'_closed)
  | let_op _ ih =>
    have ⟨h_eop, h_cop⟩ := ih (bp_letIn_fvs_c1 h_closed)
    refine ⟨h_eop, ?_⟩
    rw [BPLN.Comp.fvs_letIn]
    simp [h_cop, bp_letIn_fvs_c2 h_closed]
  | op_call =>
    simp only [BPLN.Comp.fvs_opCall] at h_closed
    exact ⟨h_closed, by simp⟩
  | app_lam _ ih =>
    rw [BPLN.Comp.fvs_app, BPLN.Expr.fvs_lam] at h_closed
    have ⟨h_cbody, h_earg⟩ := append_eq_nil h_closed
    exact ih (BPLN.Comp.fvs_open_closed h_cbody h_earg)
  | let_rec _ ih =>
    rw [BPLN.Comp.fvs_letRec] at h_closed
    have ⟨h_c1, h_c2⟩ := append_eq_nil h_closed
    exact ih (BPLN.Comp.fvs_open_closed h_c2
      (by simp [BPLN.Expr.fvs_lam, BPLN.Comp.fvs_letRec, h_c1]))
  | handle_val _ _ ih1 ih2 =>
    rw [BPLN.Comp.fvs_withHandle] at h_closed
    have ⟨h1, h_c⟩ := append_eq_nil h_closed
    have ⟨h_ret, _⟩ := append_eq_nil h1
    have h_e'_closed := ih1 h_c
    exact ih2 (BPLN.Comp.fvs_open_closed h_ret h_e'_closed)
  | handle_op _ h_findOp _ ih1 ih2 =>
    have h_c_closed := bp_withHandle_fvs_c h_closed
    obtain ⟨h_eop_closed, h_cop_closed⟩ := ih1 h_c_closed
    have h_ch_closed := bp_findOp_fvs h_closed h_findOp
    have h_hdl_fvs := bp_withHandle_fvs_hdl h_closed
    have ⟨h_ret_fvs, h_ops_fvs⟩ := append_eq_nil h_hdl_fvs
    exact ih2 (BPLN.Comp.fvs_open_closed
      (BPLN.Comp.fvs_open_closed h_ch_closed
        (by simp [BPLN.Expr.fvs_lam, BPLN.Comp.fvs_withHandle, h_ret_fvs, h_ops_fvs, h_cop_closed]))
      h_eop_closed)
  | handle_forward _ _ ih =>
    have h_c_closed := bp_withHandle_fvs_c h_closed
    obtain ⟨h_eop_closed, h_cop_closed⟩ := ih h_c_closed
    have h_hdl_fvs := bp_withHandle_fvs_hdl h_closed
    have ⟨h_ret_fvs, h_ops_fvs⟩ := append_eq_nil h_hdl_fvs
    refine ⟨h_eop_closed, ?_⟩
    simp [BPLN.Comp.fvs_withHandle, h_ret_fvs, h_ops_fvs, h_cop_closed]

/-- B&P evaluation of closed terms produces closed value results -/
theorem bp_eval_value_closed :
    BPLN.Eval c (BPLN.Result.value e') → c.fvs = [] → e'.fvs = [] := by
  intro h_eval h_closed; exact bp_eval_closed h_eval h_closed

/-- B&P evaluation of closed terms produces closed op results -/
theorem bp_eval_op_closed :
    BPLN.Eval c (BPLN.Result.op op e_op c_op) → c.fvs = [] →
    e_op.fvs = [] ∧ c_op.fvs = [] := by
  intro h_eval h_closed; exact bp_eval_closed h_eval h_closed

/-- The kont lambda `fun → with h handle c_op` is closed
    when the original `with h handle c` is closed and `c ⇓ #op e_op c_op`. -/
theorem bp_kont_lam_closed
    (h_eval : BPLN.Eval c (BPLN.Result.op op e_op c_op))
    (h_wh_closed : (BPLN.Comp.withHandle h c).fvs = []) :
    (BPLN.Expr.lam (BPLN.Comp.withHandle h c_op)).fvs = [] := by
  have h_c_closed := bp_withHandle_fvs_c h_wh_closed
  have ⟨_, h_cop_closed⟩ := bp_eval_op_closed h_eval h_c_closed
  have h_hdl_fvs := bp_withHandle_fvs_hdl h_wh_closed
  have ⟨h_ret_fvs, h_ops_fvs⟩ := append_eq_nil h_hdl_fvs
  simp [BPLN.Expr.fvs_lam, BPLN.Comp.fvs_withHandle, h_ret_fvs, h_ops_fvs, h_cop_closed]

end DMCFA.LN
