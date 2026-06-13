/-
  Completeness: B&P evaluation → ANF evaluation (locally-nameless rewrite)

  Uses height-indexed EvalN with strong Nat induction proving both standard
  completeness and kont-application completeness simultaneously. The height
  parameter lets us recurse on sub-sub-derivations (needed for sub-derivations
  unlocked by `let_rec`/`app_lam`).

  Binders are de Bruijn indices on both sides: substitution into a binding
  body is `comp_equiv_open_binding`/`expr_equiv_open_binding` (depth `n=0`)
  from `LNLemmas`, which carry no environment-domain-freshness side conditions.
-/

import DMCFA.LNLemmas

namespace DMCFA.LN

/-! ## Kont-shape impossibility lemmas

  For most BPLN.EvalN constructors (ifThenElse, matchNat, app, letRec, opCall),
  the computation shape cannot arise from kont opening (which only produces
  val, letIn, or withHandle shapes). -/

private theorem kont_subst_absurd_of_not_val_letIn_withHandle
    (h_kont : KontEquiv σ c_op κ)
    (h_eq : c' = BPLN.Comp.open_ c_op e_arg)
    (h_not_val : ∀ e, c' ≠ BPLN.Comp.val e)
    (h_not_letIn : ∀ c1 c2, c' ≠ BPLN.Comp.letIn c1 c2)
    (h_not_withHandle : ∀ h c, c' ≠ BPLN.Comp.withHandle h c) : False := by
  match h_kont with
  | .kont_end =>
    simp only [BPLN.Comp.open_, BPLN.compOpenRec, BPLN.Expr.open_bvar] at h_eq
    exact h_not_val _ h_eq
  | .kont_let _ _ =>
    simp only [BPLN.Comp.open_, BPLN.compOpenRec] at h_eq
    exact h_not_letIn _ _ h_eq
  | .kont_handle _ _ =>
    simp only [BPLN.Comp.open_, BPLN.Comp.open_withHandle] at h_eq
    exact h_not_withHandle _ _ h_eq

/-- Inversion for `EvalN` on `letRec`: extracts the inner derivation at a
strictly smaller height, so the result can feed a recursive call to
`completeness_combinedN` while leaving the decreasing proof to plain `omega`. -/
private theorem evalN_letRec_inv {n : Nat} {c1 c2 : BPLN.Comp} {r : BPLN.Result}
    (h : BPLN.EvalN n (BPLN.Comp.letRec c1 c2) r) :
    ∃ m, m < n ∧ BPLN.EvalN m (c2.open_ (BPLN.Expr.lam (BPLN.Comp.letRec c1 c1))) r := by
  cases h with
  | let_rec h_inner => exact ⟨_, by omega, h_inner⟩

/-! ## Main combined theorem -/

/-- Combined completeness (height-indexed): for any `EvalN n c r`, both standard
    completeness (P_comp) and kont-application completeness (P_kont) hold,
    both stated at depth `0` (fully resolved). -/
private theorem completeness_combinedN {n : Nat} (h_eval : BPLN.EvalN n c r) :
    -- P_comp
    (∀ (σ : Store) (ρ : Env) (e : Exp), CompEquiv σ ρ 0 c e → c.fvs = [] →
      ∃ v σ', EvalExp e ρ σ v σ' ∧ ResultEquiv σ' r v) ∧
    -- P_kont
    (∀ (σ : Store) (c_op : BPLN.Comp) (κ : Kont) (e_arg : BPLN.Expr) (d : Denotable),
      KontEquiv σ c_op κ →
      c = BPLN.Comp.open_ c_op e_arg →
      ValueEquiv σ e_arg d →
      (BPLN.Comp.open_ c_op e_arg).fvs = [] →
      e_arg.fvs = [] →
      ∃ v σ', ApplyKont κ d σ v σ' ∧ ResultEquiv σ' r v) := by
  match h_eval with
  | .val =>
    rename_i e_val
    refine ⟨?_, ?_⟩
    · intro σ ρ e h_equiv h_closed
      cases h_equiv with
      | tail h_cexp =>
        cases h_cexp with
        | atomic h_expr =>
          have h_fvs := bp_val_fvs h_closed
          obtain ⟨d, h_atomic, h_val⟩ := expr_equiv_eval_atomic h_expr h_fvs
          exact ⟨_, _, EvalExp.eval_tail (EvalCExp.eval_atomic h_atomic), ResultEquiv.value h_val⟩
    · intro σ c_op κ e_arg d h_kont h_eq h_val h_closed h_arg_closed
      match h_kont with
      | .kont_end =>
        simp only [BPLN.Comp.open_, BPLN.Comp.open_val, BPLN.Expr.open_bvar, if_pos] at h_eq
        injection h_eq with h_eq
        subst h_eq
        exact ⟨Value.den d, σ, ApplyKont.apply_continue, ResultEquiv.value h_val⟩
      | .kont_let _ _ =>
        simp only [BPLN.Comp.open_, BPLN.compOpenRec] at h_eq
        cases h_eq
      | .kont_handle _ _ =>
        simp only [BPLN.Comp.open_, BPLN.Comp.open_withHandle] at h_eq
        cases h_eq
  | .if_true h_sub =>
    have ⟨ih_comp, ih_kont⟩ := completeness_combinedN h_sub
    refine ⟨?_, ?_⟩
    · intro σ ρ e h_equiv h_closed
      cases h_equiv with
      | tail h_cexp =>
        cases h_cexp with
        | ifE h_expr h_c1 h_c2 =>
          obtain ⟨d, h_atomic, h_val⟩ := expr_equiv_eval_atomic h_expr (bp_if_fvs_scrutinee h_closed)
          have := value_equiv_true_inv h_val; subst this
          obtain ⟨v, σ', h_anf, h_res⟩ := ih_comp _ _ _ h_c1 (bp_if_fvs_c1 h_closed)
          exact ⟨v, σ', EvalExp.eval_tail (EvalCExp.eval_match h_atomic rfl (findBranch_true _ _) h_anf), h_res⟩
    · intro σ c_op κ e_arg d h_kont h_eq h_val h_closed h_arg_closed
      exact (kont_subst_absurd_of_not_val_letIn_withHandle h_kont h_eq
        (by intro e he; cases he) (by intro c1 c2 he; cases he) (by intro h c he; cases he)).elim
  | .if_false h_sub =>
    have ⟨ih_comp, ih_kont⟩ := completeness_combinedN h_sub
    refine ⟨?_, ?_⟩
    · intro σ ρ e h_equiv h_closed
      cases h_equiv with
      | tail h_cexp =>
        cases h_cexp with
        | ifE h_expr h_c1 h_c2 =>
          obtain ⟨d, h_atomic, h_val⟩ := expr_equiv_eval_atomic h_expr (bp_if_fvs_scrutinee h_closed)
          have := value_equiv_false_inv h_val; subst this
          obtain ⟨v, σ', h_anf, h_res⟩ := ih_comp _ _ _ h_c2 (bp_if_fvs_c2 h_closed)
          exact ⟨v, σ', EvalExp.eval_tail (EvalCExp.eval_match h_atomic rfl (findBranch_false _ _) h_anf), h_res⟩
    · intro σ c_op κ e_arg d h_kont h_eq h_val h_closed h_arg_closed
      exact (kont_subst_absurd_of_not_val_letIn_withHandle h_kont h_eq
        (by intro e he; cases he) (by intro c1 c2 he; cases he) (by intro h c he; cases he)).elim
  | .match_zero h_sub =>
    have ⟨ih_comp, ih_kont⟩ := completeness_combinedN h_sub
    refine ⟨?_, ?_⟩
    · intro σ ρ e h_equiv h_closed
      cases h_equiv with
      | tail h_cexp =>
        cases h_cexp with
        | matchNat h_expr h_c1 h_c2 =>
          obtain ⟨d, h_atomic, h_val⟩ := expr_equiv_eval_atomic h_expr (bp_matchNat_fvs_scrutinee h_closed)
          have := value_equiv_zero_inv h_val; subst this
          obtain ⟨v, σ', h_anf, h_res⟩ := ih_comp _ _ _ h_c1 (bp_matchNat_fvs_c1 h_closed)
          exact ⟨v, σ', EvalExp.eval_tail (EvalCExp.eval_match h_atomic rfl (findBranch_zero _ _) h_anf), h_res⟩
    · intro σ c_op κ e_arg d h_kont h_eq h_val h_closed h_arg_closed
      exact (kont_subst_absurd_of_not_val_letIn_withHandle h_kont h_eq
        (by intro e he; cases he) (by intro c1 c2 he; cases he) (by intro h c he; cases he)).elim
  | .match_succ h_sub =>
    have ⟨ih_comp, ih_kont⟩ := completeness_combinedN h_sub
    refine ⟨?_, ?_⟩
    · intro σ ρ e h_equiv h_closed
      cases h_equiv with
      | tail h_cexp =>
        cases h_cexp with
        | matchNat h_expr h_c1 h_c2 =>
          have h_fvs_scrut := bp_matchNat_fvs_scrutinee h_closed
          obtain ⟨d, h_atomic, h_val⟩ := expr_equiv_eval_atomic h_expr h_fvs_scrut
          obtain ⟨a_inner, d_inner, rfl, h_store, h_val_inner⟩ := value_equiv_succ_inv h_val
          simp only [BPLN.Expr.fvs_succ] at h_fvs_scrut
          obtain ⟨a_fresh, h_fresh⟩ := exists_fresh σ
          have h_open := comp_equiv_open_binding (n := 0) h_c2 h_val_inner h_fvs_scrut h_fresh
          have h_open_closed := BPLN.Comp.fvs_open_closed (k := 0) (bp_matchNat_fvs_c2 h_closed) h_fvs_scrut
          obtain ⟨v, σ', h_anf, h_res⟩ := ih_comp _ _ _ h_open h_open_closed
          exact ⟨v, σ', EvalExp.eval_tail (EvalCExp.eval_match_succ h_atomic
            (findBranch_succ _ _) h_store h_fresh rfl rfl h_anf), h_res⟩
    · intro σ c_op κ e_arg d h_kont h_eq h_val h_closed h_arg_closed
      exact (kont_subst_absurd_of_not_val_letIn_withHandle h_kont h_eq
        (by intro e he; cases he) (by intro c1 c2 he; cases he) (by intro h c he; cases he)).elim
  | .let_val h_eval_c1 h_eval_c2 =>
    have ⟨ih1_comp, ih1_kont⟩ := completeness_combinedN h_eval_c1
    have ⟨ih2_comp, ih2_kont⟩ := completeness_combinedN h_eval_c2
    rename_i c1_bp c2_bp e'_val r_bp
    refine ⟨?_, ?_⟩
    · -- P_comp
      intro σ ρ e h_equiv h_closed
      cases h_equiv with
      | tail h_cexp => cases h_cexp
      | letE h_cexp h_c2 =>
        have h_fvs_c1 := bp_letIn_fvs_c1 h_closed
        obtain ⟨v1, σ1, h_eval1, h_res1⟩ := ih1_comp _ _ _ (CompEquiv.tail (l := 0) h_cexp) h_fvs_c1
        obtain ⟨d1, rfl, h_val1⟩ := result_equiv_value_inv h_res1
        cases h_eval1 with
        | eval_tail h_cexp_eval =>
          have h_mono := eval_store_mono (EvalExp.eval_tail (l := 0) h_cexp_eval)
          have h_c2_σ1 := comp_equiv_store_mono h_c2 h_mono
          obtain ⟨a, h_fresh⟩ := exists_fresh σ1
          have h_e'_closed := bp_eval_value_closed (BPLN.evalN_to_eval h_eval_c1) h_fvs_c1
          have h_open := comp_equiv_open_binding (n := 0) h_c2_σ1 h_val1 h_e'_closed h_fresh
          have h_open_closed := BPLN.Comp.fvs_open_closed (k := 0) (bp_letIn_fvs_c2 h_closed) h_e'_closed
          obtain ⟨v2, σ2, h_eval2, h_res2⟩ := ih2_comp _ _ _ h_open h_open_closed
          exact ⟨v2, σ2,
            EvalExp.eval_let h_cexp_eval (ContinueFrame.continue_let h_fresh rfl h_eval2),
            h_res2⟩
    · -- P_kont
      intro σ c_op κ e_arg d h_kont h_eq h_val_arg h_closed_kont h_arg_closed
      match h_kont with
      | .kont_end =>
        simp only [BPLN.Comp.open_, BPLN.compOpenRec, BPLN.Expr.open_bvar] at h_eq
        cases h_eq
      | .kont_let h_kont_inner h_c2_equiv =>
        rename_i c_inner κ_rest ρ_kont c2 e2_kont
        simp only [BPLN.Comp.open_, BPLN.compOpenRec] at h_eq
        simp only [BPLN.Comp.open_, BPLN.Comp.open_letIn] at h_closed_kont
        obtain ⟨h_c1eq, h_c2eq⟩ := BPLN.Comp.letIn.inj h_eq
        simp only [Nat.zero_add] at h_c2eq
        have h_inner_closed : (BPLN.compOpenRec 0 e_arg c_inner).fvs = [] :=
          bp_letIn_fvs_c1 h_closed_kont
        obtain ⟨v_mid, σ_mid, h_apply_inner, h_res_inner⟩ :=
          ih1_kont _ _ _ _ _ h_kont_inner h_c1eq h_val_arg h_inner_closed h_arg_closed
        obtain ⟨d_mid, rfl, h_val_mid⟩ := result_equiv_value_inv h_res_inner
        have h_mono := eval_apply_store_mono h_apply_inner
        have h_c2_mono := comp_equiv_store_mono h_c2_equiv h_mono
        have h_c1_fvs : c1_bp.fvs = [] := by rw [h_c1eq]; exact h_inner_closed
        have h_e'_closed := bp_eval_value_closed (BPLN.evalN_to_eval h_eval_c1) h_c1_fvs
        obtain ⟨a_v, h_fresh_v⟩ := exists_fresh σ_mid
        have h_open := comp_equiv_open_binding (n := 0) h_c2_mono h_val_mid h_e'_closed h_fresh_v
        -- `compOpenRec 0 c2_bp r_bp = compOpenRec 0 c2_bp c2`, since
        -- `compOpenRec 0 c2_bp c2` is already fully closed (depth 0).
        have h_c2_lc := comp_equiv_lcAt h_open
        have h_comm := BPLN.Comp.open_open_comm (value_equiv_lc h_val_mid) (value_equiv_lc h_val_arg) c2
        have h_id := BPLN.Comp.open_of_lc h_c2_lc 1 e_arg
        have h_eq_chain : BPLN.compOpenRec 0 c2_bp r_bp = BPLN.compOpenRec 0 c2_bp c2 := by
          rw [h_c2eq, h_comm, h_id]
        have h_r_bp_fvs : r_bp.fvs = [] := by
          rw [h_c2eq]; exact bp_letIn_fvs_c2 h_closed_kont
        have h_open' : CompEquiv (Store.extend σ_mid a_v d_mid) (ρ_kont.push a_v) 0
            (BPLN.Comp.open_ r_bp c2_bp) e2_kont := by
          show CompEquiv _ _ _ (BPLN.compOpenRec 0 c2_bp r_bp) e2_kont
          rw [h_eq_chain]; exact h_open
        have h_open_closed : (BPLN.Comp.open_ r_bp c2_bp).fvs = [] :=
          BPLN.Comp.fvs_open_closed (k := 0) h_r_bp_fvs h_e'_closed
        obtain ⟨v_result, σ_result, h_eval_result, h_res_result⟩ :=
          ih2_comp _ _ _ h_open' h_open_closed
        exact ⟨v_result, σ_result,
          ApplyKont.apply_restore h_apply_inner (ContinueFrame.continue_let h_fresh_v rfl h_eval_result),
          h_res_result⟩
      | .kont_handle _ _ =>
        simp only [BPLN.Comp.open_, BPLN.Comp.open_withHandle] at h_eq
        cases h_eq
  | .let_op h_eval_c1 =>
    have ⟨ih_comp, ih_kont⟩ := completeness_combinedN h_eval_c1
    refine ⟨?_, ?_⟩
    · -- P_comp
      intro σ ρ e h_equiv h_closed
      cases h_equiv with
      | tail h_cexp => cases h_cexp
      | letE h_cexp h_c2 =>
        have h_fvs_c1 := bp_letIn_fvs_c1 h_closed
        obtain ⟨v1, σ1, h_eval1, h_res1⟩ := ih_comp _ _ _ (CompEquiv.tail (l := 0) h_cexp) h_fvs_c1
        obtain ⟨a, d_op, κ, rfl, h_store, h_val_op, h_kont⟩ := result_equiv_op_inv h_res1
        cases h_eval1 with
        | eval_tail h_cexp_eval =>
          have h_mono := eval_store_mono (EvalExp.eval_tail (l := 0) h_cexp_eval)
          have h_c2_σ1 := comp_equiv_store_mono h_c2 h_mono
          exact ⟨_, σ1,
            EvalExp.eval_let h_cexp_eval ContinueFrame.continue_op,
            ResultEquiv.op h_store h_val_op (KontEquiv.kont_let h_kont h_c2_σ1)⟩
    · -- P_kont
      intro σ c_op κ e_arg d h_kont h_eq h_val_arg h_closed_kont h_arg_closed
      match h_kont with
      | .kont_end =>
        simp only [BPLN.Comp.open_, BPLN.compOpenRec, BPLN.Expr.open_bvar] at h_eq
        cases h_eq
      | .kont_let h_kont_inner h_c2_equiv =>
        rename_i c_inner κ_rest ρ_kont c2 e2_kont
        simp only [BPLN.Comp.open_, BPLN.compOpenRec] at h_eq
        simp only [BPLN.Comp.open_, BPLN.Comp.open_letIn] at h_closed_kont
        obtain ⟨h_c1eq, h_c2eq⟩ := BPLN.Comp.letIn.inj h_eq
        have h_inner_closed : (BPLN.compOpenRec 0 e_arg c_inner).fvs = [] :=
          bp_letIn_fvs_c1 h_closed_kont
        obtain ⟨v_mid, σ_mid, h_apply_inner, h_res_inner⟩ :=
          ih_kont _ _ _ _ _ h_kont_inner h_c1eq h_val_arg h_inner_closed h_arg_closed
        obtain ⟨a_op, d_op, κ_op, rfl, h_store_op, h_val_op, h_kont_op⟩ := result_equiv_op_inv h_res_inner
        have h_mono := eval_apply_store_mono h_apply_inner
        have h_c2_mono := comp_equiv_store_mono h_c2_equiv h_mono
        -- `c2` is closed at depth 1, so opening it (at depth 1) with `e_arg` is the identity.
        simp only [Nat.zero_add] at h_c2eq
        rw [BPLN.comp_open_lc_at c2 1 1 e_arg (comp_equiv_lcAt h_c2_equiv) (le_refl 1)] at h_c2eq
        subst h_c2eq
        exact ⟨_, σ_mid,
          ApplyKont.apply_restore h_apply_inner ContinueFrame.continue_op,
          ResultEquiv.op h_store_op h_val_op (KontEquiv.kont_let h_kont_op h_c2_mono)⟩
      | .kont_handle _ _ =>
        simp only [BPLN.Comp.open_, BPLN.Comp.open_withHandle] at h_eq
        cases h_eq
  | .op_call =>
    refine ⟨?_, ?_⟩
    · intro σ ρ e h_equiv h_closed
      cases h_equiv with
      | tail h_cexp =>
        cases h_cexp with
        | opApp_bvar h_expr =>
          have h_fvs := bp_opCall_fvs h_closed
          cases h_expr with
          | var_bound h_lt => omega
          | var_subst h_le h_rho h_store h_val _ =>
            simp only [Nat.sub_zero] at h_rho
            exact ⟨_, _, EvalExp.eval_tail (EvalCExp.eval_opApp h_rho), ResultEquiv.op h_store h_val KontEquiv.kont_end⟩
    · intro σ c_op κ e_arg d h_kont h_eq h_val h_closed h_arg_closed
      exact (kont_subst_absurd_of_not_val_letIn_withHandle h_kont h_eq
        (by intro e he; cases he) (by intro c1 c2 he; cases he) (by intro h c he; cases he)).elim
  | .handle_forward h_eval_inner h_bp_not_has =>
    have ⟨ih_comp, ih_kont⟩ := completeness_combinedN h_eval_inner
    refine ⟨?_, ?_⟩
    · -- P_comp
      intro σ ρ e h_equiv h_closed
      cases h_equiv with
      | tail h_cexp =>
        cases h_cexp with
        | handler h_handler h_c =>
          have h_fvs_c := bp_withHandle_fvs_c h_closed
          obtain ⟨v1, σ1, h_eval1, h_res1⟩ := ih_comp _ _ _ h_c h_fvs_c
          obtain ⟨a, d_op, κ, rfl, h_store, h_val_op, h_kont⟩ := result_equiv_op_inv h_res1
          have h_mono := eval_store_mono h_eval1
          have h_hdl_σ1 := handler_equiv_store_mono h_handler h_mono
          have h_anf_not_has := (handler_hasOp_equiv h_hdl_σ1 ▸ h_bp_not_has : _ = false)
          exact ⟨_, σ1,
            EvalExp.eval_tail (EvalCExp.eval_handler h_eval1
              (HandleValue.handle_capture_op h_anf_not_has rfl)),
            ResultEquiv.op h_store h_val_op (KontEquiv.kont_handle h_kont h_hdl_σ1)⟩
    · -- P_kont
      intro σ c_op κ e_arg d h_kont h_eq h_val_arg h_closed h_arg_closed
      match h_kont with
      | .kont_end =>
        simp only [BPLN.Comp.open_, BPLN.compOpenRec, BPLN.Expr.open_bvar] at h_eq
        cases h_eq
      | .kont_let _ _ =>
        simp only [BPLN.Comp.open_, BPLN.compOpenRec] at h_eq
        cases h_eq
      | .kont_handle h_kont_inner h_hdl_inner =>
        rename_i c_inner_kont κ_rest ρ_hdl
        simp only [BPLN.Comp.open_, BPLN.Comp.open_withHandle] at h_eq h_closed
        obtain ⟨h_heq, h_ceq⟩ := BPLN.Comp.withHandle.inj h_eq
        subst h_ceq
        have h_inner_closed := bp_withHandle_fvs_c h_closed
        obtain ⟨v_mid, σ_mid, h_apply, h_res_mid⟩ :=
          ih_kont _ _ _ _ _ h_kont_inner rfl h_val_arg h_inner_closed h_arg_closed
        obtain ⟨a_op, d_op, κ_op, rfl, h_store_op, h_val_op, h_kont_op⟩ := result_equiv_op_inv h_res_mid
        have h_hdl_mono := handler_equiv_store_mono h_hdl_inner (eval_apply_store_mono h_apply)
        -- `κ_rest` is closed at depth 1 (`handler_equiv_lcAt_ret`/`_ops`), so opening it
        -- (at depth `0+1`) with `e_arg` is the identity; combined with `h_heq` this gives
        -- `h✝ = κ_rest`, letting us replace the opened handler with `κ_rest` everywhere.
        have h_ret_id : BPLN.compOpenRec (0+1) e_arg κ_rest.returnClause = κ_rest.returnClause :=
          BPLN.comp_open_lc_at κ_rest.returnClause 1 (0+1) e_arg (handler_equiv_lcAt_ret h_hdl_inner) (by omega)
        have h_ops_id : BPLN.opsOpenRec (0+2) e_arg κ_rest.opClauses = κ_rest.opClauses :=
          BPLN.ops_open_lc_at κ_rest.opClauses 2 (0+2) e_arg (handler_equiv_lcAt_ops h_hdl_inner) (by omega)
        rw [h_ret_id, h_ops_id] at h_heq
        have h_eta : (⟨κ_rest.returnClause, κ_rest.opClauses⟩ : BPLN.BPHandler) = κ_rest := by
          cases κ_rest; rfl
        rw [h_eta] at h_heq
        have h_heq' := h_heq.symm
        subst h_heq'
        have h_bp_not_has2 : κ_rest.hasOp _ = false := h_bp_not_has
        have h_anf_not_has := (handler_hasOp_equiv h_hdl_mono ▸ h_bp_not_has2 : _ = false)
        exact ⟨_, σ_mid,
          ApplyKont.apply_restore_handle h_apply
            (HandleValue.handle_capture_op h_anf_not_has rfl),
          ResultEquiv.op h_store_op h_val_op (KontEquiv.kont_handle h_kont_op h_hdl_mono)⟩
  | .app_lam h_eval_body =>
    rename_i cbody e_arg
    have ⟨ih_comp, ih_kont⟩ := completeness_combinedN h_eval_body
    refine ⟨?_, ?_⟩
    · -- P_comp
      intro σ ρ e h_equiv h_closed
      cases h_equiv with
      | tail h_cexp =>
        cases h_cexp with
        | funApp h_e1 h_e2 =>
          have h_fvs_e1 := bp_app_fvs_e1 h_closed
          have h_fvs_e2 := bp_app_fvs_e2 h_closed
          obtain ⟨d_fun, h_atomic1, h_val_lam⟩ := expr_equiv_eval_atomic h_e1 h_fvs_e1
          obtain ⟨d_arg, h_atomic2, h_val_arg⟩ := expr_equiv_eval_atomic h_e2 h_fvs_e2
          obtain ⟨a_arg, h_fresh_arg⟩ := exists_fresh σ
          cases h_val_lam with
          | lambda h_body =>
            rename_i ρ_clos e_body
            have h_cbody_fvs : cbody.fvs = [] := by
              simpa only [BPLN.Expr.fvs_lam] using h_fvs_e1
            have h_open := comp_equiv_open_binding (n := 0) h_body h_val_arg h_fvs_e2 h_fresh_arg
            have h_open_closed : (cbody.open_ e_arg).fvs = [] :=
              BPLN.Comp.fvs_open_closed h_cbody_fvs h_fvs_e2
            obtain ⟨v, σ', h_eval, h_res⟩ := ih_comp _ _ _ h_open h_open_closed
            exact ⟨v, σ',
              EvalExp.eval_tail (EvalCExp.eval_funApp_clos (ds := [d_arg]) (as_v := [a_arg])
                h_atomic1 (.cons h_atomic2 .nil) (.cons h_fresh_arg .nil)
                (List.nodup_singleton _) rfl rfl rfl h_eval),
              h_res⟩
          | rec_lambda h_c1_mono h_store_af =>
            rename_i ρ_clos c1_bp e1_anf a_f
            have h_c1_fvs : c1_bp.fvs = [] := by
              have h := h_fvs_e1
              simp only [BPLN.Expr.fvs_lam] at h
              exact bp_letRec_fvs_c1 h
            have h_lam_closed : (BPLN.Expr.lam (BPLN.Comp.letRec c1_bp c1_bp)).fvs = [] := by
              simp [h_c1_fvs]
            have h_ne_af_aarg : a_f ≠ a_arg := by
              intro h_eq; subst h_eq
              rw [h_fresh_arg] at h_store_af; simp at h_store_af
            have h_step1 :=
              comp_equiv_open_binding (n := 1) h_c1_mono h_val_arg h_fvs_e2 h_fresh_arg
            have h_store_af1 : (Store.extend σ a_arg d_arg) a_f =
                some (Denotable.closure ⟨e1_anf, ρ_clos, some a_f⟩) := by
              rw [Store.extend_preserves _ _ _ _ h_ne_af_aarg]; exact h_store_af
            have h_val_lam1 :=
              value_equiv_extend_store (d_new := d_arg)
                (ValueEquiv.rec_lambda h_c1_mono h_store_af) h_fresh_arg
            have h_step2 :=
              comp_equiv_open_binding_addr (n := 0) h_step1 h_val_lam1 h_lam_closed h_store_af1
            have h_X_eq : BPLN.compOpenRec 2 e_arg c1_bp = c1_bp :=
              BPLN.comp_open_lc_at c1_bp 2 2 e_arg (comp_equiv_lcAt h_c1_mono) (le_refl 2)
            have h_eval_body2 := h_eval_body
            simp only [BPLN.Comp.open_, BPLN.Comp.open_letRec, h_X_eq] at h_eval_body2
            obtain ⟨m, h_lt, h_inner⟩ := evalN_letRec_inv h_eval_body2
            have ⟨ih_comp', _⟩ := completeness_combinedN h_inner
            have h_c1_fvs' : (BPLN.compOpenRec 1 e_arg c1_bp).fvs = [] :=
              BPLN.Comp.fvs_open_closed h_c1_fvs h_fvs_e2
            have h_open_closed' :
                (BPLN.Comp.open_ (BPLN.compOpenRec 1 e_arg c1_bp)
                  (BPLN.Expr.lam (BPLN.Comp.letRec c1_bp c1_bp))).fvs = [] :=
              BPLN.Comp.fvs_open_closed (k := 0) h_c1_fvs' h_lam_closed
            obtain ⟨v, σ', h_eval, h_res⟩ := ih_comp' _ _ _ h_step2 h_open_closed'
            exact ⟨v, σ',
              EvalExp.eval_tail (EvalCExp.eval_funApp_clos (ds := [d_arg]) (as_v := [a_arg])
                h_atomic1 (.cons h_atomic2 .nil) (.cons h_fresh_arg .nil)
                (List.nodup_singleton _) rfl rfl rfl h_eval),
              h_res⟩
          | kont h_hdl_equiv h_kont_equiv =>
            rename_i ρ_h h_bp h_anf c_op_inner κ
            have h_combined_kont := KontEquiv.kont_handle h_kont_equiv h_hdl_equiv
            have h_cbody_fvs : (BPLN.Comp.withHandle h_bp c_op_inner).fvs = [] := by
              simpa only [BPLN.Expr.fvs_lam] using h_fvs_e1
            have h_body_closed : ((BPLN.Comp.withHandle h_bp c_op_inner).open_ e_arg).fvs = [] :=
              BPLN.Comp.fvs_open_closed h_cbody_fvs h_fvs_e2
            obtain ⟨v, σ', h_apply, h_res⟩ :=
              ih_kont σ (BPLN.Comp.withHandle h_bp c_op_inner) (Frame.handlerFrame h_anf ρ_h :: κ)
                e_arg d_arg h_combined_kont rfl h_val_arg h_body_closed h_fvs_e2
            cases h_apply with
            | apply_restore_handle h_apply_inner h_handle =>
              exact ⟨v, σ',
                EvalExp.eval_tail (EvalCExp.eval_funApp_kont h_atomic1 h_atomic2 h_apply_inner h_handle),
                h_res⟩
    · -- P_kont: app shape can't arise from kont opening
      intro σ c_op κ e_arg' d h_kont h_eq h_val h_closed h_arg_closed
      exact (kont_subst_absurd_of_not_val_letIn_withHandle h_kont h_eq
        (by intro e he; cases he) (by intro c1 c2 he; cases he) (by intro h c he; cases he)).elim
  | .let_rec h_eval_body =>
    rename_i c1_bp c2_bp
    have ⟨ih_comp, _⟩ := completeness_combinedN h_eval_body
    refine ⟨?_, ?_⟩
    · -- P_comp
      intro σ ρ e h_equiv h_closed
      cases h_equiv with
      | tail h_cexp => cases h_cexp
      | letRec h_c1 h_c2 =>
        rename_i e1_anf e2_anf l_anf
        obtain ⟨a_f, h_fresh_af⟩ := exists_fresh σ
        have h_c1_fvs := bp_letRec_fvs_c1 h_closed
        have h_c2_fvs := bp_letRec_fvs_c2 h_closed
        have h_lam_closed : (BPLN.Expr.lam (BPLN.Comp.letRec c1_bp c1_bp)).fvs = [] := by
          simp [h_c1_fvs]
        have h_c1_mono : CompEquiv (Store.extend σ a_f (Denotable.closure ⟨e1_anf, ρ, some a_f⟩)) ρ 2 c1_bp e1_anf :=
          comp_equiv_extend_store h_c1 h_fresh_af
        have h_val_rec : ValueEquiv (Store.extend σ a_f (Denotable.closure ⟨e1_anf, ρ, some a_f⟩))
            (BPLN.Expr.lam (BPLN.Comp.letRec c1_bp c1_bp))
            (Denotable.closure ⟨e1_anf, ρ, some a_f⟩) :=
          .rec_lambda h_c1_mono (by simp [Store.extend])
        have h_c2_mono : CompEquiv (Store.extend σ a_f (Denotable.closure ⟨e1_anf, ρ, some a_f⟩)) ρ 1 c2_bp e2_anf :=
          comp_equiv_extend_store h_c2 h_fresh_af
        obtain ⟨a_v, h_fresh_av⟩ := exists_fresh (Store.extend σ a_f (Denotable.closure ⟨e1_anf, ρ, some a_f⟩))
        have h_open := comp_equiv_open_binding (n := 0) h_c2_mono h_val_rec h_lam_closed h_fresh_av
        have h_open_closed := BPLN.Comp.fvs_open_closed (k := 0) h_c2_fvs h_lam_closed
        obtain ⟨v, σ', h_eval, h_res⟩ := ih_comp _ _ _ h_open h_open_closed
        exact ⟨v, σ',
          EvalExp.eval_let
            (EvalCExp.eval_fun h_fresh_af rfl rfl)
            (ContinueFrame.continue_let h_fresh_av rfl h_eval),
          h_res⟩
    · -- P_kont: letRec shape can't arise from kont opening
      intro σ c_op κ e_arg d h_kont h_eq h_val h_closed h_arg_closed
      exact (kont_subst_absurd_of_not_val_letIn_withHandle h_kont h_eq
        (by intro e he; cases he) (by intro c1 c2 he; cases he) (by intro h c he; cases he)).elim
  | .handle_val h_eval_inner h_eval_ret =>
    have ⟨ih1_comp, ih1_kont⟩ := completeness_combinedN h_eval_inner
    have ⟨ih2_comp, ih2_kont⟩ := completeness_combinedN h_eval_ret
    rename_i e' c h
    refine ⟨?_, ?_⟩
    · -- P_comp
      intro σ ρ e h_equiv h_closed
      cases h_equiv with
      | tail h_cexp =>
        cases h_cexp with
        | handler h_handler h_c =>
          have h_fvs_c := bp_withHandle_fvs_c h_closed
          obtain ⟨v1, σ1, h_eval1, h_res1⟩ := ih1_comp _ _ _ h_c h_fvs_c
          obtain ⟨d1, rfl, h_val1⟩ := result_equiv_value_inv h_res1
          have h_mono := eval_store_mono h_eval1
          have h_hdl_σ1 := handler_equiv_store_mono h_handler h_mono
          match h_hdl_σ1 with
          | .mk h_ret_equiv h_ops_equiv =>
            have h_e'_closed := bp_eval_value_closed (BPLN.evalN_to_eval h_eval_inner) h_fvs_c
            obtain ⟨a_ret, h_fresh_ret⟩ := exists_fresh σ1
            have h_open := comp_equiv_open_binding (n := 0) h_ret_equiv h_val1 h_e'_closed h_fresh_ret
            have h_open_closed := BPLN.Comp.fvs_open_closed (k := 0) (bp_withHandle_ret_fvs h_closed) h_e'_closed
            obtain ⟨v2, σ2, h_eval2, h_res2⟩ := ih2_comp _ _ _ h_open h_open_closed
            exact ⟨v2, σ2,
              EvalExp.eval_tail (EvalCExp.eval_handler h_eval1
                (HandleValue.handle_return rfl h_fresh_ret rfl h_eval2)),
              h_res2⟩
    · -- P_kont
      intro σ c_op κ e_arg d h_kont h_eq h_val_arg h_closed h_arg_closed
      match h_kont with
      | .kont_end =>
        simp only [BPLN.Comp.open_, BPLN.compOpenRec, BPLN.Expr.open_bvar] at h_eq
        cases h_eq
      | .kont_let _ _ =>
        simp only [BPLN.Comp.open_, BPLN.compOpenRec] at h_eq
        cases h_eq
      | .kont_handle h_kont_inner h_hdl_inner =>
        rename_i c_inner_kont κ_rest ρ_hdl
        simp only [BPLN.Comp.open_, BPLN.Comp.open_withHandle] at h_eq h_closed
        obtain ⟨h_heq, h_ceq⟩ := BPLN.Comp.withHandle.inj h_eq
        subst h_ceq
        have h_inner_closed := bp_withHandle_fvs_c h_closed
        obtain ⟨v_mid, σ_mid, h_apply, h_res_mid⟩ :=
          ih1_kont _ _ _ _ _ h_kont_inner rfl h_val_arg h_inner_closed h_arg_closed
        obtain ⟨d_mid, rfl, h_val_mid⟩ := result_equiv_value_inv h_res_mid
        have h_hdl_mono := handler_equiv_store_mono h_hdl_inner (eval_apply_store_mono h_apply)
        match h_hdl_mono with
        | .mk h_ret_equiv h_ops_equiv =>
          have h_e'_closed := bp_eval_value_closed (BPLN.evalN_to_eval h_eval_inner) h_inner_closed
          have h_ret_id : BPLN.compOpenRec (0+1) e_arg _ = _ :=
            BPLN.comp_open_lc_at _ 1 (0+1) e_arg (comp_equiv_lcAt h_ret_equiv) (by omega)
          have h_retClause_raw := congrArg BPLN.BPHandler.returnClause h_heq
          dsimp only at h_retClause_raw
          have h_retClause_eq := h_retClause_raw.trans h_ret_id
          have h_ret_fvs : h.returnClause.fvs = [] := by
            rw [h_retClause_eq, ← h_ret_id]
            exact bp_withHandle_ret_fvs h_closed
          obtain ⟨a_ret, h_fresh_ret⟩ := exists_fresh σ_mid
          have h_open := comp_equiv_open_binding (n := 0) h_ret_equiv h_val_mid h_e'_closed h_fresh_ret
          rw [← h_retClause_eq] at h_open
          have h_open_closed := BPLN.Comp.fvs_open_closed (k := 0) h_ret_fvs h_e'_closed
          obtain ⟨v_ret, σ_ret, h_eval_ret', h_res_ret⟩ := ih2_comp _ _ _ h_open h_open_closed
          exact ⟨v_ret, σ_ret,
            ApplyKont.apply_restore_handle h_apply
              (HandleValue.handle_return rfl h_fresh_ret rfl h_eval_ret'),
            h_res_ret⟩
  | .handle_op h_bp_eval_inner h_bp_findOp h_eval_op =>
    rename_i n1 c_inner op e_op c_op c_h n2 h
    have ⟨ih1_comp, ih1_kont⟩ := completeness_combinedN h_bp_eval_inner
    have ⟨ih2_comp, ih2_kont⟩ := completeness_combinedN h_eval_op
    refine ⟨?_, ?_⟩
    · -- P_comp
      intro σ ρ e h_equiv h_closed
      cases h_equiv with
      | tail h_cexp =>
        cases h_cexp with
        | handler h_handler h_c =>
          rename_i l h_anf e_body l_h
          have h_fvs_c := bp_withHandle_fvs_c h_closed
          obtain ⟨v1, σ1, h_eval1, h_res1⟩ := ih1_comp _ _ _ h_c h_fvs_c
          obtain ⟨a_op, d_op, κ_anf, rfl, h_store_op, h_val_op, h_kont_anf⟩ := result_equiv_op_inv h_res1
          have h_mono := eval_store_mono h_eval1
          have h_hdl_σ1 := handler_equiv_store_mono h_handler h_mono
          obtain ⟨e_op_anf, h_anf_findOp, h_ch_equiv⟩ := handler_findOp_equiv h_hdl_σ1 h_bp_findOp
          obtain ⟨h_eop_closed, _⟩ := bp_eval_op_closed (BPLN.evalN_to_eval h_bp_eval_inner) h_fvs_c
          have h_kontlam_closed := bp_kont_lam_closed (BPLN.evalN_to_eval h_bp_eval_inner) h_closed
          have h_ch_closed := bp_findOp_fvs h_closed h_bp_findOp
          -- open the resume binder (`bvar 1`) with the kont value, then the arg (`bvar 0`)
          obtain ⟨a_vk, h_fresh_vk⟩ := exists_fresh σ1
          have h_val_kont := ValueEquiv.kont h_hdl_σ1 h_kont_anf
          have h_open1 := comp_equiv_open_binding (n := 1) h_ch_equiv h_val_kont h_kontlam_closed h_fresh_vk
          obtain ⟨a_v', h_fresh_v'⟩ := exists_fresh (Store.extend σ1 a_vk (Denotable.kontClosure h_anf ρ κ_anf))
          have h_fresh_v'1 : σ1 a_v' = none := Store.fresh_of_fresh_extend h_fresh_v'
          have h_vk_ne_v' : a_vk ≠ a_v' := Store.ne_of_fresh_extend h_fresh_v'
          have h_val_op_ext := value_equiv_extend_store
            (d_new := Denotable.kontClosure h_anf ρ κ_anf) h_val_op h_fresh_vk
          have h_open2 := comp_equiv_open_binding (n := 0) h_open1 h_val_op_ext h_eop_closed h_fresh_v'
          have h_open_closed :
              (BPLN.compOpenRec 0 e_op
                (BPLN.compOpenRec 1 (BPLN.Expr.lam (BPLN.Comp.withHandle h c_op)) c_h)).fvs = [] :=
            BPLN.Comp.fvs_open_closed
              (BPLN.Comp.fvs_open_closed h_ch_closed h_kontlam_closed) h_eop_closed
          obtain ⟨v2, σ2, h_eval2, h_res2⟩ := ih2_comp _ _ _ h_open2 h_open_closed
          exact ⟨v2, σ2,
            EvalExp.eval_tail (EvalCExp.eval_handler h_eval1
              (HandleValue.handle_op h_anf_findOp h_fresh_v'1 h_fresh_vk (Ne.symm h_vk_ne_v') h_store_op rfl h_eval2)),
            h_res2⟩
    · -- P_kont
      intro σ c_op κ e_arg d h_kont h_eq h_val_arg h_closed_kont h_arg_closed
      match h_kont with
      | .kont_end =>
        simp only [BPLN.Comp.open_, BPLN.compOpenRec, BPLN.Expr.open_bvar] at h_eq
        cases h_eq
      | .kont_let _ _ =>
        simp only [BPLN.Comp.open_, BPLN.compOpenRec] at h_eq
        cases h_eq
      | .kont_handle h_kont_inner h_hdl_inner =>
        rename_i c_inner_kont κ_rest_fr ρ_hdl κ_rest_handler h_anf_fr
        simp only [BPLN.Comp.open_, BPLN.Comp.open_withHandle] at h_eq h_closed_kont
        obtain ⟨h_heq, h_ceq⟩ := BPLN.Comp.withHandle.inj h_eq
        subst h_ceq
        have h_inner_closed := bp_withHandle_fvs_c h_closed_kont
        obtain ⟨v_mid, σ_mid, h_apply, h_res_mid⟩ :=
          ih1_kont _ _ _ _ _ h_kont_inner rfl h_val_arg h_inner_closed h_arg_closed
        obtain ⟨a_op', d_op', κ_anf', rfl, h_store_op', h_val_op', h_kont_op'⟩ := result_equiv_op_inv h_res_mid
        have h_hdl_mono := handler_equiv_store_mono h_hdl_inner (eval_apply_store_mono h_apply)
        -- `κ_rest_handler` is closed at depth 1, so opening it (at depth `0+1`) with
        -- `e_arg` is the identity; combined with `h_heq` this gives `h = κ_rest_handler`,
        -- letting us replace the outer handler with `κ_rest_handler` everywhere.
        have h_ret_id : BPLN.compOpenRec (0+1) e_arg κ_rest_handler.returnClause = κ_rest_handler.returnClause :=
          BPLN.comp_open_lc_at κ_rest_handler.returnClause 1 (0+1) e_arg (handler_equiv_lcAt_ret h_hdl_inner) (by omega)
        have h_ops_id : BPLN.opsOpenRec (0+2) e_arg κ_rest_handler.opClauses = κ_rest_handler.opClauses :=
          BPLN.ops_open_lc_at κ_rest_handler.opClauses 2 (0+2) e_arg (handler_equiv_lcAt_ops h_hdl_inner) (by omega)
        rw [h_ret_id, h_ops_id] at h_heq
        have h_eta : (⟨κ_rest_handler.returnClause, κ_rest_handler.opClauses⟩ : BPLN.BPHandler) = κ_rest_handler := by
          cases κ_rest_handler; rfl
        rw [h_eta] at h_heq
        have h_heq' := h_heq.symm
        subst h_heq'
        -- restore the bare `κ_rest_handler` in `h_closed_kont` (the simp above opened it)
        rw [h_ret_id, h_ops_id, h_eta] at h_closed_kont
        obtain ⟨e_op_anf', h_anf_findOp', h_ch_equiv'⟩ := handler_findOp_equiv h_hdl_mono h_bp_findOp
        obtain ⟨h_eop_closed, _⟩ := bp_eval_op_closed (BPLN.evalN_to_eval h_bp_eval_inner) h_inner_closed
        have h_kontlam_closed := bp_kont_lam_closed (BPLN.evalN_to_eval h_bp_eval_inner) h_closed_kont
        have h_ch_closed := bp_findOp_fvs h_closed_kont h_bp_findOp
        obtain ⟨a_vk, h_fresh_vk⟩ := exists_fresh σ_mid
        have h_val_kont := ValueEquiv.kont h_hdl_mono h_kont_op'
        have h_open1 := comp_equiv_open_binding (n := 1) h_ch_equiv' h_val_kont h_kontlam_closed h_fresh_vk
        obtain ⟨a_v', h_fresh_v'⟩ := exists_fresh (Store.extend σ_mid a_vk (Denotable.kontClosure h_anf_fr ρ_hdl κ_anf'))
        have h_fresh_v'1 : σ_mid a_v' = none := Store.fresh_of_fresh_extend h_fresh_v'
        have h_vk_ne_v' : a_vk ≠ a_v' := Store.ne_of_fresh_extend h_fresh_v'
        have h_val_op_ext := value_equiv_extend_store
          (d_new := Denotable.kontClosure h_anf_fr ρ_hdl κ_anf') h_val_op' h_fresh_vk
        have h_open2 := comp_equiv_open_binding (n := 0) h_open1 h_val_op_ext h_eop_closed h_fresh_v'
        have h_open_closed :=
          BPLN.Comp.fvs_open_closed (k := 0)
            (BPLN.Comp.fvs_open_closed (k := 1) h_ch_closed h_kontlam_closed) h_eop_closed
        obtain ⟨v2, σ2, h_eval2, h_res2⟩ := ih2_comp _ _ _ h_open2 h_open_closed
        exact ⟨v2, σ2,
          ApplyKont.apply_restore_handle h_apply
            (HandleValue.handle_op h_anf_findOp' h_fresh_v'1 h_fresh_vk (Ne.symm h_vk_ne_v') h_store_op' rfl h_eval2),
          h_res2⟩
  termination_by n

/-- Combined completeness for BPLN.Eval: wraps the height-indexed version -/
theorem completeness_combined (h_eval : BPLN.Eval c r) :
    (∀ (σ : Store) (ρ : Env) (e : Exp), CompEquiv σ ρ 0 c e → c.fvs = [] →
      ∃ v σ', EvalExp e ρ σ v σ' ∧ ResultEquiv σ' r v) ∧
    (∀ (σ : Store) (c_op : BPLN.Comp) (κ : Kont) (e_arg : BPLN.Expr) (d : Denotable),
      KontEquiv σ c_op κ →
      c = BPLN.Comp.open_ c_op e_arg →
      ValueEquiv σ e_arg d →
      (BPLN.Comp.open_ c_op e_arg).fvs = [] →
      e_arg.fvs = [] →
      ∃ v σ', ApplyKont κ d σ v σ' ∧ ResultEquiv σ' r v) := by
  obtain ⟨n, hn⟩ := BPLN.eval_to_evalN h_eval
  exact completeness_combinedN hn

/-- Standard completeness extracted from the combined theorem -/
theorem completeness_open' (h_eval : BPLN.Eval c r) :
    CompEquiv σ ρ 0 c e → c.fvs = [] →
    ∃ v σ', EvalExp e ρ σ v σ' ∧ ResultEquiv σ' r v :=
  (completeness_combined h_eval).1 σ ρ e

end DMCFA.LN
