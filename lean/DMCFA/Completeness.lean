/-
  Completeness: B&P evaluation → ANF evaluation (refactored)

  Uses height-indexed EvalN with strong Nat induction proving both standard
  completeness and kont-application completeness simultaneously. The height
  parameter lets us recurse on sub-sub-derivations (needed for the rec_lambda
  case inside app_lam where we decompose h_eval_body via let_rec).
-/

import DMCFA.Lemmas

namespace DMCFA

/-! ## Kont-shape impossibility lemmas

  For most BP.Eval constructors (ifThenElse, matchNat, app, letRec, opCall),
  the computation shape cannot arise from kont substitution (which only produces
  val, letIn, or withHandle shapes). -/

private theorem kont_subst_absurd_of_not_val_letIn_withHandle
    (h_kont : KontEquiv σ x_c c_op κ)
    (h_eq : c' = c_op.subst x_c e_arg)
    (h_not_val : ∀ e, c' ≠ BP.Comp.val e)
    (h_not_letIn : ∀ y c1 c2, c' ≠ BP.Comp.letIn y c1 c2)
    (h_not_withHandle : ∀ h c, c' ≠ BP.Comp.withHandle h c) : False := by
  match h_kont with
  | .kont_end =>
    simp at h_eq
    exact h_not_val _ h_eq
  | .kont_let _ _ _ =>
    rw [BP.Comp.subst_letIn] at h_eq
    exact h_not_letIn _ _ _ h_eq
  | .kont_handle _ _ _ =>
    simp at h_eq
    exact h_not_withHandle _ _ h_eq

/-! ## Main combined theorem -/

/-- Combined completeness (height-indexed): for any `EvalN n c r`, both standard
    completeness (P_comp) and kont-application completeness (P_kont) hold.

    Uses strong Nat induction on the height parameter, which lets us recurse
    on sub-sub-derivations (needed for rec_lambda inside app_lam). -/
private theorem completeness_combinedN {n : Nat} (h_eval : BP.EvalN n c r) :
    -- P_comp
    (∀ (σ : Store) (ρ : Env) (e : Exp), CompEquiv σ ρ c e → c.fvs = [] →
      ∃ v σ', EvalExp e ρ σ v σ' ∧ ResultEquiv σ' r v) ∧
    -- P_kont
    (∀ (σ : Store) (x_c : Var) (c_op : BP.Comp) (κ : Kont) (e_arg : BP.Expr) (d : Denotable),
      KontEquiv σ x_c c_op κ →
      c = c_op.subst x_c e_arg →
      ValueEquiv σ e_arg d →
      (c_op.subst x_c e_arg).fvs = [] →
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
    · intro σ x_c c_op κ e_arg d h_kont h_eq h_val h_closed h_arg_closed
      match h_kont with
      | .kont_end =>
        simp [BP.Comp.subst_val, BP.Expr.subst_var_self] at h_eq; subst h_eq
        exact ⟨Value.den d, σ, ApplyKont.apply_continue, ResultEquiv.value h_val⟩
      | .kont_let _ _ h_fresh_c2 =>
        rw [BP.Comp.subst_letIn] at h_eq
        rw [BP.Comp.subst_not_mem_fvs h_fresh_c2] at h_eq
        simp only [ite_self] at h_eq; cases h_eq
      | .kont_handle _ _ h_fresh_hdl =>
        simp only [BP.Comp.subst_withHandle] at h_eq
        rw [BP.BPHandler.subst_not_mem_fvs h_fresh_hdl] at h_eq
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
          exact ⟨v, σ', EvalExp.eval_tail (EvalCExp.eval_match h_atomic rfl (findBranch_true _ _) rfl h_anf), h_res⟩
    · intro σ x_c c_op κ e_arg d h_kont h_eq h_val h_closed h_arg_closed
      exact (kont_subst_absurd_of_not_val_letIn_withHandle h_kont h_eq
        (by intro e he; cases he) (by intro y c1 c2 he; cases he) (by intro h c he; cases he)).elim
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
          exact ⟨v, σ', EvalExp.eval_tail (EvalCExp.eval_match h_atomic rfl (findBranch_false _ _) rfl h_anf), h_res⟩
    · intro σ x_c c_op κ e_arg d h_kont h_eq h_val h_closed h_arg_closed
      exact (kont_subst_absurd_of_not_val_letIn_withHandle h_kont h_eq
        (by intro e he; cases he) (by intro y c1 c2 he; cases he) (by intro h c he; cases he)).elim
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
          exact ⟨v, σ', EvalExp.eval_tail (EvalCExp.eval_match h_atomic rfl (findBranch_zero _ _ _) rfl h_anf), h_res⟩
    · intro σ x_c c_op κ e_arg d h_kont h_eq h_val h_closed h_arg_closed
      exact (kont_subst_absurd_of_not_val_letIn_withHandle h_kont h_eq
        (by intro e he; cases he) (by intro y c1 c2 he; cases he) (by intro h c he; cases he)).elim
  | .match_succ (x := x_bind) h_sub =>
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
          simp [BP.Expr.fvs_succ] at h_fvs_scrut
          obtain ⟨a_fresh, h_fresh⟩ := exists_fresh σ
          have h_subst := comp_equiv_subst_binding x_bind h_c2 h_val_inner h_fvs_scrut h_fresh (barendregt_fresh_env ρ x_bind)
          have h_subst_closed := bp_comp_subst_closed_of_fvs_sub (bp_matchNat_fvs_c2 h_closed) h_fvs_scrut
          obtain ⟨v, σ', h_anf, h_res⟩ := ih_comp _ _ _ h_subst h_subst_closed
          exact ⟨v, σ', EvalExp.eval_tail (EvalCExp.eval_match_succ h_atomic
            (findBranch_succ _ _ _) h_store h_fresh rfl rfl h_anf), h_res⟩
    · intro σ x_c c_op κ e_arg d h_kont h_eq h_val h_closed h_arg_closed
      exact (kont_subst_absurd_of_not_val_letIn_withHandle h_kont h_eq
        (by intro e he; cases he) (by intro y c1 c2 he; cases he) (by intro h c he; cases he)).elim
  | .let_val h_eval_c1 h_eval_c2 =>
    have ⟨ih1_comp, ih1_kont⟩ := completeness_combinedN h_eval_c1
    have ⟨ih2_comp, ih2_kont⟩ := completeness_combinedN h_eval_c2
    rename_i c1_bp c2_bp e'_val x_let r_bp
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
          have h_e'_closed := bp_eval_value_closed (BP.evalN_to_eval h_eval_c1) h_fvs_c1
          have h_subst := comp_equiv_subst_binding x_let h_c2_σ1 h_val1 h_e'_closed h_fresh (barendregt_fresh_env _ x_let)
          have h_subst_closed := bp_comp_subst_closed_of_fvs_sub (bp_letIn_fvs_c2 h_closed) h_e'_closed
          obtain ⟨v2, σ2, h_eval2, h_res2⟩ := ih2_comp _ _ _ h_subst h_subst_closed
          exact ⟨v2, σ2,
            EvalExp.eval_let h_cexp_eval (ContinueFrame.continue_let h_fresh rfl h_eval2),
            h_res2⟩
    · -- P_kont
      intro σ x_c c_op κ e_arg d h_kont h_eq h_val_arg h_closed_kont h_arg_closed
      match h_kont with
      | .kont_end =>
        simp [BP.Comp.subst_val, BP.Expr.subst_var_self] at h_eq
      | @KontEquiv.kont_let _ _ c_inner κ_rest ρ_kont c2_kont e2_kont y_kont h_kont_inner h_c2_equiv h_fresh_c2 =>
        rw [BP.Comp.subst_letIn] at h_eq
        rw [BP.Comp.subst_not_mem_fvs h_fresh_c2] at h_eq
        simp only [ite_self] at h_eq
        have ⟨h_yeq, h_c1eq, h_c2eq⟩ := BP.Comp.letIn.inj h_eq
        subst h_yeq; subst h_c2eq
        rw [BP.Comp.subst_letIn] at h_closed_kont
        rw [BP.Comp.subst_not_mem_fvs h_fresh_c2] at h_closed_kont
        simp only [ite_self] at h_closed_kont
        have h_inner_closed : (c_inner.subst x_c e_arg).fvs = [] := by
          rw [BP.Comp.fvs_letIn] at h_closed_kont
          exact (List.append_eq_nil_iff.mp h_closed_kont).1
        obtain ⟨v_mid, σ_mid, h_apply_inner, h_res_inner⟩ :=
          ih1_kont _ _ _ _ _ _ h_kont_inner h_c1eq h_val_arg h_inner_closed h_arg_closed
        obtain ⟨d_mid, rfl, h_val_mid⟩ := result_equiv_value_inv h_res_inner
        have h_mono := eval_apply_store_mono h_apply_inner
        have h_c2_mono := comp_equiv_store_mono h_c2_equiv h_mono
        have h_e'_closed := bp_eval_value_closed (BP.evalN_to_eval h_eval_c1) (h_c1eq ▸ h_inner_closed)
        obtain ⟨a_v, h_fresh_v⟩ := exists_fresh σ_mid
        have h_subst := comp_equiv_subst_binding x_let h_c2_mono h_val_mid h_e'_closed h_fresh_v
          (barendregt_fresh_env _ x_let)
        have h_c2_fvs : ∀ v, v ∈ r_bp.fvs → v = x_let := by
          rw [BP.Comp.fvs_letIn] at h_closed_kont
          have h_filt := (List.append_eq_nil_iff.mp h_closed_kont).2
          intro v hv; by_contra h_ne
          have := List.filter_eq_nil_iff.mp h_filt v
          simp [hv, h_ne] at this
        have h_c2_subst_closed := bp_comp_subst_closed_of_fvs_sub h_c2_fvs h_e'_closed
        obtain ⟨v_result, σ_result, h_eval_result, h_res_result⟩ :=
          ih2_comp _ _ _ h_subst h_c2_subst_closed
        exact ⟨v_result, σ_result,
          ApplyKont.apply_restore h_apply_inner (ContinueFrame.continue_let h_fresh_v rfl h_eval_result),
          h_res_result⟩
      | .kont_handle _ _ h_fresh_hdl =>
        simp only [BP.Comp.subst_withHandle] at h_eq
        rw [BP.BPHandler.subst_not_mem_fvs h_fresh_hdl] at h_eq
        cases h_eq
  | .let_op h_eval_c1 =>
    have ⟨ih_comp, ih_kont⟩ := completeness_combinedN h_eval_c1
    rename_i x_let_op c1_bp_op c2_bp_op _ _ _ _
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
            ResultEquiv.op h_store h_val_op (KontEquiv.kont_let h_kont h_c2_σ1
              (fun hm => absurd (bp_letIn_fvs_c2 h_closed _ hm) (barendregt_var_ne _ _)))⟩
    · -- P_kont
      intro σ x_c c_op κ e_arg d h_kont h_eq h_val_arg h_closed_kont h_arg_closed
      match h_kont with
      | .kont_end =>
        simp [BP.Comp.subst_val, BP.Expr.subst_var_self] at h_eq
      | @KontEquiv.kont_let _ _ c_inner κ_rest ρ_kont c2_kont e2_kont y_kont h_kont_inner h_c2_equiv h_fresh_c2 =>
        rw [BP.Comp.subst_letIn] at h_eq
        rw [BP.Comp.subst_not_mem_fvs h_fresh_c2] at h_eq
        simp only [ite_self] at h_eq
        have ⟨h_yeq, h_c1eq, h_c2eq⟩ := BP.Comp.letIn.inj h_eq
        subst h_yeq; subst h_c2eq
        rw [BP.Comp.subst_letIn] at h_closed_kont
        rw [BP.Comp.subst_not_mem_fvs h_fresh_c2] at h_closed_kont
        simp only [ite_self] at h_closed_kont
        have h_inner_closed : (c_inner.subst x_c e_arg).fvs = [] := by
          rw [BP.Comp.fvs_letIn] at h_closed_kont
          exact (List.append_eq_nil_iff.mp h_closed_kont).1
        obtain ⟨v_mid, σ_mid, h_apply_inner, h_res_inner⟩ :=
          ih_kont _ _ _ _ _ _ h_kont_inner h_c1eq h_val_arg h_inner_closed h_arg_closed
        obtain ⟨a_op, d_op, κ_op, rfl, h_store_op, h_val_op, h_kont_op⟩ := result_equiv_op_inv h_res_inner
        have h_mono := eval_apply_store_mono h_apply_inner
        have h_c2_mono := comp_equiv_store_mono h_c2_equiv h_mono
        exact ⟨_, σ_mid,
          ApplyKont.apply_restore h_apply_inner ContinueFrame.continue_op,
          ResultEquiv.op h_store_op h_val_op (KontEquiv.kont_let h_kont_op h_c2_mono
            (fun hm => absurd (bp_letIn_fvs_c2 h_closed_kont _ hm) (barendregt_var_ne _ _)))⟩
      | .kont_handle _ _ h_fresh_hdl =>
        simp only [BP.Comp.subst_withHandle] at h_eq
        rw [BP.BPHandler.subst_not_mem_fvs h_fresh_hdl] at h_eq
        cases h_eq
  | .op_call =>
    refine ⟨?_, ?_⟩
    · intro σ ρ e h_equiv h_closed
      cases h_equiv with
      | tail h_cexp =>
        cases h_cexp with
        | opApp h_expr =>
          have h_fvs := bp_opCall_fvs h_closed
          cases h_expr with
          | var => simp [BP.Expr.fvs_var] at h_fvs
          | var_subst h_rho h_store h_val _ =>
            exact ⟨_, _, EvalExp.eval_tail (EvalCExp.eval_opApp h_rho), ResultEquiv.op h_store h_val KontEquiv.kont_end⟩
    · intro σ x_c c_op κ e_arg d h_kont h_eq h_val h_closed h_arg_closed
      exact (kont_subst_absurd_of_not_val_letIn_withHandle h_kont h_eq
        (by intro e he; cases he) (by intro y c1 c2 he; cases he) (by intro h c he; cases he)).elim
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
            ResultEquiv.op h_store h_val_op (KontEquiv.kont_handle h_kont h_hdl_σ1
              (not_mem_withHandle_hdl_fvs h_closed))⟩
    · -- P_kont
      intro σ x_c c_op κ e_arg d h_kont h_eq h_val_arg h_closed h_arg_closed
      match h_kont with
      | .kont_end =>
        simp [BP.Comp.subst_val, BP.Expr.subst_var_self] at h_eq
      | .kont_let _ _ h_fresh_c2 =>
        rw [BP.Comp.subst_letIn] at h_eq
        rw [BP.Comp.subst_not_mem_fvs h_fresh_c2] at h_eq
        simp only [ite_self] at h_eq; cases h_eq
      | .kont_handle h_kont_inner h_hdl_inner h_fresh_hdl =>
        rename_i c_inner_kont κ_rest ρ_hdl _ _
        simp only [BP.Comp.subst_withHandle] at h_eq
        rw [BP.BPHandler.subst_not_mem_fvs h_fresh_hdl] at h_eq
        have ⟨h_heq, h_ceq⟩ := BP.Comp.withHandle.inj h_eq
        subst h_heq; subst h_ceq
        simp only [BP.Comp.subst_withHandle] at h_closed
        rw [BP.BPHandler.subst_not_mem_fvs h_fresh_hdl] at h_closed
        have h_inner_closed := bp_withHandle_fvs_c h_closed
        obtain ⟨v_mid, σ_mid, h_apply, h_res_mid⟩ :=
          ih_kont _ _ _ _ _ _ h_kont_inner rfl h_val_arg h_inner_closed h_arg_closed
        obtain ⟨a_op, d_op, κ_op, rfl, h_store_op, h_val_op, h_kont_op⟩ := result_equiv_op_inv h_res_mid
        have h_hdl_mono := handler_equiv_store_mono h_hdl_inner (eval_apply_store_mono h_apply)
        have h_anf_not_has := (handler_hasOp_equiv h_hdl_mono ▸ h_bp_not_has : _ = false)
        exact ⟨_, σ_mid,
          ApplyKont.apply_restore_handle h_apply
            (HandleValue.handle_capture_op h_anf_not_has rfl),
          ResultEquiv.op h_store_op h_val_op (KontEquiv.kont_handle h_kont_op h_hdl_mono
            (not_mem_withHandle_hdl_fvs h_closed))⟩
  | .app_lam h_eval_body =>
    have ⟨ih_comp, ih_kont⟩ := completeness_combinedN h_eval_body
    refine ⟨?_, ?_⟩
    · -- P_comp
      intro σ ρ e h_equiv h_closed
      rename_i x_lam c_body e_arg_lam
      cases h_equiv with
      | tail h_cexp =>
        cases h_cexp with
        | funApp h_e1 h_e2 =>
          have h_fvs_e1 := bp_app_fvs_e1 h_closed
          have h_fvs_e2 := bp_app_fvs_e2 h_closed
          obtain ⟨d_fun, h_eval_fun, h_val_fun⟩ := expr_equiv_eval_atomic h_e1 h_fvs_e1
          obtain ⟨d_arg, h_eval_arg, h_val_arg⟩ := expr_equiv_eval_atomic h_e2 h_fvs_e2
          cases h_val_fun with
          | kont h_hdl_equiv h_kont_equiv h_fresh_hdl =>
            -- KEY: use ih_kont with combined kont (handler + inner)
            rename_i _ _ ρ_h h_bp_handler h_anf_handler c_op_inner κ_inner
            have h_body_closed : ((BP.Comp.withHandle h_bp_handler c_op_inner).subst x_lam e_arg_lam).fvs = [] := by
              apply bp_comp_subst_closed_of_fvs_sub _ h_fvs_e2
              intro v hv
              have h_filt := h_fvs_e1; rw [BP.Expr.fvs_lam] at h_filt
              have := filter_eq_nil_mem h_filt v hv; simp at this; exact this
            have h_kont_combined := KontEquiv.kont_handle h_kont_equiv h_hdl_equiv h_fresh_hdl
            obtain ⟨v_final, σ_final, h_apply_combined, h_res_final⟩ :=
              ih_kont _ _ _ _ _ _ h_kont_combined rfl h_val_arg h_body_closed h_fvs_e2
            cases h_apply_combined with
            | apply_restore_handle h_apply_inner h_handle =>
              exact ⟨v_final, σ_final,
                EvalExp.eval_tail (EvalCExp.eval_funApp_kont h_eval_fun h_eval_arg h_apply_inner h_handle),
                h_res_final⟩
          | lambda h_body =>
            obtain ⟨a_arg, h_fresh_arg⟩ := exists_fresh σ
            have h_subst := comp_equiv_subst_binding x_lam h_body h_val_arg h_fvs_e2 h_fresh_arg
              (barendregt_fresh_env _ x_lam)
            have h_subst_closed : (c_body.subst x_lam e_arg_lam).fvs = [] := by
              apply bp_comp_subst_closed_of_fvs_sub _ h_fvs_e2
              intro v hv
              have h_filt := h_fvs_e1; rw [BP.Expr.fvs_lam] at h_filt
              have := filter_eq_nil_mem h_filt v hv; simp at this; exact this
            obtain ⟨v, σ', h_anf, h_res⟩ := ih_comp _ _ _ h_subst h_subst_closed
            exact ⟨v, σ',
              EvalExp.eval_tail (EvalCExp.eval_funApp_clos (ds := [d_arg]) (as_v := [a_arg]) h_eval_fun
                rfl (.cons h_eval_arg .nil) (.cons h_fresh_arg .nil)
                (List.nodup_singleton _)
                rfl rfl rfl h_anf),
              h_res⟩
          | rec_lambda h_body h_store =>
            rename_i ρ_clos f a_f c1 e1
            -- h_body : CompEquiv σ (ρ_clos.extend f a_f) c1 e1
            -- h_store : σ a_f = some (closure ⟨[x_lam], e1, ρ_clos.extend f a_f⟩)
            -- h_eval_body : BP.Eval ((letRec f x_lam c1 c1).subst x_lam e_arg_lam) r
            obtain ⟨a_arg, h_fresh_arg⟩ := exists_fresh σ
            have h_subst := comp_equiv_subst_binding x_lam h_body h_val_arg h_fvs_e2 h_fresh_arg
              (barendregt_fresh_env _ x_lam)
            have h_f_ne_x : f ≠ x_lam := barendregt_var_ne f x_lam
            have h_f_bound : (Env.extend (Env.extend ρ_clos f a_f) x_lam a_arg) f = some a_f := by
              simp [Env.extend, h_f_ne_x]
            have h_ne_addr : a_f ≠ a_arg := by
              intro h_eq; subst h_eq; rw [h_fresh_arg] at h_store; simp at h_store
            have h_f_store_ext : (Store.extend σ a_arg d_arg) a_f =
                some (Denotable.closure ⟨[x_lam], e1, Env.extend ρ_clos f a_f, List.nodup_singleton _⟩) := by
              simp [Store.extend, h_ne_addr]; exact h_store
            have h_rec_val := @value_equiv_extend_store _ _ _ a_arg d_arg
              (ValueEquiv.rec_lambda h_body h_store) h_fresh_arg
            have h_rec_closed : (BP.Expr.lam x_lam (BP.Comp.letRec f x_lam c1 c1)).fvs = [] :=
              h_fvs_e1
            have h_redundant := comp_equiv_redundant_subst f h_subst h_f_bound h_f_store_ext
              h_rec_val h_rec_closed
            -- h_redundant : CompEquiv (σ.ext a_arg d_arg)
            --   ((ρ_clos.ext f a_f).ext x_lam a_arg)
            --   ((c1.subst x_lam e_arg_lam).subst f (lam x_lam (letRec f x_lam c1 c1)))
            --   e1
            have h_xf : x_lam ≠ f := (barendregt_var_ne x_lam f)
            -- Inline extraction: cast h_eval_body and match to get inner derivation
            have h_eq := BP.Comp.subst_letRec_self_y h_xf c1 c1 e_arg_lam
            have h_inner_closed : ((c1.subst x_lam e_arg_lam).subst f
                  (BP.Expr.lam x_lam (BP.Comp.letRec f x_lam c1 c1))).fvs = [] := by
                have h_body_closed : ((BP.Comp.letRec f x_lam c1 c1).subst x_lam e_arg_lam).fvs = [] := by
                  apply bp_comp_subst_closed_of_fvs_sub _ h_fvs_e2
                  intro v hv
                  have h_filt := h_fvs_e1; rw [BP.Expr.fvs_lam] at h_filt
                  have := filter_eq_nil_mem h_filt v hv; simp at this; exact this
                rw [BP.Comp.subst_letRec_self_y h_xf] at h_body_closed
                rw [BP.Comp.fvs_letRec] at h_body_closed
                have ⟨_, h2⟩ := List.append_eq_nil_iff.mp h_body_closed
                exact bp_comp_subst_closed_of_fvs_sub
                  (fun v hv => by
                    have := filter_eq_nil_mem h2 v hv; simp at this; exact this)
                  h_rec_closed
            match h_match : h_eq ▸ h_eval_body with
            | .let_rec h_inner =>
            have ⟨ih_inner_comp, _⟩ := completeness_combinedN h_inner
            obtain ⟨v, σ', h_eval_e1, h_res⟩ := ih_inner_comp _ _ _ h_redundant h_inner_closed
            exact ⟨v, σ',
              EvalExp.eval_tail (EvalCExp.eval_funApp_clos (ds := [d_arg]) (as_v := [a_arg]) h_eval_fun
                rfl (.cons h_eval_arg .nil) (.cons h_fresh_arg .nil)
                (List.nodup_singleton _)
                rfl rfl rfl h_eval_e1),
              h_res⟩
    · -- P_kont: app shape can't arise from kont subst
      intro σ x_c c_op κ e_arg d h_kont h_eq h_val h_closed h_arg_closed
      match h_kont with
      | .kont_end => simp [BP.Comp.subst_val, BP.Expr.subst_var_self] at h_eq
      | .kont_let _ _ h_fresh_c2 =>
        rw [BP.Comp.subst_letIn] at h_eq
        rw [BP.Comp.subst_not_mem_fvs h_fresh_c2] at h_eq
        simp only [ite_self] at h_eq; cases h_eq
      | .kont_handle _ _ h_fresh_hdl =>
        simp only [BP.Comp.subst_withHandle] at h_eq
        rw [BP.BPHandler.subst_not_mem_fvs h_fresh_hdl] at h_eq
        cases h_eq
  | .let_rec h_eval_body =>
    have ⟨ih_comp, ih_kont⟩ := completeness_combinedN h_eval_body
    rename_i _ f_rec x_rec c1_bp c2_bp
    refine ⟨?_, ?_⟩
    · -- P_comp
      intro σ ρ e h_equiv h_closed
      cases h_equiv with
      | tail h_cexp => cases h_cexp
      | letRec h_c1 h_c2_eq =>
        rename_i e1_anf e2_anf l_anf
        obtain ⟨a_f, h_fresh_af⟩ := exists_fresh σ
        let v_f := Denotable.closure ⟨[x_rec], e1_anf, ρ.extend f_rec a_f, List.nodup_singleton _⟩
        have h_c1_w := @comp_equiv_weaken σ ρ c1_bp e1_anf a_f v_f f_rec h_c1 h_fresh_af (barendregt_fresh_env ρ f_rec)
        let σ' := σ.extend a_f v_f
        obtain ⟨a_v, h_fresh_av⟩ := exists_fresh σ'
        have h_val_rec : ValueEquiv σ'
            (BP.Expr.lam x_rec (BP.Comp.letRec f_rec x_rec c1_bp c1_bp))
            v_f :=
          .rec_lambda h_c1_w (by simp [σ', v_f, Store.extend])
        have h_c2_mono := @comp_equiv_extend_store σ ρ c2_bp e2_anf a_f v_f h_c2_eq h_fresh_af
        have h_lam_closed : (BP.Expr.lam x_rec (BP.Comp.letRec f_rec x_rec c1_bp c1_bp)).fvs = [] := by
          have ⟨h_c1_fvs, _⟩ := bp_letRec_fvs h_closed
          rw [BP.Expr.fvs_lam, BP.Comp.fvs_letRec]
          rw [List.filter_append]
          have h_inner1 : c1_bp.fvs.filter (fun v => decide (v ≠ f_rec) && decide (v ≠ x_rec)) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro v hv
            rcases h_c1_fvs v hv with h | h <;> simp [h]
          have h_inner2 : (c1_bp.fvs.filter (fun v => decide (v ≠ f_rec))).filter (fun v => decide (v ≠ x_rec)) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro v hv
            have hv' := (List.mem_filter.mp hv).1
            rcases h_c1_fvs v hv' with h | h <;> simp [h] at hv ⊢
          rw [h_inner1, h_inner2]; rfl
        have h_subst := comp_equiv_subst_binding f_rec h_c2_mono h_val_rec h_lam_closed h_fresh_av
          (barendregt_fresh_env _ f_rec)
        have h_subst_closed : (c2_bp.subst f_rec (BP.Expr.lam x_rec (BP.Comp.letRec f_rec x_rec c1_bp c1_bp))).fvs = [] :=
          bp_comp_subst_closed_of_fvs_sub (bp_letRec_fvs h_closed).2 h_lam_closed
        obtain ⟨v, σ'', h_eval, h_res⟩ := ih_comp _ _ _ h_subst h_subst_closed
        exact ⟨v, σ'',
          EvalExp.eval_let
            (EvalCExp.eval_fun h_fresh_af (List.nodup_singleton _) rfl rfl)
            (ContinueFrame.continue_let h_fresh_av rfl h_eval),
          h_res⟩
    · -- P_kont: letRec shape can't arise from kont subst
      intro σ x_c c_op κ e_arg d h_kont h_eq h_val h_closed h_arg_closed
      exact (kont_subst_absurd_of_not_val_letIn_withHandle h_kont h_eq
        (by intro e he; cases he) (by intro y c1 c2 he; cases he) (by intro h c he; cases he)).elim
  | .handle_val h_eval_inner h_eq_ret h_eval_ret =>
    have ⟨ih1_comp, ih1_kont⟩ := completeness_combinedN h_eval_inner
    have ⟨ih2_comp, ih2_kont⟩ := completeness_combinedN h_eval_ret
    refine ⟨?_, ?_⟩
    · -- P_comp
      intro σ ρ e h_equiv h_closed
      have h_fvs_c := bp_withHandle_fvs_c h_closed
      have h_e'_closed := bp_eval_value_closed (BP.evalN_to_eval h_eval_inner) h_fvs_c
      have h_hdl_fvs := h_closed
      rw [BP.Comp.fvs_withHandle] at h_hdl_fvs
      have ⟨h_ret_fvs, _⟩ := List.append_eq_nil_iff.mp h_hdl_fvs
      have ⟨h_ret_fvs', _⟩ := List.append_eq_nil_iff.mp h_ret_fvs
      rw [← h_eq_ret] at h_ret_fvs'
      simp at h_ret_fvs'
      cases h_equiv with
      | tail h_cexp =>
        cases h_cexp with
        | handler h_handler h_c =>
          obtain ⟨v1, σ1, h_eval1, h_res1⟩ := ih1_comp _ _ _ h_c h_fvs_c
          obtain ⟨d1, rfl, h_val1⟩ := result_equiv_value_inv h_res1
          have h_mono := eval_store_mono h_eval1
          have h_hdl_σ1 := handler_equiv_store_mono h_handler h_mono
          match h_hdl_σ1 with
          | .mk h_ret_equiv h_ops_equiv =>
            have ⟨h_xeq, h_ceq⟩ := Prod.mk.inj h_eq_ret
            subst h_xeq; subst h_ceq
            obtain ⟨a_ret, h_fresh_ret⟩ := exists_fresh σ1
            obtain ⟨v2, σ2, h_eval2, h_res2⟩ := ih2_comp _ _ _
              (comp_equiv_subst_binding _ h_ret_equiv h_val1 h_e'_closed h_fresh_ret
                (barendregt_fresh_env _ _))
              (bp_comp_subst_closed_of_fvs_sub h_ret_fvs' h_e'_closed)
            exact ⟨v2, σ2,
              EvalExp.eval_tail (EvalCExp.eval_handler h_eval1
                (HandleValue.handle_return rfl h_fresh_ret rfl h_eval2)),
              h_res2⟩
    · -- P_kont: withHandle shape
      intro σ x_c c_op κ e_arg d h_kont h_eq h_val_arg h_closed_kont h_arg_closed
      match h_kont with
      | .kont_end =>
        simp [BP.Comp.subst_val, BP.Expr.subst_var_self] at h_eq
      | .kont_let _ _ h_fresh_c2 =>
        rw [BP.Comp.subst_letIn] at h_eq
        rw [BP.Comp.subst_not_mem_fvs h_fresh_c2] at h_eq
        simp only [ite_self] at h_eq; cases h_eq
      | .kont_handle h_kont_inner h_hdl_inner h_fresh_hdl =>
        rename_i c_inner_kont κ_rest ρ_hdl _ _
        simp only [BP.Comp.subst_withHandle] at h_eq
        rw [BP.BPHandler.subst_not_mem_fvs h_fresh_hdl] at h_eq
        have ⟨h_heq, h_ceq⟩ := BP.Comp.withHandle.inj h_eq
        subst h_heq; subst h_ceq
        simp only [BP.Comp.subst_withHandle] at h_closed_kont
        rw [BP.BPHandler.subst_not_mem_fvs h_fresh_hdl] at h_closed_kont
        have h_inner_closed := bp_withHandle_fvs_c h_closed_kont
        obtain ⟨v_mid, σ_mid, h_apply, h_res_mid⟩ :=
          ih1_kont _ _ _ _ _ _ h_kont_inner rfl h_val_arg h_inner_closed h_arg_closed
        obtain ⟨d_mid, rfl, h_val_mid⟩ := result_equiv_value_inv h_res_mid
        have h_hdl_mono := handler_equiv_store_mono h_hdl_inner (eval_apply_store_mono h_apply)
        have h_e'_closed := bp_eval_value_closed (BP.evalN_to_eval h_eval_inner) h_inner_closed
        rw [BP.Comp.fvs_withHandle] at h_closed_kont
        have ⟨h_ret_ops_fvs, _⟩ := List.append_eq_nil_iff.mp h_closed_kont
        have ⟨h_ret_filt, _⟩ := List.append_eq_nil_iff.mp h_ret_ops_fvs
        rw [← h_eq_ret] at h_ret_filt
        simp at h_ret_filt
        match h_hdl_mono with
        | .mk h_ret_equiv h_ops_equiv =>
          have ⟨h_xeq, h_ceq⟩ := Prod.mk.inj h_eq_ret
          subst h_xeq; subst h_ceq
          obtain ⟨a_ret, h_fresh_ret⟩ := exists_fresh σ_mid
          have h_ret_closed := bp_comp_subst_closed_of_fvs_sub h_ret_filt h_e'_closed
          obtain ⟨v_ret, σ_ret, h_eval_ret', h_res_ret⟩ := ih2_comp _ _ _
            (comp_equiv_subst_binding _ h_ret_equiv h_val_mid h_e'_closed h_fresh_ret
              (barendregt_fresh_env _ _))
            h_ret_closed
          exact ⟨v_ret, σ_ret,
            ApplyKont.apply_restore_handle h_apply
              (HandleValue.handle_return rfl h_fresh_ret rfl h_eval_ret'),
            h_res_ret⟩
  | @BP.EvalN.handle_op _ _ _ _ _ _ x_op_bp _ _ _ _ h_bp_eval_inner h_bp_findOp h_eval_op =>
    have ⟨ih1_comp, ih1_kont⟩ := completeness_combinedN h_bp_eval_inner
    have ⟨ih2_comp, ih2_kont⟩ := completeness_combinedN h_eval_op
    refine ⟨?_, ?_⟩
    · -- P_comp
      intro σ ρ e h_equiv h_closed
      cases h_equiv with
      | tail h_cexp =>
        cases h_cexp with
        | handler h_handler h_c =>
          have h_fvs_c := bp_withHandle_fvs_c h_closed
          obtain ⟨v1, σ1, h_eval1, h_res1⟩ := ih1_comp _ _ _ h_c h_fvs_c
          obtain ⟨a_op, d_op, κ, rfl, h_store_op, h_val_op, h_kont⟩ := result_equiv_op_inv h_res1
          have h_mono := eval_store_mono h_eval1
          have h_hdl_σ1 := handler_equiv_store_mono h_handler h_mono
          obtain ⟨e_op_anf, h_anf_findOp, h_clause_equiv⟩ :=
            handler_findOp_equiv h_hdl_σ1 h_bp_findOp
          obtain ⟨a_vk, h_fresh_vk⟩ := exists_fresh σ1
          let h_anf := h_hdl_σ1.getAnf
          let kont_d := Denotable.kontClosure h_anf ρ κ
          obtain ⟨a_v', h_fresh_av⟩ := exists_fresh (σ1.extend a_vk kont_d)
          have h_fresh_av_orig := Store.fresh_of_fresh_extend h_fresh_av
          have h_ne_addrs := Store.ne_of_fresh_extend h_fresh_av
          have h_eop_closed := (bp_eval_op_closed (BP.evalN_to_eval h_bp_eval_inner) (bp_withHandle_fvs_c h_closed)).1
          have h_subst1 := comp_equiv_subst_binding x_op_bp h_clause_equiv
            h_val_op h_eop_closed h_fresh_av_orig (barendregt_fresh_env _ x_op_bp)
          have h_val_kont_mono := @value_equiv_extend_store _ _ _ a_v' d_op
            (ValueEquiv.kont h_hdl_σ1 h_kont (not_mem_withHandle_hdl_fvs h_closed)) h_fresh_av_orig
          have h_kont_closed := bp_kont_lam_closed (BP.evalN_to_eval h_bp_eval_inner) h_closed
          have h_fresh_vk_ext := Store.fresh_extend_of_fresh (d := d_op) h_fresh_vk h_ne_addrs
          have h_subst2 := comp_equiv_subst_binding "resume" h_subst1
            h_val_kont_mono h_kont_closed h_fresh_vk_ext (barendregt_fresh_env _ "resume")
          have h_ih2_closed := bp_comp_subst_closed_of_fvs_sub
            (bp_comp_subst_fvs_sub (bp_findOp_fvs h_closed h_bp_findOp) h_eop_closed)
            h_kont_closed
          obtain ⟨v2, σ2, h_eval2, h_res2⟩ := ih2_comp _ _ _ h_subst2 h_ih2_closed
          exact ⟨v2, σ2,
            EvalExp.eval_tail (EvalCExp.eval_handler h_eval1
              (HandleValue.handle_op h_anf_findOp h_fresh_av_orig h_fresh_vk (Ne.symm h_ne_addrs) h_store_op rfl h_eval2)),
            h_res2⟩
    · -- P_kont
      intro σ x_c c_op κ e_arg d h_kont h_eq h_val_arg h_closed_kont h_arg_closed
      match h_kont with
      | .kont_end =>
        simp [BP.Comp.subst_val, BP.Expr.subst_var_self] at h_eq
      | .kont_let _ _ h_fresh_c2 =>
        rw [BP.Comp.subst_letIn] at h_eq
        rw [BP.Comp.subst_not_mem_fvs h_fresh_c2] at h_eq
        simp only [ite_self] at h_eq; cases h_eq
      | .kont_handle h_kont_inner h_hdl_inner h_fresh_hdl =>
        rename_i c_inner_kont κ_rest ρ_hdl _ _
        simp only [BP.Comp.subst_withHandle] at h_eq
        rw [BP.BPHandler.subst_not_mem_fvs h_fresh_hdl] at h_eq
        have ⟨h_heq, h_ceq⟩ := BP.Comp.withHandle.inj h_eq
        subst h_heq; subst h_ceq
        simp only [BP.Comp.subst_withHandle] at h_closed_kont
        rw [BP.BPHandler.subst_not_mem_fvs h_fresh_hdl] at h_closed_kont
        have h_inner_closed := bp_withHandle_fvs_c h_closed_kont
        obtain ⟨v_mid, σ_mid, h_apply, h_res_mid⟩ :=
          ih1_kont _ _ _ _ _ _ h_kont_inner rfl h_val_arg h_inner_closed h_arg_closed
        obtain ⟨a_op, d_op, κ_op, rfl, h_store_op, h_val_op, h_kont_op⟩ := result_equiv_op_inv h_res_mid
        have h_hdl_mono := handler_equiv_store_mono h_hdl_inner (eval_apply_store_mono h_apply)
        obtain ⟨e_op_anf, h_anf_findOp, h_clause_equiv⟩ :=
          handler_findOp_equiv h_hdl_mono h_bp_findOp
        obtain ⟨a_vk, h_fresh_vk⟩ := exists_fresh σ_mid
        let h_anf_hdl' := h_hdl_mono.getAnf
        let kont_d := Denotable.kontClosure h_anf_hdl' ρ_hdl κ_op
        obtain ⟨a_v', h_fresh_av⟩ := exists_fresh (σ_mid.extend a_vk kont_d)
        have h_fresh_av_orig := Store.fresh_of_fresh_extend h_fresh_av
        have h_ne_addrs := Store.ne_of_fresh_extend h_fresh_av
        have h_eop_closed := (bp_eval_op_closed (BP.evalN_to_eval h_bp_eval_inner) h_inner_closed).1
        have h_subst1 := comp_equiv_subst_binding x_op_bp h_clause_equiv
          h_val_op h_eop_closed h_fresh_av_orig (barendregt_fresh_env _ x_op_bp)
        have h_val_kont_mono := @value_equiv_extend_store _ _ _ a_v' d_op
          (ValueEquiv.kont h_hdl_mono h_kont_op (not_mem_withHandle_hdl_fvs h_closed_kont)) h_fresh_av_orig
        have h_kont_closed := bp_kont_lam_closed (BP.evalN_to_eval h_bp_eval_inner) h_closed_kont
        have h_fresh_vk_ext := Store.fresh_extend_of_fresh (d := d_op) h_fresh_vk h_ne_addrs
        have h_subst2 := comp_equiv_subst_binding "resume" h_subst1
          h_val_kont_mono h_kont_closed h_fresh_vk_ext (barendregt_fresh_env _ "resume")
        have h_ih2_closed := bp_comp_subst_closed_of_fvs_sub
          (bp_comp_subst_fvs_sub (bp_findOp_fvs h_closed_kont h_bp_findOp) h_eop_closed)
          h_kont_closed
        obtain ⟨v2, σ2, h_eval2, h_res2⟩ := ih2_comp _ _ _ h_subst2 h_ih2_closed
        exact ⟨v2, σ2,
          ApplyKont.apply_restore_handle h_apply
            (HandleValue.handle_op h_anf_findOp h_fresh_av_orig h_fresh_vk (Ne.symm h_ne_addrs) h_store_op rfl h_eval2),
          h_res2⟩
  termination_by n

/-- Combined completeness for BP.Eval: wraps the height-indexed version -/
theorem completeness_combined (h_eval : BP.Eval c r) :
    (∀ (σ : Store) (ρ : Env) (e : Exp), CompEquiv σ ρ c e → c.fvs = [] →
      ∃ v σ', EvalExp e ρ σ v σ' ∧ ResultEquiv σ' r v) ∧
    (∀ (σ : Store) (x_c : Var) (c_op : BP.Comp) (κ : Kont) (e_arg : BP.Expr) (d : Denotable),
      KontEquiv σ x_c c_op κ →
      c = c_op.subst x_c e_arg →
      ValueEquiv σ e_arg d →
      (c_op.subst x_c e_arg).fvs = [] →
      e_arg.fvs = [] →
      ∃ v σ', ApplyKont κ d σ v σ' ∧ ResultEquiv σ' r v) := by
  obtain ⟨n, hn⟩ := BP.eval_to_evalN h_eval
  exact completeness_combinedN hn

/-- Standard completeness extracted from the combined theorem -/
theorem completeness_open' (h_eval : BP.Eval c r) :
    CompEquiv σ ρ c e → c.fvs = [] →
    ∃ v σ', EvalExp e ρ σ v σ' ∧ ResultEquiv σ' r v :=
  (completeness_combined h_eval).1 σ ρ e

end DMCFA
