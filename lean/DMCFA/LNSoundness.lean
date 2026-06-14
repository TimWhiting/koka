/-
  Soundness: ANF evaluation → B&P evaluation (locally-nameless rewrite)

  If an ANF expression evaluates to a result under (ρ, σ), and the expression
  is equivalent to a B&P computation, then the B&P computation evaluates to
  a corresponding result.

  Binders are de Bruijn indices: substitution into a binding body is
  `comp_equiv_open_binding`/`comp_equiv_open_binding_addr` (depth `n=0`), which
  carry no environment-domain-freshness side conditions, and `resume` is an
  ordinary de Bruijn binder. `KontEquiv` carries no hole variable: the hole is
  `bvar 0`, so a B&P op-clause body is filled by `c_op.open_ e_bp`.
-/

import DMCFA.LNLemmas

namespace DMCFA.LN

/-! ## Reverse direction of expr_equiv_eval_atomic -/

/-- If a B&P expression is `ExprEquiv` to an ANF atomic that evaluates to `d`,
then the B&P expression is `ValueEquiv` to `d`. Direct consequence of the
forward `expr_equiv_eval_atomic` plus determinism of `evalAtomic`. -/
theorem eval_atomic_value_equiv
    (h_equiv : ExprEquiv σ ρ 0 e_bp ae)
    (h_eval : evalAtomic ae ρ σ = some d)
    (h_closed : e_bp.fvs = []) :
    ValueEquiv σ e_bp d := by
  obtain ⟨d', h_eval', h_val⟩ := expr_equiv_eval_atomic h_equiv h_closed
  rw [h_eval'] at h_eval; cases h_eval; exact h_val

/-! ## Reverse handler findOp -/

private theorem op_clauses_findOp_equiv_rev {n : Nat}
    (h : OpClausesEquiv σ ρ n bp_ops anf_ops)
    (h_find : anf_ops.findSome? (fun p => if p.1 = op then some p.2 else none) = some e_anf) :
    ∃ c_bp, bp_ops.findSome? (fun p => if p.1 = op then some p.2 else none) = some c_bp ∧
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
      exact op_clauses_findOp_equiv_rev h_rest h_find

private theorem handler_findOp_equiv_rev {n : Nat}
    (h : HandlerEquiv σ ρ n h_bp h_anf)
    (h_find : h_anf.findOp op = some e_anf) :
    ∃ c_bp, h_bp.findOp op = some c_bp ∧ CompEquiv σ ρ (n + 2) c_bp e_anf := by
  cases h with
  | mk _ h_ops =>
    simp only [BPLN.BPHandler.findOp, Handler.findOp] at h_find ⊢
    exact op_clauses_findOp_equiv_rev h_ops h_find

/-! ## Singleton list helpers for `funApp` (single-argument application) -/

private theorem list_singleton_of_length_one {α : Type _} [Inhabited α] (l : List α) (h : l.length = 1) :
    l = [l[0]!] := by
  match l, h with | [_], _ => rfl

private theorem zip_foldl_extend_store_singleton
    (σ : Store) (as_v : List VAddr) (ds : List Denotable)
    (h_as : as_v.length = 1) (h_ds : ds.length ≥ 1) :
    (List.zip as_v ds).foldl (fun s (p : VAddr × Denotable) => s.extend p.1 p.2) σ =
    σ.extend as_v[0]! ds[0]! := by
  rw [list_singleton_of_length_one as_v h_as]
  match ds, h_ds with
  | _ :: _, _ => simp [List.zip, List.zipWith, List.foldl]

private theorem pushMany_singleton (ρ : Env) (a : VAddr) :
    ρ.pushMany [a] = ρ.push a := rfl

/-! ## Main soundness: combined height-indexed theorem -/

/-- Combined soundness (height-indexed): proves EvalExpN, EvalCExpN, and ApplyKontN
    soundness simultaneously via well-founded recursion on the height parameter. -/
private theorem soundness_allN (n : Nat) :
    -- P_exp
    (∀ e ρ σ v σ' c, EvalExpN n e ρ σ v σ' → CompEquiv σ ρ 0 c e → c.fvs = [] →
      ∃ r, BPLN.Eval c r ∧ ResultEquiv σ' r v) ∧
    -- P_cexp
    (∀ ce ρ σ v σ' c, EvalCExpN n ce ρ σ v σ' → CompEquivCExp σ ρ 0 c ce → c.fvs = [] →
      ∃ r, BPLN.Eval c r ∧ ResultEquiv σ' r v) ∧
    -- P_apply
    (∀ κ d σ v σ' c_op e_bp,
      ApplyKontN n κ d σ v σ' → KontEquiv σ c_op κ → ValueEquiv σ e_bp d →
      e_bp.fvs = [] → (c_op.open_ e_bp).fvs = [] →
      ∃ r, BPLN.Eval (c_op.open_ e_bp) r ∧ ResultEquiv σ' r v) := by
  constructor
  -- ═══════════════════════════════════════════
  -- P_exp: soundness for EvalExpN n
  -- ═══════════════════════════════════════════
  · intro e ρ σ v σ' c h_eval h_equiv h_closed
    match h_eval with
    | .eval_tail h_cexp =>
      cases h_equiv with
      | tail h_cexp_equiv =>
        exact (soundness_allN _).2.1 _ _ _ _ _ _ h_cexp h_cexp_equiv h_closed
    | .eval_let h_cexp h_cont =>
      match h_equiv with
      | .letE h_cexp_equiv h_c2_equiv =>
        obtain ⟨r1, h_bp1, h_res1⟩ := (soundness_allN _).2.1 _ _ _ _ _ _ h_cexp h_cexp_equiv (bp_letIn_fvs_c1 h_closed)
        cases h_cont with
        | continue_let h_fresh_av h_sigma_let h_eval_body =>
          cases h_res1 with
          | value h_val1 =>
            have h_mono := eval_cexp_store_mono (eval_cexpN_to h_cexp)
            have h_c2_mono := comp_equiv_store_mono h_c2_equiv h_mono
            have h_e'_closed := bp_eval_value_closed h_bp1 (bp_letIn_fvs_c1 h_closed)
            have h_c2_fvs := bp_letIn_fvs_c2 h_closed
            subst h_sigma_let
            have h_subst := comp_equiv_open_binding (n := 0) h_c2_mono h_val1 h_e'_closed h_fresh_av
            have h_subst_closed := BPLN.Comp.fvs_open_closed (k := 0) h_c2_fvs h_e'_closed
            obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_body h_subst h_subst_closed
            exact ⟨r, .let_val h_bp1 h_bp, h_res⟩
        | continue_op =>
          cases h_res1 with
          | op h_store h_val_op h_kont =>
            have h_mono := eval_cexp_store_mono (eval_cexpN_to h_cexp)
            exact ⟨_, .let_op h_bp1,
              .op h_store h_val_op (.kont_let h_kont (comp_equiv_store_mono h_c2_equiv h_mono))⟩
      | @CompEquiv.letRec _ _ _ c1_bp e1_anf c2_bp e2_anf l_anf h_c1_equiv h_c2_equiv =>
        match h_cexp with
        | .eval_fun h_fresh h_vf h_sigma =>
          rename_i a_rec
          cases h_cont with
          | continue_let h_fresh_av h_sigma_let h_eval_body =>
            subst h_vf; subst h_sigma
            have h_c1_fvs := bp_letRec_fvs_c1 h_closed
            have h_c2_fvs := bp_letRec_fvs_c2 h_closed
            have h_lam_closed : (BPLN.Expr.lam (BPLN.Comp.letRec c1_bp c1_bp)).fvs = [] := by
              simp [h_c1_fvs]
            have h_c1_mono : CompEquiv (Store.extend σ a_rec (Denotable.closure ⟨1, e1_anf, ρ, some a_rec⟩)) ρ 2 c1_bp e1_anf :=
              comp_equiv_extend_store h_c1_equiv h_fresh
            have h_rec_val : ValueEquiv (Store.extend σ a_rec (Denotable.closure ⟨1, e1_anf, ρ, some a_rec⟩))
                (BPLN.Expr.lam (BPLN.Comp.letRec c1_bp c1_bp)) (Denotable.closure ⟨1, e1_anf, ρ, some a_rec⟩) :=
              .rec_lambda h_c1_mono (by simp [Store.extend])
            have h_c2_mono : CompEquiv (Store.extend σ a_rec (Denotable.closure ⟨1, e1_anf, ρ, some a_rec⟩)) ρ 1 c2_bp e2_anf :=
              comp_equiv_extend_store h_c2_equiv h_fresh
            subst h_sigma_let
            have h_subst := comp_equiv_open_binding (n := 0) h_c2_mono h_rec_val h_lam_closed h_fresh_av
            have h_subst_closed := BPLN.Comp.fvs_open_closed (k := 0) h_c2_fvs h_lam_closed
            obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_body h_subst h_subst_closed
            exact ⟨r, .let_rec h_bp, h_res⟩
  constructor
  -- ═══════════════════════════════════════════
  -- P_cexp: soundness for EvalCExpN n
  -- ═══════════════════════════════════════════
  · intro ce ρ σ v σ' c h_eval h_equiv h_closed
    match h_eval with
    | .eval_atomic h_atomic =>
      cases h_equiv with
      | atomic h_expr =>
        exact ⟨.value _, .val, .value (eval_atomic_value_equiv h_expr h_atomic (bp_val_fvs h_closed))⟩
    | .eval_opApp h_rho =>
      cases h_equiv with
      | opApp_bvar h_expr =>
        have h_e_closed := bp_opCall_fvs h_closed
        cases h_expr with
        | var_bound h_lt => exact absurd h_lt (Nat.not_lt_zero _)
        | var_subst h_le h_rho' h_store h_val _ =>
          simp only [Nat.sub_zero] at h_rho'
          simp only [evalAddr, h_rho'] at h_rho
          obtain rfl := Option.some.inj h_rho
          exact ⟨_, .op_call, .op h_store h_val .kont_end⟩
    | .eval_match h_atomic h_d_eq h_find h_eval_body =>
      subst h_d_eq
      cases h_equiv with
      | ifE h_expr h_c1 h_c2 =>
        have h_val := eval_atomic_value_equiv h_expr h_atomic (bp_if_fvs_scrutinee h_closed)
        cases h_val with
        | con_true =>
          simp only [findBranch_true] at h_find; obtain rfl := Option.some.inj h_find
          obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_body h_c1 (bp_if_fvs_c1 h_closed)
          exact ⟨r, .if_true h_bp, h_res⟩
        | con_false =>
          simp only [findBranch_false] at h_find; obtain rfl := Option.some.inj h_find
          obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_body h_c2 (bp_if_fvs_c2 h_closed)
          exact ⟨r, .if_false h_bp, h_res⟩
        | con_unit => simp [findBranch, List.findSome?] at h_find
        | con_zero => simp [findBranch, List.findSome?] at h_find
      | matchNat h_expr h_c1 h_c2 =>
        have h_val := eval_atomic_value_equiv h_expr h_atomic (bp_matchNat_fvs_scrutinee h_closed)
        cases h_val with
        | con_zero =>
          simp only [findBranch_zero] at h_find; obtain rfl := Option.some.inj h_find
          obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_body h_c1 (bp_matchNat_fvs_c1 h_closed)
          exact ⟨r, .match_zero h_bp, h_res⟩
        | con_true => simp [findBranch, List.findSome?] at h_find
        | con_false => simp [findBranch, List.findSome?] at h_find
        | con_unit => simp [findBranch, List.findSome?] at h_find
    | .eval_match_succ h_atomic h_find h_store_inner h_fresh h_sigma h_rho_new h_eval_body =>
      cases h_equiv with
      | ifE h_expr h_c1 h_c2 =>
        simp [findBranch, List.findSome?] at h_find
      | matchNat h_expr h_c1 h_c2 =>
        have h_scrutinee_closed := bp_matchNat_fvs_scrutinee h_closed
        have h_c2_fvs := bp_matchNat_fvs_c2 h_closed
        have h_val := eval_atomic_value_equiv h_expr h_atomic h_scrutinee_closed
        cases h_val with
        | succ h_store_e' h_inner_val =>
          simp only [findBranch_succ] at h_find; obtain rfl := Option.some.inj h_find
          subst h_sigma; subst h_rho_new
          have h_e'_closed := by simp only [BPLN.Expr.fvs_succ] at h_scrutinee_closed; exact h_scrutinee_closed
          rw [h_store_e'] at h_store_inner; obtain rfl := Option.some.inj h_store_inner
          have h_subst := comp_equiv_open_binding (n := 0) h_c2 h_inner_val h_e'_closed h_fresh
          have h_subst_closed := BPLN.Comp.fvs_open_closed (k := 0) h_c2_fvs h_e'_closed
          obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_body h_subst h_subst_closed
          exact ⟨r, .match_succ h_bp, h_res⟩
    | .eval_funApp_clos h_fun h_arity h_args h_fresh_addrs h_distinct h_as_len h_sigma h_rho h_body =>
      rename_i f_ae arity e_body_anf ρ_lam selfAddr aes ds as_v σ_new ρ_new _
      cases h_equiv with
      | funApp h_e1 h_e2 =>
        rename_i e1_bp e2_bp ae2
        have h_e1_closed := bp_app_fvs_e1 h_closed
        have h_fun_val := eval_atomic_value_equiv h_e1 h_fun h_e1_closed
        have h_e2_closed := bp_app_fvs_e2 h_closed
        have h_arg_eval : evalAtomic ae2 ρ σ = some ds[0]! := by
          cases h_args with
          | cons h _ => simpa [List.getElem!_cons_zero] using h
        have h_a_fresh : σ as_v[0]! = none := by
          cases h_fresh_addrs with
          | nil => exact absurd h_args.length_eq (by simp)
          | cons h _ => simpa [List.getElem!_cons_zero] using h
        have h_as1 : as_v.length = 1 := by simp [h_as_len]
        have h_ds_len : ds.length ≥ 1 := by
          have h := h_args.length_eq; simp at h; omega
        rw [zip_foldl_extend_store_singleton _ _ _ h_as1 h_ds_len] at h_sigma
        match h_fun_val with
        | .lambda h_body_equiv =>
          rename_i c_body
          have h_arg_val := eval_atomic_value_equiv h_e2 h_arg_eval h_e2_closed
          have h_subst := comp_equiv_open_binding (n := 0) h_body_equiv h_arg_val h_e2_closed h_a_fresh
          have h_body_fvs : c_body.fvs = [] := by
            simpa only [BPLN.Expr.fvs_lam] using h_e1_closed
          have h_subst_closed := BPLN.Comp.fvs_open_closed (k := 0) h_body_fvs h_e2_closed
          rw [list_singleton_of_length_one as_v h_as1, pushMany_singleton] at h_rho
          subst h_sigma; subst h_rho
          obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_body h_subst h_subst_closed
          exact ⟨r, .app_lam h_bp, h_res⟩
        | .rec_lambda h_c1_equiv h_store_f =>
          rename_i c1_bp a_f
          have h_arg_val := eval_atomic_value_equiv h_e2 h_arg_eval h_e2_closed
          have h_c1_fvs : c1_bp.fvs = [] := by
            have h := h_e1_closed; simp only [BPLN.Expr.fvs_lam] at h; exact bp_letRec_fvs_c1 h
          have h_lam_closed : (BPLN.Expr.lam (BPLN.Comp.letRec c1_bp c1_bp)).fvs = [] := by
            simp [h_c1_fvs]
          have h_ne_af_av : a_f ≠ as_v[0]! := by
            intro h_eq; rw [h_eq] at h_store_f; rw [h_a_fresh] at h_store_f; simp at h_store_f
          have h_step1 :=
            comp_equiv_open_binding (n := 1) h_c1_equiv h_arg_val h_e2_closed h_a_fresh
          have h_store_af1 : (Store.extend σ as_v[0]! ds[0]!) a_f =
              some (Denotable.closure ⟨1, e_body_anf, ρ_lam, some a_f⟩) := by
            rw [Store.extend_preserves _ _ _ _ h_ne_af_av]; exact h_store_f
          have h_val_lam1 :=
            value_equiv_extend_store (d_new := ds[0]!)
              (ValueEquiv.rec_lambda h_c1_equiv h_store_f) h_a_fresh
          have h_step2 :=
            comp_equiv_open_binding_addr (n := 0) h_step1 h_val_lam1 h_lam_closed h_store_af1
          have h_X_eq : BPLN.compOpenRec 2 e2_bp c1_bp = c1_bp :=
            BPLN.comp_open_lc_at c1_bp 2 2 e2_bp (comp_equiv_lcAt h_c1_equiv) (le_refl 2)
          have h_c1_fvs' : (BPLN.compOpenRec 1 e2_bp c1_bp).fvs = [] :=
            BPLN.Comp.fvs_open_closed h_c1_fvs h_e2_closed
          have h_open_closed' :
              (BPLN.Comp.open_ (BPLN.compOpenRec 1 e2_bp c1_bp)
                (BPLN.Expr.lam (BPLN.Comp.letRec c1_bp c1_bp))).fvs = [] :=
            BPLN.Comp.fvs_open_closed (k := 0) h_c1_fvs' h_lam_closed
          rw [list_singleton_of_length_one as_v h_as1, pushMany_singleton] at h_rho
          subst h_sigma; subst h_rho
          obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_body h_step2 h_open_closed'
          refine ⟨r, ?_, h_res⟩
          apply BPLN.Eval.app_lam
          simp only [BPLN.Comp.open_, BPLN.Comp.open_letRec, h_X_eq]
          exact .let_rec h_bp
    | .eval_funApp_kont h_fun h_arg h_apply h_handle =>
      rename_i f_x h_anf ρ_h κ ae_x d_x n1_x v'_x σ'_x n2_x
      cases h_equiv with
      | funApp h_e1 h_e2 =>
        have h_e1_closed := bp_app_fvs_e1 h_closed
        have h_e2_closed := bp_app_fvs_e2 h_closed
        have h_fun_val := eval_atomic_value_equiv h_e1 h_fun h_e1_closed
        have h_arg_val := eval_atomic_value_equiv h_e2 h_arg h_e2_closed
        cases h_fun_val with
        | kont h_hdl_equiv h_kont_equiv =>
          rename_i e2_bp h_bp c_op_bp
          have h_body_closed : (BPLN.Comp.withHandle h_bp c_op_bp).fvs = [] := by
            simpa only [BPLN.Expr.fvs_lam] using h_e1_closed
          have h_inner_closed := bp_withHandle_fvs_c h_body_closed
          have h_open_inner_closed : (c_op_bp.open_ e2_bp).fvs = [] :=
            BPLN.Comp.fvs_open_closed h_inner_closed h_e2_closed
          obtain ⟨r_inner, h_bp_inner, h_res_inner⟩ :=
            (soundness_allN _).2.2 _ _ _ _ _ _ _ h_apply h_kont_equiv h_arg_val h_e2_closed
              h_open_inner_closed
          -- opening the captured handler `(withHandle h c_op_bp).open_ e2_bp` is
          -- `withHandle h (c_op_bp.open_ e2_bp)` since the handler is lc at depth 1.
          have h_ret_id : BPLN.compOpenRec (0 + 1) e2_bp h_bp.returnClause = h_bp.returnClause :=
            BPLN.comp_open_lc_at h_bp.returnClause 1 (0 + 1) e2_bp (handler_equiv_lcAt_ret h_hdl_equiv) (by omega)
          have h_ops_id : BPLN.opsOpenRec (0 + 2) e2_bp h_bp.opClauses = h_bp.opClauses :=
            BPLN.ops_open_lc_at h_bp.opClauses 2 (0 + 2) e2_bp (handler_equiv_lcAt_ops h_hdl_equiv) (by omega)
          have h_eta : (⟨h_bp.returnClause, h_bp.opClauses⟩ : BPLN.BPHandler) = h_bp := by
            cases h_bp; rfl
          have h_open_eq : (BPLN.Comp.withHandle h_bp c_op_bp).open_ e2_bp
              = BPLN.Comp.withHandle h_bp (c_op_bp.open_ e2_bp) := by
            simp only [BPLN.Comp.open_, BPLN.Comp.open_withHandle, h_ret_id, h_ops_id, h_eta]
          have h_wh_closed : (BPLN.Comp.withHandle h_bp (c_op_bp.open_ e2_bp)).fvs = [] :=
            h_open_eq ▸ BPLN.Comp.fvs_open_closed h_body_closed h_e2_closed
          have h_apply_mono := eval_apply_store_mono (apply_kontN_to h_apply)
          match h_handle with
          | .handle_return h_ret h_fresh_ret h_sigma_ret h_eval_ret =>
            cases h_res_inner with
            | value h_val =>
              have h_hdl_mono := handler_equiv_store_mono h_hdl_equiv h_apply_mono
              match h_hdl_mono with
              | .mk h_ret_equiv _ =>
                have h_e'_closed := bp_eval_value_closed h_bp_inner h_open_inner_closed
                have h_ret_fvs := bp_withHandle_ret_fvs h_wh_closed
                subst h_ret; subst h_sigma_ret
                have h_subst := comp_equiv_open_binding (n := 0) h_ret_equiv h_val h_e'_closed h_fresh_ret
                have h_subst_closed := BPLN.Comp.fvs_open_closed (k := 0) h_ret_fvs h_e'_closed
                obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_ret h_subst h_subst_closed
                exact ⟨r, .app_lam (h_open_eq ▸ BPLN.Eval.handle_val h_bp_inner h_bp), h_res⟩
          | .handle_op h_findOp h_fresh_v h_fresh_vk h_ne_addrs h_store_arg h_sigma_op h_eval_op =>
            cases h_res_inner with
            | op h_store h_val_op h_kont =>
              rename_i _ a_v' a_vk _ _ _ _ _ κ_susp d_bp e_op_bp _
              rw [h_store] at h_store_arg
              obtain rfl := Option.some.inj h_store_arg
              have h_hdl_mono := handler_equiv_store_mono h_hdl_equiv h_apply_mono
              obtain ⟨c_bp_clause, h_bp_findOp, h_clause_equiv⟩ :=
                handler_findOp_equiv_rev h_hdl_mono h_findOp
              have h_kontlam_closed := bp_kont_lam_closed h_bp_inner h_wh_closed
              have h_eop_closed := (bp_eval_op_closed h_bp_inner h_open_inner_closed).1
              have h_ch_closed := bp_findOp_fvs h_wh_closed h_bp_findOp
              have h_val_kont := ValueEquiv.kont h_hdl_mono h_kont
              have h_open1 := comp_equiv_open_binding (n := 1) h_clause_equiv h_val_kont h_kontlam_closed h_fresh_vk
              have h_val_op_ext := value_equiv_extend_store
                (d_new := Denotable.kontClosure h_anf ρ_h κ_susp) h_val_op h_fresh_vk
              have h_fresh_v_ext := Store.fresh_extend_of_fresh
                (d := Denotable.kontClosure h_anf ρ_h κ_susp) h_fresh_v h_ne_addrs
              have h_open2 := comp_equiv_open_binding (n := 0) h_open1 h_val_op_ext h_eop_closed h_fresh_v_ext
              have h_open2_closed := BPLN.Comp.fvs_open_closed (k := 0)
                (BPLN.Comp.fvs_open_closed (k := 1) h_ch_closed h_kontlam_closed) h_eop_closed
              subst h_sigma_op
              obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_op h_open2 h_open2_closed
              exact ⟨r, .app_lam (h_open_eq ▸ BPLN.Eval.handle_op h_bp_inner h_bp_findOp h_bp), h_res⟩
          | .handle_capture_op h_not_has h_v' =>
            cases h_res_inner with
            | op h_store h_val_op h_kont =>
              have h_hdl_mono := handler_equiv_store_mono h_hdl_equiv h_apply_mono
              have h_bp_not_has := (handler_hasOp_equiv h_hdl_mono ▸ h_not_has : _ = false)
              subst h_v'
              exact ⟨_, .app_lam (h_open_eq ▸ BPLN.Eval.handle_forward h_bp_inner h_bp_not_has),
                .op h_store h_val_op (.kont_handle h_kont h_hdl_mono)⟩
    | .eval_fun _ _ _ =>
      cases h_equiv
    | .eval_handler h_eval_body h_handle =>
      cases h_equiv with
      | handler h_hdl h_c =>
        rename_i _ _ σ_1 _ h_anf_h _ _ _
        obtain ⟨r_inner, h_bp_inner, h_res_inner⟩ :=
          (soundness_allN _).1 _ _ _ _ _ _ h_eval_body h_c (bp_withHandle_fvs_c h_closed)
        match h_handle with
        | .handle_return h_ret h_fresh_ret h_sigma_ret h_eval_ret =>
          cases h_res_inner with
          | value h_val =>
            have h_hdl_mono := handler_equiv_store_mono h_hdl (eval_store_mono (eval_expN_to h_eval_body))
            match h_hdl_mono with
            | .mk h_ret_equiv _ =>
              have h_e'_closed := bp_eval_value_closed h_bp_inner (bp_withHandle_fvs_c h_closed)
              have h_ret_fvs := bp_withHandle_ret_fvs h_closed
              subst h_ret; subst h_sigma_ret
              have h_subst := comp_equiv_open_binding (n := 0) h_ret_equiv h_val h_e'_closed h_fresh_ret
              have h_subst_closed := BPLN.Comp.fvs_open_closed (k := 0) h_ret_fvs h_e'_closed
              obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_ret h_subst h_subst_closed
              exact ⟨r, .handle_val h_bp_inner h_bp, h_res⟩
        | .handle_op h_findOp h_fresh_v h_fresh_vk h_ne_addrs h_store_arg h_sigma_op h_eval_op =>
          cases h_res_inner with
          | op h_store h_val_op h_kont =>
            rename_i _ a_v' a_vk _ _ _ _ _ κ_susp d_bp e_op_bp _
            rw [h_store] at h_store_arg
            obtain rfl := Option.some.inj h_store_arg
            have h_hdl_mono := handler_equiv_store_mono h_hdl (eval_store_mono (eval_expN_to h_eval_body))
            obtain ⟨c_bp_clause, h_bp_findOp, h_clause_equiv⟩ :=
              handler_findOp_equiv_rev h_hdl_mono h_findOp
            have h_kontlam_closed := bp_kont_lam_closed h_bp_inner h_closed
            have h_eop_closed := (bp_eval_op_closed h_bp_inner (bp_withHandle_fvs_c h_closed)).1
            have h_ch_closed := bp_findOp_fvs h_closed h_bp_findOp
            have h_val_kont := ValueEquiv.kont h_hdl_mono h_kont
            have h_open1 := comp_equiv_open_binding (n := 1) h_clause_equiv h_val_kont h_kontlam_closed h_fresh_vk
            have h_val_op_ext := value_equiv_extend_store
              (d_new := Denotable.kontClosure h_anf_h ρ κ_susp) h_val_op h_fresh_vk
            have h_fresh_v_ext := Store.fresh_extend_of_fresh
              (d := Denotable.kontClosure h_anf_h ρ κ_susp) h_fresh_v h_ne_addrs
            have h_open2 := comp_equiv_open_binding (n := 0) h_open1 h_val_op_ext h_eop_closed h_fresh_v_ext
            have h_open2_closed := BPLN.Comp.fvs_open_closed (k := 0)
              (BPLN.Comp.fvs_open_closed (k := 1) h_ch_closed h_kontlam_closed) h_eop_closed
            subst h_sigma_op
            obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_op h_open2 h_open2_closed
            exact ⟨r, .handle_op h_bp_inner h_bp_findOp h_bp, h_res⟩
        | .handle_capture_op h_not_has h_v' =>
          cases h_res_inner with
          | op h_store h_val_op h_kont =>
            have h_hdl_mono := handler_equiv_store_mono h_hdl (eval_store_mono (eval_expN_to h_eval_body))
            have h_bp_not_has := (handler_hasOp_equiv h_hdl_mono ▸ h_not_has : _ = false)
            subst h_v'
            exact ⟨_, .handle_forward h_bp_inner h_bp_not_has,
              .op h_store h_val_op (.kont_handle h_kont h_hdl_mono)⟩
  -- ═══════════════════════════════════════════
  -- P_apply: soundness for ApplyKontN n
  -- ═══════════════════════════════════════════
  · intro κ d σ v σ' c_op e_bp h_apply h_kont h_val h_closed h_c_closed
    match h_apply with
    | .apply_continue =>
      cases h_kont with
      | kont_end =>
        simp only [BPLN.Comp.open_, BPLN.compOpenRec, BPLN.Expr.open_bvar]
        exact ⟨_, .val, .value h_val⟩
    | .apply_restore h_apply_inner h_continue =>
      cases h_kont with
      | kont_let h_kont_inner h_c2_equiv =>
        rename_i _ _ _ _ c2
        simp only [BPLN.Comp.open_, BPLN.Comp.open_letIn] at h_c_closed ⊢
        have h_inner_closed := bp_letIn_fvs_c1 h_c_closed
        obtain ⟨r_inner, h_bp_inner, h_res_inner⟩ :=
          (soundness_allN _).2.2 _ _ _ _ _ _ _ h_apply_inner h_kont_inner h_val h_closed h_inner_closed
        -- c2 is lc at depth 1, so opening it with e_bp is the identity
        have h_c2_id : BPLN.compOpenRec (0 + 1) e_bp c2 = c2 :=
          BPLN.comp_open_lc_at c2 1 (0 + 1) e_bp (comp_equiv_lcAt h_c2_equiv) (by omega)
        match h_continue with
        | .continue_let h_fresh_av h_sigma_let h_eval_body =>
          cases h_res_inner with
          | value h_val_inner =>
            have h_mono := eval_apply_store_mono (apply_kontN_to h_apply_inner)
            have h_c2_mono := comp_equiv_store_mono h_c2_equiv h_mono
            have h_e'_closed := bp_eval_value_closed h_bp_inner h_inner_closed
            have h_c2_fvs : c2.fvs = [] := by
              have h := bp_letIn_fvs_c2 h_c_closed; rw [h_c2_id] at h; exact h
            subst h_sigma_let
            have h_subst := comp_equiv_open_binding (n := 0) h_c2_mono h_val_inner h_e'_closed h_fresh_av
            have h_subst_closed := BPLN.Comp.fvs_open_closed (k := 0) h_c2_fvs h_e'_closed
            obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_body h_subst h_subst_closed
            rw [h_c2_id]
            exact ⟨r, .let_val h_bp_inner h_bp, h_res⟩
        | .continue_op =>
          cases h_res_inner with
          | op h_store h_val_op h_kont_op =>
            have h_mono := eval_apply_store_mono (apply_kontN_to h_apply_inner)
            rw [h_c2_id]
            exact ⟨_, .let_op h_bp_inner,
              .op h_store h_val_op (.kont_let h_kont_op (comp_equiv_store_mono h_c2_equiv h_mono))⟩
    | .apply_restore_handle h_apply_inner h_handle_inner =>
      cases h_kont with
      | kont_handle h_kont_inner h_hdl_equiv =>
        rename_i _ _ _ σ_1 _ h_anf ρ_hdl c_inner h_bp
        -- handler is lc at depth 1, so opening at depth 0+1 is the identity
        have h_ret_id : BPLN.compOpenRec (0 + 1) e_bp h_bp.returnClause = h_bp.returnClause :=
          BPLN.comp_open_lc_at h_bp.returnClause 1 (0 + 1) e_bp (handler_equiv_lcAt_ret h_hdl_equiv) (by omega)
        have h_ops_id : BPLN.opsOpenRec (0 + 2) e_bp h_bp.opClauses = h_bp.opClauses :=
          BPLN.ops_open_lc_at h_bp.opClauses 2 (0 + 2) e_bp (handler_equiv_lcAt_ops h_hdl_equiv) (by omega)
        have h_eta : (⟨h_bp.returnClause, h_bp.opClauses⟩ : BPLN.BPHandler) = h_bp := by
          cases h_bp; rfl
        have h_open_eq : (BPLN.Comp.withHandle h_bp c_inner).open_ e_bp
            = BPLN.Comp.withHandle h_bp (c_inner.open_ e_bp) := by
          simp only [BPLN.Comp.open_, BPLN.Comp.open_withHandle, h_ret_id, h_ops_id, h_eta]
        rw [h_open_eq] at h_c_closed ⊢
        have h_inner_closed := bp_withHandle_fvs_c h_c_closed
        obtain ⟨r_inner, h_bp_inner, h_res_inner⟩ :=
          (soundness_allN _).2.2 _ _ _ _ _ _ _ h_apply_inner h_kont_inner h_val h_closed h_inner_closed
        have h_apply_mono := eval_apply_store_mono (apply_kontN_to h_apply_inner)
        match h_handle_inner with
        | .handle_return h_ret h_fresh_ret h_sigma_ret h_eval_ret =>
          cases h_res_inner with
          | value h_val_ret =>
            have h_hdl_mono := handler_equiv_store_mono h_hdl_equiv h_apply_mono
            match h_hdl_mono with
            | .mk h_ret_equiv _ =>
              have h_e'_closed := bp_eval_value_closed h_bp_inner h_inner_closed
              have h_ret_fvs := bp_withHandle_ret_fvs h_c_closed
              subst h_ret; subst h_sigma_ret
              have h_subst := comp_equiv_open_binding (n := 0) h_ret_equiv h_val_ret h_e'_closed h_fresh_ret
              have h_subst_closed := BPLN.Comp.fvs_open_closed (k := 0) h_ret_fvs h_e'_closed
              obtain ⟨r, h_bp_ev, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_ret h_subst h_subst_closed
              exact ⟨r, .handle_val h_bp_inner h_bp_ev, h_res⟩
        | .handle_op h_findOp h_fresh_v h_fresh_vk h_ne_addrs h_store_arg h_sigma_op h_eval_op =>
          cases h_res_inner with
          | op h_store h_val_op h_kont_op =>
            rename_i _ _ a_v' a_vk _ _ _ _ _ κ_susp d_bp e_op_bp _
            rw [h_store] at h_store_arg
            obtain rfl := Option.some.inj h_store_arg
            have h_hdl_mono := handler_equiv_store_mono h_hdl_equiv h_apply_mono
            obtain ⟨c_bp_clause, h_bp_findOp, h_clause_equiv⟩ :=
              handler_findOp_equiv_rev h_hdl_mono h_findOp
            have h_kontlam_closed := bp_kont_lam_closed h_bp_inner h_c_closed
            have h_eop_closed := (bp_eval_op_closed h_bp_inner h_inner_closed).1
            have h_ch_closed := bp_findOp_fvs h_c_closed h_bp_findOp
            have h_val_kont := ValueEquiv.kont h_hdl_mono h_kont_op
            have h_open1 := comp_equiv_open_binding (n := 1) h_clause_equiv h_val_kont h_kontlam_closed h_fresh_vk
            have h_val_op_ext := value_equiv_extend_store
              (d_new := Denotable.kontClosure h_anf ρ_hdl κ_susp) h_val_op h_fresh_vk
            have h_fresh_v_ext := Store.fresh_extend_of_fresh
              (d := Denotable.kontClosure h_anf ρ_hdl κ_susp) h_fresh_v h_ne_addrs
            have h_open2 := comp_equiv_open_binding (n := 0) h_open1 h_val_op_ext h_eop_closed h_fresh_v_ext
            have h_open2_closed := BPLN.Comp.fvs_open_closed (k := 0)
              (BPLN.Comp.fvs_open_closed (k := 1) h_ch_closed h_kontlam_closed) h_eop_closed
            subst h_sigma_op
            obtain ⟨r, h_bp_ev, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_op h_open2 h_open2_closed
            exact ⟨r, .handle_op h_bp_inner h_bp_findOp h_bp_ev, h_res⟩
        | .handle_capture_op h_not_has h_v' =>
          cases h_res_inner with
          | op h_store h_val_op h_kont_op =>
            have h_hdl_mono := handler_equiv_store_mono h_hdl_equiv h_apply_mono
            have h_bp_not_has := (handler_hasOp_equiv h_hdl_mono ▸ h_not_has : _ = false)
            subst h_v'
            exact ⟨_, .handle_forward h_bp_inner h_bp_not_has,
              .op h_store h_val_op (.kont_handle h_kont_op h_hdl_mono)⟩
  termination_by n

/-- Soundness for EvalExp -/
theorem soundness_exp
    (h_eval : EvalExp e ρ σ v σ')
    (h_equiv : CompEquiv σ ρ 0 c e)
    (h_closed : c.fvs = []) :
    ∃ r, BPLN.Eval c r ∧ ResultEquiv σ' r v := by
  obtain ⟨n, hn⟩ := eval_exp_to_N h_eval
  exact (soundness_allN n).1 _ _ _ _ _ _ hn h_equiv h_closed

/-- Soundness for ApplyKont -/
theorem soundness_applyKont
    (h_apply : ApplyKont κ d σ v σ')
    (h_kont : KontEquiv σ c_op κ)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = [])
    (h_c_closed : (c_op.open_ e_bp).fvs = []) :
    ∃ r, BPLN.Eval (c_op.open_ e_bp) r ∧ ResultEquiv σ' r v := by
  obtain ⟨n, hn⟩ := apply_kont_to_N h_apply
  exact (soundness_allN n).2.2 _ _ _ _ _ _ _ hn h_kont h_val h_closed h_c_closed

/-- Main soundness theorem -/
theorem soundness :
    EvalExp e ρ σ v σ' →
    CompEquiv σ ρ 0 c e →
    c.fvs = [] →
    ∃ r, BPLN.Eval c r ∧ ResultEquiv σ' r v :=
  soundness_exp

end DMCFA.LN
