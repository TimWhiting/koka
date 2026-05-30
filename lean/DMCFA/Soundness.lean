/-
  Soundness: ANF evaluation → B&P evaluation

  If an ANF expression evaluates to a result under (ρ, σ), and the expression
  is equivalent to a B&P computation, then the B&P computation evaluates to
  a corresponding result.
-/

import DMCFA.Lemmas

namespace DMCFA

/-! ## Reverse direction of expr_equiv_eval_atomic -/

private theorem evalAtomic_succE_inv {x : Var} {ρ : Env} {σ : Store} {d : Denotable} :
    evalAtomic (AExp.succE x) ρ σ = some d →
    ∃ a, ρ x = some a ∧ (∃ d', σ a = some d') ∧ d = Denotable.succVal a := by
  unfold evalAtomic; intro h
  match h_rho : ρ x with
  | none => simp [h_rho] at h
  | some a =>
    refine ⟨a, rfl, ?_⟩; simp [h_rho] at h
    match h_store : σ a with
    | none => simp [h_store] at h
    | some d' => simp [h_store] at h; exact ⟨⟨d', rfl⟩, h.symm⟩

private theorem evalAtomic_var_inv {x : Var} {ρ : Env} {σ : Store} {d : Denotable} :
    evalAtomic (AExp.var x) ρ σ = some d →
    ∃ a, ρ x = some a ∧ σ a = some d := by
  unfold evalAtomic; intro h
  match h_rho : ρ x with
  | none => simp [h_rho] at h
  | some a =>
    refine ⟨a, rfl, ?_⟩; simp [h_rho] at h
    match h_store : σ a with
    | none => simp [h_store] at h
    | some d' => simp [h_store] at h; subst h; rfl

theorem eval_atomic_value_equiv :
    ExprEquiv σ ρ e_bp ae →
    evalAtomic ae ρ σ = some d →
    e_bp.fvs = [] →
    ValueEquiv σ e_bp d := by
  intro h_equiv h_eval h_closed
  cases h_equiv with
  | var => simp [BP.Expr.fvs_var] at h_closed
  | true_ => simp [evalAtomic] at h_eval; subst h_eval; exact .con_true
  | false_ => simp [evalAtomic] at h_eval; subst h_eval; exact .con_false
  | unit => simp [evalAtomic] at h_eval; subst h_eval; exact .con_unit
  | zero => simp [evalAtomic] at h_eval; subst h_eval; exact .con_zero
  | succ h_inner =>
    obtain ⟨a, h_rho, ⟨d', h_store⟩, rfl⟩ := evalAtomic_succE_inv h_eval
    simp [BP.Expr.fvs_succ] at h_closed
    cases h_inner with
    | var => simp [BP.Expr.fvs_var] at h_closed
    | var_subst h_rho' h_store' h_val _ =>
      rw [h_rho'] at h_rho; cases h_rho; rw [h_store'] at h_store; cases h_store
      exact .succ h_store' h_val
  | lam h_body =>
    simp [evalAtomic] at h_eval; cases h_eval; exact .lambda h_body
  | var_subst h_rho h_store h_val _ =>
    obtain ⟨a, h_rho', h_store'⟩ := evalAtomic_var_inv h_eval
    rw [h_rho] at h_rho'; cases h_rho'; rw [h_store] at h_store'; cases h_store'
    exact h_val

/-! ## Reverse handler findOp -/

private theorem op_clauses_findOp_equiv_rev
    (h : OpClausesEquiv σ ρ bp_ops anf_ops)
    (h_find : anf_ops.findSome? (fun p => if p.1 = op then some (p.2.1, p.2.2) else none) = some (x_op, e_anf)) :
    ∃ c_bp, bp_ops.findSome? (fun p => if p.1 = op then some (p.2.1, p.2.2) else none) = some (x_op, c_bp) ∧
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
      exact op_clauses_findOp_equiv_rev h_rest h_find

private theorem handler_findOp_equiv_rev
    (h : HandlerEquiv σ ρ h_bp h_anf)
    (h_find : h_anf.findOp op = some (x_op, e_anf)) :
    ∃ c_bp, h_bp.findOp op = some (x_op, c_bp) ∧ CompEquiv σ ρ c_bp e_anf := by
  cases h with
  | mk _ h_ops =>
    simp only [BP.BPHandler.findOp, Handler.findOp] at h_find ⊢
    exact op_clauses_findOp_equiv_rev h_ops h_find

private theorem list_singleton_of_length_one {α : Type _} [Inhabited α] (l : List α) (h : l.length = 1) :
    l = [l[0]!] := by
  match l, h with | [a], _ => rfl

private theorem zip_foldl_extend_store_singleton
    (σ : Store) (as_v : List VAddr) (ds : List Denotable)
    (h_as : as_v.length = 1) (h_ds : ds.length ≥ 1) :
    (List.zip as_v ds).foldl (fun s (p : VAddr × Denotable) => s.extend p.1 p.2) σ =
    σ.extend as_v[0]! ds[0]! := by
  rw [list_singleton_of_length_one as_v h_as]
  match ds, h_ds with
  | d :: _, _ => simp [List.zip, List.zipWith, List.foldl]

private theorem zip_foldl_extend_env_singleton
    (ρ : Env) (xs : List Var) (as_v : List VAddr) (h : as_v.length = 1) (h2 : xs.length = 1) :
    (List.zip xs as_v).foldl (fun r (p : Var × VAddr) => r.extend p.1 p.2) ρ =
    ρ.extend xs[0]! as_v[0]! := by
  rw [list_singleton_of_length_one as_v h, list_singleton_of_length_one xs h2]
  simp [List.zip, List.zipWith, List.foldl]

/-! ## Main soundness: combined height-indexed theorem -/

/-- Combined soundness (height-indexed): proves EvalExpN, EvalCExpN, and ApplyKontN
    soundness simultaneously via well-founded recursion on the height parameter. -/
private theorem soundness_allN (n : Nat) :
    -- P_exp
    (∀ e ρ σ v σ' c, EvalExpN n e ρ σ v σ' → CompEquiv σ ρ c e → c.fvs = [] →
      ∃ r, BP.Eval c r ∧ ResultEquiv σ' r v) ∧
    -- P_cexp
    (∀ ce ρ σ v σ' c, EvalCExpN n ce ρ σ v σ' → CompEquivCExp σ ρ c ce → c.fvs = [] →
      ∃ r, BP.Eval c r ∧ ResultEquiv σ' r v) ∧
    -- P_apply
    (∀ κ d σ v σ' x_c c_op e_bp,
      ApplyKontN n κ d σ v σ' → KontEquiv σ x_c c_op κ → ValueEquiv σ e_bp d →
      e_bp.fvs = [] → (c_op.subst x_c e_bp).fvs = [] →
      ∃ r, BP.Eval (c_op.subst x_c e_bp) r ∧ ResultEquiv σ' r v) := by
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
    | @EvalExpN.eval_let _ _ _ _ _ _ _ x_bp _ _ _ _ h_cexp h_cont =>
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
            have h_subst := comp_equiv_subst_binding x_bp h_c2_mono h_val1 h_e'_closed h_fresh_av
              (barendregt_fresh_env _ x_bp)
            have h_subst_closed := bp_comp_subst_closed_of_fvs_sub h_c2_fvs h_e'_closed
            obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_body h_subst h_subst_closed
            exact ⟨r, .let_val h_bp1 h_bp, h_res⟩
        | continue_op =>
          cases h_res1 with
          | op h_store h_val_op h_kont =>
            have h_mono := eval_cexp_store_mono (eval_cexpN_to h_cexp)
            exact ⟨_, .let_op h_bp1,
              .op h_store h_val_op (.kont_let h_kont (comp_equiv_store_mono h_c2_equiv h_mono) (fun hm => absurd (bp_letIn_fvs_c2 h_closed _ hm) (barendregt_var_ne _ _)))⟩
      | @CompEquiv.letRec _ _ c1_bp _ _ _ _ _ _ h_c1_equiv h_c2_equiv =>
        match h_cexp with
        | @EvalCExpN.eval_fun _ _ [x_param] e1_rec _ _ _ a_rec h_fresh _ h_vf h_sigma =>
          cases h_cont with
          | continue_let h_fresh_av h_sigma_let h_eval_body =>
            subst h_vf; subst h_sigma
            have ⟨h_c1_fvs, h_c2_fvs⟩ := bp_letRec_fvs h_closed
            have h_c1_extended := comp_equiv_weaken
              (d := Denotable.closure ⟨[x_param], e1_rec, Env.extend ρ x_bp a_rec, List.nodup_singleton _⟩)
              x_bp h_c1_equiv h_fresh (barendregt_fresh_env ρ x_bp)
            have h_store_av : (Store.extend σ a_rec
                (Denotable.closure ⟨[x_param], e1_rec, Env.extend ρ x_bp a_rec, List.nodup_singleton _⟩)) a_rec =
                some (Denotable.closure ⟨[x_param], e1_rec, Env.extend ρ x_bp a_rec, List.nodup_singleton _⟩) := by
              simp [Store.extend]
            have h_rec_val := ValueEquiv.rec_lambda h_c1_extended h_store_av
            have h_lam_closed : (BP.Expr.lam x_param (BP.Comp.letRec x_bp x_param c1_bp c1_bp)).fvs = [] := by
              rw [BP.Expr.fvs_lam, BP.Comp.fvs_letRec, List.filter_append]
              suffices h : (c1_bp.fvs.filter (fun v => decide (v ≠ x_bp) && decide (v ≠ x_param))).filter (fun v => decide (v ≠ x_param)) = [] ∧
                  (c1_bp.fvs.filter (fun v => decide (v ≠ x_bp))).filter (fun v => decide (v ≠ x_param)) = [] by
                rw [h.1, h.2]; rfl
              refine ⟨?_, ?_⟩ <;> {
                apply List.filter_eq_nil_iff.mpr; intro v hv
                have hv' := (List.mem_filter.mp hv).1
                rcases h_c1_fvs v hv' with rfl | rfl <;> simp_all
              }
            have h_c2_mono := comp_equiv_extend_store
              (d_new := Denotable.closure ⟨[x_param], e1_rec, Env.extend ρ x_bp a_rec, List.nodup_singleton _⟩)
              h_c2_equiv h_fresh
            have h_subst := comp_equiv_subst_binding x_bp h_c2_mono h_rec_val h_lam_closed
                h_fresh_av (barendregt_fresh_env _ x_bp)
            have h_subst_closed := bp_comp_subst_closed_of_fvs_sub h_c2_fvs h_lam_closed
            subst h_sigma_let
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
      | opApp h_expr =>
        have h_e_closed := bp_opCall_fvs h_closed
        cases h_expr with
        | var => simp [BP.Expr.fvs_var] at h_e_closed
        | var_subst h_rho' h_store h_val _ =>
          rw [h_rho'] at h_rho; cases h_rho
          exact ⟨_, .op_call, .op h_store h_val .kont_end⟩
    | .eval_match h_atomic h_d_eq h_find h_xs_eq h_eval_body =>
      subst h_d_eq; subst h_xs_eq
      cases h_equiv with
      | ifE h_expr h_c1 h_c2 =>
        have h_val := eval_atomic_value_equiv h_expr h_atomic (bp_if_fvs_scrutinee h_closed)
        cases h_val with
        | con_true =>
          simp [] at h_find; subst h_find
          obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_body h_c1 (bp_if_fvs_c1 h_closed)
          exact ⟨r, .if_true h_bp, h_res⟩
        | con_false =>
          simp [] at h_find; subst h_find
          obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_body h_c2 (bp_if_fvs_c2 h_closed)
          exact ⟨r, .if_false h_bp, h_res⟩
        | con_unit => simp [findBranch, List.findSome?] at h_find
        | con_zero => simp [findBranch, List.findSome?] at h_find
      | matchNat h_expr h_c1 h_c2 =>
        have h_val := eval_atomic_value_equiv h_expr h_atomic (bp_matchNat_fvs_scrutinee h_closed)
        cases h_val with
        | con_zero =>
          simp [] at h_find; subst h_find
          obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_body h_c1 (bp_matchNat_fvs_c1 h_closed)
          exact ⟨r, .match_zero h_bp, h_res⟩
        | con_true => simp [findBranch, List.findSome?] at h_find
        | con_false => simp [findBranch, List.findSome?] at h_find
        | con_unit => simp [findBranch, List.findSome?] at h_find
    | @EvalCExpN.eval_match_succ _ _ _ _ _ _ _ _ d_inner _ _ _ _ _ h_atomic h_find h_store_inner h_fresh h_sigma h_rho_new h_eval_body =>
      cases h_equiv with
      | ifE h_expr h_c1 h_c2 =>
        simp [findBranch, List.findSome?] at h_find
      | matchNat h_expr h_c1 h_c2 =>
        rename_i _ _ _ _ _ x_bp
        have h_scrutinee_closed := bp_matchNat_fvs_scrutinee h_closed
        have h_c2_fvs := bp_matchNat_fvs_c2 h_closed
        have h_val := eval_atomic_value_equiv h_expr h_atomic h_scrutinee_closed
        cases h_val with
        | succ h_store_e' h_inner_val =>
          simp [] at h_find
          obtain ⟨rfl, rfl⟩ := h_find
          subst h_sigma; subst h_rho_new
          have h_e'_closed := by simp [BP.Expr.fvs_succ] at h_scrutinee_closed; exact h_scrutinee_closed
          rw [h_store_e'] at h_store_inner; cases h_store_inner
          have h_subst := comp_equiv_subst_binding x_bp h_c2 h_inner_val h_e'_closed
              h_fresh (barendregt_fresh_env _ x_bp)
          have h_subst_closed := bp_comp_subst_closed_of_fvs_sub h_c2_fvs h_e'_closed
          obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_body h_subst h_subst_closed
          exact ⟨r, .match_succ h_bp, h_res⟩
    | .eval_funApp_clos h_fun h_xs_len h_args h_fresh_addrs h_distinct h_as_len h_sigma h_rho h_body =>
      rename_i f_ae xs_anf e_body_anf ρ_lam _ aes ds as_v σ_new ρ_new _
      cases h_equiv with
      | funApp h_e1 h_e2 =>
        rename_i e1_bp e2_bp ae2
        have h_e1_closed := bp_app_fvs_e1 h_closed
        have h_fun_val := eval_atomic_value_equiv h_e1 h_fun h_e1_closed
        have h_e2_closed := bp_app_fvs_e2 h_closed
        -- Extract first elements from Forall₂
        have h_arg_eval : evalAtomic ae2 ρ σ = some ds[0]! := by
          cases h_args with
          | cons h _ => simpa [List.getElem!_cons_zero] using h
        have h_a_fresh : σ as_v[0]! = none := by
          cases h_fresh_addrs with
          | nil => exact absurd h_args.length_eq (by simp)
          | cons h _ => simpa [List.getElem!_cons_zero] using h
        match h_fun_val with
        | @ValueEquiv.lambda _ _ c_body _ x_lam h_body_equiv =>
          have h_arg_val := eval_atomic_value_equiv h_e2 h_arg_eval h_e2_closed
          have h_subst := comp_equiv_subst_binding x_lam h_body_equiv h_arg_val h_e2_closed
              h_a_fresh (barendregt_fresh_env _ x_lam)
          have h_body_fvs : ∀ v, v ∈ c_body.fvs → v = x_lam := by
            intro v hv
            have h_filt := BP.Expr.fvs_lam ▸ h_e1_closed
            have := filter_eq_nil_mem h_filt v hv
            simp at this; exact this
          have h_subst_closed := bp_comp_subst_closed_of_fvs_sub h_body_fvs h_e2_closed
          have h_as1 := h_as_len; simp at h_as1
          have h_xs1 : [x_lam].length = 1 := by simp
          have h_ds_len : ds.length = [ae2].length := h_args.length_eq.symm
          rw [zip_foldl_extend_store_singleton _ _ _ h_as1 (by omega)] at h_sigma
          rw [zip_foldl_extend_env_singleton _ _ _ h_as1 h_xs1] at h_rho
          simp only [List.getElem!_cons_zero] at h_rho
          subst h_sigma; subst h_rho
          obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_body h_subst h_subst_closed
          exact ⟨r, .app_lam h_bp, h_res⟩
        | @ValueEquiv.rec_lambda _ ρ_clo f a_f c1 e_body_anf x_lam h_c1_equiv h_store_f =>
          have h_arg_val := eval_atomic_value_equiv h_e2 h_arg_eval h_e2_closed
          have h_as1 := h_as_len; simp at h_as1
          have h_ds_len : ds.length = [ae2].length := h_args.length_eq.symm
          rw [zip_foldl_extend_store_singleton _ _ _ h_as1 (by omega)] at h_sigma
          have h_xs1 : [x_lam].length = 1 := by simp
          rw [zip_foldl_extend_env_singleton _ _ _ h_as1 h_xs1] at h_rho
          simp only [List.getElem!_cons_zero] at h_rho
          subst h_sigma; subst h_rho
          let d_arg := ds[0]!
          let a_v := as_v[0]!
          have h_subst_x := comp_equiv_subst_binding x_lam h_c1_equiv
              h_arg_val h_e2_closed h_a_fresh (barendregt_fresh_env _ x_lam)
          have h_f_ne_x : f ≠ x_lam := barendregt_var_ne f x_lam
          have h_ne_addr : a_f ≠ a_v := by
            intro h_eq
            have : σ a_f = none := by rw [show a_f = a_v from h_eq]; exact h_a_fresh
            rw [this] at h_store_f; simp at h_store_f
          have h_f_bound : ((ρ_clo.extend f a_f).extend x_lam a_v) f = some a_f := by
            simp [Env.extend, h_f_ne_x]
          have h_f_store_ext : (σ.extend a_v d_arg) a_f =
              some (Denotable.closure ⟨[x_lam], e_body_anf, ρ_clo.extend f a_f, List.nodup_singleton _⟩) := by
            unfold Store.extend; split
            · rename_i h_eq; exact absurd h_eq h_ne_addr
            · exact h_store_f
          have h_rec_val_ext := @value_equiv_extend_store _ _ _ a_v d_arg
            (ValueEquiv.rec_lambda h_c1_equiv h_store_f) h_a_fresh
          have h_rec_closed : (BP.Expr.lam x_lam (BP.Comp.letRec f x_lam c1 c1)).fvs = [] :=
            h_e1_closed
          have h_redundant := comp_equiv_redundant_subst f h_subst_x h_f_bound h_f_store_ext
            h_rec_val_ext h_rec_closed
          have h_xf : x_lam ≠ f := Ne.symm h_f_ne_x
          have h_inner_closed : ((c1.subst x_lam e2_bp).subst f
                (BP.Expr.lam x_lam (BP.Comp.letRec f x_lam c1 c1))).fvs = [] := by
            have h_body_closed : ((BP.Comp.letRec f x_lam c1 c1).subst x_lam e2_bp).fvs = [] := by
              apply bp_comp_subst_closed_of_fvs_sub _ h_e2_closed
              intro v hv
              have h_filt := h_e1_closed; rw [BP.Expr.fvs_lam] at h_filt
              have := filter_eq_nil_mem h_filt v hv; simp at this; exact this
            rw [BP.Comp.subst_letRec_self_y h_xf] at h_body_closed
            rw [BP.Comp.fvs_letRec] at h_body_closed
            have ⟨_, h2⟩ := List.append_eq_nil_iff.mp h_body_closed
            exact bp_comp_subst_closed_of_fvs_sub
              (fun v hv => by
                have := filter_eq_nil_mem h2 v hv; simp at this; exact this)
              h_rec_closed
          obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_body h_redundant h_inner_closed
          have h_eq := BP.Comp.subst_letRec_self_y h_xf c1 c1 e2_bp
          exact ⟨r, .app_lam (h_eq ▸ .let_rec h_bp), h_res⟩
    | .eval_funApp_kont h_fun h_arg h_apply h_handle =>
      cases h_equiv with
      | funApp h_e1 h_e2 =>
        have h_e1_closed := bp_app_fvs_e1 h_closed
        have h_e2_closed := bp_app_fvs_e2 h_closed
        have h_fun_val := eval_atomic_value_equiv h_e1 h_fun h_e1_closed
        have h_arg_val := eval_atomic_value_equiv h_e2 h_arg h_e2_closed
        match h_fun_val with
        | @ValueEquiv.kont _ _ h_bp_handler _ x_c c_op _ h_hdl_equiv h_kont_equiv h_fresh_hdl =>
          have h_body_fvs : ∀ v, v ∈ (BP.Comp.withHandle h_bp_handler c_op).fvs → v = x_c := by
            intro v hv
            have h_filt := h_e1_closed; rw [BP.Expr.fvs_lam] at h_filt
            have := filter_eq_nil_mem h_filt v hv; simp at this; exact this
          have h_body_closed := bp_comp_subst_closed_of_fvs_sub h_body_fvs h_e2_closed
          simp only [BP.Comp.subst_withHandle] at h_body_closed
          rw [BP.BPHandler.subst_not_mem_fvs h_fresh_hdl] at h_body_closed
          have h_inner_closed := bp_withHandle_fvs_c h_body_closed
          obtain ⟨r_inner, h_bp_inner, h_res_inner⟩ :=
            (soundness_allN _).2.2 _ _ _ _ _ _ _ _ h_apply h_kont_equiv h_arg_val h_e2_closed h_inner_closed
          match h_handle with
          | @HandleValueN.handle_return x_ret e_ret _ _ _ _ _ _ _ _ _ h_ret h_fresh_ret h_sigma_ret h_eval_ret =>
            cases h_res_inner with
            | value h_val_inner =>
              have h_hdl_mono := handler_equiv_store_mono h_hdl_equiv (eval_apply_store_mono (apply_kontN_to h_apply))
              obtain ⟨h_ret_equiv, _⟩ := h_hdl_mono
              have h_e'_closed := bp_eval_value_closed h_bp_inner h_inner_closed
              have h_ret_fvs := bp_withHandle_ret_fvs h_body_closed
              have h_ret_eq := h_ret
              simp only [Prod.mk.injEq] at h_ret_eq
              obtain ⟨rfl, rfl⟩ := h_ret_eq
              subst h_sigma_ret
              have h_subst := comp_equiv_subst_binding x_ret h_ret_equiv h_val_inner h_e'_closed
                  h_fresh_ret (barendregt_fresh_env _ x_ret)
              have h_subst_closed := bp_comp_subst_closed_of_fvs_sub h_ret_fvs h_e'_closed
              obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_ret h_subst h_subst_closed
              refine ⟨r, ?_, h_res⟩
              apply BP.Eval.app_lam
              simp only [BP.Comp.subst_withHandle]
              rw [BP.BPHandler.subst_not_mem_fvs h_fresh_hdl]
              exact .handle_val h_bp_inner rfl h_bp
          | @HandleValueN.handle_op x_op _ _ _ _ _ _ _ _ _ _ _ _ _ _ h_findOp h_fresh_v h_fresh_vk h_ne_addrs h_store_arg h_sigma_op h_eval_op =>
            match h_res_inner with
            | @ResultEquiv.op _ d_arg _ _ _ _ _ _ h_store h_val_op h_kont_op =>
              rw [h_store] at h_store_arg
              obtain rfl := Option.some.inj h_store_arg
              have h_hdl_mono := handler_equiv_store_mono h_hdl_equiv (eval_apply_store_mono (apply_kontN_to h_apply))
              obtain ⟨c_bp_clause, h_bp_findOp, h_clause_equiv⟩ :=
                handler_findOp_equiv_rev h_hdl_mono h_findOp
              have h_kont_closed := bp_kont_lam_closed h_bp_inner h_body_closed
              have h_eop_closed := (bp_eval_op_closed h_bp_inner h_inner_closed).1
              have h_subst1 := comp_equiv_subst_binding x_op h_clause_equiv
                  h_val_op h_eop_closed h_fresh_v (barendregt_fresh_env _ x_op)
              have h_val_kont : ValueEquiv _ _ (Denotable.kontClosure _ _ _) :=
                .kont
                  (handler_equiv_extend_store (d_new := d_arg) h_hdl_mono h_fresh_v)
                  (kont_equiv_extend_store h_kont_op h_fresh_v)
                  (not_mem_withHandle_hdl_fvs h_body_closed)
              have h_subst1_fvs := bp_comp_subst_fvs_sub
                (bp_findOp_fvs h_body_closed h_bp_findOp) h_eop_closed
              have h_fresh_vk_ext := Store.fresh_extend_of_fresh (d := d_arg) h_fresh_vk (Ne.symm h_ne_addrs)
              have h_subst2 := comp_equiv_subst_binding "resume" h_subst1
                  h_val_kont h_kont_closed h_fresh_vk_ext (barendregt_fresh_env _ "resume")
              have h_subst2_closed := bp_comp_subst_closed_of_fvs_sub h_subst1_fvs h_kont_closed
              subst h_sigma_op
              obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_op h_subst2 h_subst2_closed
              refine ⟨r, ?_, h_res⟩
              apply BP.Eval.app_lam
              simp only [BP.Comp.subst_withHandle]
              rw [BP.BPHandler.subst_not_mem_fvs h_fresh_hdl]
              exact .handle_op h_bp_inner h_bp_findOp h_bp
          | @HandleValueN.handle_capture_op _ _ _ _ _ _ _ h_not_has h_v' =>
            cases h_res_inner with
            | op h_store h_val_op h_kont_op =>
              have h_hdl_mono := handler_equiv_store_mono h_hdl_equiv (eval_apply_store_mono (apply_kontN_to h_apply))
              have h_bp_not_has := (handler_hasOp_equiv h_hdl_mono ▸ h_not_has : _ = false)
              subst h_v'
              refine ⟨_, ?_, .op h_store h_val_op (.kont_handle h_kont_op h_hdl_mono (not_mem_withHandle_hdl_fvs h_body_closed))⟩
              apply BP.Eval.app_lam
              simp only [BP.Comp.subst_withHandle]
              rw [BP.BPHandler.subst_not_mem_fvs h_fresh_hdl]
              exact .handle_forward h_bp_inner h_bp_not_has
    | .eval_fun _ _ _ _ =>
      cases h_equiv
    | .eval_handler h_eval_body h_handle =>
      cases h_equiv with
      | handler h_hdl h_c =>
        obtain ⟨r_inner, h_bp_inner, h_res_inner⟩ :=
          (soundness_allN _).1 _ _ _ _ _ _ h_eval_body h_c (bp_withHandle_fvs_c h_closed)
        match h_handle with
        | @HandleValueN.handle_return x_ret e_ret _ _ _ _ _ _ _ _ _ h_ret h_fresh_ret h_sigma_ret h_eval_ret =>
          cases h_res_inner with
          | value h_val =>
            have h_hdl_mono := handler_equiv_store_mono h_hdl (eval_store_mono (eval_expN_to h_eval_body))
            obtain ⟨h_ret_equiv, _⟩ := h_hdl_mono
            have h_e'_closed := bp_eval_value_closed h_bp_inner (bp_withHandle_fvs_c h_closed)
            have h_ret_fvs := bp_withHandle_ret_fvs h_closed
            have h_ret_eq := h_ret
            simp only [Prod.mk.injEq] at h_ret_eq
            obtain ⟨rfl, rfl⟩ := h_ret_eq
            subst h_sigma_ret
            have h_subst := comp_equiv_subst_binding x_ret h_ret_equiv h_val h_e'_closed
                h_fresh_ret (barendregt_fresh_env _ x_ret)
            have h_subst_closed := bp_comp_subst_closed_of_fvs_sub h_ret_fvs h_e'_closed
            obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_ret h_subst h_subst_closed
            exact ⟨r, .handle_val h_bp_inner rfl h_bp, h_res⟩
        | @HandleValueN.handle_op x_op _ _ _ _ _ _ _ _ _ _ _ _ _ _ h_findOp h_fresh_v h_fresh_vk h_ne_addrs h_store_arg h_sigma_op h_eval_op =>
          match h_res_inner with
          | @ResultEquiv.op _ d_arg _ _ _ _ _ _ h_store h_val_op h_kont =>
            rw [h_store] at h_store_arg
            obtain rfl := Option.some.inj h_store_arg
            have h_hdl_mono := handler_equiv_store_mono h_hdl (eval_store_mono (eval_expN_to h_eval_body))
            obtain ⟨c_bp_clause, h_bp_findOp, h_clause_equiv⟩ :=
              handler_findOp_equiv_rev h_hdl_mono h_findOp
            have h_kont_closed := bp_kont_lam_closed h_bp_inner h_closed
            have h_eop_closed := (bp_eval_op_closed h_bp_inner (bp_withHandle_fvs_c h_closed)).1
            have h_subst1 := comp_equiv_subst_binding x_op h_clause_equiv
                h_val_op h_eop_closed h_fresh_v (barendregt_fresh_env _ x_op)
            have h_val_kont : ValueEquiv _ _ (Denotable.kontClosure _ ρ _) :=
              .kont
                (handler_equiv_extend_store (d_new := d_arg) h_hdl_mono h_fresh_v)
                (kont_equiv_extend_store h_kont h_fresh_v)
                (not_mem_withHandle_hdl_fvs h_closed)
            have h_subst1_fvs := bp_comp_subst_fvs_sub
              (bp_findOp_fvs h_closed h_bp_findOp) h_eop_closed
            have h_fresh_vk_ext := Store.fresh_extend_of_fresh (d := d_arg) h_fresh_vk (Ne.symm h_ne_addrs)
            have h_subst2 := comp_equiv_subst_binding "resume" h_subst1
                h_val_kont h_kont_closed h_fresh_vk_ext (barendregt_fresh_env _ "resume")
            have h_subst2_closed := bp_comp_subst_closed_of_fvs_sub h_subst1_fvs h_kont_closed
            subst h_sigma_op
            obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_op h_subst2 h_subst2_closed
            exact ⟨r, .handle_op h_bp_inner h_bp_findOp h_bp, h_res⟩
        | @HandleValueN.handle_capture_op _ _ _ _ _ _ _ h_not_has h_v' =>
          cases h_res_inner with
          | op h_store h_val_op h_kont =>
            have h_hdl_mono := handler_equiv_store_mono h_hdl (eval_store_mono (eval_expN_to h_eval_body))
            have h_bp_not_has := (handler_hasOp_equiv h_hdl_mono ▸ h_not_has : _ = false)
            subst h_v'
            exact ⟨_, .handle_forward h_bp_inner h_bp_not_has,
              .op h_store h_val_op (.kont_handle h_kont h_hdl_mono (not_mem_withHandle_hdl_fvs h_closed))⟩
  -- ═══════════════════════════════════════════
  -- P_apply: soundness for ApplyKontN n
  -- ═══════════════════════════════════════════
  · intro κ d σ v σ' x_c c_op e_bp h_apply h_kont h_val h_closed h_c_closed
    match h_apply with
    | .apply_continue =>
      cases h_kont with
      | kont_end =>
        simp [BP.Comp.subst_val, BP.Expr.subst_var_self]
        exact ⟨_, .val, .value h_val⟩
    | .apply_restore h_apply_inner h_continue =>
      cases h_kont with
      | kont_let h_kont_inner h_c2_equiv h_fresh_c2 =>
        rw [BP.Comp.subst_letIn] at h_c_closed ⊢
        rw [BP.Comp.subst_not_mem_fvs h_fresh_c2] at h_c_closed ⊢
        simp only [ite_self] at h_c_closed ⊢
        have h_inner_closed := bp_letIn_fvs_c1 h_c_closed
        have h_c2_fvs := bp_letIn_fvs_c2 h_c_closed
        obtain ⟨r_inner, h_bp_inner, h_res_inner⟩ :=
          (soundness_allN _).2.2 _ _ _ _ _ _ _ _ h_apply_inner h_kont_inner h_val h_closed h_inner_closed
        match h_continue with
        | .continue_let h_fresh_av h_sigma_let h_eval_body =>
          rename_i _ _ _ _ _ _ _ _ _ _ y_let _ _ _ _
          cases h_res_inner with
          | value h_val_inner =>
            have h_mono := eval_apply_store_mono (apply_kontN_to h_apply_inner)
            have h_c2_mono := comp_equiv_store_mono h_c2_equiv h_mono
            have h_e'_closed := bp_eval_value_closed h_bp_inner h_inner_closed
            subst h_sigma_let
            have h_subst := comp_equiv_subst_binding y_let h_c2_mono h_val_inner h_e'_closed
                h_fresh_av (barendregt_fresh_env _ y_let)
            have h_subst_closed := bp_comp_subst_closed_of_fvs_sub h_c2_fvs h_e'_closed
            obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_body h_subst h_subst_closed
            exact ⟨r, .let_val h_bp_inner h_bp, h_res⟩
        | .continue_op =>
          cases h_res_inner with
          | op h_store h_val_op h_kont_op =>
            have h_mono := eval_apply_store_mono (apply_kontN_to h_apply_inner)
            exact ⟨_, .let_op h_bp_inner,
              .op h_store h_val_op (.kont_let h_kont_op (comp_equiv_store_mono h_c2_equiv h_mono) (fun hm => absurd (h_c2_fvs _ hm) (barendregt_var_ne _ _)))⟩
    | .apply_restore_handle h_apply_inner h_handle_inner =>
      cases h_kont with
      | kont_handle h_kont_inner h_hdl_equiv h_fresh_hdl =>
        rw [BP.Comp.subst_withHandle] at h_c_closed ⊢
        rw [BP.BPHandler.subst_not_mem_fvs h_fresh_hdl] at h_c_closed ⊢
        have h_inner_closed := bp_withHandle_fvs_c h_c_closed
        obtain ⟨r_inner, h_bp_inner, h_res_inner⟩ :=
          (soundness_allN _).2.2 _ _ _ _ _ _ _ _ h_apply_inner h_kont_inner h_val h_closed h_inner_closed
        match h_handle_inner with
        | @HandleValueN.handle_return x_ret e_ret _ _ _ _ _ _ _ _ _ h_ret h_fresh_ret h_sigma_ret h_eval_ret =>
          cases h_res_inner with
          | value h_val_inner =>
            have h_hdl_mono := handler_equiv_store_mono h_hdl_equiv (eval_apply_store_mono (apply_kontN_to h_apply_inner))
            obtain ⟨h_ret_equiv, _⟩ := h_hdl_mono
            have h_e'_closed := bp_eval_value_closed h_bp_inner h_inner_closed
            have h_ret_fvs := bp_withHandle_ret_fvs h_c_closed
            have h_ret_eq := h_ret
            simp only [Prod.mk.injEq] at h_ret_eq
            obtain ⟨rfl, rfl⟩ := h_ret_eq
            subst h_sigma_ret
            have h_subst := comp_equiv_subst_binding x_ret h_ret_equiv h_val_inner h_e'_closed
                h_fresh_ret (barendregt_fresh_env _ x_ret)
            have h_subst_closed := bp_comp_subst_closed_of_fvs_sub h_ret_fvs h_e'_closed
            obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_ret h_subst h_subst_closed
            exact ⟨r, .handle_val h_bp_inner rfl h_bp, h_res⟩
        | @HandleValueN.handle_op x_op _ _ _ _ _ _ _ _ _ _ _ _ _ _ h_findOp h_fresh_v h_fresh_vk h_ne_addrs h_store_arg h_sigma_op h_eval_op =>
          match h_res_inner with
          | @ResultEquiv.op _ d_arg _ _ _ _ _ _ h_store h_val_op h_kont_op =>
            rw [h_store] at h_store_arg
            obtain rfl := Option.some.inj h_store_arg
            have h_hdl_mono := handler_equiv_store_mono h_hdl_equiv (eval_apply_store_mono (apply_kontN_to h_apply_inner))
            obtain ⟨c_bp_clause, h_bp_findOp, h_clause_equiv⟩ :=
              handler_findOp_equiv_rev h_hdl_mono h_findOp
            have h_kont_closed := bp_kont_lam_closed h_bp_inner h_c_closed
            have h_eop_closed := (bp_eval_op_closed h_bp_inner h_inner_closed).1
            have h_subst1 := comp_equiv_subst_binding x_op h_clause_equiv
                h_val_op h_eop_closed h_fresh_v (barendregt_fresh_env _ x_op)
            have h_val_kont : ValueEquiv _ _ (Denotable.kontClosure _ _ _) :=
              .kont
                (handler_equiv_extend_store (d_new := d_arg) h_hdl_mono h_fresh_v)
                (kont_equiv_extend_store h_kont_op h_fresh_v)
                (not_mem_withHandle_hdl_fvs h_c_closed)
            have h_subst1_fvs := bp_comp_subst_fvs_sub
              (bp_findOp_fvs h_c_closed h_bp_findOp) h_eop_closed
            have h_fresh_vk_ext := Store.fresh_extend_of_fresh (d := d_arg) h_fresh_vk (Ne.symm h_ne_addrs)
            have h_subst2 := comp_equiv_subst_binding "resume" h_subst1
                h_val_kont h_kont_closed h_fresh_vk_ext (barendregt_fresh_env _ "resume")
            have h_subst2_closed := bp_comp_subst_closed_of_fvs_sub h_subst1_fvs h_kont_closed
            subst h_sigma_op
            obtain ⟨r, h_bp, h_res⟩ := (soundness_allN _).1 _ _ _ _ _ _ h_eval_op h_subst2 h_subst2_closed
            exact ⟨r, .handle_op h_bp_inner h_bp_findOp h_bp, h_res⟩
        | @HandleValueN.handle_capture_op _ _ _ _ _ _ _ h_not_has h_v' =>
          cases h_res_inner with
          | op h_store h_val_op h_kont_op =>
            have h_hdl_mono := handler_equiv_store_mono h_hdl_equiv (eval_apply_store_mono (apply_kontN_to h_apply_inner))
            have h_bp_not_has := (handler_hasOp_equiv h_hdl_mono ▸ h_not_has : _ = false)
            subst h_v'
            exact ⟨_, .handle_forward h_bp_inner h_bp_not_has,
              .op h_store h_val_op (.kont_handle h_kont_op h_hdl_mono (not_mem_withHandle_hdl_fvs h_c_closed))⟩
  termination_by n

/-- Soundness for EvalExp -/
theorem soundness_exp
    (h_eval : EvalExp e ρ σ v σ')
    (h_equiv : CompEquiv σ ρ c e)
    (h_closed : c.fvs = []) :
    ∃ r, BP.Eval c r ∧ ResultEquiv σ' r v := by
  obtain ⟨n, hn⟩ := eval_exp_to_N h_eval
  exact (soundness_allN n).1 _ _ _ _ _ _ hn h_equiv h_closed

/-- Soundness for ApplyKont -/
theorem soundness_applyKont
    (h_apply : ApplyKont κ d σ v σ')
    (h_kont : KontEquiv σ x_c c_op κ)
    (h_val : ValueEquiv σ e_bp d)
    (h_closed : e_bp.fvs = [])
    (h_c_closed : (c_op.subst x_c e_bp).fvs = []) :
    ∃ r, BP.Eval (c_op.subst x_c e_bp) r ∧ ResultEquiv σ' r v := by
  obtain ⟨n, hn⟩ := apply_kont_to_N h_apply
  exact (soundness_allN n).2.2 _ _ _ _ _ _ _ _ hn h_kont h_val h_closed h_c_closed

/-- Main soundness theorem -/
theorem soundness :
    EvalExp e ρ σ v σ' →
    CompEquiv σ ρ c e →
    c.fvs = [] →
    ∃ r, BP.Eval c r ∧ ResultEquiv σ' r v :=
  soundness_exp

end DMCFA
