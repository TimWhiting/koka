/-
  Naive Timestamped Semantics — no freshness premises

  Mirrors TSemantics exactly but removes ALL freshness premises:
  - No `σ (.val a) = none` premises
  - No `σ (.kont a) = none` premises
  - No `a_x ≠ a_resume` premises

  This allows address collisions (extend just overwrites).
  The simulation theorem (Freshness2) proves that for well-labeled programs,
  collisions never actually happen.
-/

import DMCFA.FreshSemantics

namespace DMCFA

/-!
## Naive Big-Step Evaluation Relations (no freshness checks)
-/

mutual

inductive TEvalExp : Exp → TEnv → TStore → Time → TValue → TStore → Prop where
  | eval_let :
      TEvalCExp ce ρ σ t l v σ₁ →
      TContinueFrame l (.letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩) t v σ₁ v' σ' →
      TEvalExp (Exp.letE y ce e l) ρ σ t v' σ'
  | eval_tail :
      TEvalCExp ce ρ σ t l_tail v σ' →
      TEvalExp (Exp.tail ce l_tail) ρ σ t v σ'

inductive TEvalCExp : CExp → TEnv → TStore → Time → Label → TValue → TStore → Prop where
  | eval_atomic :
      evalTAtomic ae ρ σ = some d →
      TEvalCExp (CExp.atomic ae) ρ σ t l (TValue.den d) σ

  | eval_funApp_clos :
      evalTAtomic f ρ σ = some (TDenotable.closure ⟨xs, e_body, ρ_lam, _h_nd⟩) →
      xs.length = aes.length →
      List.Forall₂ (fun ae d => evalTAtomic ae ρ σ = some d) aes ds →
      t_new = ⟨l :: t.tk, t.tmk⟩ →
      -- NO freshness premises for parameter addresses
      σ_new = (xs.zip ds).foldl
        (fun s (x, d) => s.extend (.val ⟨x, t_new⟩) (.denotable d)) σ →
      ρ_new = xs.foldl (fun r x => r.extend x ⟨x, t_new⟩) ρ_lam →
      TEvalExp e_body ρ_new σ_new t_new v' σ' →
      TEvalCExp (CExp.funApp f aes) ρ σ t l v' σ'

  | eval_opApp :
      Finmap.lookup x ρ = some a_v →
      -- NO store write, no freshness premise
      TEvalCExp (CExp.opApp op x) ρ σ t l
        (TValue.suspended op [a_v] none) σ

  | eval_funApp_kont :
      evalTAtomic f ρ σ = some (TDenotable.kontClosure h ρ_h a_κ) →
      evalTAtomic ae ρ σ = some d →
      tmk_apply = ((l, l :: t.tk) :: t.tmk) →
      TApplyKont a_κ d σ tmk_apply v' σ₁ →
      t_handle = ⟨l :: t.tk, t.tmk⟩ →
      THandleValue l h ρ_h v' σ₁ t_handle v'' σ' →
      TEvalCExp (CExp.funApp f [ae]) ρ σ t l v'' σ'

  | eval_fun :
      a_v = TVAddr.mk f t →
      -- NO freshness premise
      (h_nd : xs.Nodup) →
      v_f = TDenotable.closure ⟨xs, e1, (ρ.extend f a_v), h_nd⟩ →
      σ' = σ.extend (.val a_v) (.denotable v_f) →
      TEvalCExp (CExp.funDef f xs e1) ρ σ t l (TValue.den v_f) σ'

  | eval_match :
      evalTAtomic ae ρ σ = some d →
      d = TDenotable.conLabel c →
      findBranch bs c = some (xs, e) →
      xs = [] →
      TEvalExp e ρ σ t v' σ' →
      TEvalCExp (CExp.matchE ae bs) ρ σ t l v' σ'

  | eval_match_succ :
      evalTAtomic ae ρ σ = some (TDenotable.succVal a_inner) →
      findBranch bs ConLabel.succ = some (xs, e) →
      σ (.val a_inner) = some (.denotable d_inner) →
      xs = [x_bind] →
      a_fresh = TVAddr.mk x_bind t →
      -- NO freshness premise for a_fresh
      σ_new = σ.extend (.val a_fresh) (.denotable d_inner) →
      ρ_new = (xs.zip [a_fresh]).foldl (fun r (x, a) => r.extend x a) ρ →
      TEvalExp e ρ_new σ_new t v' σ' →
      TEvalCExp (CExp.matchE ae bs) ρ σ t l v' σ'

  | eval_handler :
      t_body = ⟨[], (l_h, t.tk) :: t.tmk⟩ →
      TEvalExp e_body ρ σ t_body v σ₁ →
      THandleValue l_h h ρ v σ₁ t v' σ' →
      TEvalCExp (CExp.handler h e_body l_h) ρ σ t l v' σ'

inductive TContinueFrame : Label → TFrameContent → Time → TValue → TStore →
                           TValue → TStore → Prop where
  | continue_let :
      a_new = TVAddr.mk y t →
      -- NO freshness premise
      TEvalExp e (ρ.extend y a_new) (σ.extend (.val a_new) (.denotable d)) t v' σ' →
      TContinueFrame l (.letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩) t (TValue.den d) σ v' σ'

  | continue_op :
      ψ = ⟨.letFrame clo, t, l⟩ →
      a_κ = TKAddr.mk ψ op →
      -- NO freshness premise
      σ' = σ.extend (.kont a_κ) (.kontLink a_κ_prev) →
      TContinueFrame l (.letFrame clo) t
        (TValue.suspended op as_v a_κ_prev) σ
        (TValue.suspended op as_v (some a_κ)) σ'

inductive THandleValue : Label → Handler → TEnv → TValue → TStore → Time →
                         TValue → TStore → Prop where
  | handle_return :
      (x_ret, e_ret) = h.returnClause →
      a_new = TVAddr.mk x_ret t →
      -- NO freshness premise
      TEvalExp e_ret (ρ.extend x_ret a_new)
        (σ.extend (.val a_new) (.denotable d)) t v' σ' →
      THandleValue l h ρ (TValue.den d) σ t v' σ'

  | handle_op :
      Handler.findOp h op = some (x, e_op) →
      a_x = TVAddr.mk x t →
      a_resume = TVAddr.mk "resume" t →
      -- NO freshness premises, NO a_x ≠ a_resume premise
      as_v = [a_arg] →
      σ (.val a_arg) = some (.denotable d_arg) →
      d_kont = TDenotable.kontClosure h ρ a_κ →
      σ_op = TStore.extend (σ.extend (.val a_x) (.denotable d_arg))
              (.val a_resume) (.denotable d_kont) →
      TEvalExp e_op ((ρ.extend x a_x).extend "resume" a_resume) σ_op t v σ' →
      THandleValue l h ρ (TValue.suspended op as_v a_κ) σ t v σ'

  | handle_capture_op :
      Handler.hasOp h op = false →
      ψ = ⟨.handlerFrame h ρ, t, l⟩ →
      a_κ_new = TKAddr.mk ψ op →
      -- NO freshness premise
      σ' = σ.extend (.kont a_κ_new) (.kontLink a_κ_prev) →
      THandleValue l h ρ (TValue.suspended op as_v a_κ_prev) σ t
        (TValue.suspended op as_v (some a_κ_new)) σ'

inductive TApplyKont : Option TKAddr → TDenotable → TStore → MKTime → TValue → TStore → Prop where
  | apply_continue :
      TApplyKont none d σ tmk (TValue.den d) σ

  | apply_restore :
      σ (.kont a_κ) = some (.kontLink a_next) →
      a_κ.frame.content = .letFrame clo →
      TApplyKont a_next d σ tmk v' σ₁ →
      t_restored = ⟨a_κ.frame.time.tk, tmk⟩ →
      TContinueFrame a_κ.frame.label (.letFrame clo) t_restored v' σ₁ v'' σ' →
      TApplyKont (some a_κ) d σ tmk v'' σ'

  | apply_restore_handle :
      σ (.kont a_κ) = some (.kontLink a_next) →
      a_κ.frame.content = .handlerFrame h ρ →
      tmk' = (a_κ.frame.label, a_κ.frame.time.tk) :: tmk →
      TApplyKont a_next d σ tmk' v' σ₁ →
      t_restored = ⟨a_κ.frame.time.tk, tmk⟩ →
      THandleValue a_κ.frame.label h ρ v' σ₁ t_restored v'' σ' →
      TApplyKont (some a_κ) d σ tmk v'' σ'

end

/-! ## Height-indexed naive evaluation relations -/

mutual

inductive TEvalExpN : Nat → Exp → TEnv → TStore → Time → TValue → TStore → Prop where
  | eval_let :
      TEvalCExpN n1 ce ρ σ t l v σ₁ →
      TContinueFrameN n2 l (.letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩) t v σ₁ v' σ' →
      TEvalExpN (n1 + n2 + 1) (Exp.letE y ce e l) ρ σ t v' σ'
  | eval_tail :
      TEvalCExpN n ce ρ σ t l_tail v σ' →
      TEvalExpN (n + 1) (Exp.tail ce l_tail) ρ σ t v σ'

inductive TEvalCExpN : Nat → CExp → TEnv → TStore → Time → Label → TValue → TStore → Prop where
  | eval_atomic :
      evalTAtomic ae ρ σ = some d →
      TEvalCExpN 0 (CExp.atomic ae) ρ σ t l (TValue.den d) σ
  | eval_funApp_clos :
      evalTAtomic f ρ σ = some (TDenotable.closure ⟨xs, e_body, ρ_lam, _h_nd⟩) →
      xs.length = aes.length →
      List.Forall₂ (fun ae d => evalTAtomic ae ρ σ = some d) aes ds →
      t_new = ⟨l :: t.tk, t.tmk⟩ →
      σ_new = (xs.zip ds).foldl
        (fun s (x, d) => s.extend (.val ⟨x, t_new⟩) (.denotable d)) σ →
      ρ_new = xs.foldl (fun r x => r.extend x ⟨x, t_new⟩) ρ_lam →
      TEvalExpN n e_body ρ_new σ_new t_new v' σ' →
      TEvalCExpN (n + 1) (CExp.funApp f aes) ρ σ t l v' σ'
  | eval_opApp :
      Finmap.lookup x ρ = some a_v →
      TEvalCExpN 0 (CExp.opApp op x) ρ σ t l
        (TValue.suspended op [a_v] none) σ
  | eval_funApp_kont :
      evalTAtomic f ρ σ = some (TDenotable.kontClosure h ρ_h a_κ) →
      evalTAtomic ae ρ σ = some d →
      tmk_apply = ((l, l :: t.tk) :: t.tmk) →
      TApplyKontN n1 a_κ d σ tmk_apply v' σ₁ →
      t_handle = ⟨l :: t.tk, t.tmk⟩ →
      THandleValueN n2 l h ρ_h v' σ₁ t_handle v'' σ' →
      TEvalCExpN (n1 + n2 + 1) (CExp.funApp f [ae]) ρ σ t l v'' σ'
  | eval_fun :
      a_v = TVAddr.mk f t →
      (h_nd : xs.Nodup) →
      v_f = TDenotable.closure ⟨xs, e1, (ρ.extend f a_v), h_nd⟩ →
      σ' = σ.extend (.val a_v) (.denotable v_f) →
      TEvalCExpN 0 (CExp.funDef f xs e1) ρ σ t l (TValue.den v_f) σ'
  | eval_match :
      evalTAtomic ae ρ σ = some d →
      d = TDenotable.conLabel c →
      findBranch bs c = some (xs, e) →
      xs = [] →
      TEvalExpN n e ρ σ t v' σ' →
      TEvalCExpN (n + 1) (CExp.matchE ae bs) ρ σ t l v' σ'
  | eval_match_succ :
      evalTAtomic ae ρ σ = some (TDenotable.succVal a_inner) →
      findBranch bs ConLabel.succ = some (xs, e) →
      σ (.val a_inner) = some (.denotable d_inner) →
      xs = [x_bind] →
      a_fresh = TVAddr.mk x_bind t →
      σ_new = σ.extend (.val a_fresh) (.denotable d_inner) →
      ρ_new = (xs.zip [a_fresh]).foldl (fun r (x, a) => r.extend x a) ρ →
      TEvalExpN n e ρ_new σ_new t v' σ' →
      TEvalCExpN (n + 1) (CExp.matchE ae bs) ρ σ t l v' σ'
  | eval_handler :
      t_body = ⟨[], (l_h, t.tk) :: t.tmk⟩ →
      TEvalExpN n1 e_body ρ σ t_body v σ₁ →
      THandleValueN n2 l_h h ρ v σ₁ t v' σ' →
      TEvalCExpN (n1 + n2 + 1) (CExp.handler h e_body l_h) ρ σ t l v' σ'

inductive TContinueFrameN : Nat → Label → TFrameContent → Time → TValue → TStore →
                            TValue → TStore → Prop where
  | continue_let :
      a_new = TVAddr.mk y t →
      TEvalExpN n e (ρ.extend y a_new) (σ.extend (.val a_new) (.denotable d)) t v' σ' →
      TContinueFrameN (n + 1) l (.letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩) t (TValue.den d) σ v' σ'
  | continue_op :
      ψ = ⟨.letFrame clo, t, l⟩ →
      a_κ = TKAddr.mk ψ op →
      σ' = σ.extend (.kont a_κ) (.kontLink a_κ_prev) →
      TContinueFrameN 0 l (.letFrame clo) t
        (TValue.suspended op as_v a_κ_prev) σ
        (TValue.suspended op as_v (some a_κ)) σ'

inductive THandleValueN : Nat → Label → Handler → TEnv → TValue → TStore → Time →
                          TValue → TStore → Prop where
  | handle_return :
      (x_ret, e_ret) = h.returnClause →
      a_new = TVAddr.mk x_ret t →
      TEvalExpN n e_ret (ρ.extend x_ret a_new)
        (σ.extend (.val a_new) (.denotable d)) t v' σ' →
      THandleValueN (n + 1) l h ρ (TValue.den d) σ t v' σ'
  | handle_op :
      Handler.findOp h op = some (x, e_op) →
      a_x = TVAddr.mk x t →
      a_resume = TVAddr.mk "resume" t →
      as_v = [a_arg] →
      σ (.val a_arg) = some (.denotable d_arg) →
      d_kont = TDenotable.kontClosure h ρ a_κ →
      σ_op = TStore.extend (σ.extend (.val a_x) (.denotable d_arg))
              (.val a_resume) (.denotable d_kont) →
      TEvalExpN n e_op ((ρ.extend x a_x).extend "resume" a_resume) σ_op t v σ' →
      THandleValueN (n + 1) l h ρ (TValue.suspended op as_v a_κ) σ t v σ'
  | handle_capture_op :
      Handler.hasOp h op = false →
      ψ = ⟨.handlerFrame h ρ, t, l⟩ →
      a_κ_new = TKAddr.mk ψ op →
      σ' = σ.extend (.kont a_κ_new) (.kontLink a_κ_prev) →
      THandleValueN 0 l h ρ (TValue.suspended op as_v a_κ_prev) σ t
        (TValue.suspended op as_v (some a_κ_new)) σ'

inductive TApplyKontN : Nat → Option TKAddr → TDenotable → TStore → MKTime → TValue → TStore → Prop where
  | apply_continue :
      TApplyKontN 0 none d σ tmk (TValue.den d) σ
  | apply_restore :
      σ (.kont a_κ) = some (.kontLink a_next) →
      a_κ.frame.content = .letFrame clo →
      TApplyKontN n1 a_next d σ tmk v' σ₁ →
      t_restored = ⟨a_κ.frame.time.tk, tmk⟩ →
      TContinueFrameN n2 a_κ.frame.label (.letFrame clo) t_restored v' σ₁ v'' σ' →
      TApplyKontN (n1 + n2 + 1) (some a_κ) d σ tmk v'' σ'
  | apply_restore_handle :
      σ (.kont a_κ) = some (.kontLink a_next) →
      a_κ.frame.content = .handlerFrame h ρ →
      tmk' = (a_κ.frame.label, a_κ.frame.time.tk) :: tmk →
      TApplyKontN n1 a_next d σ tmk' v' σ₁ →
      t_restored = ⟨a_κ.frame.time.tk, tmk⟩ →
      THandleValueN n2 a_κ.frame.label h ρ v' σ₁ t_restored v'' σ' →
      TApplyKontN (n1 + n2 + 1) (some a_κ) d σ tmk v'' σ'

end

/-! ## Conversion theorems between indexed and non-indexed -/

mutual

theorem tneval_exp_to_N (h : TEvalExp e ρ σ t v σ') : ∃ n, TEvalExpN n e ρ σ t v σ' :=
  match h with
  | .eval_let h1 h2 =>
    let ⟨n1, hn1⟩ := tneval_cexp_to_N h1
    let ⟨n2, hn2⟩ := tncontinue_frame_to_N h2
    ⟨n1 + n2 + 1, .eval_let hn1 hn2⟩
  | .eval_tail h1 =>
    let ⟨n1, hn1⟩ := tneval_cexp_to_N h1
    ⟨n1 + 1, .eval_tail hn1⟩

theorem tneval_cexp_to_N (h : TEvalCExp ce ρ σ t l v σ') : ∃ n, TEvalCExpN n ce ρ σ t l v σ' :=
  match h with
  | .eval_atomic h1 => ⟨0, .eval_atomic h1⟩
  | .eval_funApp_clos h1 h2 h3 h4 h5 h6 h7 =>
    let ⟨n, hn⟩ := tneval_exp_to_N h7
    ⟨n + 1, .eval_funApp_clos h1 h2 h3 h4 h5 h6 hn⟩
  | .eval_opApp h1 => ⟨0, .eval_opApp h1⟩
  | .eval_funApp_kont h1 h2 h3 h4 h5 h6 =>
    let ⟨n1, hn1⟩ := tnapply_kont_to_N h4
    let ⟨n2, hn2⟩ := tnhandle_value_to_N h6
    ⟨n1 + n2 + 1, .eval_funApp_kont h1 h2 h3 hn1 h5 hn2⟩
  | .eval_fun h1 h2 h3 h4 => ⟨0, .eval_fun h1 h2 h3 h4⟩
  | .eval_match h1 h2 h3 h4 h5 =>
    let ⟨n, hn⟩ := tneval_exp_to_N h5
    ⟨n + 1, .eval_match h1 h2 h3 h4 hn⟩
  | .eval_match_succ h1 h2 h3 h4 h5 h6 h7 h8 =>
    let ⟨n, hn⟩ := tneval_exp_to_N h8
    ⟨n + 1, .eval_match_succ h1 h2 h3 h4 h5 h6 h7 hn⟩
  | .eval_handler h1 h2 h3 =>
    let ⟨n1, hn1⟩ := tneval_exp_to_N h2
    let ⟨n2, hn2⟩ := tnhandle_value_to_N h3
    ⟨n1 + n2 + 1, .eval_handler h1 hn1 hn2⟩

theorem tncontinue_frame_to_N (h : TContinueFrame l fc t_f v σ v' σ') :
    ∃ n, TContinueFrameN n l fc t_f v σ v' σ' :=
  match h with
  | .continue_let h1 h2 =>
    let ⟨n, hn⟩ := tneval_exp_to_N h2
    ⟨n + 1, .continue_let h1 hn⟩
  | .continue_op h1 h2 h3 => ⟨0, .continue_op h1 h2 h3⟩

theorem tnhandle_value_to_N (h : THandleValue l hh ρ v σ t v' σ') :
    ∃ n, THandleValueN n l hh ρ v σ t v' σ' :=
  match h with
  | .handle_return h1 h2 h3 =>
    let ⟨n, hn⟩ := tneval_exp_to_N h3
    ⟨n + 1, .handle_return h1 h2 hn⟩
  | .handle_op h1 h2 h3 h4 h5 h6 h7 h8 =>
    let ⟨n, hn⟩ := tneval_exp_to_N h8
    ⟨n + 1, .handle_op h1 h2 h3 h4 h5 h6 h7 hn⟩
  | .handle_capture_op h1 h2 h3 h4 => ⟨0, .handle_capture_op h1 h2 h3 h4⟩

theorem tnapply_kont_to_N (h : TApplyKont oa_κ d σ tmk v σ') :
    ∃ n, TApplyKontN n oa_κ d σ tmk v σ' :=
  match h with
  | .apply_continue => ⟨0, .apply_continue⟩
  | .apply_restore h1 h2 h3 h4 h5 =>
    let ⟨n1, hn1⟩ := tnapply_kont_to_N h3
    let ⟨n2, hn2⟩ := tncontinue_frame_to_N h5
    ⟨n1 + n2 + 1, .apply_restore h1 h2 hn1 h4 hn2⟩
  | .apply_restore_handle h1 h2 h3 h4 h5 h6 =>
    let ⟨n1, hn1⟩ := tnapply_kont_to_N h4
    let ⟨n2, hn2⟩ := tnhandle_value_to_N h6
    ⟨n1 + n2 + 1, .apply_restore_handle h1 h2 h3 hn1 h5 hn2⟩

end

end DMCFA
