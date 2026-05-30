/-
  Timestamped Concrete Big-Step Semantics for λ^h

  Five mutual inductive judgments mirroring Semantics.lean but threading timestamps.
  Each timestamp-extending rule uses the label from the enclosing letE.
-/

import DMCFA.Syntax
import DMCFA.TimestampedComponents
import DMCFA.Semantics

namespace DMCFA

-- Needed for [i]! notation in inductive premises
instance : Inhabited TVAddr := ⟨⟨"", Time.empty⟩⟩

/-- Meta-function A: evaluate atomic expressions in timestamped setting -/
def evalTAtomic (ae : AExp) (ρ : TEnv) (σ : TStore) : Option TDenotable :=
  match ae with
  | .var x => do
      let a ← Finmap.lookup x ρ
      let s ← σ (.val a)
      match s with
      | .denotable d => some d
      | _ => none
  | .lam xs body => if h : xs.Nodup then some (.closure ⟨xs, body, ρ, h⟩) else none
  | .con c => some (.conLabel c)
  | .succE x => do
      let a ← Finmap.lookup x ρ
      let s ← σ (.val a)
      match s with
      | .denotable _ => some (.succVal a)
      | _ => none

/-- Helper to build store from parallel lists of addresses and denotables -/
def TStore.extendMany_val (σ : TStore) (addrs : List TVAddr) (ds : List TDenotable) : TStore :=
  (addrs.zip ds).foldl (fun s (a, d) => s.extend (.val a) (.denotable d)) σ

/-!
## Timestamped Big-Step Evaluation Relations
-/

mutual

inductive TFreshEvalExp : Exp → TEnv → TStore → Time → TValue → TStore → Prop where
  | eval_let :
      TFreshEvalCExp ce ρ σ t l v σ₁ →
      TFreshContinueFrame l (.letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩) t v σ₁ v' σ' →
      TFreshEvalExp (Exp.letE y ce e l) ρ σ t v' σ'
  | eval_tail :
      TFreshEvalCExp ce ρ σ t l_tail v σ' →
      TFreshEvalExp (Exp.tail ce l_tail) ρ σ t v σ'

inductive TFreshEvalCExp : CExp → TEnv → TStore → Time → Label → TValue → TStore → Prop where
  | eval_atomic :
      evalTAtomic ae ρ σ = some d →
      TFreshEvalCExp (CExp.atomic ae) ρ σ t l (TValue.den d) σ

  | eval_funApp_clos :
      evalTAtomic f ρ σ = some (TDenotable.closure ⟨xs, e_body, ρ_lam, _h_nd⟩) →
      xs.length = aes.length →
      List.Forall₂ (fun ae d => evalTAtomic ae ρ σ = some d) aes ds →
      t_new = ⟨l :: t.tk, t.tmk⟩ →
      -- Each arg gets address (xs[i], t_new); addresses are fresh
      (∀ i, (h : i < xs.length) → σ (.val ⟨xs[i], t_new⟩) = none) →
      σ_new = (xs.zip ds).foldl
        (fun s (x, d) => s.extend (.val ⟨x, t_new⟩) (.denotable d)) σ →
      ρ_new = xs.foldl (fun r x => r.extend x ⟨x, t_new⟩) ρ_lam →
      TFreshEvalExp e_body ρ_new σ_new t_new v' σ' →
      TFreshEvalCExp (CExp.funApp f aes) ρ σ t l v' σ'

  | eval_opApp :
      Finmap.lookup x ρ = some a_v →
      TFreshEvalCExp (CExp.opApp op x) ρ σ t l
        (TValue.suspended op [a_v] none) σ

  | eval_funApp_kont :
      evalTAtomic f ρ σ = some (TDenotable.kontClosure h ρ_h a_κ) →
      evalTAtomic ae ρ σ = some d →
      tmk_apply = ((l, l :: t.tk) :: t.tmk) →
      TFreshApplyKont a_κ d σ tmk_apply v' σ₁ →
      t_handle = ⟨l :: t.tk, t.tmk⟩ →
      TFreshHandleValue l h ρ_h v' σ₁ t_handle v'' σ' →
      TFreshEvalCExp (CExp.funApp f [ae]) ρ σ t l v'' σ'

  | eval_fun :
      a_v = TVAddr.mk f t →
      σ (.val a_v) = none →
      (h_nd : xs.Nodup) →
      v_f = TDenotable.closure ⟨xs, e1, (ρ.extend f a_v), h_nd⟩ →
      σ' = σ.extend (.val a_v) (.denotable v_f) →
      TFreshEvalCExp (CExp.funDef f xs e1) ρ σ t l (TValue.den v_f) σ'

  | eval_match :
      evalTAtomic ae ρ σ = some d →
      d = TDenotable.conLabel c →
      findBranch bs c = some (xs, e) →
      xs = [] →
      TFreshEvalExp e ρ σ t v' σ' →
      TFreshEvalCExp (CExp.matchE ae bs) ρ σ t l v' σ'

  | eval_match_succ :
      evalTAtomic ae ρ σ = some (TDenotable.succVal a_inner) →
      findBranch bs ConLabel.succ = some (xs, e) →
      σ (.val a_inner) = some (.denotable d_inner) →
      xs = [x_bind] →
      a_fresh = TVAddr.mk x_bind t →
      σ (.val a_fresh) = none →
      σ_new = σ.extend (.val a_fresh) (.denotable d_inner) →
      ρ_new = (xs.zip [a_fresh]).foldl (fun r (x, a) => r.extend x a) ρ →
      TFreshEvalExp e ρ_new σ_new t v' σ' →
      TFreshEvalCExp (CExp.matchE ae bs) ρ σ t l v' σ'

  | eval_handler :
      t_body = ⟨[], (l_h, t.tk) :: t.tmk⟩ →
      TFreshEvalExp e_body ρ σ t_body v σ₁ →
      TFreshHandleValue l_h h ρ v σ₁ t v' σ' →
      TFreshEvalCExp (CExp.handler h e_body l_h) ρ σ t l v' σ'

inductive TFreshContinueFrame : Label → TFrameContent → Time → TValue → TStore →
                           TValue → TStore → Prop where
  | continue_let :
      a_new = TVAddr.mk y t →
      σ (.val a_new) = none →
      TFreshEvalExp e (ρ.extend y a_new) (σ.extend (.val a_new) (.denotable d)) t v' σ' →
      TFreshContinueFrame l (.letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩) t (TValue.den d) σ v' σ'

  | continue_op :
      ψ = ⟨.letFrame clo, t, l⟩ →
      a_κ = TKAddr.mk ψ op →
      σ (.kont a_κ) = none →
      σ' = σ.extend (.kont a_κ) (.kontLink a_κ_prev) →
      TFreshContinueFrame l (.letFrame clo) t
        (TValue.suspended op as_v a_κ_prev) σ
        (TValue.suspended op as_v (some a_κ)) σ'

inductive TFreshHandleValue : Label → Handler → TEnv → TValue → TStore → Time →
                         TValue → TStore → Prop where
  | handle_return :
      (x_ret, e_ret) = h.returnClause →
      a_new = TVAddr.mk x_ret t →
      σ (.val a_new) = none →
      TFreshEvalExp e_ret (ρ.extend x_ret a_new)
        (σ.extend (.val a_new) (.denotable d)) t v' σ' →
      TFreshHandleValue l h ρ (TValue.den d) σ t v' σ'

  | handle_op :
      Handler.findOp h op = some (x, e_op) →
      a_x = TVAddr.mk x t →
      a_resume = TVAddr.mk "resume" t →
      σ (.val a_x) = none → σ (.val a_resume) = none →
      a_x ≠ a_resume →
      as_v = [a_arg] →
      σ (.val a_arg) = some (.denotable d_arg) →
      d_kont = TDenotable.kontClosure h ρ a_κ →
      σ_op = TStore.extend (σ.extend (.val a_x) (.denotable d_arg))
              (.val a_resume) (.denotable d_kont) →
      TFreshEvalExp e_op ((ρ.extend x a_x).extend "resume" a_resume) σ_op t v σ' →
      TFreshHandleValue l h ρ (TValue.suspended op as_v a_κ) σ t v σ'

  | handle_capture_op :
      Handler.hasOp h op = false →
      ψ = ⟨.handlerFrame h ρ, t, l⟩ →
      a_κ_new = TKAddr.mk ψ op →
      σ (.kont a_κ_new) = none →
      σ' = σ.extend (.kont a_κ_new) (.kontLink a_κ_prev) →
      TFreshHandleValue l h ρ (TValue.suspended op as_v a_κ_prev) σ t
        (TValue.suspended op as_v (some a_κ_new)) σ'

inductive TFreshApplyKont : Option TKAddr → TDenotable → TStore → MKTime → TValue → TStore → Prop where
  | apply_continue :
      TFreshApplyKont none d σ tmk (TValue.den d) σ

  | apply_restore :
      σ (.kont a_κ) = some (.kontLink a_next) →
      a_κ.frame.content = .letFrame clo →
      TFreshApplyKont a_next d σ tmk v' σ₁ →
      t_restored = ⟨a_κ.frame.time.tk, tmk⟩ →
      TFreshContinueFrame a_κ.frame.label (.letFrame clo) t_restored v' σ₁ v'' σ' →
      TFreshApplyKont (some a_κ) d σ tmk v'' σ'

  | apply_restore_handle :
      σ (.kont a_κ) = some (.kontLink a_next) →
      a_κ.frame.content = .handlerFrame h ρ →
      tmk' = (a_κ.frame.label, a_κ.frame.time.tk) :: tmk →
      TFreshApplyKont a_next d σ tmk' v' σ₁ →
      t_restored = ⟨a_κ.frame.time.tk, tmk⟩ →
      TFreshHandleValue a_κ.frame.label h ρ v' σ₁ t_restored v'' σ' →
      TFreshApplyKont (some a_κ) d σ tmk v'' σ'

end

/-! ## Height-indexed evaluation relations for structural recursion -/

mutual

inductive TFreshEvalExpN : Nat → Exp → TEnv → TStore → Time → TValue → TStore → Prop where
  | eval_let :
      TFreshEvalCExpN n1 ce ρ σ t l v σ₁ →
      TFreshContinueFrameN n2 l (.letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩) t v σ₁ v' σ' →
      TFreshEvalExpN (n1 + n2 + 1) (Exp.letE y ce e l) ρ σ t v' σ'
  | eval_tail :
      TFreshEvalCExpN n ce ρ σ t l_tail v σ' →
      TFreshEvalExpN (n + 1) (Exp.tail ce l_tail) ρ σ t v σ'

inductive TFreshEvalCExpN : Nat → CExp → TEnv → TStore → Time → Label → TValue → TStore → Prop where
  | eval_atomic :
      evalTAtomic ae ρ σ = some d →
      TFreshEvalCExpN 0 (CExp.atomic ae) ρ σ t l (TValue.den d) σ
  | eval_funApp_clos :
      evalTAtomic f ρ σ = some (TDenotable.closure ⟨xs, e_body, ρ_lam, _h_nd⟩) →
      xs.length = aes.length →
      List.Forall₂ (fun ae d => evalTAtomic ae ρ σ = some d) aes ds →
      t_new = ⟨l :: t.tk, t.tmk⟩ →
      (∀ i, (h : i < xs.length) → σ (.val ⟨xs[i], t_new⟩) = none) →
      σ_new = (xs.zip ds).foldl
        (fun s (x, d) => s.extend (.val ⟨x, t_new⟩) (.denotable d)) σ →
      ρ_new = xs.foldl (fun r x => r.extend x ⟨x, t_new⟩) ρ_lam →
      TFreshEvalExpN n e_body ρ_new σ_new t_new v' σ' →
      TFreshEvalCExpN (n + 1) (CExp.funApp f aes) ρ σ t l v' σ'
  | eval_opApp :
      Finmap.lookup x ρ = some a_v →
      TFreshEvalCExpN 0 (CExp.opApp op x) ρ σ t l
        (TValue.suspended op [a_v] none) σ
  | eval_funApp_kont :
      evalTAtomic f ρ σ = some (TDenotable.kontClosure h ρ_h a_κ) →
      evalTAtomic ae ρ σ = some d →
      tmk_apply = ((l, l :: t.tk) :: t.tmk) →
      TFreshApplyKontN n1 a_κ d σ tmk_apply v' σ₁ →
      t_handle = ⟨l :: t.tk, t.tmk⟩ →
      TFreshHandleValueN n2 l h ρ_h v' σ₁ t_handle v'' σ' →
      TFreshEvalCExpN (n1 + n2 + 1) (CExp.funApp f [ae]) ρ σ t l v'' σ'
  | eval_fun :
      a_v = TVAddr.mk f t →
      σ (.val a_v) = none →
      (h_nd : xs.Nodup) →
      v_f = TDenotable.closure ⟨xs, e1, (ρ.extend f a_v), h_nd⟩ →
      σ' = σ.extend (.val a_v) (.denotable v_f) →
      TFreshEvalCExpN 0 (CExp.funDef f xs e1) ρ σ t l (TValue.den v_f) σ'
  | eval_match :
      evalTAtomic ae ρ σ = some d →
      d = TDenotable.conLabel c →
      findBranch bs c = some (xs, e) →
      xs = [] →
      TFreshEvalExpN n e ρ σ t v' σ' →
      TFreshEvalCExpN (n + 1) (CExp.matchE ae bs) ρ σ t l v' σ'
  | eval_match_succ :
      evalTAtomic ae ρ σ = some (TDenotable.succVal a_inner) →
      findBranch bs ConLabel.succ = some (xs, e) →
      σ (.val a_inner) = some (.denotable d_inner) →
      xs = [x_bind] →
      a_fresh = TVAddr.mk x_bind t →
      σ (.val a_fresh) = none →
      σ_new = σ.extend (.val a_fresh) (.denotable d_inner) →
      ρ_new = (xs.zip [a_fresh]).foldl (fun r (x, a) => r.extend x a) ρ →
      TFreshEvalExpN n e ρ_new σ_new t v' σ' →
      TFreshEvalCExpN (n + 1) (CExp.matchE ae bs) ρ σ t l v' σ'
  | eval_handler :
      t_body = ⟨[], (l_h, t.tk) :: t.tmk⟩ →
      TFreshEvalExpN n1 e_body ρ σ t_body v σ₁ →
      TFreshHandleValueN n2 l_h h ρ v σ₁ t v' σ' →
      TFreshEvalCExpN (n1 + n2 + 1) (CExp.handler h e_body l_h) ρ σ t l v' σ'

inductive TFreshContinueFrameN : Nat → Label → TFrameContent → Time → TValue → TStore →
                            TValue → TStore → Prop where
  | continue_let :
      a_new = TVAddr.mk y t →
      σ (.val a_new) = none →
      TFreshEvalExpN n e (ρ.extend y a_new) (σ.extend (.val a_new) (.denotable d)) t v' σ' →
      TFreshContinueFrameN (n + 1) l (.letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩) t (TValue.den d) σ v' σ'
  | continue_op :
      ψ = ⟨.letFrame clo, t, l⟩ →
      a_κ = TKAddr.mk ψ op →
      σ (.kont a_κ) = none →
      σ' = σ.extend (.kont a_κ) (.kontLink a_κ_prev) →
      TFreshContinueFrameN 0 l (.letFrame clo) t
        (TValue.suspended op as_v a_κ_prev) σ
        (TValue.suspended op as_v (some a_κ)) σ'

inductive TFreshHandleValueN : Nat → Label → Handler → TEnv → TValue → TStore → Time →
                          TValue → TStore → Prop where
  | handle_return :
      (x_ret, e_ret) = h.returnClause →
      a_new = TVAddr.mk x_ret t →
      σ (.val a_new) = none →
      TFreshEvalExpN n e_ret (ρ.extend x_ret a_new)
        (σ.extend (.val a_new) (.denotable d)) t v' σ' →
      TFreshHandleValueN (n + 1) l h ρ (TValue.den d) σ t v' σ'
  | handle_op :
      Handler.findOp h op = some (x, e_op) →
      a_x = TVAddr.mk x t →
      a_resume = TVAddr.mk "resume" t →
      σ (.val a_x) = none → σ (.val a_resume) = none →
      a_x ≠ a_resume →
      as_v = [a_arg] →
      σ (.val a_arg) = some (.denotable d_arg) →
      d_kont = TDenotable.kontClosure h ρ a_κ →
      σ_op = TStore.extend (σ.extend (.val a_x) (.denotable d_arg))
              (.val a_resume) (.denotable d_kont) →
      TFreshEvalExpN n e_op ((ρ.extend x a_x).extend "resume" a_resume) σ_op t v σ' →
      TFreshHandleValueN (n + 1) l h ρ (TValue.suspended op as_v a_κ) σ t v σ'
  | handle_capture_op :
      Handler.hasOp h op = false →
      ψ = ⟨.handlerFrame h ρ, t, l⟩ →
      a_κ_new = TKAddr.mk ψ op →
      σ (.kont a_κ_new) = none →
      σ' = σ.extend (.kont a_κ_new) (.kontLink a_κ_prev) →
      TFreshHandleValueN 0 l h ρ (TValue.suspended op as_v a_κ_prev) σ t
        (TValue.suspended op as_v (some a_κ_new)) σ'

inductive TFreshApplyKontN : Nat → Option TKAddr → TDenotable → TStore → MKTime → TValue → TStore → Prop where
  | apply_continue :
      TFreshApplyKontN 0 none d σ tmk (TValue.den d) σ
  | apply_restore :
      σ (.kont a_κ) = some (.kontLink a_next) →
      a_κ.frame.content = .letFrame clo →
      TFreshApplyKontN n1 a_next d σ tmk v' σ₁ →
      t_restored = ⟨a_κ.frame.time.tk, tmk⟩ →
      TFreshContinueFrameN n2 a_κ.frame.label (.letFrame clo) t_restored v' σ₁ v'' σ' →
      TFreshApplyKontN (n1 + n2 + 1) (some a_κ) d σ tmk v'' σ'
  | apply_restore_handle :
      σ (.kont a_κ) = some (.kontLink a_next) →
      a_κ.frame.content = .handlerFrame h ρ →
      tmk' = (a_κ.frame.label, a_κ.frame.time.tk) :: tmk →
      TFreshApplyKontN n1 a_next d σ tmk' v' σ₁ →
      t_restored = ⟨a_κ.frame.time.tk, tmk⟩ →
      TFreshHandleValueN n2 a_κ.frame.label h ρ v' σ₁ t_restored v'' σ' →
      TFreshApplyKontN (n1 + n2 + 1) (some a_κ) d σ tmk v'' σ'

end

/-! ## Conversion theorems between indexed and non-indexed -/

mutual

theorem teval_exp_to_N (h : TFreshEvalExp e ρ σ t v σ') : ∃ n, TFreshEvalExpN n e ρ σ t v σ' :=
  match h with
  | .eval_let h1 h2 =>
    let ⟨n1, hn1⟩ := teval_cexp_to_N h1
    let ⟨n2, hn2⟩ := tcontinue_frame_to_N h2
    ⟨n1 + n2 + 1, .eval_let hn1 hn2⟩
  | .eval_tail h1 =>
    let ⟨n1, hn1⟩ := teval_cexp_to_N h1
    ⟨n1 + 1, .eval_tail hn1⟩

theorem teval_cexp_to_N (h : TFreshEvalCExp ce ρ σ t l v σ') : ∃ n, TFreshEvalCExpN n ce ρ σ t l v σ' :=
  match h with
  | .eval_atomic h1 => ⟨0, .eval_atomic h1⟩
  | .eval_funApp_clos h1 h2 h3 h4 h5 h6 h7 h8 =>
    let ⟨n, hn⟩ := teval_exp_to_N h8
    ⟨n + 1, .eval_funApp_clos h1 h2 h3 h4 h5 h6 h7 hn⟩
  | .eval_opApp h1 => ⟨0, .eval_opApp h1⟩
  | .eval_funApp_kont h1 h2 h3 h4 h5 h6 =>
    let ⟨n1, hn1⟩ := tapply_kont_to_N h4
    let ⟨n2, hn2⟩ := thandle_value_to_N h6
    ⟨n1 + n2 + 1, .eval_funApp_kont h1 h2 h3 hn1 h5 hn2⟩
  | .eval_fun h1 h2 h3 h4 h5 => ⟨0, .eval_fun h1 h2 h3 h4 h5⟩
  | .eval_match h1 h2 h3 h4 h5 =>
    let ⟨n, hn⟩ := teval_exp_to_N h5
    ⟨n + 1, .eval_match h1 h2 h3 h4 hn⟩
  | .eval_match_succ h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    let ⟨n, hn⟩ := teval_exp_to_N h9
    ⟨n + 1, .eval_match_succ h1 h2 h3 h4 h5 h6 h7 h8 hn⟩
  | .eval_handler h1 h2 h3 =>
    let ⟨n1, hn1⟩ := teval_exp_to_N h2
    let ⟨n2, hn2⟩ := thandle_value_to_N h3
    ⟨n1 + n2 + 1, .eval_handler h1 hn1 hn2⟩

theorem tcontinue_frame_to_N (h : TFreshContinueFrame l fc t_f v σ v' σ') :
    ∃ n, TFreshContinueFrameN n l fc t_f v σ v' σ' :=
  match h with
  | .continue_let h1 h2 h3 =>
    let ⟨n, hn⟩ := teval_exp_to_N h3
    ⟨n + 1, .continue_let h1 h2 hn⟩
  | .continue_op h1 h2 h3 h4 => ⟨0, .continue_op h1 h2 h3 h4⟩

theorem thandle_value_to_N (h : TFreshHandleValue l hh ρ v σ t v' σ') :
    ∃ n, TFreshHandleValueN n l hh ρ v σ t v' σ' :=
  match h with
  | .handle_return h1 h2 h3 h4 =>
    let ⟨n, hn⟩ := teval_exp_to_N h4
    ⟨n + 1, .handle_return h1 h2 h3 hn⟩
  | .handle_op h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
    let ⟨n, hn⟩ := teval_exp_to_N h11
    ⟨n + 1, .handle_op h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 hn⟩
  | .handle_capture_op h1 h2 h3 h4 h5 => ⟨0, .handle_capture_op h1 h2 h3 h4 h5⟩

theorem tapply_kont_to_N (h : TFreshApplyKont oa_κ d σ tmk v σ') :
    ∃ n, TFreshApplyKontN n oa_κ d σ tmk v σ' :=
  match h with
  | .apply_continue => ⟨0, .apply_continue⟩
  | .apply_restore h1 h2 h3 h4 h5 =>
    let ⟨n1, hn1⟩ := tapply_kont_to_N h3
    let ⟨n2, hn2⟩ := tcontinue_frame_to_N h5
    ⟨n1 + n2 + 1, .apply_restore h1 h2 hn1 h4 hn2⟩
  | .apply_restore_handle h1 h2 h3 h4 h5 h6 =>
    let ⟨n1, hn1⟩ := tapply_kont_to_N h4
    let ⟨n2, hn2⟩ := thandle_value_to_N h6
    ⟨n1 + n2 + 1, .apply_restore_handle h1 h2 h3 hn1 h5 hn2⟩

end

mutual

theorem teval_expN_to (h : TFreshEvalExpN n e ρ σ t v σ') : TFreshEvalExp e ρ σ t v σ' :=
  match h with
  | .eval_let h1 h2 => .eval_let (teval_cexpN_to h1) (tcontinue_frameN_to h2)
  | .eval_tail h1 => .eval_tail (teval_cexpN_to h1)

theorem teval_cexpN_to (h : TFreshEvalCExpN n ce ρ σ t l v σ') : TFreshEvalCExp ce ρ σ t l v σ' :=
  match h with
  | .eval_atomic h1 => .eval_atomic h1
  | .eval_funApp_clos h1 h2 h3 h4 h5 h6 h7 h8 =>
    .eval_funApp_clos h1 h2 h3 h4 h5 h6 h7 (teval_expN_to h8)
  | .eval_opApp h1 => .eval_opApp h1
  | .eval_funApp_kont h1 h2 h3 h4 h5 h6 =>
    .eval_funApp_kont h1 h2 h3 (tapply_kontN_to h4) h5 (thandle_valueN_to h6)
  | .eval_fun h1 h2 h3 h4 h5 => .eval_fun h1 h2 h3 h4 h5
  | .eval_match h1 h2 h3 h4 h5 => .eval_match h1 h2 h3 h4 (teval_expN_to h5)
  | .eval_match_succ h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    .eval_match_succ h1 h2 h3 h4 h5 h6 h7 h8 (teval_expN_to h9)
  | .eval_handler h1 h2 h3 => .eval_handler h1 (teval_expN_to h2) (thandle_valueN_to h3)

theorem tcontinue_frameN_to (h : TFreshContinueFrameN n l fc t_f v σ v' σ') :
    TFreshContinueFrame l fc t_f v σ v' σ' :=
  match h with
  | .continue_let h1 h2 h3 => .continue_let h1 h2 (teval_expN_to h3)
  | .continue_op h1 h2 h3 h4 => .continue_op h1 h2 h3 h4

theorem thandle_valueN_to (h : TFreshHandleValueN n l hh ρ v σ t v' σ') :
    TFreshHandleValue l hh ρ v σ t v' σ' :=
  match h with
  | .handle_return h1 h2 h3 h4 => .handle_return h1 h2 h3 (teval_expN_to h4)
  | .handle_op h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 =>
    .handle_op h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 (teval_expN_to h11)
  | .handle_capture_op h1 h2 h3 h4 h5 => .handle_capture_op h1 h2 h3 h4 h5

theorem tapply_kontN_to (h : TFreshApplyKontN n oa_κ d σ tmk v σ') :
    TFreshApplyKont oa_κ d σ tmk v σ' :=
  match h with
  | .apply_continue => .apply_continue
  | .apply_restore h1 h2 h3 h4 h5 =>
    .apply_restore h1 h2 (tapply_kontN_to h3) h4 (tcontinue_frameN_to h5)
  | .apply_restore_handle h1 h2 h3 h4 h5 h6 =>
    .apply_restore_handle h1 h2 h3 (tapply_kontN_to h4) h5 (thandle_valueN_to h6)

end

end DMCFA
