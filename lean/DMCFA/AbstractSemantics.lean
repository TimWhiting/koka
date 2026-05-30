/-
  Abstract Big-Step Semantics

  Finitized version of the timestamped semantics. The abstract rules mirror
  the timestamped rules exactly, with three changes:
  1. Timestamps are truncated at each extension point (⌊l:t_k⌋_m, ⌊(l,t_k):t_mk⌋_h)
  2. Store lookups are non-deterministic (d ∈ σ(a) instead of σ(a) = some d)
  3. Store updates use weak update (σ ⊔ [a ↦ {d}] instead of σ[a ↦ d])

  Parameterized by (m h : Nat) for context sensitivity.

  Five mutual judgment forms, mirroring the timestamped semantics:
  - AbsEvalExp:       (e, ρ, σ, t) ⇓ea (v, σ')
  - AbsEvalCExp:      (ce, ρ, σ, t, l) ⇓eca (v, σ')
  - AbsContinueFrame: (fc, v, σ, t) ⇒ca (v', σ')
  - AbsHandleValue:   (h, ρ, l, v, σ, t) ⇓ha (v', σ')
  - AbsApplyKont:     (a_κ, d, σ, t_mk) ⇓apa (v, σ')
-/

import DMCFA.AbstractComponents
import DMCFA.Syntax
import DMCFA.Semantics

namespace DMCFA

/-! ## Abstract Evaluation Relations -/

mutual

/-- Abstract expression evaluation: (e, ρ, σ, t) ⇓ea (v, σ') -/
inductive AbsEvalExp (m h : Nat) : Exp → TEnv → AStore → Time → TValue → AStore → Prop where
  | eval_let :
      AbsEvalCExp m h ce ρ σ t l_enc v σ' →
      AbsContinueFrame m h (.letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩) v σ' t v' σ'' →
      AbsEvalExp m h (Exp.letE y ce e l_enc) ρ σ t v' σ''
  | eval_tail :
      AbsEvalCExp m h ce ρ σ t l v σ' →
      AbsEvalExp m h (Exp.tail ce l) ρ σ t v σ'

/-- Abstract complex expression evaluation: (ce, ρ, σ, t, l) ⇓eca (v, σ') -/
inductive AbsEvalCExp (m h : Nat) : CExp → TEnv → AStore → Time → Label → TValue → AStore → Prop where
  | eval_atomic :
      d ∈ evalAbsAtomic ae ρ σ →
      AbsEvalCExp m h (CExp.atomic ae) ρ σ t l (TValue.den d) σ

  | eval_funApp_clos :
      TDenotable.closure ⟨xs, e_body, ρ_lam, h_nd⟩ ∈ evalAbsAtomic f ρ σ →
      xs.length = aes.length →
      -- Each arg evaluates to some denotable (non-deterministic)
      List.Forall₂ (fun ae d => d ∈ evalAbsAtomic ae ρ σ) aes ds →
      -- Truncated timestamp
      t_new = ⟨extKTime m l t.tk, t.tmk⟩ →
      -- Weak update: join all arg bindings into store
      σ_new = (xs.zip ds).foldl
        (fun s (x, d) => s.update (.val ⟨x, t_new⟩) (.denotable d)) σ →
      ρ_new = xs.foldl (fun r x => r.extend x ⟨x, t_new⟩) ρ_lam →
      AbsEvalExp m h e_body ρ_new σ_new t_new v' σ' →
      AbsEvalCExp m h (CExp.funApp f aes) ρ σ t l v' σ'

  | eval_opApp :
      Finmap.lookup x ρ = some a_v →
      AbsEvalCExp m h (CExp.opApp op x) ρ σ t l
        (TValue.suspended op [a_v] none) σ

  | eval_funApp_kont :
      TDenotable.kontClosure hdl ρ_h a_κ ∈ evalAbsAtomic f ρ σ →
      d ∈ evalAbsAtomic ae ρ σ →
      -- Apply with truncated tmk (concrete: (l, l::t.tk)::t.tmk)
      AbsApplyKont m h a_κ d σ (extMKTimeApp m h l t.tk t.tmk) v' σ' →
      -- Handle with truncated tk
      AbsHandleValue m h l_enc hdl ρ_h v' σ' ⟨extKTime m l t.tk, t.tmk⟩ v'' σ'' →
      AbsEvalCExp m h (CExp.funApp f [ae]) ρ σ t l v'' σ''

  | eval_fun :
      a_v = TVAddr.mk f t →
      (h_nd : xs.Nodup) →
      v_f = TDenotable.closure ⟨xs, e1, ρ.extend f a_v, h_nd⟩ →
      σ' = σ.update (.val a_v) (.denotable v_f) →
      AbsEvalCExp m h (CExp.funDef f xs e1) ρ σ t l (TValue.den v_f) σ'

  | eval_match :
      d ∈ evalAbsAtomic ae ρ σ →
      d = TDenotable.conLabel c →
      findBranch bs c = some (xs, e) →
      xs = [] →
      AbsEvalExp m h e ρ σ t v' σ' →
      AbsEvalCExp m h (CExp.matchE ae bs) ρ σ t l v' σ'

  | eval_match_succ :
      d ∈ evalAbsAtomic ae ρ σ →
      d = TDenotable.succVal a_inner →
      findBranch bs .succ = some ([x_succ], e) →
      .denotable d_inner ∈ σ (.val a_inner) →
      a_v = ⟨x_succ, t⟩ →
      σ_m = σ.update (.val a_v) (.denotable d_inner) →
      ρ_m = ρ.extend x_succ a_v →
      AbsEvalExp m h e ρ_m σ_m t v' σ' →
      AbsEvalCExp m h (CExp.matchE ae bs) ρ σ t l v' σ'

  | eval_handler :
      AbsEvalExp m h e_body ρ σ_body ⟨[], extMKTime m h l_h t.tk t.tmk⟩ v σ_v →
      AbsHandleValue m h l_h hdl ρ v σ_v t v' σ' →
      AbsEvalCExp m h (CExp.handler hdl e_body l_h) ρ σ_body t l v' σ'

/-- Abstract frame continuation: (fc, v, σ, t) ⇒ca (v', σ') -/
inductive AbsContinueFrame (m h : Nat) : TFrameContent → TValue → AStore → Time → TValue → AStore → Prop where
  | continue_let :
      σ_let = σ.update (.val ⟨y, t⟩) (.denotable d) →
      AbsEvalExp m h e (ρ.extend y ⟨y, t⟩) σ_let t v' σ' →
      AbsContinueFrame m h (.letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩) (TValue.den d) σ t v' σ'
  | continue_op :
      ψ = ⟨.letFrame clo, t, l⟩ →
      a_κ_new = TKAddr.mk ψ op →
      σ' = σ.update (.kont a_κ_new) (.kontLink a_κ_prev) →
      AbsContinueFrame m h (.letFrame clo) (TValue.suspended op as_v a_κ_prev)
        σ t (TValue.suspended op as_v (some a_κ_new)) σ'

/-- Abstract handle value: (h, ρ, l, v, σ, t) ⇓ha (v', σ') -/
inductive AbsHandleValue (m h : Nat) : Label → Handler → TEnv → TValue → AStore → Time → TValue → AStore → Prop where
  | handle_return :
      (x_ret, e_ret) = hdl.returnClause →
      a_v = ⟨x_ret, t⟩ →
      σ_ret = σ.update (.val a_v) (.denotable d) →
      AbsEvalExp m h e_ret (ρ.extend x_ret a_v) σ_ret t v' σ' →
      AbsHandleValue m h l_enc hdl ρ (TValue.den d) σ t v' σ'

  | handle_op :
      Handler.findOp hdl op = some (x_op, e_op) →
      -- Weak-update arg copy + kont closure
      σ_op = ((σ.update (.val ⟨x_op, t⟩) (.denotable d_arg)).update
              (.val ⟨"resume", t⟩) (.denotable (.kontClosure hdl ρ a_κ))) →
      AbsEvalExp m h e_op ((ρ.extend x_op ⟨x_op, t⟩).extend "resume" ⟨"resume", t⟩) σ_op t v σ' →
      AbsHandleValue m h l_enc hdl ρ
        (TValue.suspended op [a_arg] a_κ) σ t v σ'

  | handle_capture_op :
      Handler.hasOp hdl op = false →
      ψ = ⟨.handlerFrame hdl ρ, t, l_enc⟩ →
      a_κ_new = TKAddr.mk ψ op →
      σ' = σ.update (.kont a_κ_new) (.kontLink a_κ_prev) →
      AbsHandleValue m h l_enc hdl ρ
        (TValue.suspended op as_v a_κ_prev)
        σ t
        (TValue.suspended op as_v (some a_κ_new)) σ'

/-- Abstract apply kont: (a_κ, d, σ, t_mk) ⇓apa (v, σ') -/
inductive AbsApplyKont (m h : Nat) : Option TKAddr → TDenotable → AStore → MKTime → TValue → AStore → Prop where
  | apply_continue :
      AbsApplyKont m h none d σ tmk (TValue.den d) σ

  | apply_restore :
      .kontLink next ∈ σ (.kont a) →
      AbsApplyKont m h next d σ tmk v' σ' →
      AbsContinueFrame m h a.frame.content v' σ' ⟨a.frame.time.tk, tmk⟩ v'' σ'' →
      AbsApplyKont m h (some a) d σ tmk v'' σ''

  | apply_restore_handle :
      .kontLink next ∈ σ (.kont a) →
      a.frame.content = .handlerFrame hdl ρ_h →
      AbsApplyKont m h next d σ (extMKTime m h a.frame.label a.frame.time.tk tmk) v' σ' →
      AbsHandleValue m h a.frame.label hdl ρ_h v' σ' ⟨a.frame.time.tk, tmk⟩ v'' σ'' →
      AbsApplyKont m h (some a) d σ tmk v'' σ''

end

end DMCFA
