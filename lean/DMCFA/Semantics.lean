/-
  Concrete Big-Step Semantics for λ^h (our semantics)

  Defines the evaluation relations:
  - ⇓e : Expression evaluation
  - ⇓ec : Complex expression evaluation
  - ⇒c : Frame continuation
  - ⇓h : Handler evaluation
  - ⇓a : Apply/restore continuation
-/

import DMCFA.Syntax
import DMCFA.Components

namespace DMCFA

/-- Result of an evaluation: value paired with updated store and fresh state -/
structure EvalResult where
  value : Value
  store : Store
  freshState : FreshState

/-- Meta-function A: evaluate atomic expressions -/
@[simp, grind =] def evalAtomic (ae : AExp) (ρ : Env) (σ : Store) : Option Denotable :=
  match ae with
  | .var x => do
      let a ← ρ x
      σ a
  | .lam xs body => if h : xs.Nodup then some (.closure ⟨xs, body, ρ, h⟩) else none
  | .con c => some (.conLabel c)
  | .succE x => do
      let a ← ρ x
      let _ ← σ a
      some (.succVal a)

/-- Find matching branch for a constructor -/
@[simp, grind =] def findBranch (bs : Branches) (c : ConLabel) : Option (List Var × Exp) :=
  bs.findSome? fun b =>
    match b with
    | .branch c' xs e => if c' = c then some (xs, e) else none

/-- Check if operation is in handler -/
@[simp, grind =] def Handler.hasOp (h : Handler) (op : OpName) : Bool :=
  h.opClauses.any fun (op', _, _) => op' = op

/-- Find operation clause in handler -/
@[simp, grind =] def Handler.findOp (h : Handler) (op : OpName) : Option (Var × Exp) :=
  h.opClauses.findSome? fun (op', x, e) =>
    if op' = op then some (x, e) else none

/-!
## Big-Step Evaluation Relations

We define these as inductive predicates (relations), which directly
correspond to the inference rules in the paper.
-/

/-- Configuration for expression evaluation -/
structure ExpConfig where
  exp : Exp
  env : Env
  store : Store

/-- Configuration for complex expression evaluation -/
structure CExpConfig where
  cexp : CExp
  env : Env
  store : Store

/-- Result configuration -/
structure ResultConfig where
  value : Value
  store : Store

mutual

/--
Expression evaluation: (e, ρ, σ) ⇓e (v, σ')

This is the main entry point for evaluation.
-/
inductive EvalExp : Exp → Env → Store → Value → Store → Prop where
  /-- [eval-let]: let y = ce; e evaluates ce then continues with frame -/
  | eval_let :
      EvalCExp ce ρ σ v σ' →
      ContinueFrame (Frame.letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩) v σ' v' σ'' →
      EvalExp (Exp.letE y ce e l) ρ σ v' σ''
  /-- [eval-tail]: complex expression in tail position -/
  | eval_tail :
      EvalCExp ce ρ σ v σ' →
      EvalExp (Exp.tail ce l) ρ σ v σ'

/--
Complex expression evaluation: (ce, ρ, σ) ⇓ec (v, σ')
-/
inductive EvalCExp : CExp → Env → Store → Value → Store → Prop where
  /-- [eval-atomic]: atomic expression evaluation -/
  | eval_atomic :
      evalAtomic ae ρ σ = some d →
      EvalCExp (CExp.atomic ae) ρ σ (Value.den d) σ

  /-- [eval-funApp-clos]: closure (lambda) application - args are AExp, allocates fresh addresses -/
  | eval_funApp_clos :
      evalAtomic f ρ σ = some (Denotable.closure ⟨xs, e_body, ρ_lam, _h_nd⟩) →
      xs.length = aes.length →
      List.Forall₂ (fun ae d => evalAtomic ae ρ σ = some d) aes ds →
      List.Forall₂ (fun a (_ : Denotable) => σ a = none) as_v ds →  -- addresses fresh in σ
      as_v.Nodup →  -- distinct
      as_v.length = xs.length →
      σ_new = (List.zip as_v ds).foldl (fun s (a, d) => s.extend a d) σ →
      ρ_new = (List.zip xs as_v).foldl (fun r (x, a) => r.extend x a) ρ_lam →
      EvalExp e_body ρ_new σ_new v' σ' →
      EvalCExp (CExp.funApp f aes) ρ σ v' σ'

  /-- [eval-opApp]: operation application - arg is Var, store unchanged -/
  | eval_opApp :
      ρ x = some a_v →
      EvalCExp (CExp.opApp op x) ρ σ (Value.suspended op [a_v] []) σ

  /-- [eval-funApp-kont]: continuation application -/
  | eval_funApp_kont :
      evalAtomic f ρ σ = some (Denotable.kontClosure h ρ_h κ) →
      evalAtomic ae ρ σ = some d →
      ApplyKont κ d σ v' σ' →
      HandleValue h ρ_h v' σ' v'' σ'' →
      EvalCExp (CExp.funApp f [ae]) ρ σ v'' σ''

  /-- [eval-fun]: recursive function definition -/
  | eval_fun :
      σ a_v = none →
      (h_nd : xs.Nodup) →
      v_f = Denotable.closure ⟨xs, e1, ρ.extend f a_v, h_nd⟩ →
      σ' = σ.extend a_v v_f →
      EvalCExp (CExp.funDef f xs e1) ρ σ (Value.den v_f) σ'

  /-- [eval-match]: match expression -/
  | eval_match :
      evalAtomic ae ρ σ = some d →
      -- For simplicity, handle the case of simple constructor labels
      d = Denotable.conLabel c →
      findBranch bs c = some (xs, e) →
      xs = [] →  -- No binding for simple constructors
      EvalExp e ρ σ v' σ' →
      EvalCExp (CExp.matchE ae bs) ρ σ v' σ'

  /-- [eval-match-succ]: match (succ x) branch with binding (reallocates) -/
  | eval_match_succ :
      evalAtomic ae ρ σ = some (Denotable.succVal a_inner) →
      findBranch bs ConLabel.succ = some ([x_bind], e) →
      σ a_inner = some d_inner →
      σ a_fresh = none →
      σ_new = σ.extend a_fresh d_inner →
      ρ_new = ρ.extend x_bind a_fresh →
      EvalExp e ρ_new σ_new v' σ' →
      EvalCExp (CExp.matchE ae bs) ρ σ v' σ'

  /-- [eval-handler]: handler expression -/
  | eval_handler :
      EvalExp e_body ρ σ v' σ' →
      HandleValue h ρ v' σ' v'' σ'' →
      EvalCExp (CExp.handler h e_body l_h) ρ σ v'' σ''

/--
Frame continuation: (ψ, v, σ) ⇒c (v', σ')
-/
inductive ContinueFrame : Frame → Value → Store → Value → Store → Prop where
  /-- [continue-let]: continue with let frame when value is denotable -/
  | continue_let :
      σ a_v = none →  -- a_v is fresh
      σ_let = σ.extend a_v d →
      EvalExp e (ρ.extend y a_v) σ_let v' σ' →
      ContinueFrame (Frame.letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩) (Value.den d) σ v' σ'

  /-- [continue-op]: propagate operation through let frame -/
  | continue_op :
      ContinueFrame (Frame.letFrame clo) (Value.suspended op as_v κ) σ
                    (Value.suspended op as_v (Frame.letFrame clo :: κ)) σ

/--
Handler evaluation: (h, ρ, v, σ) ⇓h (v', σ')
-/
inductive HandleValue : Handler → Env → Value → Store → Value → Store → Prop where
  /-- [handle-return]: handle return value -/
  | handle_return :
      (x_ret, e_ret) = h.returnClause →
      σ a_v = none →  -- a_v is fresh
      σ_ret = σ.extend a_v d →
      EvalExp e_ret (ρ.extend x_ret a_v) σ_ret v' σ' →
      HandleValue h ρ (Value.den d) σ v' σ'

  /-- [handle-op]: handle operation -/
  | handle_op :
      h.findOp op = some (x, e_op) →
      σ a_v' = none →  -- a_v' is fresh (for argument)
      σ a_vk = none →  -- a_vk is fresh (for resume)
      a_v' ≠ a_vk →    -- distinct addresses
      σ a_arg = some d_arg →
      σ_op = (σ.extend a_v' d_arg).extend a_vk (Denotable.kontClosure h ρ κ) →
      EvalExp e_op ((ρ.extend x a_v').extend "resume" a_vk) σ_op v σ' →
      HandleValue h ρ (Value.suspended op [a_arg] κ) σ v σ'

  /-- [handle-capture-op]: capture unhandled operation -/
  | handle_capture_op :
      h.hasOp op = false →
      v' = Value.suspended op as_v (Frame.handlerFrame h ρ :: κ) →
      HandleValue h ρ (Value.suspended op as_v κ) σ v' σ

/--
Apply/restore continuation: (κ, d, σ) ⇓a (v, σ')
-/
inductive ApplyKont : Kont → Denotable → Store → Value → Store → Prop where
  /-- [apply-continue]: empty continuation returns value -/
  | apply_continue :
      ApplyKont [] d σ (Value.den d) σ

  /-- [apply-restore]: restore frame from continuation -/
  | apply_restore :
      ApplyKont κ d σ v' σ' →
      ContinueFrame (Frame.letFrame clo) v' σ' v'' σ'' →
      ApplyKont (Frame.letFrame clo :: κ) d σ v'' σ''

  /-- [apply-restore-handle]: restore handler frame -/
  | apply_restore_handle :
      ApplyKont κ d σ v' σ' →
      HandleValue h ρ v' σ' v'' σ'' →
      ApplyKont (Frame.handlerFrame h ρ :: κ) d σ v'' σ''

end

/-! ## Height-indexed evaluation relations for structural recursion -/

mutual

inductive EvalExpN : Nat → Exp → Env → Store → Value → Store → Prop where
  | eval_let :
      EvalCExpN n1 ce ρ σ v σ' →
      ContinueFrameN n2 (Frame.letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩) v σ' v' σ'' →
      EvalExpN (n1 + n2 + 1) (Exp.letE y ce e l) ρ σ v' σ''
  | eval_tail :
      EvalCExpN n ce ρ σ v σ' →
      EvalExpN (n + 1) (Exp.tail ce l) ρ σ v σ'

inductive EvalCExpN : Nat → CExp → Env → Store → Value → Store → Prop where
  | eval_atomic :
      evalAtomic ae ρ σ = some d →
      EvalCExpN 0 (CExp.atomic ae) ρ σ (Value.den d) σ
  | eval_funApp_clos :
      evalAtomic f ρ σ = some (Denotable.closure ⟨xs, e_body, ρ_lam, _h_nd⟩) →
      xs.length = aes.length →
      List.Forall₂ (fun ae d => evalAtomic ae ρ σ = some d) aes ds →
      List.Forall₂ (fun a (_ : Denotable) => σ a = none) as_v ds →  -- addresses fresh in σ
      as_v.Nodup →  -- distinct
      as_v.length = xs.length →
      σ_new = (List.zip as_v ds).foldl (fun s (a, d) => s.extend a d) σ →
      ρ_new = (List.zip xs as_v).foldl (fun r (x, a) => r.extend x a) ρ_lam →
      EvalExpN n e_body ρ_new σ_new v' σ' →
      EvalCExpN (n + 1) (CExp.funApp f aes) ρ σ v' σ'
  | eval_opApp :
      ρ x = some a_v →
      EvalCExpN 0 (CExp.opApp op x) ρ σ (Value.suspended op [a_v] []) σ
  | eval_funApp_kont :
      evalAtomic f ρ σ = some (Denotable.kontClosure h ρ_h κ) →
      evalAtomic ae ρ σ = some d →
      ApplyKontN n1 κ d σ v' σ' →
      HandleValueN n2 h ρ_h v' σ' v'' σ'' →
      EvalCExpN (n1 + n2 + 1) (CExp.funApp f [ae]) ρ σ v'' σ''
  | eval_fun :
      σ a_v = none →
      (h_nd : xs.Nodup) →
      v_f = Denotable.closure ⟨xs, e1, ρ.extend f a_v, h_nd⟩ →
      σ' = σ.extend a_v v_f →
      EvalCExpN 0 (CExp.funDef f xs e1) ρ σ (Value.den v_f) σ'
  | eval_match :
      evalAtomic ae ρ σ = some d →
      d = Denotable.conLabel c →
      findBranch bs c = some (xs, e) →
      xs = [] →
      EvalExpN n e ρ σ v' σ' →
      EvalCExpN (n + 1) (CExp.matchE ae bs) ρ σ v' σ'
  | eval_match_succ :
      evalAtomic ae ρ σ = some (Denotable.succVal a_inner) →
      findBranch bs ConLabel.succ = some ([x_bind], e) →
      σ a_inner = some d_inner →
      σ a_fresh = none →
      σ_new = σ.extend a_fresh d_inner →
      ρ_new = ρ.extend x_bind a_fresh →
      EvalExpN n e ρ_new σ_new v' σ' →
      EvalCExpN (n + 1) (CExp.matchE ae bs) ρ σ v' σ'
  | eval_handler :
      EvalExpN n1 e_body ρ σ v' σ' →
      HandleValueN n2 h ρ v' σ' v'' σ'' →
      EvalCExpN (n1 + n2 + 1) (CExp.handler h e_body l_h) ρ σ v'' σ''

inductive ContinueFrameN : Nat → Frame → Value → Store → Value → Store → Prop where
  | continue_let :
      σ a_v = none →
      σ_let = σ.extend a_v d →
      EvalExpN n e (ρ.extend y a_v) σ_let v' σ' →
      ContinueFrameN (n + 1) (Frame.letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩) (Value.den d) σ v' σ'
  | continue_op :
      ContinueFrameN 0 (Frame.letFrame clo) (Value.suspended op as_v κ) σ
                    (Value.suspended op as_v (Frame.letFrame clo :: κ)) σ

inductive HandleValueN : Nat → Handler → Env → Value → Store → Value → Store → Prop where
  | handle_return :
      (x_ret, e_ret) = h.returnClause →
      σ a_v = none →
      σ_ret = σ.extend a_v d →
      EvalExpN n e_ret (ρ.extend x_ret a_v) σ_ret v' σ' →
      HandleValueN (n + 1) h ρ (Value.den d) σ v' σ'
  | handle_op :
      h.findOp op = some (x, e_op) →
      σ a_v' = none →
      σ a_vk = none →
      a_v' ≠ a_vk →
      σ a_arg = some d_arg →
      σ_op = (σ.extend a_v' d_arg).extend a_vk (Denotable.kontClosure h ρ κ) →
      EvalExpN n e_op ((ρ.extend x a_v').extend "resume" a_vk) σ_op v σ' →
      HandleValueN (n + 1) h ρ (Value.suspended op [a_arg] κ) σ v σ'
  | handle_capture_op :
      h.hasOp op = false →
      v' = Value.suspended op as_v (Frame.handlerFrame h ρ :: κ) →
      HandleValueN 0 h ρ (Value.suspended op as_v κ) σ v' σ

inductive ApplyKontN : Nat → Kont → Denotable → Store → Value → Store → Prop where
  | apply_continue :
      ApplyKontN 0 [] d σ (Value.den d) σ
  | apply_restore :
      ApplyKontN n1 κ d σ v' σ' →
      ContinueFrameN n2 (Frame.letFrame clo) v' σ' v'' σ'' →
      ApplyKontN (n1 + n2 + 1) (Frame.letFrame clo :: κ) d σ v'' σ''
  | apply_restore_handle :
      ApplyKontN n1 κ d σ v' σ' →
      HandleValueN n2 h ρ v' σ' v'' σ'' →
      ApplyKontN (n1 + n2 + 1) (Frame.handlerFrame h ρ :: κ) d σ v'' σ''

end

mutual

theorem eval_exp_to_N (h : EvalExp e ρ σ v σ') : ∃ n, EvalExpN n e ρ σ v σ' :=
  match h with
  | .eval_let h1 h2 =>
    let ⟨n1, hn1⟩ := eval_cexp_to_N h1
    let ⟨n2, hn2⟩ := continue_frame_to_N h2
    ⟨n1 + n2 + 1, .eval_let hn1 hn2⟩
  | .eval_tail h1 =>
    let ⟨n1, hn1⟩ := eval_cexp_to_N h1
    ⟨n1 + 1, .eval_tail hn1⟩

theorem eval_cexp_to_N (h : EvalCExp ce ρ σ v σ') : ∃ n, EvalCExpN n ce ρ σ v σ' :=
  match h with
  | .eval_atomic h1 => ⟨0, .eval_atomic h1⟩
  | .eval_funApp_clos h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    let ⟨n, hn⟩ := eval_exp_to_N h9
    ⟨n + 1, .eval_funApp_clos h1 h2 h3 h4 h5 h6 h7 h8 hn⟩
  | .eval_opApp h1 => ⟨0, .eval_opApp h1⟩
  | .eval_funApp_kont h1 h2 h3 h4 =>
    let ⟨n1, hn1⟩ := apply_kont_to_N h3
    let ⟨n2, hn2⟩ := handle_value_to_N h4
    ⟨n1 + n2 + 1, .eval_funApp_kont h1 h2 hn1 hn2⟩
  | .eval_fun h1 h2 h3 h4 => ⟨0, .eval_fun h1 h2 h3 h4⟩
  | .eval_match h1 h2 h3 h4 h5 =>
    let ⟨n, hn⟩ := eval_exp_to_N h5
    ⟨n + 1, .eval_match h1 h2 h3 h4 hn⟩
  | .eval_match_succ h1 h2 h3 h4 h5 h6 h7 =>
    let ⟨n, hn⟩ := eval_exp_to_N h7
    ⟨n + 1, .eval_match_succ h1 h2 h3 h4 h5 h6 hn⟩
  | .eval_handler h1 h2 =>
    let ⟨n1, hn1⟩ := eval_exp_to_N h1
    let ⟨n2, hn2⟩ := handle_value_to_N h2
    ⟨n1 + n2 + 1, .eval_handler hn1 hn2⟩

theorem continue_frame_to_N (h : ContinueFrame f v σ v' σ') : ∃ n, ContinueFrameN n f v σ v' σ' :=
  match h with
  | .continue_let h1 h2 h3 =>
    let ⟨n, hn⟩ := eval_exp_to_N h3
    ⟨n + 1, .continue_let h1 h2 hn⟩
  | .continue_op => ⟨0, .continue_op⟩

theorem handle_value_to_N (h : HandleValue hh ρ v σ v' σ') : ∃ n, HandleValueN n hh ρ v σ v' σ' :=
  match h with
  | .handle_return h1 h2 h3 h4 =>
    let ⟨n, hn⟩ := eval_exp_to_N h4
    ⟨n + 1, .handle_return h1 h2 h3 hn⟩
  | .handle_op h1 h2 h3 h4 h5 h6 h7 =>
    let ⟨n, hn⟩ := eval_exp_to_N h7
    ⟨n + 1, .handle_op h1 h2 h3 h4 h5 h6 hn⟩
  | .handle_capture_op h1 h2 => ⟨0, .handle_capture_op h1 h2⟩

theorem apply_kont_to_N (h : ApplyKont κ d σ v σ') : ∃ n, ApplyKontN n κ d σ v σ' :=
  match h with
  | .apply_continue => ⟨0, .apply_continue⟩
  | .apply_restore h1 h2 =>
    let ⟨n1, hn1⟩ := apply_kont_to_N h1
    let ⟨n2, hn2⟩ := continue_frame_to_N h2
    ⟨n1 + n2 + 1, .apply_restore hn1 hn2⟩
  | .apply_restore_handle h1 h2 =>
    let ⟨n1, hn1⟩ := apply_kont_to_N h1
    let ⟨n2, hn2⟩ := handle_value_to_N h2
    ⟨n1 + n2 + 1, .apply_restore_handle hn1 hn2⟩

end

mutual

theorem eval_expN_to (h : EvalExpN n e ρ σ v σ') : EvalExp e ρ σ v σ' :=
  match h with
  | .eval_let h1 h2 => .eval_let (eval_cexpN_to h1) (continue_frameN_to h2)
  | .eval_tail h1 => .eval_tail (eval_cexpN_to h1)

theorem eval_cexpN_to (h : EvalCExpN n ce ρ σ v σ') : EvalCExp ce ρ σ v σ' :=
  match h with
  | .eval_atomic h1 => .eval_atomic h1
  | .eval_funApp_clos h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    .eval_funApp_clos h1 h2 h3 h4 h5 h6 h7 h8 (eval_expN_to h9)
  | .eval_opApp h1 => .eval_opApp h1
  | .eval_funApp_kont h1 h2 h3 h4 =>
    .eval_funApp_kont h1 h2 (apply_kontN_to h3) (handle_valueN_to h4)
  | .eval_fun h1 h2 h3 h4 => .eval_fun h1 h2 h3 h4
  | .eval_match h1 h2 h3 h4 h5 => .eval_match h1 h2 h3 h4 (eval_expN_to h5)
  | .eval_match_succ h1 h2 h3 h4 h5 h6 h7 =>
    .eval_match_succ h1 h2 h3 h4 h5 h6 (eval_expN_to h7)
  | .eval_handler h1 h2 => .eval_handler (eval_expN_to h1) (handle_valueN_to h2)

theorem continue_frameN_to (h : ContinueFrameN n f v σ v' σ') : ContinueFrame f v σ v' σ' :=
  match h with
  | .continue_let h1 h2 h3 => .continue_let h1 h2 (eval_expN_to h3)
  | .continue_op => .continue_op

theorem handle_valueN_to (h : HandleValueN n hh ρ v σ v' σ') : HandleValue hh ρ v σ v' σ' :=
  match h with
  | .handle_return h1 h2 h3 h4 => .handle_return h1 h2 h3 (eval_expN_to h4)
  | .handle_op h1 h2 h3 h4 h5 h6 h7 => .handle_op h1 h2 h3 h4 h5 h6 (eval_expN_to h7)
  | .handle_capture_op h1 h2 => .handle_capture_op h1 h2

theorem apply_kontN_to (h : ApplyKontN n κ d σ v σ') : ApplyKont κ d σ v σ' :=
  match h with
  | .apply_continue => .apply_continue
  | .apply_restore h1 h2 => .apply_restore (apply_kontN_to h1) (continue_frameN_to h2)
  | .apply_restore_handle h1 h2 =>
    .apply_restore_handle (apply_kontN_to h1) (handle_valueN_to h2)

end

end DMCFA
