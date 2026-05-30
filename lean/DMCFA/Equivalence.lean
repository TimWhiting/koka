/-
  Equivalence Relations between B&P and ANF semantics

  All relations in one mutual block because:
  - ValueEquiv references CompEquiv (lambda case)
  - ExprEquiv references ValueEquiv (var_subst) and CompEquiv (lam)
  - CompEquiv references CompEquivCExp
  - CompEquivCExp references ExprEquiv, CompEquiv, HandlerEquiv
-/

import DMCFA.BPSyntax
import DMCFA.Components

namespace DMCFA

mutual

/-- Value equivalence: closed B&P value expression ↔ ANF denotable -/
inductive ValueEquiv : Store → BP.Expr → Denotable → Prop where
  | con_true : ValueEquiv σ BP.Expr.true_ (Denotable.conLabel ConLabel.true_)
  | con_false : ValueEquiv σ BP.Expr.false_ (Denotable.conLabel ConLabel.false_)
  | con_unit : ValueEquiv σ BP.Expr.unit (Denotable.conLabel ConLabel.unit)
  | con_zero : ValueEquiv σ BP.Expr.zero (Denotable.conLabel ConLabel.zero)
  | succ :
      σ a = some d →
      ValueEquiv σ e d →
      ValueEquiv σ (BP.Expr.succ e) (Denotable.succVal a)
  -- Tier 2: closures
  | lambda :
      CompEquiv σ ρ c e_body →
      ValueEquiv σ (BP.Expr.lam x c) (Denotable.closure ⟨[x], e_body, ρ, List.nodup_singleton _⟩)
  | rec_lambda :
      CompEquiv σ (Env.extend ρ f a_f) c1 e1 →
      σ a_f = some (Denotable.closure ⟨[x], e1, Env.extend ρ f a_f, List.nodup_singleton _⟩) →
      ValueEquiv σ
        (BP.Expr.lam x (BP.Comp.letRec f x c1 c1))
        (Denotable.closure ⟨[x], e1, Env.extend ρ f a_f, List.nodup_singleton _⟩)
  -- Tier 3: continuation closures
  | kont :
      HandlerEquiv σ ρ h h_anf →
      KontEquiv σ x_c c_op κ →
      x_c ∉ h.fvs →
      ValueEquiv σ
        (BP.Expr.lam x_c (BP.Comp.withHandle h c_op))
        (Denotable.kontClosure h_anf ρ κ)

/-- Expression equivalence: B&P expression ↔ ANF atomic expression -/
inductive ExprEquiv : Store → Env → BP.Expr → AExp → Prop where
  | var : ExprEquiv σ ρ (BP.Expr.var x) (AExp.var x)
  | true_ : ExprEquiv σ ρ BP.Expr.true_ (AExp.con ConLabel.true_)
  | false_ : ExprEquiv σ ρ BP.Expr.false_ (AExp.con ConLabel.false_)
  | unit : ExprEquiv σ ρ BP.Expr.unit (AExp.con ConLabel.unit)
  | zero : ExprEquiv σ ρ BP.Expr.zero (AExp.con ConLabel.zero)
  | succ :
      ExprEquiv σ ρ e (AExp.var x) →
      ExprEquiv σ ρ (BP.Expr.succ e) (AExp.succE x)
  | lam :
      CompEquiv σ ρ c e_body →
      ExprEquiv σ ρ (BP.Expr.lam x c) (AExp.lam [x] e_body)
  /-- After substitution: B&P has value inline, ANF looks up variable -/
  | var_subst :
      ρ y = some a →
      σ a = some d →
      ValueEquiv σ e_bp d →
      e_bp.fvs = [] →
      ExprEquiv σ ρ e_bp (AExp.var y)

/-- Computation equivalence: B&P computation ↔ ANF expression -/
inductive CompEquiv : Store → Env → BP.Comp → Exp → Prop where
  | tail :
      CompEquivCExp σ ρ c ce →
      CompEquiv σ ρ c (Exp.tail ce l)
  | letE :
      CompEquivCExp σ ρ c1 ce →
      CompEquiv σ ρ c2 e2 →
      CompEquiv σ ρ (BP.Comp.letIn x c1 c2) (Exp.letE x ce e2 l)
  -- Tier 2: recursive let
  | letRec :
      CompEquiv σ ρ c1 e1 →
      CompEquiv σ ρ c2 e2 →
      CompEquiv σ ρ (BP.Comp.letRec f x c1 c2) (Exp.letE f (CExp.funDef f [x] e1) e2 l)

/-- Complex expression equivalence: B&P computation ↔ ANF complex expression -/
inductive CompEquivCExp : Store → Env → BP.Comp → CExp → Prop where
  | atomic :
      ExprEquiv σ ρ e ae →
      CompEquivCExp σ ρ (BP.Comp.val e) (CExp.atomic ae)
  | funApp :
      ExprEquiv σ ρ e1 ae1 →
      ExprEquiv σ ρ e2 ae2 →
      CompEquivCExp σ ρ (BP.Comp.app e1 e2) (CExp.funApp ae1 [ae2])
  | ifE :
      ExprEquiv σ ρ e ae →
      CompEquiv σ ρ c1 e1 →
      CompEquiv σ ρ c2 e2 →
      CompEquivCExp σ ρ (BP.Comp.ifThenElse e c1 c2)
        (CExp.matchE ae [Branch.branch ConLabel.true_ [] e1,
                         Branch.branch ConLabel.false_ [] e2])
  | matchNat :
      ExprEquiv σ ρ e ae →
      CompEquiv σ ρ c1 e1 →
      CompEquiv σ ρ c2 e2 →
      CompEquivCExp σ ρ (BP.Comp.matchNat e c1 x c2)
        (CExp.matchE ae [Branch.branch ConLabel.zero [] e1,
                         Branch.branch ConLabel.succ [x] e2])
  -- Tier 3: effects
  | opApp :
      ExprEquiv σ ρ e (AExp.var x) →
      CompEquivCExp σ ρ (BP.Comp.opCall op e) (CExp.opApp op x)
  | handler :
      HandlerEquiv σ ρ h h_anf →
      CompEquiv σ ρ c e_body →
      CompEquivCExp σ ρ (BP.Comp.withHandle h c) (CExp.handler h_anf e_body l_h)

/-- Handler equivalence -/
inductive HandlerEquiv : Store → Env → BP.BPHandler → Handler → Prop where
  | mk :
      CompEquiv σ ρ c_ret e_ret →
      OpClausesEquiv σ ρ bp_ops anf_ops →
      HandlerEquiv σ ρ ⟨(x_ret, c_ret), bp_ops⟩ ⟨(x_ret, e_ret), anf_ops⟩

/-- Operation clauses equivalence -/
inductive OpClausesEquiv : Store → Env → List (OpName × Var × BP.Comp) → List (OpName × Var × Exp) → Prop where
  | nil : OpClausesEquiv σ ρ [] []
  | cons :
      CompEquiv σ ρ c e →
      OpClausesEquiv σ ρ rest rest' →
      OpClausesEquiv σ ρ ((op, x, c) :: rest) ((op, x, e) :: rest')

/-- Continuation equivalence: B&P syntactic continuation ↔ ANF frame stack -/
inductive KontEquiv : Store → Var → BP.Comp → Kont → Prop where
  | kont_end :
      KontEquiv σ x_c (BP.Comp.val (BP.Expr.var x_c)) []
  | kont_let :
      KontEquiv σ x_c c_inner κ_rest →
      CompEquiv σ ρ c2 e2 →
      x_c ∉ c2.fvs →
      KontEquiv σ x_c (BP.Comp.letIn y c_inner c2)
        (Frame.letFrame ⟨[y], e2, ρ, List.nodup_singleton _⟩ :: κ_rest)
  | kont_handle :
      KontEquiv σ x_c c_inner κ_rest →
      HandlerEquiv σ ρ h h_anf →
      x_c ∉ h.fvs →
      KontEquiv σ x_c (BP.Comp.withHandle h c_inner)
        (Frame.handlerFrame h_anf ρ :: κ_rest)

/-- Result equivalence: B&P result ↔ ANF value -/
inductive ResultEquiv : Store → BP.Result → Value → Prop where
  | value :
      ValueEquiv σ e d →
      ResultEquiv σ (BP.Result.value e) (Value.den d)
  | op :
      σ a = some d →
      ValueEquiv σ e_op d →
      KontEquiv σ x_c c_op κ →
      ResultEquiv σ (BP.Result.op op e_op x_c c_op) (Value.suspended op [a] κ)

end -- mutual

end DMCFA
