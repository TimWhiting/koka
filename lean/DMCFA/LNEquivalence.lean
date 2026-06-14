/-
  Equivalence Relations between B&P and ANF semantics (fully locally nameless)

  All relations in one mutual block because:
  - ValueEquiv references CompEquiv (lambda case)
  - ExprEquiv references ValueEquiv (var_subst) and CompEquiv (lam)
  - CompEquiv references CompEquivCExp
  - CompEquivCExp references ExprEquiv, CompEquiv, HandlerEquiv

  Both B&P (`BPLN`) and ANF (`LN`) terms are locally nameless: bound variables
  are de Bruijn indices (`BPLN.Expr.bvar` / `AExp.bvar`). Since both sides use
  the SAME index space, the relations carry a single depth counter
  `n : Nat` (replacing the old named-ANF `Γ : List Var`):

  - For `i < n`, index `i` is *open* on both sides: `BPLN.Expr.bvar i`
    corresponds literally to `AExp.bvar i` (`ExprEquiv.var_bound`).
  - For `i ≥ n`, index `i` has already been *resolved*: on the B&P side the
    (substitution-based) term carries the concrete value `e_bp` that replaced
    `bvar i`; on the ANF side `AExp.bvar i` resolves via the environment
    stack: `ρ.lookup (i - n) = some a` and `σ a` denotes the same value
    (`ExprEquiv.var_subst`).

  The continuation `resume` is an ordinary binder: in a handler op-clause it
  is `bvar 1` (`bvar 0` being the operation argument) on both sides, related
  by the normal `ExprEquiv.var_bound`/`var_subst` machinery.
-/

import DMCFA.LNBPSyntax
import DMCFA.LNSyntax
import DMCFA.LNComponents

namespace DMCFA.LN

mutual

/-- Value equivalence: closed B&P value expression ↔ ANF denotable -/
inductive ValueEquiv : Store → BPLN.Expr → Denotable → Prop where
  | con_true : ValueEquiv σ BPLN.Expr.true_ (Denotable.conLabel ConLabel.true_)
  | con_false : ValueEquiv σ BPLN.Expr.false_ (Denotable.conLabel ConLabel.false_)
  | con_unit : ValueEquiv σ BPLN.Expr.unit (Denotable.conLabel ConLabel.unit)
  | con_zero : ValueEquiv σ BPLN.Expr.zero (Denotable.conLabel ConLabel.zero)
  | succ :
      σ a = some d →
      ValueEquiv σ e d →
      ValueEquiv σ (BPLN.Expr.succ e) (Denotable.succVal a)
  -- Tier 2: closures
  | lambda :
      CompEquiv σ ρ 1 c e_body →
      ValueEquiv σ (BPLN.Expr.lam c) (Denotable.closure ⟨1, e_body, ρ, none⟩)
  | rec_lambda :
      CompEquiv σ ρ 2 c1 e1 →
      σ a_f = some (Denotable.closure ⟨1, e1, ρ, some a_f⟩) →
      ValueEquiv σ
        (BPLN.Expr.lam (BPLN.Comp.letRec c1 c1))
        (Denotable.closure ⟨1, e1, ρ, some a_f⟩)
  -- Tier 3: continuation closures
  | kont :
      HandlerEquiv σ ρ 0 h h_anf →
      KontEquiv σ c_op κ →
      ValueEquiv σ
        (BPLN.Expr.lam (BPLN.Comp.withHandle h c_op))
        (Denotable.kontClosure h_anf ρ κ)

/-- Expression equivalence: B&P expression ↔ ANF atomic expression, at depth `n`. -/
inductive ExprEquiv : Store → Env → Nat → BPLN.Expr → AExp → Prop where
  /-- An index still open on both sides corresponds literally. -/
  | var_bound :
      i < n →
      ExprEquiv σ ρ n (BPLN.Expr.bvar i) (AExp.bvar i)
  | true_ : ExprEquiv σ ρ n BPLN.Expr.true_ (AExp.con ConLabel.true_)
  | false_ : ExprEquiv σ ρ n BPLN.Expr.false_ (AExp.con ConLabel.false_)
  | unit : ExprEquiv σ ρ n BPLN.Expr.unit (AExp.con ConLabel.unit)
  | zero : ExprEquiv σ ρ n BPLN.Expr.zero (AExp.con ConLabel.zero)
  /-- `S(ae)` is always applied to a variable reference (`bvar i`), never a
  constructed value -- mirrors `opApp_bvar`/`opApp_resume`'s restriction. -/
  | succ :
      ExprEquiv σ ρ n e (AExp.bvar i) →
      ExprEquiv σ ρ n (BPLN.Expr.succ e) (AExp.succE (AExp.bvar i))
  | lam :
      CompEquiv σ ρ (n + 1) c e_body →
      ExprEquiv σ ρ n (BPLN.Expr.lam c) (AExp.lam 1 e_body)
  /-- An already-resolved index: B&P carries the substituted value `e_bp`;
  ANF's `bvar i` (`i ≥ n`) resolves via `ρ` to the same value. -/
  | var_subst :
      n ≤ i →
      ρ.lookup (i - n) = some a →
      σ a = some d →
      ValueEquiv σ e_bp d →
      e_bp.fvs = [] →
      ExprEquiv σ ρ n e_bp (AExp.bvar i)

/-- Computation equivalence: B&P computation ↔ ANF expression, at depth `n`. -/
inductive CompEquiv : Store → Env → Nat → BPLN.Comp → Exp → Prop where
  | tail :
      CompEquivCExp σ ρ n c ce →
      CompEquiv σ ρ n c (Exp.tail ce l)
  | letE :
      CompEquivCExp σ ρ n c1 ce →
      CompEquiv σ ρ (n + 1) c2 e2 →
      CompEquiv σ ρ n (BPLN.Comp.letIn c1 c2) (Exp.letE ce e2 l)
  -- Tier 2: recursive let
  | letRec :
      CompEquiv σ ρ (n + 2) c1 e1 →
      CompEquiv σ ρ (n + 1) c2 e2 →
      CompEquiv σ ρ n (BPLN.Comp.letRec c1 c2) (Exp.letE (CExp.funDef 1 e1) e2 l)

/-- Complex expression equivalence: B&P computation ↔ ANF complex expression, at depth `n`. -/
inductive CompEquivCExp : Store → Env → Nat → BPLN.Comp → CExp → Prop where
  | atomic :
      ExprEquiv σ ρ n e ae →
      CompEquivCExp σ ρ n (BPLN.Comp.val e) (CExp.atomic ae)
  | funApp :
      ExprEquiv σ ρ n e1 ae1 →
      ExprEquiv σ ρ n e2 ae2 →
      CompEquivCExp σ ρ n (BPLN.Comp.app e1 e2) (CExp.funApp ae1 [ae2])
  | ifE :
      ExprEquiv σ ρ n e ae →
      CompEquiv σ ρ n c1 e1 →
      CompEquiv σ ρ n c2 e2 →
      CompEquivCExp σ ρ n (BPLN.Comp.ifThenElse e c1 c2)
        (CExp.matchE ae [Branch.branch ConLabel.true_ e1,
                         Branch.branch ConLabel.false_ e2])
  | matchNat :
      ExprEquiv σ ρ n e ae →
      CompEquiv σ ρ n c1 e1 →
      CompEquiv σ ρ (n + 1) c2 e2 →
      CompEquivCExp σ ρ n (BPLN.Comp.matchNat e c1 c2)
        (CExp.matchE ae [Branch.branch ConLabel.zero e1,
                         Branch.branch ConLabel.succ e2])
  -- Tier 3: effects
  | opApp_bvar :
      ExprEquiv σ ρ n e (AExp.bvar i) →
      CompEquivCExp σ ρ n (BPLN.Comp.opCall op e) (CExp.opApp op (AExp.bvar i))
  | handler :
      HandlerEquiv σ ρ n h h_anf →
      CompEquiv σ ρ n c e_body →
      CompEquivCExp σ ρ n (BPLN.Comp.withHandle h c) (CExp.handler h_anf e_body l_h)

/-- Handler equivalence, at depth `n`. -/
inductive HandlerEquiv : Store → Env → Nat → BPLN.BPHandler → Handler → Prop where
  | mk :
      CompEquiv σ ρ (n + 1) c_ret e_ret →
      OpClausesEquiv σ ρ n bp_ops anf_ops →
      HandlerEquiv σ ρ n ⟨c_ret, bp_ops⟩ ⟨e_ret, anf_ops⟩

/-- Operation clauses equivalence, at depth `n` (each clause binds 1 more). -/
inductive OpClausesEquiv : Store → Env → Nat → List (BPLN.OpName × BPLN.Comp) → List (OpName × Exp) → Prop where
  | nil : OpClausesEquiv σ ρ n [] []
  | cons :
      CompEquiv σ ρ (n + 2) c e →
      OpClausesEquiv σ ρ n rest rest' →
      OpClausesEquiv σ ρ n ((op, c) :: rest) ((op, e) :: rest')

/-- Continuation equivalence: a 1-hole B&P computation (`bvar 0` = the hole)
↔ ANF frame stack. -/
inductive KontEquiv : Store → BPLN.Comp → Kont → Prop where
  | kont_end :
      KontEquiv σ (BPLN.Comp.val (BPLN.Expr.bvar 0)) []
  | kont_let :
      KontEquiv σ c_inner κ_rest →
      CompEquiv σ ρ 1 c2 e2 →
      KontEquiv σ (BPLN.Comp.letIn c_inner c2)
        (Frame.letFrame e2 ρ :: κ_rest)
  | kont_handle :
      KontEquiv σ c_inner κ_rest →
      HandlerEquiv σ ρ 0 h h_anf →
      KontEquiv σ (BPLN.Comp.withHandle h c_inner)
        (Frame.handlerFrame h_anf ρ :: κ_rest)

/-- Result equivalence: B&P result ↔ ANF value -/
inductive ResultEquiv : Store → BPLN.Result → Value → Prop where
  | value :
      ValueEquiv σ e d →
      ResultEquiv σ (BPLN.Result.value e) (Value.den d)
  | op :
      σ a = some d →
      ValueEquiv σ e_op d →
      KontEquiv σ c_op κ →
      ResultEquiv σ (BPLN.Result.op op e_op c_op) (Value.suspended op [a] κ)

end -- mutual

end DMCFA.LN
