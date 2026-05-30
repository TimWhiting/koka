/-
  Bauer & Pretnar Big-Step Semantics

  Defines the substitution-based evaluation relation for B&P:
    c ⇓ r
  where c is a computation and r is a result (val e or # op e (x_c. c))
-/

import DMCFA.BPSyntax

namespace DMCFA.BP

/-- Checks if operation is handled by handler -/
def BPHandler.hasOp (h : BPHandler) (op : OpName) : Bool :=
  h.opClauses.any fun (op', _, _) => op' = op

/-- Find operation clause in handler -/
def BPHandler.findOp (h : BPHandler) (op : OpName) : Option (Var × Comp) :=
  h.opClauses.findSome? fun (op', x, c) =>
    if op' = op then some (x, c) else none

/--
Big-step evaluation for B&P: c ⇓ r

This is a substitution-based semantics where:
- val e evaluates to val e
- Function application substitutes argument into body
- let binds values or propagates operations
- Handlers handle operations or propagate them with extended continuation
-/
inductive Eval : Comp → Result → Prop where
  /-- val e ⇓ val e -/
  | val : Eval (Comp.val e) (Result.value e)

  /-- Lambda application: (fun x → c) e ⇓ r if c[e/x] ⇓ r -/
  | app_lam :
      Eval (c.subst x e_arg) r →
      Eval (Comp.app (Expr.lam x c) e_arg) r

  /-- let x = c1 in c2 ⇓ r when c1 ⇓ val e' and c2[e'/x] ⇓ r -/
  | let_val :
      Eval c1 (Result.value e') →
      Eval (c2.subst x e') r →
      Eval (Comp.letIn x c1 c2) r

  /-- let x = c1 in c2 ⇓ # op e_op (x_c. let x = c_op in c2)
      when c1 ⇓ # op e_op (x_c. c_op) -/
  | let_op :
      Eval c1 (Result.op op e_op x_c c_op) →
      Eval (Comp.letIn x c1 c2) (Result.op op e_op x_c (Comp.letIn x c_op c2))

  /-- let rec f x = c1 in c2 ⇓ r
      when c2[(fun x → let rec f x = c1 in c1)/f] ⇓ r -/
  | let_rec :
      Eval (c2.subst f (Expr.lam x (Comp.letRec f x c1 c1))) r →
      Eval (Comp.letRec f x c1 c2) r

  /-- if true then c1 else c2 ⇓ r when c1 ⇓ r -/
  | if_true :
      Eval c1 r →
      Eval (Comp.ifThenElse Expr.true_ c1 c2) r

  /-- if false then c1 else c2 ⇓ r when c2 ⇓ r -/
  | if_false :
      Eval c2 r →
      Eval (Comp.ifThenElse Expr.false_ c1 c2) r

  /-- match 0 with 0 → c1 | succ x → c2 ⇓ r when c1 ⇓ r -/
  | match_zero :
      Eval c1 r →
      Eval (Comp.matchNat Expr.zero c1 x c2) r

  /-- match (succ e') with 0 → c1 | succ x → c2 ⇓ r when c2[e'/x] ⇓ r -/
  | match_succ :
      Eval (c2.subst x e') r →
      Eval (Comp.matchNat (Expr.succ e') c1 x c2) r

  /-- with h handle c ⇓ r when c ⇓ val e' and (c_ret)[e'/x_ret] ⇓ r
      where (val x_ret → c_ret) ∈ h -/
  | handle_val :
      Eval c (Result.value e') →
      (x_ret, c_ret) = h.returnClause →
      Eval (c_ret.subst x_ret e') r →
      Eval (Comp.withHandle h c) r

  /-- with h handle c ⇓ r when c ⇓ # op e_op (x_c. c_op) and op ∈ h
      and c_h[e_op/x, (fun x_c → with h handle c_op)/resume] ⇓ r -/
  | handle_op :
      Eval c (Result.op op e_op x_c c_op) →
      h.findOp op = some (x, c_h) →
      Eval ((c_h.subst x e_op).subst "resume"
            (Expr.lam x_c (Comp.withHandle h c_op))) r →
      Eval (Comp.withHandle h c) r

  /-- with h handle c ⇓ # op e_op (x_c. with h handle c_op)
      when c ⇓ # op e_op (x_c. c_op) and op ∉ h -/
  | handle_forward :
      Eval c (Result.op op e_op x_c c_op) →
      h.hasOp op = false →
      Eval (Comp.withHandle h c) (Result.op op e_op x_c (Comp.withHandle h c_op))

  /-- op e ⇓ # op e (x. val x) -/
  | op_call :
      Eval (Comp.opCall op e) (Result.op op e "x" (Comp.val (Expr.var "x")))

/-- Height-indexed evaluation: mirrors Eval with an explicit Nat height parameter.
    Used for strong induction in the completeness proof. -/
inductive EvalN : Nat → Comp → Result → Prop where
  | val : EvalN 0 (Comp.val e) (Result.value e)
  | app_lam : EvalN n (c.subst x e_arg) r →
      EvalN (n+1) (Comp.app (Expr.lam x c) e_arg) r
  | let_val : EvalN n1 c1 (Result.value e') → EvalN n2 (c2.subst x e') r →
      EvalN (n1+n2+1) (Comp.letIn x c1 c2) r
  | let_op : EvalN n c1 (Result.op op e_op x_c c_op) →
      EvalN (n+1) (Comp.letIn x c1 c2) (Result.op op e_op x_c (Comp.letIn x c_op c2))
  | let_rec : EvalN n (c2.subst f (Expr.lam x (Comp.letRec f x c1 c1))) r →
      EvalN (n+1) (Comp.letRec f x c1 c2) r
  | if_true : EvalN n c1 r → EvalN (n+1) (Comp.ifThenElse Expr.true_ c1 c2) r
  | if_false : EvalN n c2 r → EvalN (n+1) (Comp.ifThenElse Expr.false_ c1 c2) r
  | match_zero : EvalN n c1 r → EvalN (n+1) (Comp.matchNat Expr.zero c1 x c2) r
  | match_succ : EvalN n (c2.subst x e') r →
      EvalN (n+1) (Comp.matchNat (Expr.succ e') c1 x c2) r
  | handle_val : EvalN n1 c (Result.value e') → (x_ret, c_ret) = h.returnClause →
      EvalN n2 (c_ret.subst x_ret e') r →
      EvalN (n1+n2+1) (Comp.withHandle h c) r
  | handle_op : EvalN n1 c (Result.op op e_op x_c c_op) →
      h.findOp op = some (x, c_h) →
      EvalN n2 ((c_h.subst x e_op).subst "resume" (Expr.lam x_c (Comp.withHandle h c_op))) r →
      EvalN (n1+n2+1) (Comp.withHandle h c) r
  | handle_forward : EvalN n c (Result.op op e_op x_c c_op) → h.hasOp op = false →
      EvalN (n+1) (Comp.withHandle h c) (Result.op op e_op x_c (Comp.withHandle h c_op))
  | op_call : EvalN 0 (Comp.opCall op e) (Result.op op e "x" (Comp.val (Expr.var "x")))

theorem eval_to_evalN : Eval c r → ∃ n, EvalN n c r := by
  intro h
  induction h with
  | val => exact ⟨0, .val⟩
  | app_lam _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, .app_lam hn⟩
  | let_val _ _ ih1 ih2 =>
    obtain ⟨n1, hn1⟩ := ih1; obtain ⟨n2, hn2⟩ := ih2
    exact ⟨n1+n2+1, .let_val hn1 hn2⟩
  | let_op _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, .let_op hn⟩
  | let_rec _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, .let_rec hn⟩
  | if_true _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, .if_true hn⟩
  | if_false _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, .if_false hn⟩
  | match_zero _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, .match_zero hn⟩
  | match_succ _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, .match_succ hn⟩
  | handle_val _ _ _ ih1 ih2 =>
    obtain ⟨n1, hn1⟩ := ih1; obtain ⟨n2, hn2⟩ := ih2
    exact ⟨n1+n2+1, .handle_val hn1 ‹_› hn2⟩
  | handle_op _ _ _ ih1 ih2 =>
    obtain ⟨n1, hn1⟩ := ih1; obtain ⟨n2, hn2⟩ := ih2
    exact ⟨n1+n2+1, .handle_op hn1 ‹_› hn2⟩
  | handle_forward _ _ ih => obtain ⟨n, hn⟩ := ih; exact ⟨n+1, .handle_forward hn ‹_›⟩
  | op_call => exact ⟨0, .op_call⟩

theorem evalN_to_eval : EvalN n c r → Eval c r := by
  intro h
  induction h with
  | val => exact .val
  | app_lam _ ih => exact .app_lam ih
  | let_val _ _ ih1 ih2 => exact .let_val ih1 ih2
  | let_op _ ih => exact .let_op ih
  | let_rec _ ih => exact .let_rec ih
  | if_true _ ih => exact .if_true ih
  | if_false _ ih => exact .if_false ih
  | match_zero _ ih => exact .match_zero ih
  | match_succ _ ih => exact .match_succ ih
  | handle_val _ _ _ ih1 ih2 => exact .handle_val ih1 ‹_› ih2
  | handle_op _ _ _ ih1 ih2 => exact .handle_op ih1 ‹_› ih2
  | handle_forward _ _ ih => exact .handle_forward ih ‹_›
  | op_call => exact .op_call

end DMCFA.BP
