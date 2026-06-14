/-
  ANF target syntax (locally nameless)

  This is a locally-nameless re-encoding of `DMCFA.Syntax`'s ANF λ^h calculus,
  used as the target of the LN equivalence proof (parallel to `LNBPSyntax`).

  Key design point: in ANF, every "name" introduced by a binder (let, lambda
  param, match-branch binder, recursive-function name, handler-clause binder)
  is replaced by a de Bruijn index `AExp.bvar`. The runtime environment `Env`
  (see `LNComponents`) becomes a *stack* of addresses (`List VAddr`): binding
  a variable is *pushing* an address, never overwriting an existing name, so
  there is no notion of "shadowing" or "freshness w.r.t. ρ's domain" at all.

  - `AExp.lam k e_body` binds `k` (the parameters = `bvar 0 .. bvar (k-1)` in
    `e_body`). The arity `k` is the de Bruijn analog of the named `lam`'s
    parameter *list* (a list of names collapses to its length once names become
    positions); the syntax is fully n-ary. B&P, being single-argument, only ever
    instantiates `k = 1` via the equivalence relation.
  - `CExp.funDef k e1` binds `k+1` in `e1` (`bvar 0 .. bvar (k-1)` = the
    function's `k` parameters, `bvar k` = the recursive name), mirroring
    `BP.Comp.letRec` (which uses `k = 1`).
  - `Exp.letE ce e cont` binds 1 in `cont` (`bvar 0` = the bound value).
  - `Branch.branch .succ e`: `e` binds 1 (`bvar 0` = the predecessor).
    All other constructor labels bind 0.
  - `Handler.returnClause` binds 1 (`bvar 0` = the returned value).
    Each op clause in `Handler.opClauses` binds 2 (`bvar 0` = the operation
    argument, `bvar 1` = the captured continuation `resume`).

  Since ANF terms are never substituted into (unlike `BP.Expr`/`BP.Comp`,
  which carry the actual values produced during evaluation), there is no
  `open_`/`openRec` machinery here -- only local-closedness (`lcAt`/`lc`),
  used as a well-formedness invariant in the equivalence relations.
-/

import DMCFA.Syntax

namespace DMCFA.LN

abbrev OpName := String

-- AExp, CExp, Exp, Branch, Handler are mutually recursive.
mutual

/-- Atomic expressions - can be evaluated without computation -/
inductive AExp where
  | bvar : Nat → AExp                     -- de Bruijn reference (also used for "Var"-position args)
  | lam : Nat → Exp → AExp                 -- fn(x̄) e_body, binds `arity` (de Bruijn analog of `List Var`)
  | con : ConLabel → AExp                  -- Constants
  | succE : AExp → AExp                    -- S(ae) - constructor applied to a variable reference

/-- Complex expressions - require computation -/
inductive CExp where
  | atomic : AExp → CExp                    -- Atomic in complex position
  | funApp : AExp → List AExp → CExp        -- f(aes) application - allocates fresh addresses
  | opApp : OpName → AExp → CExp            -- op(ae) operation application - store unchanged
  | matchE : AExp → List Branch → CExp      -- match(ae){b}
  | handler : Handler → Exp → Label → CExp  -- handler{h}(e_body) with label for handler frame
  | funDef : Nat → Exp → CExp               -- fun(x̄) e1 (recursive def; e1 binds arity+1: params then self)

/-- Top-level expressions (ANF) -/
inductive Exp where
  | letE : CExp → Exp → Label → Exp         -- let _ = ce; cont (cont binds 1)
  | tail : CExp → Label → Exp               -- ce in tail position, with label

/-- Match branches -/
inductive Branch where
  | branch : ConLabel → Exp → Branch        -- e binds 1 iff the label is `succ`, else 0

/-- Handler definition -/
structure Handler where
  returnClause : Exp                        -- return(_) e_ret, binds 1
  opClauses : List (OpName × Exp)           -- op(_; resume) e_op clauses, each binds 2 (bvar 0 = arg, bvar 1 = resume)

end

abbrev Branches := List Branch

instance : Inhabited AExp := ⟨AExp.con ConLabel.unit⟩

/-- Get the label from a let expression -/
def Exp.getLabel : Exp → Option Label
  | Exp.letE _ _ l => some l
  | _ => none

/-!
## Local closedness

`lcAt n t` holds when every `AExp.bvar i` occurring in `t` (outside of `t`'s
own binders) satisfies `i < n`. `lc := lcAt 0` means `t` is fully closed
w.r.t. de Bruijn indices (its only free references are via `Env`'s address
stack, which is not part of the syntax).
-/

mutual

@[grind =] def aexpLcAt (n : Nat) (ae : AExp) : Prop :=
  match ae with
  | .bvar i => i < n
  | .lam k e => expLcAt (n+k) e
  | .con _ => True
  | .succE ae => aexpLcAt n ae
termination_by sizeOf ae

@[grind =] def cexpLcAt (n : Nat) (ce : CExp) : Prop :=
  match ce with
  | .atomic ae => aexpLcAt n ae
  | .funApp f aes => aexpLcAt n f ∧ aexpListLcAt n aes
  | .opApp _ ae => aexpLcAt n ae
  | .matchE ae bs => aexpLcAt n ae ∧ branchesLcAt n bs
  | .handler ⟨ret, ops⟩ e _l_h => expLcAt (n+1) ret ∧ opsLcAt (n+1) ops ∧ expLcAt n e
  | .funDef k e1 => expLcAt (n+k+1) e1
termination_by sizeOf ce

@[grind =] def expLcAt (n : Nat) (e : Exp) : Prop :=
  match e with
  | .letE ce e2 _l => cexpLcAt n ce ∧ expLcAt (n+1) e2
  | .tail ce _l => cexpLcAt n ce
termination_by sizeOf e

@[grind =] def branchLcAt (n : Nat) (b : Branch) : Prop :=
  match b with
  | .branch .succ e => expLcAt (n+1) e
  | .branch _ e => expLcAt n e
termination_by sizeOf b

-- Explicit list recursion helpers (avoid inline lambdas; visible structural descent)
@[grind =] def aexpListLcAt (n : Nat) : List AExp → Prop
  | [] => True
  | ae :: rest => aexpLcAt n ae ∧ aexpListLcAt n rest
termination_by aes => sizeOf aes

@[grind =] def branchesLcAt (n : Nat) : List Branch → Prop
  | [] => True
  | b :: rest => branchLcAt n b ∧ branchesLcAt n rest
termination_by bs => sizeOf bs

@[grind =] def opsLcAt (n : Nat) : List (OpName × Exp) → Prop
  | [] => True
  | (_, e) :: rest => expLcAt (n+1) e ∧ opsLcAt n rest
termination_by ops => sizeOf ops

end

/-- An expression is locally closed (no loose `bvar`s) -/
@[grind =] def AExp.lc (ae : AExp) : Prop := aexpLcAt 0 ae
@[grind =] def CExp.lc (ce : CExp) : Prop := cexpLcAt 0 ce
@[grind =] def Exp.lc (e : Exp) : Prop := expLcAt 0 e
@[grind =] def Branch.lc (b : Branch) : Prop := branchLcAt 0 b
@[grind =] def Handler.lc (h : Handler) : Prop := expLcAt 1 h.returnClause ∧ opsLcAt 1 h.opClauses

end DMCFA.LN
