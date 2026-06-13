/-
  Bauer & Pretnar Syntax (locally nameless)

  This defines the syntax used in Bauer & Pretnar's substitution-based
  semantics, using a locally-nameless representation:
  - `Expr.bvar : Nat → Expr` is a bound variable (de Bruijn index)
  - `Expr.fvar : Var → Expr` is a free variable (atom)
  - Binder constructors no longer carry an explicit name; opening a binder
    (`open_`) instantiates index 0 (the innermost binder) with a term.
  - `Comp.letRec c1 c2`: `c1` binds 2 (index 0 = the function's own
    parameter, index 1 = the recursive name), `c2` binds 1 (index 0 = the
    recursive name).
  - `BPHandler.returnClause` binds 1 (index 0 = the returned value).
  - Each op clause in `BPHandler.opClauses` binds 2 (index 0 = the clause's
    argument, index 1 = the continuation `resume`). `resume` is an ordinary
    de Bruijn binder, like every other bound variable.
  - `Result.op op e c`: `c` is 1-open, with `bvar 0` standing for "the value
    the suspended computation should resume with".
-/

namespace DMCFA.BPLN

/-- Variable names (used only for free variables / atoms) -/
abbrev Var := String

/-- Operation names -/
abbrev OpName := String

-- Expr, Comp, and BPHandler are mutually recursive:
-- Expr.lam contains Comp; Comp.withHandle contains BPHandler; BPHandler contains Comp.
mutual

/-- Expressions (pure values) in B&P -/
inductive Expr where
  | bvar : Nat → Expr
  | fvar : Var → Expr
  | true_ : Expr
  | false_ : Expr
  | unit : Expr
  | zero : Expr
  | succ : Expr → Expr
  | lam : Comp → Expr                              -- binds 1 in its body

/-- Computations in B&P -/
inductive Comp where
  | val : Expr → Comp                              -- val e
  | app : Expr → Expr → Comp                       -- e1 e2
  | letIn : Comp → Comp → Comp                     -- let _ = c1 in c2 (c2 binds 1)
  | letRec : Comp → Comp → Comp                    -- let rec _ _ = c1 in c2
                                                    -- (c1 binds 2, c2 binds 1)
  | ifThenElse : Expr → Comp → Comp → Comp         -- if e then c1 else c2
  | matchNat : Expr → Comp → Comp → Comp           -- match e with 0 → c1 | succ _ → c2
                                                    -- (c2 binds 1)
  | withHandle : BPHandler → Comp → Comp           -- with h handle c
  | opCall : OpName → Expr → Comp                  -- op e

/-- Handler definition in B&P -/
structure BPHandler where
  returnClause : Comp                              -- val _ → c_ret (binds 1)
  opClauses : List (OpName × Comp)                 -- op(_; resume) → c_op (binds 2: bvar 0 = arg, bvar 1 = resume)

end

/-- Result of B&P computation -/
inductive Result where
  | value : Expr → Result                          -- val e
  | op : OpName → Expr → Comp → Result             -- # op e (c : 1-open, bvar 0 = resume slot)

/-!
## Opening

`open_ u t` instantiates the outermost bound variable (index 0) of `t` with
`u`. `compOpenRec k u c` / `exprOpenRec k u e` instantiate index `k`,
incrementing `k` as binders are entered.
-/

mutual

@[grind =] def exprOpenRec (k : Nat) (u : Expr) (e : Expr) : Expr :=
  match e with
  | .bvar i => if i = k then u else .bvar i
  | .fvar x => .fvar x
  | .true_ => .true_
  | .false_ => .false_
  | .unit => .unit
  | .zero => .zero
  | .succ e => .succ (exprOpenRec k u e)
  | .lam c => .lam (compOpenRec (k+1) u c)
termination_by sizeOf e

@[grind =] def compOpenRec (k : Nat) (u : Expr) (c : Comp) : Comp :=
  match c with
  | .val e => .val (exprOpenRec k u e)
  | .app e1 e2 => .app (exprOpenRec k u e1) (exprOpenRec k u e2)
  | .letIn c1 c2 => .letIn (compOpenRec k u c1) (compOpenRec (k+1) u c2)
  | .letRec c1 c2 => .letRec (compOpenRec (k+2) u c1) (compOpenRec (k+1) u c2)
  | .ifThenElse e c1 c2 =>
      .ifThenElse (exprOpenRec k u e) (compOpenRec k u c1) (compOpenRec k u c2)
  | .matchNat e c1 c2 =>
      .matchNat (exprOpenRec k u e) (compOpenRec k u c1) (compOpenRec (k+1) u c2)
  | .withHandle ⟨c_ret, ops⟩ c =>
      .withHandle ⟨compOpenRec (k+1) u c_ret, opsOpenRec (k+2) u ops⟩ (compOpenRec k u c)
  | .opCall op e => .opCall op (exprOpenRec k u e)
termination_by sizeOf c

-- Explicit list recursion so the termination checker sees structural descent
@[grind =] def opsOpenRec (k : Nat) (u : Expr) (ops : List (OpName × Comp)) : List (OpName × Comp) :=
  match ops with
  | [] => []
  | (op, c) :: rest => (op, compOpenRec k u c) :: opsOpenRec k u rest
termination_by sizeOf ops

end

/-- Open the outermost bound variable of an expression with `u` -/
@[grind =] def Expr.open_ (e : Expr) (u : Expr) : Expr := exprOpenRec 0 u e

/-- Open the outermost bound variable of a computation with `u` -/
@[grind =] def Comp.open_ (c : Comp) (u : Expr) : Comp := compOpenRec 0 u c

/-- Open the return-clause and every op-clause body of a handler (each binds 1) with `u` -/
@[grind =] def BPHandler.open1 (h : BPHandler) (u : Expr) : BPHandler :=
  ⟨compOpenRec 1 u h.returnClause, opsOpenRec 1 u h.opClauses⟩

@[simp, grind =] theorem Expr.open_bvar (i k : Nat) (u : Expr) :
    exprOpenRec k u (Expr.bvar i) = if i = k then u else .bvar i := by grind

@[simp, grind =] theorem Expr.open_fvar (x : Var) (k : Nat) (u : Expr) :
    exprOpenRec k u (Expr.fvar x) = Expr.fvar x := by grind

@[simp, grind =] theorem Expr.open_true (k : Nat) (u : Expr) :
    exprOpenRec k u Expr.true_ = Expr.true_ := by grind
@[simp, grind =] theorem Expr.open_false (k : Nat) (u : Expr) :
    exprOpenRec k u Expr.false_ = Expr.false_ := by grind
@[simp, grind =] theorem Expr.open_unit (k : Nat) (u : Expr) :
    exprOpenRec k u Expr.unit = Expr.unit := by grind
@[simp, grind =] theorem Expr.open_zero (k : Nat) (u : Expr) :
    exprOpenRec k u Expr.zero = Expr.zero := by grind

@[simp, grind =] theorem Expr.open_succ (e : Expr) (k : Nat) (u : Expr) :
    exprOpenRec k u (Expr.succ e) = Expr.succ (exprOpenRec k u e) := by grind

@[simp, grind =] theorem Expr.open_lam (c : Comp) (k : Nat) (u : Expr) :
    exprOpenRec k u (Expr.lam c) = Expr.lam (compOpenRec (k+1) u c) := by grind

@[simp, grind =] theorem Comp.open_val (e : Expr) (k : Nat) (u : Expr) :
    compOpenRec k u (Comp.val e) = Comp.val (exprOpenRec k u e) := by grind

@[simp, grind =] theorem Comp.open_app (e1 e2 : Expr) (k : Nat) (u : Expr) :
    compOpenRec k u (Comp.app e1 e2) = Comp.app (exprOpenRec k u e1) (exprOpenRec k u e2) := by grind

@[simp, grind =] theorem Comp.open_letIn (c1 c2 : Comp) (k : Nat) (u : Expr) :
    compOpenRec k u (Comp.letIn c1 c2) = Comp.letIn (compOpenRec k u c1) (compOpenRec (k+1) u c2) := by
  grind

@[simp, grind =] theorem Comp.open_letRec (c1 c2 : Comp) (k : Nat) (u : Expr) :
    compOpenRec k u (Comp.letRec c1 c2) = Comp.letRec (compOpenRec (k+2) u c1) (compOpenRec (k+1) u c2) := by
  grind

@[simp, grind =] theorem Comp.open_ifThenElse (e : Expr) (c1 c2 : Comp) (k : Nat) (u : Expr) :
    compOpenRec k u (Comp.ifThenElse e c1 c2) =
      Comp.ifThenElse (exprOpenRec k u e) (compOpenRec k u c1) (compOpenRec k u c2) := by grind

@[simp, grind =] theorem Comp.open_matchNat (e : Expr) (c1 c2 : Comp) (k : Nat) (u : Expr) :
    compOpenRec k u (Comp.matchNat e c1 c2) =
      Comp.matchNat (exprOpenRec k u e) (compOpenRec k u c1) (compOpenRec (k+1) u c2) := by grind

@[simp, grind =] theorem Comp.open_opCall (op : OpName) (e : Expr) (k : Nat) (u : Expr) :
    compOpenRec k u (Comp.opCall op e) = Comp.opCall op (exprOpenRec k u e) := by grind

@[simp, grind =] theorem Comp.open_withHandle (h : BPHandler) (c : Comp) (k : Nat) (u : Expr) :
    compOpenRec k u (Comp.withHandle h c) =
      Comp.withHandle ⟨compOpenRec (k+1) u h.returnClause, opsOpenRec (k+2) u h.opClauses⟩
        (compOpenRec k u c) := by
  obtain ⟨c_ret, ops⟩ := h; grind

@[simp, grind =] theorem BPHandler.open1_mk (c_ret : Comp) (ops : List (OpName × Comp)) (u : Expr) :
    BPHandler.open1 ⟨c_ret, ops⟩ u = ⟨compOpenRec 1 u c_ret, opsOpenRec 1 u ops⟩ := by grind

@[simp, grind =] theorem opsOpenRec_nil (k : Nat) (u : Expr) :
    opsOpenRec k u ([] : List (OpName × Comp)) = [] := by grind

@[simp, grind =] theorem opsOpenRec_cons (op : OpName) (c : Comp) (rest : List (OpName × Comp)) (k : Nat) (u : Expr) :
    opsOpenRec k u ((op, c) :: rest) = (op, compOpenRec k u c) :: opsOpenRec k u rest := by grind

/-!
## Free variables

Only `fvar` occurrences contribute; `bvar` indices never do. The literal
`"resume"` is filtered out of operation-clause bodies, as it is the one
remaining reserved free atom.
-/

mutual

@[grind =] private def exprFvs (e : Expr) : List Var :=
  match e with
  | .bvar _ => []
  | .fvar x => [x]
  | .true_ | .false_ | .unit | .zero => []
  | .succ e => exprFvs e
  | .lam c => compFvs c
termination_by sizeOf e

@[grind =] private def compFvs (c : Comp) : List Var :=
  match c with
  | .val e => exprFvs e
  | .app e1 e2 => exprFvs e1 ++ exprFvs e2
  | .letIn c1 c2 => compFvs c1 ++ compFvs c2
  | .letRec c1 c2 => compFvs c1 ++ compFvs c2
  | .ifThenElse e c1 c2 => exprFvs e ++ compFvs c1 ++ compFvs c2
  | .matchNat e c1 c2 => exprFvs e ++ compFvs c1 ++ compFvs c2
  | .withHandle ⟨c_ret, ops⟩ c => compFvs c_ret ++ opsFvs ops ++ compFvs c
  | .opCall _ e => exprFvs e
termination_by sizeOf c

-- Explicit list recursion so the termination checker sees structural descent
@[grind =] def opsFvs (ops : List (OpName × Comp)) : List Var :=
  match ops with
  | [] => []
  | (_, c) :: rest => compFvs c ++ opsFvs rest
termination_by sizeOf ops

end

/-- Free variables of an expression -/
@[grind =] def Expr.fvs : Expr → List Var := exprFvs

/-- Free variables of a computation -/
@[grind =] def Comp.fvs : Comp → List Var := compFvs

/-- Free variables of an operation clause list -/
@[grind =] def opClauses_fvs : List (OpName × Comp) → List Var := opsFvs

/-- Free variables of a handler -/
@[grind =] def BPHandler.fvs (h : BPHandler) : List Var :=
  Comp.fvs h.returnClause ++ opClauses_fvs h.opClauses

-- Simp lemmas for Expr.fvs / Comp.fvs (private WF defs don't unfold definitionally)
@[simp, grind =] theorem Expr.fvs_bvar (i : Nat) : (Expr.bvar i).fvs = [] := by
  show exprFvs _ = _; simp [exprFvs]
@[simp, grind =] theorem Expr.fvs_fvar (x : Var) : (Expr.fvar x).fvs = [x] := by
  show exprFvs _ = _; simp [exprFvs]
@[simp, grind =] theorem Expr.fvs_true : Expr.true_.fvs = [] := by
  show exprFvs _ = _; simp [exprFvs]
@[simp, grind =] theorem Expr.fvs_false : Expr.false_.fvs = [] := by
  show exprFvs _ = _; simp [exprFvs]
@[simp, grind =] theorem Expr.fvs_unit : Expr.unit.fvs = [] := by
  show exprFvs _ = _; simp [exprFvs]
@[simp, grind =] theorem Expr.fvs_zero : Expr.zero.fvs = [] := by
  show exprFvs _ = _; simp [exprFvs]
@[simp, grind =] theorem Expr.fvs_succ (e : Expr) : (Expr.succ e).fvs = e.fvs := by
  show exprFvs _ = _; simp [exprFvs, Expr.fvs]
@[simp, grind =] theorem Expr.fvs_lam (c : Comp) : (Expr.lam c).fvs = c.fvs := by
  show exprFvs _ = _; simp [exprFvs, Comp.fvs]

@[simp, grind =] theorem Comp.fvs_val (e : Expr) : (Comp.val e).fvs = e.fvs := by
  show compFvs _ = _; simp [compFvs, Expr.fvs]
@[simp, grind =] theorem Comp.fvs_app (e1 e2 : Expr) : (Comp.app e1 e2).fvs = e1.fvs ++ e2.fvs := by
  show compFvs _ = _; simp [compFvs, Expr.fvs]
@[simp, grind =] theorem Comp.fvs_opCall (op : OpName) (e : Expr) :
    (Comp.opCall op e).fvs = e.fvs := by
  show compFvs _ = _; simp [compFvs, Expr.fvs]
@[simp, grind =] theorem Comp.fvs_ifThenElse (e : Expr) (c1 c2 : Comp) :
    (Comp.ifThenElse e c1 c2).fvs = e.fvs ++ c1.fvs ++ c2.fvs := by
  show compFvs _ = _; simp [compFvs, Expr.fvs, Comp.fvs]
@[simp, grind =] theorem Comp.fvs_matchNat (e : Expr) (c1 c2 : Comp) :
    (Comp.matchNat e c1 c2).fvs = e.fvs ++ c1.fvs ++ c2.fvs := by
  show compFvs _ = _; simp [compFvs, Expr.fvs, Comp.fvs]
@[simp, grind =] theorem Comp.fvs_letIn (c1 c2 : Comp) :
    (Comp.letIn c1 c2).fvs = c1.fvs ++ c2.fvs := by
  show compFvs _ = _; simp [compFvs, Comp.fvs]
@[simp, grind =] theorem Comp.fvs_letRec (c1 c2 : Comp) :
    (Comp.letRec c1 c2).fvs = c1.fvs ++ c2.fvs := by
  show compFvs _ = _; simp [compFvs, Comp.fvs]

@[simp, grind =] theorem Comp.fvs_withHandle (h : BPHandler) (c : Comp) :
    (Comp.withHandle h c).fvs = h.returnClause.fvs ++ opClauses_fvs h.opClauses ++ c.fvs := by
  obtain ⟨c_ret, ops⟩ := h
  show compFvs _ = _; simp [compFvs, Comp.fvs, opClauses_fvs]

@[simp, grind =] theorem BPHandler.fvs_mk (c_ret : Comp) (ops : List (OpName × Comp)) :
    (BPHandler.mk c_ret ops).fvs = c_ret.fvs ++ opClauses_fvs ops := by
  simp [BPHandler.fvs, Comp.fvs]

@[simp, grind =] theorem opClauses_fvs_nil : opClauses_fvs ([] : List (OpName × Comp)) = [] := by
  show opsFvs _ = _; simp [opsFvs]

@[simp, grind =] theorem opClauses_fvs_cons (op : OpName) (c : Comp) (rest : List (OpName × Comp)) :
    opClauses_fvs ((op, c) :: rest) = c.fvs ++ opClauses_fvs rest := by
  show opsFvs _ = _; simp [opsFvs, Comp.fvs, opClauses_fvs]

/-!
## Free variables of opening

General property: fvs of (exprOpenRec k u e) ⊆ fvs(e) ∪ fvs(u). Opening only
ever replaces a `bvar`, which contributes nothing to `fvs`, with `u`.
-/

mutual
@[grind ->] private theorem expr_fvs_open_sub :
    ∀ (e : Expr) (k : Nat) (u : Expr) (v : Var),
      v ∈ exprFvs (exprOpenRec k u e) → v ∈ exprFvs e ∨ v ∈ exprFvs u
  | .bvar i, k, u, v, h => by
      simp only [exprOpenRec] at h
      split at h
      · exact Or.inr h
      · simp [exprFvs] at h
  | .fvar y, _, _, _, h => by simp only [exprOpenRec, exprFvs] at h ⊢; exact Or.inl h
  | .true_, _, _, _, h => by simp [exprFvs] at h
  | .false_, _, _, _, h => by simp [exprFvs] at h
  | .unit, _, _, _, h => by simp [exprFvs] at h
  | .zero, _, _, _, h => by simp [exprFvs] at h
  | .succ e, k, u, v, h => by
      simp only [exprOpenRec, exprFvs] at h ⊢
      exact expr_fvs_open_sub e k u v h
  | .lam c, k, u, v, h => by
      simp only [exprOpenRec, exprFvs] at h ⊢
      exact comp_fvs_open_sub c (k+1) u v h

@[grind ->] private theorem comp_fvs_open_sub :
    ∀ (c : Comp) (k : Nat) (u : Expr) (v : Var),
      v ∈ compFvs (compOpenRec k u c) → v ∈ compFvs c ∨ v ∈ exprFvs u
  | .val e, k, u, v, h => by
      simp only [compOpenRec, compFvs] at h ⊢
      exact expr_fvs_open_sub e k u v h
  | .app e1 e2, k, u, v, h => by
      simp only [compOpenRec, compFvs, List.mem_append] at h ⊢
      rcases h with h1 | h2
      · rcases expr_fvs_open_sub e1 k u v h1 with he | he'
        · exact Or.inl (Or.inl he)
        · exact Or.inr he'
      · rcases expr_fvs_open_sub e2 k u v h2 with he | he'
        · exact Or.inl (Or.inr he)
        · exact Or.inr he'
  | .opCall op e, k, u, v, h => by
      simp only [compOpenRec, compFvs] at h ⊢
      exact expr_fvs_open_sub e k u v h
  | .ifThenElse e c1 c2, k, u, v, h => by
      simp only [compOpenRec, compFvs, List.mem_append] at h ⊢
      rcases h with (h1 | h2) | h3
      · rcases expr_fvs_open_sub e k u v h1 with he | he'
        · exact Or.inl (Or.inl (Or.inl he))
        · exact Or.inr he'
      · rcases comp_fvs_open_sub c1 k u v h2 with hc | he'
        · exact Or.inl (Or.inl (Or.inr hc))
        · exact Or.inr he'
      · rcases comp_fvs_open_sub c2 k u v h3 with hc | he'
        · exact Or.inl (Or.inr hc)
        · exact Or.inr he'
  | .matchNat e c1 c2, k, u, v, h => by
      simp only [compOpenRec, compFvs, List.mem_append] at h ⊢
      rcases h with (h1 | h2) | h3
      · rcases expr_fvs_open_sub e k u v h1 with he | he'
        · exact Or.inl (Or.inl (Or.inl he))
        · exact Or.inr he'
      · rcases comp_fvs_open_sub c1 k u v h2 with hc | he'
        · exact Or.inl (Or.inl (Or.inr hc))
        · exact Or.inr he'
      · rcases comp_fvs_open_sub c2 (k+1) u v h3 with hc | he'
        · exact Or.inl (Or.inr hc)
        · exact Or.inr he'
  | .letIn c1 c2, k, u, v, h => by
      simp only [compOpenRec, compFvs, List.mem_append] at h ⊢
      rcases h with h1 | h2
      · rcases comp_fvs_open_sub c1 k u v h1 with hc | he'
        · exact Or.inl (Or.inl hc)
        · exact Or.inr he'
      · rcases comp_fvs_open_sub c2 (k+1) u v h2 with hc | he'
        · exact Or.inl (Or.inr hc)
        · exact Or.inr he'
  | .letRec c1 c2, k, u, v, h => by
      simp only [compOpenRec, compFvs, List.mem_append] at h ⊢
      rcases h with h1 | h2
      · rcases comp_fvs_open_sub c1 (k+2) u v h1 with hc | he'
        · exact Or.inl (Or.inl hc)
        · exact Or.inr he'
      · rcases comp_fvs_open_sub c2 (k+1) u v h2 with hc | he'
        · exact Or.inl (Or.inr hc)
        · exact Or.inr he'
  | .withHandle ⟨c_ret, ops⟩ c, k, u, v, h => by
      simp only [compOpenRec, compFvs, List.mem_append] at h ⊢
      rcases h with (h1 | h2) | h3
      · rcases comp_fvs_open_sub c_ret (k+1) u v h1 with hc | he'
        · exact Or.inl (Or.inl (Or.inl hc))
        · exact Or.inr he'
      · rcases ops_fvs_open_sub ops (k+2) u v h2 with ho | he'
        · exact Or.inl (Or.inl (Or.inr ho))
        · exact Or.inr he'
      · rcases comp_fvs_open_sub c k u v h3 with hc | he'
        · exact Or.inl (Or.inr hc)
        · exact Or.inr he'

@[grind ->] private theorem ops_fvs_open_sub :
    ∀ (ops : List (OpName × Comp)) (k : Nat) (u : Expr) (v : Var),
      v ∈ opsFvs (opsOpenRec k u ops) → v ∈ opsFvs ops ∨ v ∈ exprFvs u
  | [], _, _, _, h => by simp [opsFvs] at h
  | (op, c) :: rest, k, u, v, h => by
      simp only [opsOpenRec_cons, opsFvs, List.mem_append] at h ⊢
      rcases h with h1 | h2
      · rcases comp_fvs_open_sub c k u v h1 with hc | he'
        · exact Or.inl (Or.inl hc)
        · exact Or.inr he'
      · rcases ops_fvs_open_sub rest k u v h2 with ho | he'
        · exact Or.inl (Or.inr ho)
        · exact Or.inr he'
end -- mutual fvs_open_sub

/-- comp_fvs_open_sub with public API types -/
theorem Comp.fvs_open_sub {c : Comp} {k : Nat} {u : Expr} {v : Var} :
    v ∈ (compOpenRec k u c).fvs → v ∈ c.fvs ∨ v ∈ u.fvs :=
  comp_fvs_open_sub c k u v

/-- Opening a closed computation with a closed expression yields a closed computation -/
theorem Comp.fvs_open_closed {c : Comp} {k : Nat} {u : Expr}
    (hc : c.fvs = []) (hu : u.fvs = []) : (compOpenRec k u c).fvs = [] := by
  match h : compFvs (compOpenRec k u c) with
  | [] => exact h
  | v :: rest =>
    exfalso
    have hv : v ∈ compFvs (compOpenRec k u c) := by rw [h]; simp
    rcases Comp.fvs_open_sub hv with hc' | hu'
    · rw [hc] at hc'; simp at hc'
    · rw [hu] at hu'; simp at hu'

/-!
## Local closedness

`lcAt n t` holds when every loose bound variable in `t` has index `< n`
(i.e. `t` is "n-open at most"). `Expr.lc`/`Comp.lc` are the `n = 0` case
(fully locally closed: no loose bound variables at all).

The key consequence: opening at any depth `k ≥ n` is the identity on a term
satisfying `lcAt n`. This is what lets the `var_subst` case of the
substitution/opening lemmas go through: a value `e_bp` with `e_bp.fvs = []`
that arises from `ValueEquiv` is fully locally closed (`Expr.lc e_bp`), so
`exprOpenRec k u e_bp = e_bp` for every `k`.
-/

mutual

@[grind =] def exprLcAt (n : Nat) (e : Expr) : Prop :=
  match e with
  | .bvar i => i < n
  | .fvar _ => True
  | .true_ | .false_ | .unit | .zero => True
  | .succ e => exprLcAt n e
  | .lam c => compLcAt (n+1) c
termination_by sizeOf e

@[grind =] def compLcAt (n : Nat) (c : Comp) : Prop :=
  match c with
  | .val e => exprLcAt n e
  | .app e1 e2 => exprLcAt n e1 ∧ exprLcAt n e2
  | .letIn c1 c2 => compLcAt n c1 ∧ compLcAt (n+1) c2
  | .letRec c1 c2 => compLcAt (n+2) c1 ∧ compLcAt (n+1) c2
  | .ifThenElse e c1 c2 => exprLcAt n e ∧ compLcAt n c1 ∧ compLcAt n c2
  | .matchNat e c1 c2 => exprLcAt n e ∧ compLcAt n c1 ∧ compLcAt (n+1) c2
  | .withHandle ⟨c_ret, ops⟩ c => compLcAt (n+1) c_ret ∧ opsLcAt (n+2) ops ∧ compLcAt n c
  | .opCall _ e => exprLcAt n e
termination_by sizeOf c

@[grind =] def opsLcAt (n : Nat) (ops : List (OpName × Comp)) : Prop :=
  match ops with
  | [] => True
  | (_, c) :: rest => compLcAt n c ∧ opsLcAt n rest
termination_by sizeOf ops

end

/-- Fully locally closed: no loose bound variables at all -/
def Expr.lc (e : Expr) : Prop := exprLcAt 0 e

/-- Fully locally closed: no loose bound variables at all -/
def Comp.lc (c : Comp) : Prop := compLcAt 0 c

mutual

theorem expr_open_lc_at :
    ∀ (e : Expr) (n k : Nat) (u : Expr), exprLcAt n e → n ≤ k → exprOpenRec k u e = e
  | .bvar i, n, k, u, h, hnk => by
      simp only [exprLcAt] at h
      have : i ≠ k := by omega
      simp [this]
  | .fvar _, _, _, _, _, _ => by simp
  | .true_, _, _, _, _, _ => by simp
  | .false_, _, _, _, _, _ => by simp
  | .unit, _, _, _, _, _ => by simp
  | .zero, _, _, _, _, _ => by simp
  | .succ e, n, k, u, h, hnk => by
      simp only [exprLcAt] at h
      simp only [exprOpenRec, expr_open_lc_at e n k u h hnk]
  | .lam c, n, k, u, h, hnk => by
      simp only [exprLcAt] at h
      simp only [exprOpenRec, comp_open_lc_at c (n+1) (k+1) u h (by omega)]

theorem comp_open_lc_at :
    ∀ (c : Comp) (n k : Nat) (u : Expr), compLcAt n c → n ≤ k → compOpenRec k u c = c
  | .val e, n, k, u, h, hnk => by
      simp only [compLcAt] at h
      simp only [compOpenRec, expr_open_lc_at e n k u h hnk]
  | .app e1 e2, n, k, u, h, hnk => by
      simp only [compLcAt] at h
      simp only [compOpenRec, expr_open_lc_at e1 n k u h.1 hnk, expr_open_lc_at e2 n k u h.2 hnk]
  | .letIn c1 c2, n, k, u, h, hnk => by
      simp only [compLcAt] at h
      simp only [compOpenRec, comp_open_lc_at c1 n k u h.1 hnk,
        comp_open_lc_at c2 (n+1) (k+1) u h.2 (by omega)]
  | .letRec c1 c2, n, k, u, h, hnk => by
      simp only [compLcAt] at h
      simp only [compOpenRec, comp_open_lc_at c1 (n+2) (k+2) u h.1 (by omega),
        comp_open_lc_at c2 (n+1) (k+1) u h.2 (by omega)]
  | .ifThenElse e c1 c2, n, k, u, h, hnk => by
      simp only [compLcAt] at h
      simp only [compOpenRec, expr_open_lc_at e n k u h.1 hnk,
        comp_open_lc_at c1 n k u h.2.1 hnk, comp_open_lc_at c2 n k u h.2.2 hnk]
  | .matchNat e c1 c2, n, k, u, h, hnk => by
      simp only [compLcAt] at h
      simp only [compOpenRec, expr_open_lc_at e n k u h.1 hnk,
        comp_open_lc_at c1 n k u h.2.1 hnk, comp_open_lc_at c2 (n+1) (k+1) u h.2.2 (by omega)]
  | .withHandle ⟨c_ret, ops⟩ c, n, k, u, h, hnk => by
      simp only [compLcAt] at h
      simp only [compOpenRec, comp_open_lc_at c_ret (n+1) (k+1) u h.1 (by omega),
        ops_open_lc_at ops (n+2) (k+2) u h.2.1 (by omega), comp_open_lc_at c n k u h.2.2 hnk]
  | .opCall op e, n, k, u, h, hnk => by
      simp only [compLcAt] at h
      simp only [compOpenRec, expr_open_lc_at e n k u h hnk]

theorem ops_open_lc_at :
    ∀ (ops : List (OpName × Comp)) (n k : Nat) (u : Expr), opsLcAt n ops → n ≤ k → opsOpenRec k u ops = ops
  | [], _, _, _, _, _ => by simp
  | (op, c) :: rest, n, k, u, h, hnk => by
      simp only [opsLcAt] at h
      rw [opsOpenRec_cons, comp_open_lc_at c n k u h.1 hnk,
        ops_open_lc_at rest n k u h.2 hnk]

end

/-- Opening a fully locally closed expression at any depth is the identity -/
theorem Expr.open_of_lc {e : Expr} (h : e.lc) (k : Nat) (u : Expr) :
    exprOpenRec k u e = e :=
  expr_open_lc_at e 0 k u h (Nat.zero_le k)

/-- Opening a fully locally closed computation at any depth is the identity -/
theorem Comp.open_of_lc {c : Comp} (h : c.lc) (k : Nat) (u : Expr) :
    compOpenRec k u c = c :=
  comp_open_lc_at c 0 k u h (Nat.zero_le k)

/-! ## Opening at distinct depths commutes (for locally closed instantiations)

Used to instantiate a `letRec` body's two binders (`bvar 0` = own param,
`bvar 1` = recursive name) with two closed values in either order. -/

mutual

theorem expr_openRec_comm {u u' : Expr} (hu : u.lc) (hu' : u'.lc) :
    ∀ (e : Expr) (j k : Nat), j ≠ k →
      exprOpenRec j u (exprOpenRec k u' e) = exprOpenRec k u' (exprOpenRec j u e)
  | .bvar i, j, k, hjk => by
      by_cases hik : i = k
      · by_cases hij : i = j
        · exact absurd (hik ▸ hij : k = j) (Ne.symm hjk)
        · simp [hik, Ne.symm hjk, Expr.open_of_lc hu' j u]
      · by_cases hij : i = j
        · simp [hij, hjk, Expr.open_of_lc hu k u']
        · simp [hik, hij]
  | .fvar _, _, _, _ => by simp
  | .true_, _, _, _ => by simp
  | .false_, _, _, _ => by simp
  | .unit, _, _, _ => by simp
  | .zero, _, _, _ => by simp
  | .succ e, j, k, hjk => by
      simp only [Expr.open_succ, expr_openRec_comm hu hu' e j k hjk]
  | .lam c, j, k, hjk => by
      simp only [Expr.open_lam, comp_openRec_comm hu hu' c (j+1) (k+1) (by omega)]

theorem comp_openRec_comm {u u' : Expr} (hu : u.lc) (hu' : u'.lc) :
    ∀ (c : Comp) (j k : Nat), j ≠ k →
      compOpenRec j u (compOpenRec k u' c) = compOpenRec k u' (compOpenRec j u c)
  | .val e, j, k, hjk => by
      simp only [Comp.open_val, expr_openRec_comm hu hu' e j k hjk]
  | .app e1 e2, j, k, hjk => by
      simp only [Comp.open_app, expr_openRec_comm hu hu' e1 j k hjk,
        expr_openRec_comm hu hu' e2 j k hjk]
  | .letIn c1 c2, j, k, hjk => by
      simp only [Comp.open_letIn, comp_openRec_comm hu hu' c1 j k hjk,
        comp_openRec_comm hu hu' c2 (j+1) (k+1) (by omega)]
  | .letRec c1 c2, j, k, hjk => by
      simp only [Comp.open_letRec, comp_openRec_comm hu hu' c1 (j+2) (k+2) (by omega),
        comp_openRec_comm hu hu' c2 (j+1) (k+1) (by omega)]
  | .ifThenElse e c1 c2, j, k, hjk => by
      simp only [Comp.open_ifThenElse, expr_openRec_comm hu hu' e j k hjk,
        comp_openRec_comm hu hu' c1 j k hjk, comp_openRec_comm hu hu' c2 j k hjk]
  | .matchNat e c1 c2, j, k, hjk => by
      simp only [Comp.open_matchNat, expr_openRec_comm hu hu' e j k hjk,
        comp_openRec_comm hu hu' c1 j k hjk, comp_openRec_comm hu hu' c2 (j+1) (k+1) (by omega)]
  | .withHandle ⟨c_ret, ops⟩ c, j, k, hjk => by
      simp only [Comp.open_withHandle, comp_openRec_comm hu hu' c_ret (j+1) (k+1) (by omega),
        ops_openRec_comm hu hu' ops (j+2) (k+2) (by omega), comp_openRec_comm hu hu' c j k hjk]
  | .opCall op e, j, k, hjk => by
      simp only [Comp.open_opCall, expr_openRec_comm hu hu' e j k hjk]

theorem ops_openRec_comm {u u' : Expr} (hu : u.lc) (hu' : u'.lc) :
    ∀ (ops : List (OpName × Comp)) (j k : Nat), j ≠ k →
      opsOpenRec j u (opsOpenRec k u' ops) = opsOpenRec k u' (opsOpenRec j u ops)
  | [], _, _, _ => by simp
  | (op, c) :: rest, j, k, hjk => by
      simp only [opsOpenRec_cons, comp_openRec_comm hu hu' c j k hjk,
        ops_openRec_comm hu hu' rest j k hjk]

end -- mutual openRec_comm

/-- Opening a `letRec` body's two binders (`bvar 0` = own param, `bvar 1` =
    recursive name) with two locally closed terms commutes. -/
theorem Comp.open_open_comm {u u' : Expr} (hu : u.lc) (hu' : u'.lc) (c : Comp) :
    compOpenRec 0 u (compOpenRec 1 u' c) = compOpenRec 1 u' (compOpenRec 0 u c) :=
  comp_openRec_comm hu hu' c 0 1 (by omega)

/-! ## Monotonicity of `lcAt` -/

mutual

theorem exprLcAt_mono : ∀ (e : Expr) (n m : Nat), exprLcAt n e → n ≤ m → exprLcAt m e
  | .bvar i, n, m, h, hnm => by simp only [exprLcAt] at h ⊢; omega
  | .fvar _, _, _, _, _ => by simp [exprLcAt]
  | .true_, _, _, _, _ => by simp [exprLcAt]
  | .false_, _, _, _, _ => by simp [exprLcAt]
  | .unit, _, _, _, _ => by simp [exprLcAt]
  | .zero, _, _, _, _ => by simp [exprLcAt]
  | .succ e, n, m, h, hnm => by
      simp only [exprLcAt] at h ⊢; exact exprLcAt_mono e n m h hnm
  | .lam c, n, m, h, hnm => by
      simp only [exprLcAt] at h ⊢; exact compLcAt_mono c (n+1) (m+1) h (by omega)

theorem compLcAt_mono : ∀ (c : Comp) (n m : Nat), compLcAt n c → n ≤ m → compLcAt m c
  | .val e, n, m, h, hnm => by
      simp only [compLcAt] at h ⊢; exact exprLcAt_mono e n m h hnm
  | .app e1 e2, n, m, h, hnm => by
      simp only [compLcAt] at h ⊢
      exact ⟨exprLcAt_mono e1 n m h.1 hnm, exprLcAt_mono e2 n m h.2 hnm⟩
  | .letIn c1 c2, n, m, h, hnm => by
      simp only [compLcAt] at h ⊢
      exact ⟨compLcAt_mono c1 n m h.1 hnm, compLcAt_mono c2 (n+1) (m+1) h.2 (by omega)⟩
  | .letRec c1 c2, n, m, h, hnm => by
      simp only [compLcAt] at h ⊢
      exact ⟨compLcAt_mono c1 (n+2) (m+2) h.1 (by omega), compLcAt_mono c2 (n+1) (m+1) h.2 (by omega)⟩
  | .ifThenElse e c1 c2, n, m, h, hnm => by
      simp only [compLcAt] at h ⊢
      exact ⟨exprLcAt_mono e n m h.1 hnm, compLcAt_mono c1 n m h.2.1 hnm, compLcAt_mono c2 n m h.2.2 hnm⟩
  | .matchNat e c1 c2, n, m, h, hnm => by
      simp only [compLcAt] at h ⊢
      exact ⟨exprLcAt_mono e n m h.1 hnm, compLcAt_mono c1 n m h.2.1 hnm,
        compLcAt_mono c2 (n+1) (m+1) h.2.2 (by omega)⟩
  | .withHandle ⟨c_ret, ops⟩ c, n, m, h, hnm => by
      simp only [compLcAt] at h ⊢
      exact ⟨compLcAt_mono c_ret (n+1) (m+1) h.1 (by omega), opsLcAt_mono ops (n+2) (m+2) h.2.1 (by omega),
        compLcAt_mono c n m h.2.2 hnm⟩
  | .opCall op e, n, m, h, hnm => by
      simp only [compLcAt] at h ⊢; exact exprLcAt_mono e n m h hnm

theorem opsLcAt_mono : ∀ (ops : List (OpName × Comp)) (n m : Nat), opsLcAt n ops → n ≤ m → opsLcAt m ops
  | [], _, _, _, _ => by simp [opsLcAt]
  | (_, c) :: rest, n, m, h, hnm => by
      simp only [opsLcAt] at h ⊢
      exact ⟨compLcAt_mono c n m h.1 hnm, opsLcAt_mono rest n m h.2 hnm⟩

end

end DMCFA.BPLN
