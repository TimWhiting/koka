/-
  Bauer & Pretnar Syntax

  This defines the syntax used in Bauer & Pretnar's substitution-based semantics.
  Key differences from our ANF syntax:
  - Uses syntactic substitution instead of environments
  - Computations (c) vs expressions (e)
  - Explicit continuation variables (x_c) in operation results
-/

namespace DMCFA.BP

/-- Variable names -/
abbrev Var := String

/-- Operation names -/
abbrev OpName := String

-- Expr, Comp, and BPHandler are mutually recursive:
-- Expr.lam contains Comp; Comp.withHandle contains BPHandler; BPHandler contains Comp.
mutual

/-- Expressions (pure values) in B&P -/
inductive Expr where
  | var : Var → Expr
  | true_ : Expr
  | false_ : Expr
  | unit : Expr
  | zero : Expr
  | succ : Expr → Expr
  | lam : Var → Comp → Expr

/-- Computations in B&P -/
inductive Comp where
  | val : Expr → Comp                              -- val e
  | app : Expr → Expr → Comp                       -- e1 e2
  | letIn : Var → Comp → Comp → Comp               -- let x = c1 in c2
  | letRec : Var → Var → Comp → Comp → Comp        -- let rec f x = c1 in c2
  | ifThenElse : Expr → Comp → Comp → Comp         -- if e then c1 else c2
  | matchNat : Expr → Comp → Var → Comp → Comp     -- match e with 0 → c1 | succ x → c2
  | withHandle : BPHandler → Comp → Comp           -- with h handle c
  | opCall : OpName → Expr → Comp                  -- op e

/-- Handler definition in B&P -/
structure BPHandler where
  returnClause : Var × Comp                        -- val x → c_ret
  opClauses : List (OpName × Var × Comp)           -- op(x) → c_op with implicit resume

end

/-- Result of B&P computation -/
inductive Result where
  | value : Expr → Result                          -- val e
  | op : OpName → Expr → Var → Comp → Result       -- # op e (x_c. c)

/-!
## Free variables

Mutually recursive with `termination_by sizeOf`. List cases use explicit
recursive helpers (`opsFvs`) instead of inline `flatMap` lambdas so the
termination checker can see the structural descent directly.
-/

mutual

@[grind =] private def exprFvs : Expr → List Var
  | .var x => [x]
  | .true_ | .false_ | .unit | .zero => []
  | .succ e => exprFvs e
  | .lam x c => (compFvs c).filter (· ≠ x)
termination_by e => sizeOf e

@[grind =] private def compFvs : Comp → List Var
  | .val e => exprFvs e
  | .app e1 e2 => exprFvs e1 ++ exprFvs e2
  | .letIn x c1 c2 => compFvs c1 ++ (compFvs c2).filter (· ≠ x)
  | .letRec f x c1 c2 =>
      (compFvs c1).filter (fun v => v ≠ f && v ≠ x) ++ (compFvs c2).filter (· ≠ f)
  | .ifThenElse e c1 c2 => exprFvs e ++ compFvs c1 ++ compFvs c2
  | .matchNat e c1 x c2 => exprFvs e ++ compFvs c1 ++ (compFvs c2).filter (· ≠ x)
  | .withHandle ⟨(x_ret, c_ret), ops⟩ c =>
      (compFvs c_ret).filter (· ≠ x_ret) ++
      opsFvs ops ++
      compFvs c
  | .opCall _ e => exprFvs e
termination_by c => sizeOf c

-- Explicit list recursion so the termination checker sees structural descent
@[grind =] def opsFvs : List (OpName × Var × Comp) → List Var
  | [] => []
  | (_, x, c) :: rest =>
      (compFvs c).filter (fun v => v ≠ x && v ≠ "resume") ++ opsFvs rest
termination_by ops => sizeOf ops

end

/-- Free variables of an expression -/
@[grind =] def Expr.fvs : Expr → List Var := exprFvs

/-- Free variables of a computation -/
@[grind =]def Comp.fvs : Comp → List Var := compFvs

/-- Free variables of a handler -/
@[grind =]def BPHandler.fvs (h : BPHandler) : List Var :=
  let (x_ret, c_ret) := h.returnClause
  (Comp.fvs c_ret).filter (· ≠ x_ret) ++
  h.opClauses.flatMap fun (_, x, c) => (Comp.fvs c).filter (fun v => v ≠ x && v ≠ "resume")

-- Simp lemmas for Expr.fvs / Comp.fvs (private WF defs don't unfold definitionally)
@[simp] theorem Expr.fvs_var : (Expr.var x).fvs = [x] := by
  show exprFvs _ = _; simp [exprFvs]
@[simp] theorem Expr.fvs_true : Expr.true_.fvs = [] := by
  show exprFvs _ = _; simp [exprFvs]
@[simp] theorem Expr.fvs_false : Expr.false_.fvs = [] := by
  show exprFvs _ = _; simp [exprFvs]
@[simp] theorem Expr.fvs_unit : Expr.unit.fvs = [] := by
  show exprFvs _ = _; simp [exprFvs]
@[simp] theorem Expr.fvs_zero : Expr.zero.fvs = [] := by
  show exprFvs _ = _; simp [exprFvs]
@[simp] theorem Expr.fvs_succ : (Expr.succ e).fvs = e.fvs := by
  show exprFvs _ = _; simp [exprFvs, Expr.fvs]
@[simp] theorem Expr.fvs_lam : (Expr.lam x c).fvs = c.fvs.filter (· ≠ x) := by
  show exprFvs _ = _; simp [exprFvs, Comp.fvs]

@[simp] theorem Comp.fvs_val : (Comp.val e).fvs = e.fvs := by
  show compFvs _ = _; simp [compFvs, Expr.fvs]
@[simp] theorem Comp.fvs_app : (Comp.app e1 e2).fvs = e1.fvs ++ e2.fvs := by
  show compFvs _ = _; simp [compFvs, Expr.fvs]
@[simp] theorem Comp.fvs_opCall : (Comp.opCall op e).fvs = e.fvs := by
  show compFvs _ = _; simp [compFvs, Expr.fvs]
@[simp] theorem Comp.fvs_ifThenElse : (Comp.ifThenElse e c1 c2).fvs = e.fvs ++ c1.fvs ++ c2.fvs := by
  show compFvs _ = _; simp [compFvs, Expr.fvs, Comp.fvs]
@[simp] theorem Comp.fvs_matchNat : (Comp.matchNat e c1 x c2).fvs = e.fvs ++ c1.fvs ++ (c2.fvs).filter (· ≠ x) := by
  show compFvs _ = _; simp [compFvs, Expr.fvs, Comp.fvs]
@[simp] theorem Comp.fvs_letIn : (Comp.letIn x c1 c2).fvs = c1.fvs ++ (c2.fvs).filter (· ≠ x) := by
  show compFvs _ = _; simp [compFvs, Comp.fvs]
@[simp] theorem Comp.fvs_letRec : (Comp.letRec f x c1 c2).fvs = (c1.fvs).filter (fun v => v ≠ f && v ≠ x) ++ (c2.fvs).filter (· ≠ f) := by
  show compFvs _ = _; simp [compFvs, Comp.fvs]

@[grind =]theorem Comp.fvs_withHandle (hdl : BPHandler) (c : Comp) :
    (Comp.withHandle hdl c).fvs =
      (hdl.returnClause.2.fvs).filter (· ≠ hdl.returnClause.1) ++
      opsFvs hdl.opClauses ++ c.fvs := by
  obtain ⟨⟨x_ret, c_ret⟩, ops⟩ := hdl
  show compFvs _ = _; simp [compFvs, Comp.fvs]

/-!
## Substitution

Mutual recursion with `termination_by sizeOf`. The `withHandle` case uses an
explicit `opsSubst` list helper (instead of an inline `map` lambda) so the
termination checker can verify structural descent directly.
-/

mutual

@[grind =]private def exprSubst (e : Expr) (x : Var) (e' : Expr) : Expr :=
  match e with
  | .var y => if y = x then e' else .var y
  | .true_ => .true_
  | .false_ => .false_
  | .unit => .unit
  | .zero => .zero
  | .succ e1 => .succ (exprSubst e1 x e')
  | .lam y c => if y = x then .lam y c else .lam y (compSubst c x e')
termination_by sizeOf e

@[grind =]private def compSubst (c : Comp) (x : Var) (e' : Expr) : Comp :=
  match c with
  | .val e => .val (exprSubst e x e')
  | .app e1 e2 => .app (exprSubst e1 x e') (exprSubst e2 x e')
  | .letIn y c1 c2 =>
      if y = x then .letIn y (compSubst c1 x e') c2
      else .letIn y (compSubst c1 x e') (compSubst c2 x e')
  | .letRec f y c1 c2 =>
      let c1' := if x = f || x = y then c1 else compSubst c1 x e'
      let c2' := if x = f then c2 else compSubst c2 x e'
      .letRec f y c1' c2'
  | .ifThenElse e c1 c2 =>
      .ifThenElse (exprSubst e x e') (compSubst c1 x e') (compSubst c2 x e')
  | .matchNat e c1 y c2 =>
      .matchNat (exprSubst e x e') (compSubst c1 x e')
        y (if y = x then c2 else compSubst c2 x e')
  | .withHandle ⟨(x_ret, c_ret), ops⟩ c =>
      let c_ret' := if x_ret = x then c_ret else compSubst c_ret x e'
      .withHandle ⟨(x_ret, c_ret'), opsSubst x e' ops⟩ (compSubst c x e')
  | .opCall op e => .opCall op (exprSubst e x e')
termination_by sizeOf c

-- Explicit list recursion so the termination checker sees structural descent
@[grind =] private def opsSubst (x : Var) (e' : Expr) : List (OpName × Var × Comp) → List (OpName × Var × Comp)
  | [] => []
  | (op, y, c) :: rest =>
      (op, y, if y = x || "resume" = x then c else compSubst c x e') :: opsSubst x e' rest
termination_by ops => sizeOf ops

end

/-- Substitution in expressions: e[e'/x] -/
@[grind =] def Expr.subst (e : Expr) (x : Var) (e' : Expr) : Expr := exprSubst e x e'

/-- Substitution in computations: c[e'/x] -/
@[grind =] def Comp.subst (c : Comp) (x : Var) (e' : Expr) : Comp := compSubst c x e'

/-!
## Simp Lemmas for Substitution

Expose key reduction equations so that proofs in other files can use simp.
-/

@[simp, grind =] theorem Expr.subst_var_self (x : Var) (e : Expr) :
    Expr.subst (Expr.var x) x e = e := by grind

@[simp, grind =] theorem Expr.subst_var_ne {y x : Var} (h : y ≠ x) (e : Expr) :
    Expr.subst (Expr.var y) x e = Expr.var y := by grind

@[simp, grind =] theorem Expr.subst_true (x : Var) (e : Expr) : Expr.subst Expr.true_ x e = Expr.true_ := by grind

@[simp, grind =] theorem Expr.subst_false (x : Var) (e : Expr) : Expr.subst Expr.false_ x e = Expr.false_ := by grind

@[simp, grind =] theorem Expr.subst_unit (x : Var) (e : Expr) : Expr.subst Expr.unit x e = Expr.unit := by grind

@[simp, grind =] theorem Expr.subst_zero (x : Var) (e : Expr) : Expr.subst Expr.zero x e = Expr.zero := by grind

@[simp, grind =] theorem Expr.subst_succ (e_inner : Expr) (x : Var) (e_sub : Expr) :
    Expr.subst (Expr.succ e_inner) x e_sub = Expr.succ (Expr.subst e_inner x e_sub) := by grind

@[simp, grind =]theorem Expr.subst_lam_self (z : Var) (c : Comp) (e : Expr) :
    Expr.subst (Expr.lam z c) z e = Expr.lam z c := by grind

@[simp, grind =]theorem Expr.subst_lam_ne {z x : Var} (h : z ≠ x) (c : Comp) (e : Expr) :
    Expr.subst (Expr.lam z c) x e = Expr.lam z (Comp.subst c x e) := by grind

@[simp, grind =] theorem Comp.subst_val (e : Expr) (x : Var) (e' : Expr) :
    Comp.subst (Comp.val e) x e' = Comp.val (Expr.subst e x e') := by grind

@[simp, grind =] theorem Comp.subst_app (e1 e2 : Expr) (x : Var) (e : Expr) :
    Comp.subst (Comp.app e1 e2) x e = Comp.app (Expr.subst e1 x e) (Expr.subst e2 x e) := by grind

@[simp, grind =] theorem Comp.subst_letIn_self (y : Var) (c1 c2 : Comp) (e : Expr) :
    Comp.subst (Comp.letIn y c1 c2) y e = Comp.letIn y (Comp.subst c1 y e) c2 := by grind

@[simp, grind =] theorem Comp.subst_letIn_ne {x y : Var} (h : y ≠ x) (c1 c2 : Comp) (e : Expr) :
    Comp.subst (Comp.letIn y c1 c2) x e =
    Comp.letIn y (Comp.subst c1 x e) (Comp.subst c2 x e) := by grind

/-- General form: exposes the if-condition so proofs can use split_ifs -/
@[simp, grind =] theorem Comp.subst_letIn (y x : Var) (c1 c2 : Comp) (e' : Expr) :
    Comp.subst (Comp.letIn y c1 c2) x e' =
    Comp.letIn y (Comp.subst c1 x e') (if y = x then c2 else Comp.subst c2 x e') := by grind

@[simp, grind =] theorem Comp.subst_letRec_self_f (f y : Var) (c1 c2 : Comp) (e' : Expr) :
    Comp.subst (Comp.letRec f y c1 c2) f e' = Comp.letRec f y c1 c2 := by grind

@[simp, grind =] theorem Comp.subst_letRec_self_y {f y : Var} (h : y ≠ f) (c1 c2 : Comp) (e' : Expr) :
    Comp.subst (Comp.letRec f y c1 c2) y e' = Comp.letRec f y c1 (Comp.subst c2 y e') := by grind

@[simp, grind =] theorem Comp.subst_letRec_ne {x f y : Var} (hf : x ≠ f) (hy : x ≠ y) (c1 c2 : Comp) (e' : Expr) :
    Comp.subst (Comp.letRec f y c1 c2) x e' =
    Comp.letRec f y (Comp.subst c1 x e') (Comp.subst c2 x e') := by grind

/-- General form: exposes both if-conditions so proofs can use split_ifs -/
@[grind =] theorem Comp.subst_letRec (x f y : Var) (c1 c2 : Comp) (e' : Expr) :
    Comp.subst (Comp.letRec f y c1 c2) x e' =
    Comp.letRec f y
      (if x = f ∨ x = y then c1 else Comp.subst c1 x e')
      (if x = f then c2 else Comp.subst c2 x e') := by grind

@[simp, grind =] theorem Comp.subst_matchNat_self (y : Var) (e : Expr) (c1 c2 : Comp) (e' : Expr) :
    Comp.subst (Comp.matchNat e c1 y c2) y e' =
    Comp.matchNat (Expr.subst e y e') (Comp.subst c1 y e') y c2 := by grind

@[simp, grind =] theorem Comp.subst_matchNat_ne {x y : Var} (h : y ≠ x) (e : Expr) (c1 c2 : Comp) (e' : Expr) :
    Comp.subst (Comp.matchNat e c1 y c2) x e' =
    Comp.matchNat (Expr.subst e x e') (Comp.subst c1 x e') y (Comp.subst c2 x e') := by grind

/-- General form: exposes the if-condition so proofs can use split_ifs -/
@[grind =] theorem Comp.subst_matchNat (y x : Var) (e_scrut : Expr) (c1 c2 : Comp) (e' : Expr) :
    Comp.subst (Comp.matchNat e_scrut c1 y c2) x e' =
    Comp.matchNat (Expr.subst e_scrut x e') (Comp.subst c1 x e') y
      (if y = x then c2 else Comp.subst c2 x e') := by grind

@[simp, grind =] theorem Comp.subst_ifThenElse (e_cond : Expr) (c1 c2 : Comp) (x : Var) (e : Expr) :
    Comp.subst (Comp.ifThenElse e_cond c1 c2) x e =
    Comp.ifThenElse (Expr.subst e_cond x e) (Comp.subst c1 x e) (Comp.subst c2 x e) := by grind

@[simp, grind =] theorem Comp.subst_opCall (op : OpName) (e_arg : Expr) (x : Var) (e : Expr) :
    Comp.subst (Comp.opCall op e_arg) x e = Comp.opCall op (Expr.subst e_arg x e) := by grind

/-- Substitution in handlers -/
@[grind =] def BPHandler.subst (h : BPHandler) (x : Var) (e' : Expr) : BPHandler :=
  let (x_ret, c_ret) := h.returnClause
  let c_ret' := if x_ret = x then c_ret else Comp.subst c_ret x e'
  let opClauses' := h.opClauses.map fun (op, y, c) =>
    (op, y, if y = x || "resume" = x then c else Comp.subst c x e')
  ⟨(x_ret, c_ret'), opClauses'⟩

/-- opsSubst equals List.map with the same predicate (using compSubst internally) -/
private theorem opsSubst_eq_map (x : Var) (e' : Expr) :
    ∀ ops : List (OpName × Var × Comp),
    opsSubst x e' ops = ops.map fun p =>
        (p.1, p.2.1, if p.2.1 = x || "resume" = x then p.2.2 else compSubst p.2.2 x e') := by
  intro ops
  induction ops with
  | nil => simp [opsSubst]
  | cons head tail ih =>
    obtain ⟨op, y, c⟩ := head
    simp only [opsSubst, List.map, ih]

/-- Substitution distributes over withHandle -/
@[simp] theorem Comp.subst_withHandle (h : BPHandler) (c : Comp) (x : Var) (e' : Expr) :
    Comp.subst (Comp.withHandle h c) x e' =
    Comp.withHandle (BPHandler.subst h x e') (Comp.subst c x e') := by
  obtain ⟨⟨x_ret, c_ret⟩, ops⟩ := h
  simp only [Comp.subst, compSubst, BPHandler.subst, opsSubst_eq_map]

/-!
## Substitution is identity when variable is not free
-/

mutual

private theorem expr_subst_not_free :
    ∀ (e : Expr) (x : Var) (e' : Expr), x ∉ exprFvs e → exprSubst e x e' = e
  | .var y, x, e', h => by
      simp only [exprFvs, List.mem_singleton] at h
      simp only [exprSubst, if_neg (Ne.symm h)]
  | .true_, _, _, _ => by simp [exprSubst]
  | .false_, _, _, _ => by simp [exprSubst]
  | .unit, _, _, _ => by simp [exprSubst]
  | .zero, _, _, _ => by simp [exprSubst]
  | .succ e1, x, e', h => by
      simp only [exprFvs] at h
      simp only [exprSubst]
      exact congrArg Expr.succ (expr_subst_not_free e1 x e' h)
  | .lam y c, x, e', h => by
      simp only [exprFvs] at h
      by_cases h_eq : y = x
      · grind
      · simp only [exprSubst, h_eq, ite_false]
        exact congrArg (Expr.lam y) (comp_subst_not_free c x e' (fun hx =>
          h (List.mem_filter.mpr ⟨hx, decide_eq_true (Ne.symm h_eq)⟩)))

private theorem comp_subst_not_free :
    ∀ (c : Comp) (x : Var) (e' : Expr), x ∉ compFvs c → compSubst c x e' = c
  | .val e, x, e', h => by
      simp only [compFvs] at h
      simp only [compSubst]
      exact congrArg Comp.val (expr_subst_not_free e x e' h)
  | .app e1 e2, x, e', h => by
      simp only [compFvs] at h
      have h1 : x ∉ exprFvs e1 := fun hx => h (List.mem_append.mpr (Or.inl hx))
      have h2 : x ∉ exprFvs e2 := fun hx => h (List.mem_append.mpr (Or.inr hx))
      simp only [compSubst]
      exact congr (congrArg Comp.app (expr_subst_not_free e1 x e' h1))
                   (expr_subst_not_free e2 x e' h2)
  | .letIn y c1 c2, x, e', h => by
      simp only [compFvs] at h
      have h1 : x ∉ compFvs c1 := fun hx => h (List.mem_append.mpr (Or.inl hx))
      simp only [compSubst]
      by_cases h_eq : y = x
      · simp only [h_eq, ite_true]
        congr 1; exact comp_subst_not_free c1 x e' h1
      · have h2 : x ∉ compFvs c2 := fun hx =>
          h (List.mem_append.mpr (Or.inr
            (List.mem_filter.mpr ⟨hx, decide_eq_true (Ne.symm h_eq)⟩)))
        simp only [h_eq, ite_false]
        exact congr (congrArg (Comp.letIn y) (comp_subst_not_free c1 x e' h1))
                     (comp_subst_not_free c2 x e' h2)
  | .letRec f y c1 c2, x, e', h => by
      simp only [compFvs] at h
      simp only [compSubst]
      congr 1
      · -- c1 branch: if x = f || x = y then c1 else compSubst c1 x e'
        by_cases hf : x = f
        · subst hf; simp
        · by_cases hy : x = y
          · subst hy; simp [hf]
          · simp [hf, hy]
            exact comp_subst_not_free c1 x e' (fun hx =>
              h (List.mem_append.mpr (Or.inl
                (List.mem_filter.mpr ⟨hx, by rw [decide_eq_true hf, decide_eq_true hy]; rfl⟩))))
      · -- c2 branch: if x = f then c2 else compSubst c2 x e'
        by_cases hf : x = f
        · subst hf; simp
        · simp only [hf, ite_false]
          exact comp_subst_not_free c2 x e' (fun hx =>
            h (List.mem_append.mpr (Or.inr
              (List.mem_filter.mpr ⟨hx, decide_eq_true hf⟩))))
  | .ifThenElse e c1 c2, x, e', h => by
      simp only [compFvs] at h
      have he : x ∉ exprFvs e := fun hx =>
        h (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hx))))
      have h1 : x ∉ compFvs c1 := fun hx =>
        h (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hx))))
      have h2 : x ∉ compFvs c2 := fun hx =>
        h (List.mem_append.mpr (Or.inr hx))
      simp only [compSubst]
      exact congr (congr (congrArg Comp.ifThenElse (expr_subst_not_free e x e' he))
                         (comp_subst_not_free c1 x e' h1))
                   (comp_subst_not_free c2 x e' h2)
  | .matchNat e c1 y c2, x, e', h => by
      simp only [compFvs] at h
      have he : x ∉ exprFvs e := fun hx =>
        h (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hx))))
      have h1 : x ∉ compFvs c1 := fun hx =>
        h (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hx))))
      simp only [compSubst]
      congr 1
      · exact expr_subst_not_free e x e' he
      · exact comp_subst_not_free c1 x e' h1
      · by_cases h_eq : y = x
        · subst h_eq; simp
        · simp only [h_eq, ite_false]
          exact comp_subst_not_free c2 x e' (fun hx =>
            h (List.mem_append.mpr (Or.inr
              (List.mem_filter.mpr ⟨hx, decide_eq_true (Ne.symm h_eq)⟩))))
  | .withHandle ⟨⟨x_ret, c_ret⟩, ops⟩ c, x, e', h => by
      simp only [compFvs] at h
      have hc : x ∉ compFvs c := fun hx =>
        h (List.mem_append.mpr (Or.inr hx))
      have hops : x ∉ opsFvs ops := fun hx =>
        h (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hx))))
      simp only [compSubst]
      congr 1
      · congr 1
        · congr 1
          by_cases h_eq : x_ret = x
          · subst h_eq; simp
          · simp only [h_eq, ite_false]
            exact comp_subst_not_free c_ret x e' (fun hx =>
              h (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
                (List.mem_filter.mpr ⟨hx, decide_eq_true (Ne.symm h_eq)⟩))))))
        · exact ops_subst_not_free ops x e' hops
      · exact comp_subst_not_free c x e' hc
  | .opCall _op e, x, e', h => by
      simp only [compFvs] at h
      simp only [compSubst]
      exact congrArg (Comp.opCall _op) (expr_subst_not_free e x e' h)

private theorem ops_subst_not_free :
    ∀ (ops : List (OpName × Var × Comp)) (x : Var) (e' : Expr),
      x ∉ opsFvs ops → opsSubst x e' ops = ops
  | [], _, _, _ => by simp [opsSubst]
  | (op, y, c_op) :: rest, x, e', h => by
      simp only [opsFvs] at h
      have h_rest : x ∉ opsFvs rest := fun hx =>
        h (List.mem_append.mpr (Or.inr hx))
      simp only [opsSubst]
      congr 1
      · congr 1
        by_cases hy : y = x
        · subst hy; simp
        · by_cases hr : "resume" = x
          · simp [hy, hr]
          · simp [hy, hr]
            exact comp_subst_not_free c_op x e' (fun hx =>
              h (List.mem_append.mpr (Or.inl
                (List.mem_filter.mpr ⟨hx, by
                  rw [decide_eq_true (Ne.symm hy), decide_eq_true (Ne.symm hr)]; rfl⟩))))
      · exact ops_subst_not_free rest x e' h_rest

end -- mutual (subst_not_free)

/-- Substitution on expressions is identity when variable is not free -/
theorem Expr.subst_not_mem_fvs {e : Expr} {x : Var} {e' : Expr}
    (h : x ∉ e.fvs) : e.subst x e' = e :=
  expr_subst_not_free e x e' (by simp only [Expr.fvs] at h; exact h)

/-- Substitution on computations is identity when variable is not free -/
theorem Comp.subst_not_mem_fvs {c : Comp} {x : Var} {e' : Expr}
    (h : x ∉ c.fvs) : c.subst x e' = c :=
  comp_subst_not_free c x e' (by simp only [Comp.fvs] at h; exact h)

/-- Corollary: substitution on closed expressions is identity -/
theorem Expr.subst_of_fvs_nil {e : Expr} (h : e.fvs = []) (x : Var) (e' : Expr) :
    e.subst x e' = e :=
  expr_subst_not_free e x e' (show x ∉ exprFvs e by rw [show exprFvs e = e.fvs from rfl, h]; exact nofun)

theorem Comp.subst_of_fvs_nil {c : Comp} (h : c.fvs = []) (x : Var) (e' : Expr) :
    c.subst x e' = c :=
  comp_subst_not_free c x e' (show x ∉ compFvs c by rw [show compFvs c = c.fvs from rfl, h]; exact nofun)

/-- Substitution on handlers is identity when variable is not free -/
theorem BPHandler.subst_not_mem_fvs {h : BPHandler} {x : Var} {e' : Expr}
    (hx : x ∉ h.fvs) : h.subst x e' = h := by
  -- Reduce to Comp.subst_withHandle and use comp_subst_not_free on the withHandle representation
  -- Strategy: show that (withHandle h c).subst x e' = withHandle h c for any c when x ∉ h.fvs,
  -- by extracting the handler part from the withHandle subst
  obtain ⟨⟨x_ret, c_ret⟩, ops⟩ := h
  simp only [BPHandler.subst]
  congr 1
  · -- return clause: show (x_ret, if x_ret = x then c_ret else c_ret.subst x e') = (x_ret, c_ret)
    congr 1
    split
    · rfl
    · rename_i h_ne
      apply Comp.subst_not_mem_fvs
      intro hc
      grind
  · -- op clauses: show map with subst = identity
    have hx_ops : x ∉ ops.flatMap (fun p => (Comp.fvs p.2.2).filter (fun v => v ≠ p.2.1 && v ≠ "resume")) := by
      intro hm; exact hx (by simp only [BPHandler.fvs]; exact List.mem_append.mpr (Or.inr hm))
    clear hx
    induction ops with
    | nil => simp
    | cons hd tl ih =>
      obtain ⟨op, y, c⟩ := hd
      simp only [List.flatMap_cons] at hx_ops
      have hx_hd : x ∉ (Comp.fvs c).filter (fun v => v ≠ y && v ≠ "resume") :=
        fun hm => hx_ops (List.mem_append.mpr (Or.inl hm))
      have hx_tl : x ∉ tl.flatMap (fun p => (Comp.fvs p.2.2).filter (fun v => v ≠ p.2.1 && v ≠ "resume")) :=
        fun hm => hx_ops (List.mem_append.mpr (Or.inr hm))
      simp only [List.map_cons, List.cons.injEq]
      constructor
      · -- head element
        show (op, y, if y = x || "resume" = x then c else c.subst x e') = (op, y, c)
        split
        · rfl
        · rename_i h_guard
          simp only [Bool.or_eq_true, decide_eq_true_eq] at h_guard
          congr 1; congr 1; exact Comp.subst_not_mem_fvs (fun hc =>
            hx_hd (List.mem_filter.mpr ⟨hc, by
              simp only [Bool.and_eq_true, decide_eq_true_eq]
              exact ⟨fun heq => h_guard (Or.inl heq.symm), fun heq => h_guard (Or.inr heq.symm)⟩⟩))
      · -- tail
        exact ih hx_tl

/-!
## Free variables of substitution

General property: fvs of (e.subst x e') ⊆ (fvs(e) \ {x}) ∪ fvs(e').
We prove: v ∈ fvs(subst) → (v ∈ fvs(original) ∧ v ≠ x) ∨ v ∈ fvs(e').
-/

-- Helper: extract membership from filter with decidable predicate
private theorem mem_of_mem_filter {l : List α} {p : α → Bool} {a : α}
    (h : a ∈ l.filter p) : a ∈ l :=
  (List.mem_filter.mp h).1

private theorem pred_of_mem_filter {l : List α} {p : α → Bool} {a : α}
    (h : a ∈ l.filter p) : p a = true :=
  (List.mem_filter.mp h).2

private theorem mem_filter_of {l : List α} {p : α → Bool} {a : α}
    (h1 : a ∈ l) (h2 : p a = true) : a ∈ l.filter p :=
  List.mem_filter.mpr ⟨h1, h2⟩

mutual
@[simp, grind ->] private theorem expr_fvs_subst_sub :
    ∀ (e : Expr) (x : Var) (e' : Expr) (v : Var),
      v ∈ exprFvs (exprSubst e x e') →
      (v ∈ exprFvs e ∧ v ≠ x) ∨ v ∈ exprFvs e'
  | .var y, x, e', v, h => by grind
  | .true_, _, _, _, h => by grind
  | .false_, _, _, _, h => by grind
  | .unit, _, _, _, h => by grind
  | .zero, _, _, _, h => by grind
  | .succ e, x, e', v, h => by
      simp only [exprSubst, exprFvs] at h ⊢
      exact expr_fvs_subst_sub e x e' v h
  | .lam y c, x, e', v, h => by
      simp only [exprSubst] at h
      by_cases h_eq : y = x
      · subst h_eq; simp only [ite_true, exprFvs] at h ⊢
        exact Or.inl ⟨h, by have := pred_of_mem_filter h; simp at this; exact this⟩
      · simp only [h_eq, ite_false, exprFvs] at h ⊢
        have hv_in := mem_of_mem_filter h
        have hv_pred := pred_of_mem_filter h
        rcases comp_fvs_subst_sub c x e' v hv_in with ⟨hc, hne⟩ | he'
        · exact Or.inl ⟨mem_filter_of hc hv_pred, hne⟩
        · exact Or.inr he'
termination_by e => sizeOf e

@[simp, grind ->] theorem comp_fvs_subst_sub :
    ∀ (c : Comp) (x : Var) (e' : Expr) (v : Var),
      v ∈ compFvs (compSubst c x e') →
      (v ∈ compFvs c ∧ v ≠ x) ∨ v ∈ exprFvs e'
  | .val e, x, e', v, h => by
      simp only [compSubst, compFvs] at h ⊢
      exact expr_fvs_subst_sub e x e' v h
  | .app e1 e2, x, e', v, h => by
      simp only [compSubst, compFvs] at h ⊢
      rcases List.mem_append.mp h with h1 | h2
      · rcases expr_fvs_subst_sub e1 x e' v h1 with ⟨he, hne⟩ | he'
        · exact Or.inl ⟨List.mem_append.mpr (Or.inl he), hne⟩
        · exact Or.inr he'
      · rcases expr_fvs_subst_sub e2 x e' v h2 with ⟨he, hne⟩ | he'
        · exact Or.inl ⟨List.mem_append.mpr (Or.inr he), hne⟩
        · exact Or.inr he'
  | .opCall op e, x, e', v, h => by
      simp only [compSubst, compFvs] at h ⊢
      exact expr_fvs_subst_sub e x e' v h
  | .ifThenElse e c1 c2, x, e', v, h => by
      simp only [compSubst, compFvs] at h ⊢
      rcases List.mem_append.mp h with h12 | h3
      · rcases List.mem_append.mp h12 with h1 | h2
        · rcases expr_fvs_subst_sub e x e' v h1 with ⟨he, hne⟩ | he'
          · exact Or.inl ⟨List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl he))), hne⟩
          · exact Or.inr he'
        · rcases comp_fvs_subst_sub c1 x e' v h2 with ⟨hc, hne⟩ | he'
          · exact Or.inl ⟨List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hc))), hne⟩
          · exact Or.inr he'
      · rcases comp_fvs_subst_sub c2 x e' v h3 with ⟨hc, hne⟩ | he'
        · exact Or.inl ⟨List.mem_append.mpr (Or.inr hc), hne⟩
        · exact Or.inr he'
  | .letIn y c1 c2, x, e', v, h => by
      simp only [compSubst, compFvs] at h ⊢
      by_cases h_eq : y = x
      · simp only [h_eq, ite_true, compFvs] at h
        rcases List.mem_append.mp h with h1 | h2
        · rcases comp_fvs_subst_sub c1 x e' v h1 with ⟨hc, hne⟩ | he'
          · exact Or.inl ⟨List.mem_append.mpr (Or.inl hc), hne⟩
          · exact Or.inr he'
        · have hv_ne : v ≠ x := by
            have := pred_of_mem_filter h2; simp at this; exact this
          exact Or.inl ⟨List.mem_append.mpr (Or.inr (by rw [h_eq]; exact h2)), hv_ne⟩
      · simp only [h_eq, ite_false, compFvs] at h
        rcases List.mem_append.mp h with h1 | h2
        · rcases comp_fvs_subst_sub c1 x e' v h1 with ⟨hc, hne⟩ | he'
          · exact Or.inl ⟨List.mem_append.mpr (Or.inl hc), hne⟩
          · exact Or.inr he'
        · have hv_pred := pred_of_mem_filter h2
          rcases comp_fvs_subst_sub c2 x e' v (mem_of_mem_filter h2) with ⟨hc, hne⟩ | he'
          · exact Or.inl ⟨List.mem_append.mpr (Or.inr (mem_filter_of hc hv_pred)), hne⟩
          · exact Or.inr he'
  | .matchNat e c1 y c2, x, e', v, h => by
      simp only [compSubst, compFvs] at h ⊢
      rcases List.mem_append.mp h with h12 | h3
      · rcases List.mem_append.mp h12 with h1 | h2
        · rcases expr_fvs_subst_sub e x e' v h1 with ⟨he, hne⟩ | he'
          · exact Or.inl ⟨List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl he))), hne⟩
          · exact Or.inr he'
        · rcases comp_fvs_subst_sub c1 x e' v h2 with ⟨hc, hne⟩ | he'
          · exact Or.inl ⟨List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hc))), hne⟩
          · exact Or.inr he'
      · by_cases h_eq : y = x
        · subst h_eq; simp only [ite_true] at h3
          exact Or.inl ⟨List.mem_append.mpr (Or.inr h3),
            by have := pred_of_mem_filter h3; simp at this; exact this⟩
        · simp only [h_eq, ite_false] at h3
          have hv_pred := pred_of_mem_filter h3
          rcases comp_fvs_subst_sub c2 x e' v (mem_of_mem_filter h3) with ⟨hc, hne⟩ | he'
          · exact Or.inl ⟨List.mem_append.mpr (Or.inr (mem_filter_of hc hv_pred)), hne⟩
          · exact Or.inr he'
  | .letRec f y c1 c2, x, e', v, h => by
      simp only [compSubst, compFvs] at h ⊢
      by_cases h_xf : x = f
      · subst h_xf; simp at h ⊢
        exact Or.inl ⟨h, by rcases h with ⟨_, hne, _⟩ | ⟨_, hne⟩ <;> exact hne⟩
      · by_cases h_xy : x = y
        · -- x = y, x ≠ f: c1 unchanged, c2 substituted
          subst h_xy; simp [h_xf] at h ⊢
          rcases h with ⟨h1, hne_f, hne_x⟩ | ⟨h2, hne_f⟩
          · exact Or.inl ⟨Or.inl ⟨h1, hne_f, hne_x⟩, hne_x⟩
          · rcases comp_fvs_subst_sub c2 x e' v h2 with ⟨hc, hne⟩ | he'
            · exact Or.inl ⟨Or.inr ⟨hc, hne_f⟩, hne⟩
            · exact Or.inr he'
        · -- x ≠ f, x ≠ y: both substituted
          simp [h_xf, h_xy] at h ⊢
          rcases h with ⟨h1, hne_f, hne_y⟩ | ⟨h2, hne_f⟩
          · rcases comp_fvs_subst_sub c1 x e' v h1 with ⟨hc, hne⟩ | he'
            · exact Or.inl ⟨Or.inl ⟨hc, hne_f, hne_y⟩, hne⟩
            · exact Or.inr he'
          · rcases comp_fvs_subst_sub c2 x e' v h2 with ⟨hc, hne⟩ | he'
            · exact Or.inl ⟨Or.inr ⟨hc, hne_f⟩, hne⟩
            · exact Or.inr he'
  | .withHandle ⟨(x_ret, c_ret), ops⟩ c, x, e', v, h => by
      simp only [compSubst, compFvs] at h ⊢
      by_cases h_eq : x_ret = x
      · subst h_eq; simp at h ⊢
        rcases h with ⟨h1, hne⟩ | h2 | h3
        · exact Or.inl ⟨Or.inl ⟨h1, hne⟩, hne⟩
        · rcases ops_fvs_subst_sub ops x_ret e' v h2 with ⟨ho, hne⟩ | he'
          · exact Or.inl ⟨Or.inr (Or.inl ho), hne⟩
          · exact Or.inr he'
        · rcases comp_fvs_subst_sub c x_ret e' v h3 with ⟨hc, hne⟩ | he'
          · exact Or.inl ⟨Or.inr (Or.inr hc), hne⟩
          · exact Or.inr he'
      · simp [h_eq] at h ⊢
        rcases h with ⟨h1, hne_xr⟩ | h2 | h3
        · rcases comp_fvs_subst_sub c_ret x e' v h1 with ⟨hc, hne⟩ | he'
          · exact Or.inl ⟨Or.inl ⟨hc, hne_xr⟩, hne⟩
          · exact Or.inr he'
        · rcases ops_fvs_subst_sub ops x e' v h2 with ⟨ho, hne⟩ | he'
          · exact Or.inl ⟨Or.inr (Or.inl ho), hne⟩
          · exact Or.inr he'
        · rcases comp_fvs_subst_sub c x e' v h3 with ⟨hc, hne⟩ | he'
          · exact Or.inl ⟨Or.inr (Or.inr hc), hne⟩
          · exact Or.inr he'
termination_by c => sizeOf c

private theorem ops_fvs_subst_sub :
    ∀ (ops : List (OpName × Var × Comp)) (x : Var) (e' : Expr) (v : Var),
      v ∈ opsFvs (opsSubst x e' ops) →
      (v ∈ opsFvs ops ∧ v ≠ x) ∨ v ∈ exprFvs e'
  | [], _, _, _, h => by simp [opsSubst, opsFvs] at h
  | (op, y, c) :: rest, x, e', v, h => by
      simp only [opsSubst, opsFvs] at h ⊢
      by_cases h_yx : y = x
      · -- y = x: c not substituted
        simp [h_yx] at h ⊢
        rcases h with ⟨h1, hne_x, hne_r⟩ | h2
        · exact Or.inl ⟨Or.inl ⟨h1, hne_x, hne_r⟩, hne_x⟩
        · rcases ops_fvs_subst_sub rest x e' v h2 with ⟨ho, hne⟩ | he'
          · exact Or.inl ⟨Or.inr ho, hne⟩
          · exact Or.inr he'
      · by_cases h_rx : "resume" = x
        · -- "resume" = x: c not substituted
          simp [h_yx, h_rx] at h ⊢
          rcases h with ⟨h1, hne_y, hne_x⟩ | h2
          · exact Or.inl ⟨Or.inl ⟨h1, hne_y, hne_x⟩, hne_x⟩
          · rcases ops_fvs_subst_sub rest x e' v h2 with ⟨ho, hne⟩ | he'
            · exact Or.inl ⟨Or.inr ho, hne⟩
            · exact Or.inr he'
        · -- neither: c substituted
          simp [h_yx, h_rx] at h ⊢
          rcases h with ⟨h1, hne_y, hne_r⟩ | h2
          · rcases comp_fvs_subst_sub c x e' v h1 with ⟨hc, hne⟩ | he'
            · exact Or.inl ⟨Or.inl ⟨hc, hne_y, hne_r⟩, hne⟩
            · exact Or.inr he'
          · rcases ops_fvs_subst_sub rest x e' v h2 with ⟨ho, hne⟩ | he'
            · exact Or.inl ⟨Or.inr ho, hne⟩
            · exact Or.inr he'
termination_by ops => sizeOf ops

end -- mutual fvs_subst_sub

/-- Corollary: substitution preserves closedness -/
theorem Comp.fvs_subst_closed {c : Comp} {x : Var} {e' : Expr} :
    (∀ v, v ∈ c.fvs → v = x) → e'.fvs = [] → (c.subst x e').fvs = [] := by
  intro h1 h2
  rw [show (c.subst x e').fvs = compFvs (compSubst c x e') from rfl]
  match h : compFvs (compSubst c x e') with
  | [] => rfl
  | v :: rest =>
    exfalso
    have hv : v ∈ compFvs (compSubst c x e') := by rw [h]; simp
    rcases comp_fvs_subst_sub c x e' v hv with ⟨hc, hne⟩ | he'
    · exact hne (h1 v (by rwa [Comp.fvs]))
    · have : exprFvs e' = e'.fvs := rfl; rw [this, h2] at he'; simp at he'

/-- comp_fvs_subst_sub with public API types -/
theorem Comp.fvs_subst_sub {c : Comp} {x : Var} {e' : Expr} {v : Var} :
    v ∈ (c.subst x e').fvs →
    (v ∈ c.fvs ∧ v ≠ x) ∨ v ∈ e'.fvs := by
  intro hv
  rcases comp_fvs_subst_sub c x e' v hv with ⟨hc, hne⟩ | he'
  · exact Or.inl ⟨hc, hne⟩
  · exact Or.inr (by rwa [show exprFvs e' = e'.fvs from rfl] at he')

end DMCFA.BP
