/-
  Syntax for the ANF λ^h calculus (our semantics)

  The syntax is in Administrative Normal Form (ANF):
  - Complex expressions may only appear in let bindings
  - Complex expressions are always let-bound or in tail position, never nested
-/

namespace DMCFA

/-- Labels uniquely identify each expression -/
abbrev Label := Nat

/-- Variable names -/
abbrev Var := String

/-- Operation names for effect handlers -/
abbrev OpName := String

/-- Constructor labels for data constructors -/
inductive ConLabel
  | true_
  | false_
  | unit
  | zero
  | succ
  deriving DecidableEq, Repr

-- AExp, CExp, Exp, Branch, Handler are mutually recursive.
-- The explicit `mutual` block ensures correct constructor types across files.
mutual

/-- Atomic expressions - can be evaluated without computation -/
inductive AExp where
  | var : Var → AExp
  | lam : List Var → Exp → AExp           -- fn(xs) e_body
  | con : ConLabel → AExp                  -- Constants
  | succE : Var → AExp                     -- S(x) - constructor applied to variable

/-- Complex expressions - require computation -/
inductive CExp where
  | atomic : AExp → CExp                    -- Atomic in complex position
  | funApp : AExp → List AExp → CExp        -- f(aes) application - args are AExp, allocates fresh addrs
  | opApp : OpName → Var → CExp             -- op(x) operation application - arg is Var, store unchanged
  | matchE : AExp → List Branch → CExp      -- match(ae){b}
  | handler : Handler → Exp → Label → CExp   -- handler{h}(e_body) with label for handler frame
  | funDef : Var → List Var → Exp → CExp    -- fun f(xs) e1 (recursive def)

/-- Top-level expressions (ANF) -/
inductive Exp where
  | letE : Var → CExp → Exp → Label → Exp   -- let y = ce; e with label
  | tail : CExp → Label → Exp               -- ce in tail position, with label

/-- Match branches -/
inductive Branch where
  | branch : ConLabel → List Var → Exp → Branch

/-- Handler definition -/
structure Handler where
  returnClause : Var × Exp                  -- return(x) e_ret
  opClauses : List (OpName × Var × Exp)     -- op(x) e_op clauses

end

-- DecidableEq for mutual inductives (Lean can't auto-derive for mutual blocks)
private def listDecEq {α : Type} (deq : (a b : α) → Decidable (a = b)) : (as bs : List α) → Decidable (as = bs)
  | [], [] => .isTrue rfl
  | [], _::_ | _::_, [] => .isFalse nofun
  | a::as, b::bs => match deq a b, listDecEq deq as bs with
    | .isTrue h1, .isTrue h2 => .isTrue (h1 ▸ h2 ▸ rfl)
    | .isFalse h, _ => .isFalse (fun | rfl => h rfl)
    | _, .isFalse h => .isFalse (fun | rfl => h rfl)

mutual
def AExp.decEq : (a b : AExp) → Decidable (a = b)
  | .var x, .var y => if h : x = y then .isTrue (h ▸ rfl) else .isFalse (fun | rfl => h rfl)
  | .lam xs e, .lam ys f =>
    match decEq xs ys, Exp.decEq e f with
    | .isTrue h1, .isTrue h2 => .isTrue (h1 ▸ h2 ▸ rfl)
    | .isFalse h, _ => .isFalse (fun | rfl => h rfl)
    | _, .isFalse h => .isFalse (fun | rfl => h rfl)
  | .con c1, .con c2 => if h : c1 = c2 then .isTrue (h ▸ rfl) else .isFalse (fun | rfl => h rfl)
  | .succE x, .succE y => if h : x = y then .isTrue (h ▸ rfl) else .isFalse (fun | rfl => h rfl)
  | .var _, .lam _ _ | .var _, .con _ | .var _, .succE _ => .isFalse nofun
  | .lam _ _, .var _ | .lam _ _, .con _ | .lam _ _, .succE _ => .isFalse nofun
  | .con _, .var _ | .con _, .lam _ _ | .con _, .succE _ => .isFalse nofun
  | .succE _, .var _ | .succE _, .lam _ _ | .succE _, .con _ => .isFalse nofun
def CExp.decEq : (a b : CExp) → Decidable (a = b)
  | .atomic a1, .atomic a2 =>
    match AExp.decEq a1 a2 with
    | .isTrue h => .isTrue (h ▸ rfl) | .isFalse h => .isFalse (fun | rfl => h rfl)
  | .funApp f1 as1, .funApp f2 as2 =>
    match AExp.decEq f1 f2, AExpList.decEq as1 as2 with
    | .isTrue h1, .isTrue h2 => .isTrue (h1 ▸ h2 ▸ rfl)
    | .isFalse h, _ => .isFalse (fun | rfl => h rfl)
    | _, .isFalse h => .isFalse (fun | rfl => h rfl)
  | .opApp o1 x1, .opApp o2 x2 =>
    match decEq o1 o2, decEq x1 x2 with
    | .isTrue h1, .isTrue h2 => .isTrue (h1 ▸ h2 ▸ rfl)
    | .isFalse h, _ => .isFalse (fun | rfl => h rfl)
    | _, .isFalse h => .isFalse (fun | rfl => h rfl)
  | .matchE a1 bs1, .matchE a2 bs2 =>
    match AExp.decEq a1 a2, BranchList.decEq bs1 bs2 with
    | .isTrue h1, .isTrue h2 => .isTrue (h1 ▸ h2 ▸ rfl)
    | .isFalse h, _ => .isFalse (fun | rfl => h rfl)
    | _, .isFalse h => .isFalse (fun | rfl => h rfl)
  | .handler h1 e1 l1, .handler h2 e2 l2 =>
    match Handler.decEq h1 h2, Exp.decEq e1 e2, decEq l1 l2 with
    | .isTrue h1, .isTrue h2, .isTrue h3 => .isTrue (h1 ▸ h2 ▸ h3 ▸ rfl)
    | .isFalse h, _, _ => .isFalse (fun | rfl => h rfl)
    | _, .isFalse h, _ => .isFalse (fun | rfl => h rfl)
    | _, _, .isFalse h => .isFalse (fun | rfl => h rfl)
  | .funDef f1 xs1 e1, .funDef f2 xs2 e2 =>
    match decEq f1 f2, decEq xs1 xs2, Exp.decEq e1 e2 with
    | .isTrue h1, .isTrue h2, .isTrue h3 => .isTrue (h1 ▸ h2 ▸ h3 ▸ rfl)
    | .isFalse h, _, _ => .isFalse (fun | rfl => h rfl)
    | _, .isFalse h, _ => .isFalse (fun | rfl => h rfl)
    | _, _, .isFalse h => .isFalse (fun | rfl => h rfl)
  | .atomic _, .funApp _ _ | .atomic _, .opApp _ _ | .atomic _, .matchE _ _ | .atomic _, .handler _ _ _ | .atomic _, .funDef _ _ _ => .isFalse nofun
  | .funApp _ _, .atomic _ | .funApp _ _, .opApp _ _ | .funApp _ _, .matchE _ _ | .funApp _ _, .handler _ _ _ | .funApp _ _, .funDef _ _ _ => .isFalse nofun
  | .opApp _ _, .atomic _ | .opApp _ _, .funApp _ _ | .opApp _ _, .matchE _ _ | .opApp _ _, .handler _ _ _ | .opApp _ _, .funDef _ _ _ => .isFalse nofun
  | .matchE _ _, .atomic _ | .matchE _ _, .funApp _ _ | .matchE _ _, .opApp _ _ | .matchE _ _, .handler _ _ _ | .matchE _ _, .funDef _ _ _ => .isFalse nofun
  | .handler _ _ _, .atomic _ | .handler _ _ _, .funApp _ _ | .handler _ _ _, .opApp _ _ | .handler _ _ _, .matchE _ _ | .handler _ _ _, .funDef _ _ _ => .isFalse nofun
  | .funDef _ _ _, .atomic _ | .funDef _ _ _, .funApp _ _ | .funDef _ _ _, .opApp _ _ | .funDef _ _ _, .matchE _ _ | .funDef _ _ _, .handler _ _ _ => .isFalse nofun
def Exp.decEq : (a b : Exp) → Decidable (a = b)
  | .letE y1 ce1 e1 l1, .letE y2 ce2 e2 l2 =>
    match decEq y1 y2, CExp.decEq ce1 ce2, Exp.decEq e1 e2, decEq l1 l2 with
    | .isTrue h1, .isTrue h2, .isTrue h3, .isTrue h4 => .isTrue (h1 ▸ h2 ▸ h3 ▸ h4 ▸ rfl)
    | .isFalse h, _, _, _ => .isFalse (fun | rfl => h rfl)
    | _, .isFalse h, _, _ => .isFalse (fun | rfl => h rfl)
    | _, _, .isFalse h, _ => .isFalse (fun | rfl => h rfl)
    | _, _, _, .isFalse h => .isFalse (fun | rfl => h rfl)
  | .tail ce1 l1, .tail ce2 l2 =>
    match CExp.decEq ce1 ce2, decEq l1 l2 with
    | .isTrue h1, .isTrue h2 => .isTrue (h1 ▸ h2 ▸ rfl)
    | .isFalse h, _ => .isFalse (fun | rfl => h rfl)
    | _, .isFalse h => .isFalse (fun | rfl => h rfl)
  | .letE _ _ _ _, .tail _ _ | .tail _ _, .letE _ _ _ _ => .isFalse nofun
def Handler.decEq : (a b : Handler) → Decidable (a = b)
  | ⟨r1, ops1⟩, ⟨r2, ops2⟩ =>
    match ReturnClause.decEq r1 r2, OpClauseList.decEq ops1 ops2 with
    | .isTrue h1, .isTrue h2 => .isTrue (by subst h1; subst h2; rfl)
    | .isFalse h, _ => .isFalse (fun | rfl => h rfl)
    | _, .isFalse h => .isFalse (fun | rfl => h rfl)
def ReturnClause.decEq : (a b : Var × Exp) → Decidable (a = b)
  | (v1, e1), (v2, e2) =>
    match decEq v1 v2, Exp.decEq e1 e2 with
    | .isTrue h1, .isTrue h2 => .isTrue (by subst h1; subst h2; rfl)
    | .isFalse h, _ => .isFalse (fun | rfl => h rfl)
    | _, .isFalse h => .isFalse (fun | rfl => h rfl)
def OpClause.decEq : (a b : OpName × Var × Exp) → Decidable (a = b)
  | (o1, v1, e1), (o2, v2, e2) =>
    match decEq o1 o2, decEq v1 v2, Exp.decEq e1 e2 with
    | .isTrue h1, .isTrue h2, .isTrue h3 => .isTrue (by subst h1; subst h2; subst h3; rfl)
    | .isFalse h, _, _ => .isFalse (fun | rfl => h rfl)
    | _, .isFalse h, _ => .isFalse (fun | rfl => h rfl)
    | _, _, .isFalse h => .isFalse (fun | rfl => h rfl)
def OpClauseList.decEq : (as bs : List (OpName × Var × Exp)) → Decidable (as = bs)
  | [], [] => .isTrue rfl
  | [], _::_ | _::_, [] => .isFalse nofun
  | a::as, b::bs => match OpClause.decEq a b, OpClauseList.decEq as bs with
    | .isTrue h1, .isTrue h2 => .isTrue (h1 ▸ h2 ▸ rfl)
    | .isFalse h, _ => .isFalse (fun | rfl => h rfl)
    | _, .isFalse h => .isFalse (fun | rfl => h rfl)
def AExpList.decEq : (as bs : List AExp) → Decidable (as = bs)
  | [], [] => .isTrue rfl
  | [], _::_ | _::_, [] => .isFalse nofun
  | a::as, b::bs => match AExp.decEq a b, AExpList.decEq as bs with
    | .isTrue h1, .isTrue h2 => .isTrue (h1 ▸ h2 ▸ rfl)
    | .isFalse h, _ => .isFalse (fun | rfl => h rfl)
    | _, .isFalse h => .isFalse (fun | rfl => h rfl)
def BranchList.decEq : (as bs : List Branch) → Decidable (as = bs)
  | [], [] => .isTrue rfl
  | [], _::_ | _::_, [] => .isFalse nofun
  | a::as, b::bs => match Branch.decEq a b, BranchList.decEq as bs with
    | .isTrue h1, .isTrue h2 => .isTrue (h1 ▸ h2 ▸ rfl)
    | .isFalse h, _ => .isFalse (fun | rfl => h rfl)
    | _, .isFalse h => .isFalse (fun | rfl => h rfl)
def Branch.decEq : (a b : Branch) → Decidable (a = b)
  | .branch c1 xs1 e1, .branch c2 xs2 e2 =>
    match decEq c1 c2, decEq xs1 xs2, Exp.decEq e1 e2 with
    | .isTrue h1, .isTrue h2, .isTrue h3 => .isTrue (h1 ▸ h2 ▸ h3 ▸ rfl)
    | .isFalse h, _, _ => .isFalse (fun | rfl => h rfl)
    | _, .isFalse h, _ => .isFalse (fun | rfl => h rfl)
    | _, _, .isFalse h => .isFalse (fun | rfl => h rfl)
end

instance : DecidableEq AExp := AExp.decEq
instance : DecidableEq CExp := CExp.decEq
instance : DecidableEq Exp := Exp.decEq
instance : DecidableEq Branch := Branch.decEq
instance : DecidableEq Handler := fun a b =>
  match @decEq (Var × Exp) inferInstance a.returnClause b.returnClause,
        @decEq (List (OpName × Var × Exp)) inferInstance a.opClauses b.opClauses with
  | .isTrue h1, .isTrue h2 => .isTrue (by cases a; cases b; simp at *; exact ⟨h1, h2⟩)
  | .isFalse h1, _ => .isFalse (fun h => h1 (by subst h; rfl))
  | _, .isFalse h2 => .isFalse (fun h => h2 (by subst h; rfl))

abbrev Branches := List Branch

instance : Inhabited AExp := ⟨AExp.con ConLabel.unit⟩

/-- Get the label from a let expression -/
def Exp.getLabel : Exp → Option Label
  | Exp.letE _ _ _ l => some l
  | _ => none

/-!
## Free Variables

Mutually recursive with `termination_by sizeOf`. List cases use explicit
recursive helpers (`aexpListFvs`, `branchListFvs`, `opClauseListFvs`) to
make structural descent visible to the termination checker. `Handler.fvs` is
included in the mutual block so `CExp.fvs` can call it, and uses pattern
matching (not `let`) so `e_ret` is a direct structural subterm.
-/

mutual

/-- Free variables of an atomic expression -/
def AExp.fvs : AExp → List Var
  | .var x => [x]
  | .lam xs e => e.fvs.filter (· ∉ xs)
  | .con _ => []
  | .succE x => [x]
termination_by a => sizeOf a

/-- Free variables of a complex expression -/
def CExp.fvs : CExp → List Var
  | .atomic ae => ae.fvs
  | .funApp f aes => f.fvs ++ aexpListFvs aes
  | .opApp _ x => [x]
  | .matchE ae bs => ae.fvs ++ branchListFvs bs
  | .handler h e _l_h => Handler.fvs h ++ e.fvs   -- delegate to Handler.fvs (sizeOf h < sizeOf ce)
  | .funDef f xs e => e.fvs.filter (fun v => v ∉ xs && v ≠ f)
termination_by ce => sizeOf ce

/-- Free variables of an expression -/
def Exp.fvs : Exp → List Var
  | .letE y ce e _ => ce.fvs ++ e.fvs.filter (· ≠ y)
  | .tail ce _l => ce.fvs
termination_by e => sizeOf e

/-- Free variables of a branch -/
def Branch.fvs : Branch → List Var
  | .branch _ xs e => e.fvs.filter (· ∉ xs)
termination_by b => sizeOf b

/-- Free variables of a handler (in mutual block so CExp.fvs can call it) -/
def Handler.fvs : Handler → List Var
  | ⟨(x_ret, e_ret), ops⟩ =>
      e_ret.fvs.filter (· ≠ x_ret) ++ opClauseListFvs ops
termination_by h => sizeOf h

-- Explicit list recursion helpers (avoid inline lambdas in flatMap)
def aexpListFvs : List AExp → List Var
  | [] => []
  | ae :: rest => ae.fvs ++ aexpListFvs rest
termination_by aes => sizeOf aes

def branchListFvs : List Branch → List Var
  | [] => []
  | b :: rest => b.fvs ++ branchListFvs rest
termination_by bs => sizeOf bs

def opClauseListFvs : List (OpName × Var × Exp) → List Var
  | [] => []
  | (_, x, e) :: rest =>
      e.fvs.filter (fun v => v ≠ x && v ≠ "resume") ++ opClauseListFvs rest
termination_by ops => sizeOf ops

end

end DMCFA
