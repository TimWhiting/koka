/-
  Bridge between the concrete *named* ANF machine (`DMCFA.Semantics`,
  `Env = Var → Option VAddr`) and the concrete *locally-nameless* ANF machine
  (`DMCFA.LN.Semantics`, `Env = List VAddr`).

  WHY THIS FILE EXISTS
  --------------------
  After the locally-nameless rework, the concrete semantics appears in two
  representations:
    * B&P  ↔  Concrete(LN)        — proved in `DMCFA.LN.*`
    * Concrete(named)  ↔  …  ↔  Abstract   — the timestamped/abstract chain
  These two "Concrete" nodes are different Lean objects, so the end-to-end
  B&P → Abstract story does not literally compose without a connecting lemma.
  This file builds that lemma: a name↔de-Bruijn translation `toLN` together with
  a bidirectional simulation between the two evaluation relations.

  STATUS: complete, no `sorry`; imported by the package root (`DMCFA.lean`) and
  covered by `DMCFA/AxiomAudit.lean`. Depends only on Lean's standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`).

  PROVEN (no sorry):
    * `toLN*`            — the full name→de-Bruijn translation.
    * `WF*`             — source-program well-formedness (binder hygiene).
    * `EnvRel.push/.pushMany/.pushManySelf` — environment coherence.
    * `StoreRel.some/.none/.some'/.none'/.extend/.extendManyZip` — store transfer.
    * `evalAtomic_forward/.backward` — atomic-evaluation correspondence.
    * `findBranch_forward/.backward/.wf`, `findOp_forward/.backward`, `hasOp_eq`,
      `handlerRel_of_scope` — handler/branch lookup + scoping/WF infrastructure.
    * `sim_forward` / `sim_backward` — the two big-step simulations, by
      well-founded recursion on the height-indexed eval relations (mirroring
      `DMCFA.LN.soundness_allN`). Every named rule maps to its same-named LN
      counterpart; allocation uses `StoreRel.extend(ManyZip)`, binders use
      `EnvRel.push`/`pushMany`/`pushManySelf`, atomics use `evalAtomic_*`.

  WELL-FORMEDNESS — the bare evaluation relations do not carry source-level
  binding hygiene, so `sim_forward`/`sim_backward` take a `WFExp e` premise. The
  predicate `WFExp` records exactly the conditions the translation depends on:
    * lambda / recursive-function parameters are `Nodup` and the recursive name
      is not among the parameters (`f ∉ xs`);
    * a handler operation parameter is not the reserved name `"resume"`;
    * non-`succ` match branches bind nothing, the `succ` branch binds one;
    * a literal `con` never carries the reserved `succ` label (this travels with
      `con`-values through `DenotableRel.con`).
  `WFExp` is threaded through the relations (parallel to the `fvs ⊆ Γ` scoping
  premises) and consumed at exactly the spots above.

  DESIGN
  ------
  `toLN Γ t` rewrites a named term to its de Bruijn form under a context `Γ`
  (the binders in scope, innermost first); a `var x` becomes `bvar (Γ.idxOf x)`
  (first/innermost occurrence, so shadowing is handled). Binder arities match by
  construction: a named `lam xs` becomes an LN `lam xs.length`, etc.

  The runtime correspondence decomposes cleanly (no step-indexed logical
  relation needed): addresses are shared (`VAddr = Nat`), so
    * `EnvRel Γ ρn ρl`     relates a named env to an LN address stack (store-free);
    * `DenotableRel`/`ValueRel`/`KontRel` relate stored values structurally
       (closures carry an `EnvRel` for their captured env + a `toLN` of their body);
    * `StoreRel σn σl`     is pointwise `DenotableRel`.
-/
import DMCFA.Semantics
import DMCFA.LNSemantics

namespace DMCFA.Bridge

open DMCFA

/-! ## Name → de Bruijn translation -/

mutual

def toLNAExp (Γ : List Var) : AExp → LN.AExp
  | .var x => .bvar (Γ.idxOf x)
  | .lam xs body => .lam xs.length (toLNExp (xs ++ Γ) body)
  | .con c => .con c
  | .succE x => .succE (.bvar (Γ.idxOf x))
termination_by ae => sizeOf ae

def toLNCExp (Γ : List Var) : CExp → LN.CExp
  | .atomic ae => .atomic (toLNAExp Γ ae)
  | .funApp f aes => .funApp (toLNAExp Γ f) (toLNAExpList Γ aes)
  | .opApp op x => .opApp op (.bvar (Γ.idxOf x))
  | .matchE ae bs => .matchE (toLNAExp Γ ae) (toLNBranchList Γ bs)
  | .handler h e l => .handler (toLNHandler Γ h) (toLNExp Γ e) l
  -- recursive def: self at `bvar 0`, the `xs.length` params at `bvar 1..`
  | .funDef f xs e => .funDef xs.length (toLNExp (f :: xs ++ Γ) e)
termination_by ce => sizeOf ce

def toLNExp (Γ : List Var) : Exp → LN.Exp
  | .letE y ce e l => .letE (toLNCExp Γ ce) (toLNExp (y :: Γ) e) l
  | .tail ce l => .tail (toLNCExp Γ ce) l
termination_by e => sizeOf e

def toLNBranch (Γ : List Var) : Branch → LN.Branch
  -- named branches bind `[]` (non-succ) or `[x]` (succ); LN binds 0 / 1 by label
  | .branch c xs e => .branch c (toLNExp (xs ++ Γ) e)
termination_by b => sizeOf b

def toLNHandler (Γ : List Var) : Handler → LN.Handler
  | ⟨(x_ret, e_ret), ops⟩ =>
      ⟨toLNExp (x_ret :: Γ) e_ret, toLNOpClauses Γ ops⟩
termination_by h => sizeOf h

def toLNAExpList (Γ : List Var) : List AExp → List LN.AExp
  | [] => []
  | ae :: rest => toLNAExp Γ ae :: toLNAExpList Γ rest
termination_by aes => sizeOf aes

def toLNBranchList (Γ : List Var) : List Branch → List LN.Branch
  | [] => []
  | b :: rest => toLNBranch Γ b :: toLNBranchList Γ rest
termination_by bs => sizeOf bs

-- op-clause body binds `bvar 0 = arg`, `bvar 1 = resume`
def toLNOpClauses (Γ : List Var) : List (OpName × Var × Exp) → List (OpName × LN.Exp)
  | [] => []
  | (op, x, e) :: rest => (op, toLNExp (x :: "resume" :: Γ) e) :: toLNOpClauses Γ rest
termination_by ops => sizeOf ops

end

/-! ## Source-program well-formedness

The bare evaluation relations do not carry the source-level binding hygiene that
the name↔de-Bruijn translation depends on:
  * lambda / recursive-function parameters are `Nodup` and the recursive name is
    not among the parameters (`f ∉ xs`);
  * a handler operation parameter is not the reserved name `"resume"`;
  * non-`succ` match branches bind nothing, the `succ` branch binds exactly one.
`WFExp` packages exactly these conditions; it is threaded through the relations
(parallel to the `fvs ⊆ Γ` scoping premises) and the simulations. -/

mutual

def WFAExp : AExp → Prop
  | .var _ => True
  | .lam xs body => xs.Nodup ∧ WFExp body
  -- a literal `con` never carries the reserved `succ` label (successors use `succE`),
  -- so a con-value's match always selects a non-`succ` (zero-binder) branch
  | .con c => c ≠ ConLabel.succ
  | .succE _ => True
termination_by ae => sizeOf ae

def WFCExp : CExp → Prop
  | .atomic ae => WFAExp ae
  | .funApp f aes => WFAExp f ∧ WFAExpList aes
  | .opApp _ _ => True
  | .matchE ae bs => WFAExp ae ∧ WFBranchList bs
  | .handler h e _ => WFHandler h ∧ WFExp e
  | .funDef f xs e => xs.Nodup ∧ f ∉ xs ∧ WFExp e
termination_by ce => sizeOf ce

def WFExp : Exp → Prop
  | .letE _ ce e _ => WFCExp ce ∧ WFExp e
  | .tail ce _ => WFCExp ce
termination_by e => sizeOf e

def WFBranch : Branch → Prop
  | .branch .succ xs e => (∃ x, xs = [x]) ∧ WFExp e
  | .branch _ xs e => xs = [] ∧ WFExp e
termination_by b => sizeOf b

def WFHandler : Handler → Prop
  | ⟨(_, e_ret), ops⟩ => WFExp e_ret ∧ WFOpList ops
termination_by h => sizeOf h

def WFAExpList : List AExp → Prop
  | [] => True
  | a :: r => WFAExp a ∧ WFAExpList r
termination_by aes => sizeOf aes

def WFBranchList : List Branch → Prop
  | [] => True
  | b :: r => WFBranch b ∧ WFBranchList r
termination_by bs => sizeOf bs

def WFOpList : List (OpName × Var × Exp) → Prop
  | [] => True
  | (_, x, e) :: r => x ≠ "resume" ∧ WFExp e ∧ WFOpList r
termination_by ops => sizeOf ops
end

/-! ## Environment relation

`EnvRel Γ ρn ρl` says the LN address stack `ρl` realizes the named environment
`ρn` over the in-scope names `Γ`: same length, and each in-scope name resolves
(via its innermost/`idxOf` index) to the same address on both sides. It is
store-independent — addresses are shared between the two machines. -/

structure EnvRel (Γ : List Var) (ρn : Env) (ρl : LN.Env) : Prop where
  len : ρl.stack.length = Γ.length
  lookup : ∀ x ∈ Γ, ρn x = ρl.lookup (Γ.idxOf x)

/-- Pushing one binding: `let`, lambda parameter, match-succ binder, etc. -/
theorem EnvRel.push {Γ ρn ρl} (h : EnvRel Γ ρn ρl) (y : Var) (a : VAddr) :
    EnvRel (y :: Γ) (ρn.extend y a) (ρl.push a) := by
  constructor
  · simp [LN.Env.push, h.len]
  · intro x hx
    by_cases hxy : x = y
    · subst hxy
      simp [Env.extend, LN.Env.push, LN.Env.lookup]
    · have hxΓ : x ∈ Γ := by simpa [hxy] using hx
      have hyx : (y == x) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact fun heq => hxy heq.symm
      have hidx : (y :: Γ).idxOf x = Γ.idxOf x + 1 := by
        simp [List.idxOf_cons, hyx]
      have hext : (ρn.extend y a) x = ρn x := by simp [Env.extend, hxy]
      rw [hext, hidx, h.lookup x hxΓ]
      simp [LN.Env.push, LN.Env.lookup]

/-- `extendMany` over a `zip` leaves names outside `xs` untouched. -/
private theorem extendMany_zip_not_mem {ρ : Env} {xs : List Var} {as : List VAddr} {y : Var}
    (hy : y ∉ xs) : (ρ.extendMany (xs.zip as)) y = ρ y := by
  induction xs generalizing ρ as with
  | nil => simp [Env.extendMany]
  | cons x xs' ih =>
    cases as with
    | nil => simp [Env.extendMany]
    | cons a as' =>
      have hne : y ≠ x := fun heq => hy (heq ▸ List.mem_cons_self ..)
      have hy' : y ∉ xs' := fun hm => hy (List.mem_cons_of_mem _ hm)
      have hstep : ρ.extendMany ((x, a) :: xs'.zip as') = (ρ.extend x a).extendMany (xs'.zip as') := by
        simp only [Env.extendMany, List.foldl_cons]
      rw [List.zip_cons_cons, hstep, ih hy']
      simp [Env.extend, hne]

/-- For distinct `xs` of matching length, `extendMany` binds `y = xs[i]` to `as[i]`. -/
private theorem extendMany_zip_mem {ρ : Env} {xs : List Var} {as : List VAddr} {y : Var}
    (hlen : xs.length = as.length) (hnd : xs.Nodup) (hy : y ∈ xs) :
    (ρ.extendMany (xs.zip as)) y = as[xs.idxOf y]? := by
  induction xs generalizing ρ as with
  | nil => exact absurd hy (List.not_mem_nil)
  | cons x xs' ih =>
    cases as with
    | nil => simp at hlen
    | cons a as' =>
      have hlen' : xs'.length = as'.length := by simpa using hlen
      have hstep : ρ.extendMany ((x, a) :: xs'.zip as') = (ρ.extend x a).extendMany (xs'.zip as') := by
        simp only [Env.extendMany, List.foldl_cons]
      rw [List.zip_cons_cons, hstep, List.idxOf_cons]
      rcases List.mem_cons.mp hy with h | h
      · subst h
        rw [extendMany_zip_not_mem (List.nodup_cons.mp hnd).1]
        simp [Env.extend]
      · have hyx : y ≠ x := fun heq => (List.nodup_cons.mp hnd).1 (heq ▸ h)
        rw [ih hlen' (List.nodup_cons.mp hnd).2 h,
            show (x == y) = false by simpa using fun he => hyx he.symm]
        simp

/-- `idxOf` of a member of the left part of an append. -/
private theorem idxOf_append_left {xs Γ : List Var} {y : Var} (hy : y ∈ xs) :
    (xs ++ Γ).idxOf y = xs.idxOf y := by
  induction xs with
  | nil => exact absurd hy (List.not_mem_nil)
  | cons x xs' ih =>
    rw [List.cons_append, List.idxOf_cons, List.idxOf_cons]
    by_cases hxy : x = y
    · simp [hxy]
    · rw [show (x == y) = false by simpa using hxy]
      rcases List.mem_cons.mp hy with h | h
      · exact absurd h.symm hxy
      · simp [ih h]

/-- `idxOf` of an element not in the left part shifts past it. -/
private theorem idxOf_append_right {xs Γ : List Var} {y : Var} (hy : y ∉ xs) :
    (xs ++ Γ).idxOf y = xs.length + Γ.idxOf y := by
  induction xs with
  | nil => simp
  | cons x xs' ih =>
    have hne : x ≠ y := fun heq => hy (heq ▸ List.mem_cons_self ..)
    have hy' : y ∉ xs' := fun hm => hy (List.mem_cons_of_mem _ hm)
    rw [List.cons_append, List.idxOf_cons, show (x == y) = false by simpa using hne]
    simp [ih hy', List.length_cons]
    omega

/-- Pushing several distinct bindings at once (non-recursive function call):
`ρl.pushMany as` realizes `ρn.extendMany (xs.zip as)` over `xs ++ Γ`.
Requires `xs.Nodup` (the named `Closure.params_nodup`) so the de Bruijn index
of each parameter (`idxOf`, innermost) coincides with its position. -/
theorem EnvRel.pushMany {Γ ρn ρl} (h : EnvRel Γ ρn ρl) {xs : List Var} {as : List VAddr}
    (hlen : xs.length = as.length) (hnd : xs.Nodup) :
    EnvRel (xs ++ Γ) (ρn.extendMany (xs.zip as)) (ρl.pushMany as) := by
  constructor
  · simp only [LN.Env.pushMany, List.length_append, h.len, hlen]
  · intro y hy
    by_cases hyxs : y ∈ xs
    · -- y is one of the freshly-pushed parameters
      have hidx_lt : xs.idxOf y < xs.length := List.idxOf_lt_length_of_mem hyxs
      rw [extendMany_zip_mem hlen hnd hyxs, idxOf_append_left hyxs]
      simp only [LN.Env.pushMany, LN.Env.lookup]
      rw [List.getElem?_append_left (by omega)]
    · -- y comes from the outer context Γ
      have hyΓ : y ∈ Γ := (List.mem_append.mp hy).resolve_left hyxs
      rw [extendMany_zip_not_mem hyxs, h.lookup y hyΓ, idxOf_append_right hyxs]
      simp only [LN.Env.pushMany, LN.Env.lookup]
      rw [List.getElem?_append_right (by omega)]
      congr 1
      omega

/-- Recursive function call: self at `bvar 0`, the `xs` args at `bvar 1..`.
The named env extends `f ↦ a_f` first (innermost) then the params on top; the
LN env pushes the params then the self address, so self lands at the front.
Faithfulness requires `f ∉ xs` (otherwise the context `f :: xs ++ Γ` would put
`f` at index `0`, but the named env would have `f` shadowed by a parameter). -/
theorem EnvRel.pushManySelf {Γ ρn ρl} (h : EnvRel Γ ρn ρl) {xs : List Var} {as : List VAddr}
    {f : Var} {a_f : VAddr} (hlen : xs.length = as.length) (hnd : xs.Nodup) (hf : f ∉ xs) :
    EnvRel (f :: xs ++ Γ) ((ρn.extend f a_f).extendMany (xs.zip as)) ((ρl.pushMany as).push a_f) := by
  constructor
  · simp only [LN.Env.push, LN.Env.pushMany, List.length_cons, List.length_append, h.len, hlen]
    omega
  · intro y hy
    by_cases hyf : y = f
    · subst hyf
      -- y = f is the head; idxOf = 0, resolves to a_f on both sides
      have hidx : (y :: xs ++ Γ).idxOf y = 0 := by simp
      rw [hidx, extendMany_zip_not_mem hf]
      simp [Env.extend, LN.Env.push, LN.Env.lookup]
    · have hyne : (f == y) = false := by simpa using fun he => hyf he.symm
      have hidx : (f :: xs ++ Γ).idxOf y = (xs ++ Γ).idxOf y + 1 := by
        simp [List.idxOf_cons, hyne]
      rw [hidx]
      have hyrest : y ∈ xs ++ Γ := (List.mem_cons.mp hy).resolve_left hyf
      have hyrest' := List.mem_append.mp hyrest
      by_cases hyxs : y ∈ xs
      · have hidx_lt : xs.idxOf y < xs.length := List.idxOf_lt_length_of_mem hyxs
        rw [extendMany_zip_mem hlen hnd hyxs, idxOf_append_left hyxs]
        simp only [LN.Env.push, LN.Env.pushMany, LN.Env.lookup, List.getElem?_cons_succ]
        rw [List.getElem?_append_left (by omega)]
      · have hyΓ : y ∈ Γ := hyrest'.resolve_left hyxs
        have hext : (ρn.extend f a_f) y = ρn y := by simp [Env.extend, hyf]
        rw [extendMany_zip_not_mem hyxs, hext, h.lookup y hyΓ, idxOf_append_right hyxs]
        simp only [LN.Env.push, LN.Env.pushMany, LN.Env.lookup, List.getElem?_cons_succ]
        rw [List.getElem?_append_right (by omega)]
        congr 1
        omega

/-! ## Value / denotable / continuation relations

Structural correspondences between stored values on the two machines. A closure
relates to an LN closure when their captured environments relate (`EnvRel`),
their arities agree, and the LN body is the `toLN` of the named body under the
capture context. Recursion differs by representation: the named machine captures
the function's own name in its environment (`ρ.extend f a_f`); the LN machine
records `selfAddr = some a_f` (self at `bvar 0`). Both are handled by
`ClosureRel.rec`. -/

mutual

inductive DenotableRel : Denotable → LN.Denotable → Prop where
  | closure {dn dl} : ClosureRel dn dl → DenotableRel (Denotable.closure dn) (LN.Denotable.closure dl)
  | kont {Γ ρn ρl hn hl κn κl} :
      EnvRel Γ ρn ρl → HandlerRel Γ hn hl → KontRel κn κl →
      DenotableRel (Denotable.kontClosure hn ρn κn) (LN.Denotable.kontClosure hl ρl κl)
  | con {c} : c ≠ ConLabel.succ → DenotableRel (Denotable.conLabel c) (LN.Denotable.conLabel c)
  | succ {a} : DenotableRel (Denotable.succVal a) (LN.Denotable.succVal a)

inductive ClosureRel : Closure → LN.Closure → Prop where
  | lam {Γ xs body ρn hnd ρl arity bodyl} :
      EnvRel Γ ρn ρl → arity = xs.length → bodyl = toLNExp (xs ++ Γ) body →
      body.fvs ⊆ xs ++ Γ → WFExp body →
      ClosureRel ⟨xs, body, ρn, hnd⟩ ⟨arity, bodyl, ρl, none⟩
  | recF {Γ xs body f a_f ρn hnd ρl arity bodyl} :
      EnvRel Γ ρn ρl → arity = xs.length → bodyl = toLNExp (f :: xs ++ Γ) body →
      body.fvs ⊆ f :: xs ++ Γ → f ∉ xs → WFExp body →
      ClosureRel ⟨xs, body, ρn.extend f a_f, hnd⟩ ⟨arity, bodyl, ρl, some a_f⟩

inductive HandlerRel : List Var → Handler → LN.Handler → Prop where
  | mk {Γ x_ret e_ret ops e_retl opsl} :
      e_retl = toLNExp (x_ret :: Γ) e_ret →
      opsl = toLNOpClauses Γ ops →
      e_ret.fvs ⊆ x_ret :: Γ →
      (∀ op x e, (op, x, e) ∈ ops → e.fvs ⊆ x :: "resume" :: Γ) →
      WFExp e_ret →
      (∀ op x e, (op, x, e) ∈ ops → x ≠ "resume" ∧ WFExp e) →
      HandlerRel Γ ⟨(x_ret, e_ret), ops⟩ ⟨e_retl, opsl⟩

inductive FrameRel : Frame → LN.Frame → Prop where
  | letFrame {Γ y e ρn ρl hy el} :
      EnvRel Γ ρn ρl → el = toLNExp (y :: Γ) e →
      e.fvs ⊆ y :: Γ → WFExp e →
      FrameRel (Frame.letFrame ⟨[y], e, ρn, hy⟩) (LN.Frame.letFrame el ρl)
  | handlerFrame {Γ hn hl ρn ρl} :
      EnvRel Γ ρn ρl → HandlerRel Γ hn hl →
      FrameRel (Frame.handlerFrame hn ρn) (LN.Frame.handlerFrame hl ρl)

inductive KontRel : Kont → LN.Kont → Prop where
  | nil : KontRel [] []
  | cons {frn frl κn κl} : FrameRel frn frl → KontRel κn κl → KontRel (frn :: κn) (frl :: κl)

end

/-- Result-value relation. -/
inductive ValueRel : Value → LN.Value → Prop where
  | den {dn dl} : DenotableRel dn dl → ValueRel (Value.den dn) (LN.Value.den dl)
  | suspended {op as κn κl} : KontRel κn κl →
      ValueRel (Value.suspended op as κn) (LN.Value.suspended op as κl)

/-- Store relation: pointwise denotable correspondence (shared address space). -/
def StoreRel (σn : Store) (σl : LN.Store) : Prop :=
  ∀ a, (σn a = none ∧ σl a = none) ∨
       ∃ dn dl, σn a = some dn ∧ σl a = some dl ∧ DenotableRel dn dl

/-- A named store hit transfers to the LN store, with related denotables. -/
theorem StoreRel.some {σn σl} (h : StoreRel σn σl) {a dn} (ha : σn a = some dn) :
    ∃ dl, σl a = some dl ∧ DenotableRel dn dl := by
  rcases h a with ⟨h1, _⟩ | ⟨dn', dl, h1, h2, h3⟩
  · rw [ha] at h1; exact absurd h1 (by simp)
  · rw [ha] at h1; cases h1; exact ⟨dl, h2, h3⟩

/-- A named store miss transfers to the LN store. -/
theorem StoreRel.none {σn σl} (h : StoreRel σn σl) {a} (ha : σn a = none) : σl a = none := by
  rcases h a with ⟨_, h2⟩ | ⟨dn', dl, h1, _, _⟩
  · exact h2
  · rw [ha] at h1; exact absurd h1 (by simp)

/-- A LN store miss transfers back to the named store. -/
theorem StoreRel.none' {σn σl} (h : StoreRel σn σl) {a} (ha : σl a = Option.none) :
    σn a = Option.none := by
  rcases h a with ⟨h1, _⟩ | ⟨dn', dl, _, h2, _⟩
  · exact h1
  · rw [ha] at h2; exact absurd h2 (by simp)

/-- A LN store hit transfers back to the named store, with related denotables. -/
theorem StoreRel.some' {σn σl} (h : StoreRel σn σl) {a dl} (ha : σl a = Option.some dl) :
    ∃ dn, σn a = Option.some dn ∧ DenotableRel dn dl := by
  rcases h a with ⟨_, h2⟩ | ⟨dn', dl', h1, h2, h3⟩
  · rw [ha] at h2; exact absurd h2 (by simp)
  · rw [ha] at h2; cases h2; exact ⟨dn', h1, h3⟩

/-- Extending both stores at the *same* address with related denotables
preserves the relation (both machines allocate from the shared address space). -/
theorem StoreRel.extend {σn σl} (h : StoreRel σn σl) {a dn dl} (hrel : DenotableRel dn dl) :
    StoreRel (σn.extend a dn) (σl.extend a dl) := by
  intro a'
  by_cases ha : a' = a
  · subst ha
    exact Or.inr ⟨dn, dl, by simp [Store.extend], by simp [LN.Store.extend], hrel⟩
  · rcases h a' with ⟨h1, h2⟩ | ⟨dn', dl', h1, h2, h3⟩
    · exact Or.inl ⟨by simpa [Store.extend, ha] using h1, by simpa [LN.Store.extend, ha] using h2⟩
    · exact Or.inr ⟨dn', dl', by simpa [Store.extend, ha] using h1,
                    by simpa [LN.Store.extend, ha] using h2, h3⟩

/-- A named store extended at every freshly-allocated zipped address transfers to
the LN store extended at the *same* addresses, given pointwise `DenotableRel`. -/
theorem StoreRel.extendManyZip {σn σl} (h : StoreRel σn σl) {as : List VAddr}
    {ds : List Denotable} {dsl : List LN.Denotable}
    (hrel : List.Forall₂ DenotableRel ds dsl) :
    StoreRel ((List.zip as ds).foldl (fun s (p : VAddr × Denotable) => s.extend p.1 p.2) σn)
             ((List.zip as dsl).foldl (fun s (p : VAddr × LN.Denotable) => s.extend p.1 p.2) σl) := by
  induction as generalizing σn σl ds dsl with
  | nil => simpa using h
  | cons a as' ih =>
    cases hrel with
    | nil => simpa using h
    | cons hd htl =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      exact ih (h.extend hd) htl

/-! ## Atomic evaluation correspondence -/

/-- Evaluating an atomic expression corresponds across the two machines: the
translation of `ae` evaluates to a related denotable. -/
theorem evalAtomic_forward {Γ ρn ρl σn σl} (henv : EnvRel Γ ρn ρl) (hst : StoreRel σn σl)
    {ae : AExp} (hsc : ae.fvs ⊆ Γ) (hwf : WFAExp ae)
    {dn : Denotable} (h : evalAtomic ae ρn σn = some dn) :
    ∃ dl, LN.evalAtomic (toLNAExp Γ ae) ρl σl = some dl ∧ DenotableRel dn dl := by
  cases ae with
  | var x =>
    have hxΓ : x ∈ Γ := hsc (by simp [AExp.fvs])
    have hlk := henv.lookup x hxΓ
    change (ρn x).bind (fun a => σn a) = some dn at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨a, hρ, hσ⟩ := h
    obtain ⟨dl, hσl, hrel⟩ := hst.some hσ
    have hlk2 : ρl.lookup (Γ.idxOf x) = some a := by rw [← hlk]; exact hρ
    refine ⟨dl, ?_, hrel⟩
    simp [toLNAExp, LN.evalAtomic, hlk2, hσl]
  | lam xs body =>
    simp only [evalAtomic] at h
    split at h
    · cases h
      have hbody : body.fvs ⊆ xs ++ Γ := by
        intro y hy
        rw [List.mem_append]
        by_cases hyxs : y ∈ xs
        · exact Or.inl hyxs
        · refine Or.inr (hsc ?_)
          simp only [AExp.fvs, List.mem_filter, decide_eq_true_eq]
          exact ⟨hy, hyxs⟩
      rw [WFAExp] at hwf
      exact ⟨_, by simp only [toLNAExp, LN.evalAtomic],
             .closure (.lam henv rfl rfl hbody hwf.2)⟩
    · simp at h
  | con c =>
    simp only [evalAtomic] at h; cases h
    rw [WFAExp] at hwf
    exact ⟨_, by simp only [toLNAExp, LN.evalAtomic], .con hwf⟩
  | succE x =>
    have hxΓ : x ∈ Γ := hsc (by simp [AExp.fvs])
    have hlk := henv.lookup x hxΓ
    change (ρn x).bind (fun a => (σn a).bind (fun _ => some (Denotable.succVal a))) = some dn at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨a, hρ, hσbind⟩ := h
    rw [Option.bind_eq_some_iff] at hσbind
    obtain ⟨d0, hσ, heq⟩ := hσbind
    obtain ⟨dl, hσl, _⟩ := hst.some hσ
    have hlk2 : ρl.lookup (Γ.idxOf x) = some a := by rw [← hlk]; exact hρ
    rw [← Option.some_inj.mp heq]
    refine ⟨_, ?_, .succ⟩
    simp [toLNAExp, LN.evalAtomic, LN.evalAddr, hlk2, hσl]

/-! ## findBranch / findOp correspondence -/

/-- Forward: a named branch lookup transfers to the LN branch list. -/
private theorem findBranch_forward {Γ : List Var} {bs : List Branch} {c : ConLabel}
    {xs : List Var} {e : Exp} (h : findBranch bs c = some (xs, e)) :
    LN.findBranch (toLNBranchList Γ bs) c = some (toLNExp (xs ++ Γ) e) := by
  induction bs with
  | nil => simp [findBranch, List.findSome?] at h
  | cons b rest ih =>
    cases b with
    | branch c' xs' e' =>
      simp only [findBranch, List.findSome?] at h
      simp only [toLNBranchList, toLNBranch, LN.findBranch, List.findSome?]
      by_cases hc : c' = c
      · simp only [hc] at h ⊢
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        rfl
      · simp only [if_neg hc] at h ⊢
        exact ih h

/-- Backward: an LN branch lookup transfers back to the named branch list. -/
private theorem findBranch_backward {Γ : List Var} {bs : List Branch} {c : ConLabel}
    {el : LN.Exp} (h : LN.findBranch (toLNBranchList Γ bs) c = some el) :
    ∃ xs e, findBranch bs c = some (xs, e) ∧ el = toLNExp (xs ++ Γ) e := by
  induction bs with
  | nil => simp [toLNBranchList, LN.findBranch] at h
  | cons b rest ih =>
    cases b with
    | branch c' xs' e' =>
      simp only [toLNBranchList, toLNBranch, LN.findBranch, List.findSome?] at h
      simp only [findBranch, List.findSome?]
      by_cases hc : c' = c
      · simp only [hc] at h ⊢
        exact ⟨xs', e', rfl, (Option.some.inj h).symm⟩
      · simp only [if_neg hc] at h ⊢
        exact ih h

/-- The filtered free variables of a found branch are contained in the list's fvs. -/
private theorem findBranch_fvs {bs : List Branch} {c : ConLabel} {xs : List Var} {e : Exp}
    (h : findBranch bs c = some (xs, e)) : e.fvs.filter (· ∉ xs) ⊆ branchListFvs bs := by
  induction bs with
  | nil => simp [findBranch, List.findSome?] at h
  | cons b rest ih =>
    cases b with
    | branch c' xs' e' =>
      simp only [findBranch, List.findSome?] at h
      simp only [branchListFvs, Branch.fvs]
      by_cases hc : c' = c
      · simp only [hc] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        exact List.subset_append_left _ _
      · simp only [if_neg hc] at h
        exact (ih h).trans (List.subset_append_right _ _)

/-- Scoping transfer for a found branch: `e.fvs ⊆ xs ++ Γ` when the branch list
is scoped under `Γ`. -/
private theorem findBranch_scope {Γ : List Var} {bs : List Branch} {c : ConLabel}
    {xs : List Var} {e : Exp} (hfind : findBranch bs c = some (xs, e))
    (hsc : branchListFvs bs ⊆ Γ) : e.fvs ⊆ xs ++ Γ := by
  intro y hy
  rw [List.mem_append]
  by_cases hyxs : y ∈ xs
  · exact Or.inl hyxs
  · refine Or.inr (hsc (findBranch_fvs hfind ?_))
    rw [List.mem_filter]
    exact ⟨hy, by simp [hyxs]⟩

/-- Well-formedness transfer for a found branch: the branch body is well-formed,
and (for a `succ` branch) it binds exactly one variable / (otherwise) none. -/
private theorem findBranch_wf {bs : List Branch} {c : ConLabel} {xs : List Var} {e : Exp}
    (hfind : findBranch bs c = some (xs, e)) (hwf : WFBranchList bs) :
    WFExp e ∧ (c = ConLabel.succ → ∃ x, xs = [x]) ∧ (c ≠ ConLabel.succ → xs = []) := by
  induction bs with
  | nil => simp [findBranch, List.findSome?] at hfind
  | cons b rest ih =>
    cases b with
    | branch c' xs' e' =>
      simp only [findBranch, List.findSome?] at hfind
      rw [WFBranchList] at hwf
      by_cases hc : c' = c
      · subst hc
        simp only [if_pos] at hfind
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj hfind
        cases c' with
        | succ =>
          simp only [WFBranch] at hwf
          obtain ⟨⟨xb, hxb⟩, hbody⟩ := hwf.1
          exact ⟨hbody, fun _ => ⟨xb, hxb⟩, fun hne => absurd rfl hne⟩
        | _ =>
          simp only [WFBranch] at hwf
          obtain ⟨hnil, hbody⟩ := hwf.1
          exact ⟨hbody, fun h => by simp at h, fun _ => hnil⟩
      · simp only [if_neg hc] at hfind
        exact ih hfind hwf.2

/-- Forward: a named op lookup transfers to the LN handler given a `HandlerRel`. -/
private theorem findOp_forward {Γ : List Var} {hn : Handler} {hl : LN.Handler} {op : OpName}
    {x : Var} {e : Exp} (hrel : HandlerRel Γ hn hl) (h : hn.findOp op = some (x, e)) :
    hl.findOp op = some (toLNExp (x :: "resume" :: Γ) e) := by
  obtain ⟨⟨xret, eret⟩, ops⟩ := hn
  cases hrel with
  | mk hret hops hretsc hopssc hretwf hopswf =>
    subst hops
    clear hret hretsc hopssc hretwf hopswf
    simp only [Handler.findOp] at h
    simp only [LN.Handler.findOp]
    induction ops with
    | nil => simp [List.findSome?] at h
    | cons p rest ih =>
      obtain ⟨op', x', e'⟩ := p
      simp only [List.findSome?, toLNOpClauses] at h ⊢
      by_cases hop : op' = op
      · simp only [hop] at h ⊢
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
        rfl
      · simp only [if_neg hop] at h ⊢
        exact ih h

/-- Backward: an LN op lookup transfers back to the named handler. -/
private theorem findOp_backward {Γ : List Var} {hn : Handler} {hl : LN.Handler} {op : OpName}
    {el : LN.Exp} (hrel : HandlerRel Γ hn hl) (h : hl.findOp op = some el) :
    ∃ x e, hn.findOp op = some (x, e) ∧ el = toLNExp (x :: "resume" :: Γ) e := by
  obtain ⟨⟨xret, eret⟩, ops⟩ := hn
  cases hrel with
  | mk hret hops hretsc hopssc hretwf hopswf =>
    subst hops
    clear hret hretsc hopssc hretwf hopswf
    simp only [LN.Handler.findOp] at h
    simp only [Handler.findOp]
    induction ops with
    | nil => simp [toLNOpClauses] at h
    | cons p rest ih =>
      obtain ⟨op', x', e'⟩ := p
      simp only [List.findSome?, toLNOpClauses] at h ⊢
      by_cases hop : op' = op
      · simp only [hop] at h ⊢
        exact ⟨x', e', rfl, (Option.some.inj h).symm⟩
      · simp only [if_neg hop] at h ⊢
        exact ih h

/-- A successful named `findOp` yields membership in the op-clause list. -/
private theorem findOp_mem {ops : List (OpName × Var × Exp)} {op : OpName} {x : Var} {e : Exp}
    (h : (Handler.findOp ⟨pr, ops⟩ op) = some (x, e)) : (op, x, e) ∈ ops := by
  simp only [Handler.findOp] at h
  induction ops with
  | nil => simp [List.findSome?] at h
  | cons p rest ih =>
    obtain ⟨op', x', e'⟩ := p
    simp only [List.findSome?] at h
    by_cases hop : op' = op
    · subst hop
      simp only [if_pos rfl] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ Option.some.inj h
      exact List.mem_cons_self ..
    · simp only [if_neg hop] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- `hasOp` agrees across the relation (used for the capture case). -/
private theorem hasOp_eq {Γ : List Var} {hn : Handler} {hl : LN.Handler} {op : OpName}
    (hrel : HandlerRel Γ hn hl) : hl.hasOp op = hn.hasOp op := by
  obtain ⟨⟨xret, eret⟩, ops⟩ := hn
  cases hrel with
  | mk hret hops hretsc hopssc hretwf hopswf =>
    subst hops
    clear hret hretsc hopssc hretwf hopswf
    simp only [Handler.hasOp, LN.Handler.hasOp]
    induction ops with
    | nil => simp [toLNOpClauses]
    | cons p rest ih =>
      obtain ⟨op', x', e'⟩ := p
      simp only [toLNOpClauses, List.any_cons]
      rw [ih]

/-- An op clause's filtered fvs are contained in the clause list's fvs. -/
private theorem opClause_fvs {ops : List (OpName × Var × Exp)} {op : OpName} {x : Var} {e : Exp}
    (h : (op, x, e) ∈ ops) :
    e.fvs.filter (fun v => v ≠ x && v ≠ "resume") ⊆ opClauseListFvs ops := by
  induction ops with
  | nil => exact absurd h (List.not_mem_nil)
  | cons p rest ih =>
    obtain ⟨op', x', e'⟩ := p
    simp only [opClauseListFvs]
    rcases List.mem_cons.mp h with heq | hmem
    · obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq .. ▸ (Prod.mk.injEq .. ▸ heq)
      exact List.subset_append_left _ _
    · exact (ih hmem).trans (List.subset_append_right _ _)

/-- Membership-form of `WFOpList`: every op clause has `x ≠ "resume"` and a
well-formed body. -/
private theorem wfOpList_mem {ops : List (OpName × Var × Exp)} (hwf : WFOpList ops)
    {op : OpName} {x : Var} {e : Exp} (hmem : (op, x, e) ∈ ops) : x ≠ "resume" ∧ WFExp e := by
  induction ops with
  | nil => exact absurd hmem (List.not_mem_nil)
  | cons p rest ih =>
    obtain ⟨op', x', e'⟩ := p
    rw [WFOpList] at hwf
    rcases List.mem_cons.mp hmem with heq | hm
    · obtain ⟨_, rfl, rfl⟩ := Prod.mk.injEq .. ▸ (Prod.mk.injEq .. ▸ heq)
      exact ⟨hwf.1, hwf.2.1⟩
    · exact ih hwf.2.2 hm

/-- Build a `HandlerRel` from handler-scoping and well-formedness. -/
private theorem handlerRel_of_scope {Γ : List Var} {hn : Handler} (hsc : Handler.fvs hn ⊆ Γ)
    (hwf : WFHandler hn) :
    HandlerRel Γ hn (toLNHandler Γ hn) := by
  obtain ⟨⟨xret, eret⟩, ops⟩ := hn
  simp only [Handler.fvs] at hsc
  rw [WFHandler] at hwf
  have hsc_split := List.append_subset.mp hsc
  simp only [toLNHandler]
  refine .mk rfl rfl ?_ ?_ hwf.1 (fun op x e hmem => wfOpList_mem hwf.2 hmem)
  · intro y hy
    by_cases hyx : y = xret
    · subst hyx; exact List.mem_cons_self ..
    · refine List.mem_cons_of_mem _ (hsc_split.1 ?_)
      rw [List.mem_filter]; exact ⟨hy, by simp [hyx]⟩
  · intro op x e hmem y hy
    by_cases hyx : y = x
    · subst hyx; exact List.mem_cons_self ..
    · by_cases hyr : y = "resume"
      · subst hyr; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
      · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hsc_split.2 (opClause_fvs hmem ?_)))
        rw [List.mem_filter]; exact ⟨hy, by simp [hyx, hyr]⟩

/-! ## Backward atomic evaluation correspondence -/

/-- The reverse of `evalAtomic_forward`: an LN atomic evaluation of the
translation transfers back to the named machine. -/
theorem evalAtomic_backward {Γ ρn ρl σn σl} (henv : EnvRel Γ ρn ρl) (hst : StoreRel σn σl)
    {ae : AExp} (hsc : ae.fvs ⊆ Γ) (hwf : WFAExp ae) {dl : LN.Denotable}
    (h : LN.evalAtomic (toLNAExp Γ ae) ρl σl = some dl) :
    ∃ dn, evalAtomic ae ρn σn = some dn ∧ DenotableRel dn dl := by
  cases ae with
  | var x =>
    have hxΓ : x ∈ Γ := hsc (by simp [AExp.fvs])
    have hlk := henv.lookup x hxΓ
    simp only [toLNAExp] at h
    change (ρl.lookup (Γ.idxOf x)).bind (fun a => σl a) = some dl at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨a, hρl, hσl⟩ := h
    have hρn : ρn x = some a := by rw [hlk]; exact hρl
    -- find the LN-stored denotable, transfer back via StoreRel
    rcases hst a with ⟨h1, h2⟩ | ⟨dn', dl', h1, h2, h3⟩
    · rw [h2] at hσl; exact absurd hσl (by simp)
    · rw [h2] at hσl; cases hσl
      refine ⟨dn', ?_, h3⟩
      change (ρn x).bind (fun a => σn a) = some dn'
      rw [hρn]; exact h1
  | lam xs body =>
    simp only [toLNAExp, LN.evalAtomic] at h
    cases h
    have hbody : body.fvs ⊆ xs ++ Γ := by
      intro y hy
      rw [List.mem_append]
      by_cases hyxs : y ∈ xs
      · exact Or.inl hyxs
      · refine Or.inr (hsc ?_)
        simp only [AExp.fvs, List.mem_filter, decide_eq_true_eq]
        exact ⟨hy, hyxs⟩
    rw [WFAExp] at hwf
    have hnd : xs.Nodup := hwf.1
    exact ⟨Denotable.closure ⟨xs, body, ρn, hnd⟩,
      by simp only [evalAtomic, dif_pos hnd], .closure (.lam henv rfl rfl hbody hwf.2)⟩
  | con c =>
    simp only [toLNAExp, LN.evalAtomic] at h; cases h
    rw [WFAExp] at hwf
    exact ⟨_, by simp only [evalAtomic], .con hwf⟩
  | succE x =>
    have hxΓ : x ∈ Γ := hsc (by simp [AExp.fvs])
    have hlk := henv.lookup x hxΓ
    simp only [toLNAExp] at h
    change (ρl.lookup (Γ.idxOf x)).bind
      (fun a => (σl a).bind (fun _ => some (LN.Denotable.succVal a))) = some dl at h
    rw [Option.bind_eq_some_iff] at h
    obtain ⟨a, hρl, hσbind⟩ := h
    rw [Option.bind_eq_some_iff] at hσbind
    obtain ⟨d0, hσl, heq⟩ := hσbind
    have hρn : ρn x = some a := by rw [hlk]; exact hρl
    rcases hst a with ⟨h1, h2⟩ | ⟨dn', dl', h1, h2, h3⟩
    · rw [h2] at hσl; exact absurd hσl (by simp)
    · rw [h2] at hσl; cases hσl
      rw [← Option.some_inj.mp heq]
      refine ⟨_, ?_, .succ⟩
      change (ρn x).bind (fun a => (σn a).bind (fun _ => some (Denotable.succVal a))) = some _
      rw [hρn]; simp only [Option.bind_some]; rw [h1]; rfl

/-- Forward correspondence for a list of atomic arguments. -/
private theorem evalArgs_forward {Γ ρn ρl σn σl} (henv : EnvRel Γ ρn ρl) (hst : StoreRel σn σl)
    {aes : List AExp} (hsc : aexpListFvs aes ⊆ Γ) (hwf : WFAExpList aes) {ds : List Denotable}
    (h : List.Forall₂ (fun ae d => evalAtomic ae ρn σn = some d) aes ds) :
    ∃ dsl, List.Forall₂ (fun ae d => LN.evalAtomic ae ρl σl = some d) (toLNAExpList Γ aes) dsl ∧
      List.Forall₂ DenotableRel ds dsl := by
  induction h with
  | nil => exact ⟨[], by simp only [toLNAExpList]; exact .nil, .nil⟩
  | @cons ae d aes' ds' hd htl ih =>
    have hsc_split := List.append_subset.mp (by simpa only [aexpListFvs] using hsc)
    rw [WFAExpList] at hwf
    obtain ⟨dl, hevl, hrel⟩ := evalAtomic_forward henv hst hsc_split.1 hwf.1 hd
    obtain ⟨dsl, htll, hrell⟩ := ih hsc_split.2 hwf.2
    exact ⟨dl :: dsl, by simp only [toLNAExpList]; exact .cons hevl htll, .cons hrel hrell⟩

/-- Backward correspondence for a list of atomic arguments. -/
private theorem evalArgs_backward {Γ ρn ρl σn σl} (henv : EnvRel Γ ρn ρl) (hst : StoreRel σn σl)
    {aes : List AExp} (hsc : aexpListFvs aes ⊆ Γ) (hwf : WFAExpList aes) {dsl : List LN.Denotable}
    (h : List.Forall₂ (fun ae d => LN.evalAtomic ae ρl σl = some d) (toLNAExpList Γ aes) dsl) :
    ∃ ds, List.Forall₂ (fun ae d => evalAtomic ae ρn σn = some d) aes ds ∧
      List.Forall₂ DenotableRel ds dsl := by
  induction aes generalizing dsl with
  | nil =>
    simp only [toLNAExpList] at h
    cases h
    exact ⟨[], .nil, .nil⟩
  | cons ae aes' ih =>
    simp only [toLNAExpList] at h
    rw [WFAExpList] at hwf
    cases h with
    | cons hd htl =>
      have hsc_split := List.append_subset.mp (by simpa only [aexpListFvs] using hsc)
      obtain ⟨dn, hevn, hrel⟩ := evalAtomic_backward henv hst hsc_split.1 hwf.1 hd
      obtain ⟨ds, htln, hreln⟩ := ih hsc_split.2 hwf.2 htl
      exact ⟨dn :: ds, .cons hevn htln, .cons hrel hreln⟩

/-- `toLNAExpList` preserves length. -/
private theorem toLNAExpList_length (Γ : List Var) (aes : List AExp) :
    (toLNAExpList Γ aes).length = aes.length := by
  induction aes with
  | nil => simp [toLNAExpList]
  | cons ae rest ih => simp [toLNAExpList, ih]

/-- Two store extensions at distinct addresses commute. -/
private theorem LN.Store.extend_comm (σ : LN.Store) {a b : VAddr} (hab : a ≠ b)
    (d e : LN.Denotable) : (σ.extend a d).extend b e = (σ.extend b e).extend a d := by
  funext a'
  simp only [LN.Store.extend]
  by_cases h1 : a' = b <;> by_cases h2 : a' = a <;> simp_all

/-- Transfer per-address freshness from the named store to the LN store. -/
private theorem fresh_forward {σn σl} (hst : StoreRel σn σl) {as_v : List VAddr}
    {ds : List Denotable} {dsl : List LN.Denotable}
    (hfresh : List.Forall₂ (fun a (_ : Denotable) => σn a = none) as_v ds)
    (hrel : List.Forall₂ DenotableRel ds dsl) :
    List.Forall₂ (fun a (_ : LN.Denotable) => σl a = none) as_v dsl := by
  induction hrel generalizing as_v with
  | nil => cases hfresh; exact .nil
  | cons _ _ ih =>
    cases hfresh with
    | cons hd htl => exact .cons (hst.none hd) (ih htl)

/-- Transfer per-address freshness from the LN store back to the named store. -/
private theorem fresh_backward {σn σl} (hst : StoreRel σn σl) {as_v : List VAddr}
    {ds : List Denotable} {dsl : List LN.Denotable}
    (hfresh : List.Forall₂ (fun a (_ : LN.Denotable) => σl a = none) as_v dsl)
    (hrel : List.Forall₂ DenotableRel ds dsl) :
    List.Forall₂ (fun a (_ : Denotable) => σn a = none) as_v ds := by
  induction hrel generalizing as_v with
  | nil => cases hfresh; exact .nil
  | cons _ _ ih =>
    cases hfresh with
    | cons hd htl => exact .cons (hst.none' hd) (ih htl)

/-! ## Simulation theorems

The two machines run in lock-step: the named evaluation of `e` corresponds to
the LN evaluation of `toLN Γ e`, allocating the *same* fresh addresses on both
sides (the address space is shared). Proven by well-founded recursion on the
height-indexed evaluation relations, mirroring `DMCFA.LN.soundness_allN`. -/

/-- Forward height-indexed 5-conjunction. -/
private theorem sim_forward_allN (n : Nat) :
    -- P_exp
    (∀ {e ρn σn v σn'}, EvalExpN n e ρn σn v σn' →
      ∀ {Γ ρl σl}, EnvRel Γ ρn ρl → StoreRel σn σl → e.fvs ⊆ Γ → WFExp e →
        ∃ vl σl', LN.EvalExp (toLNExp Γ e) ρl σl vl σl' ∧ ValueRel v vl ∧ StoreRel σn' σl') ∧
    -- P_cexp
    (∀ {ce ρn σn v σn'}, EvalCExpN n ce ρn σn v σn' →
      ∀ {Γ ρl σl}, EnvRel Γ ρn ρl → StoreRel σn σl → ce.fvs ⊆ Γ → WFCExp ce →
        ∃ vl σl', LN.EvalCExp (toLNCExp Γ ce) ρl σl vl σl' ∧ ValueRel v vl ∧ StoreRel σn' σl') ∧
    -- P_continue: continue a let-frame whose body/env are described by FrameRel
    (∀ {frn frl v σn v' σn'}, ContinueFrameN n frn v σn v' σn' →
      ∀ {vl σl}, FrameRel frn frl → ValueRel v vl → StoreRel σn σl →
        ∃ vl' σl', LN.ContinueFrame frl vl σl vl' σl' ∧ ValueRel v' vl' ∧ StoreRel σn' σl') ∧
    -- P_handle
    (∀ {hn ρn v σn v' σn'}, HandleValueN n hn ρn v σn v' σn' →
      ∀ {Γ hl ρl vl σl}, EnvRel Γ ρn ρl → HandlerRel Γ hn hl → ValueRel v vl → StoreRel σn σl →
        ∃ vl' σl', LN.HandleValue hl ρl vl σl vl' σl' ∧ ValueRel v' vl' ∧ StoreRel σn' σl') ∧
    -- P_apply
    (∀ {κn d σn v σn'}, ApplyKontN n κn d σn v σn' →
      ∀ {κl dl σl}, KontRel κn κl → DenotableRel d dl → StoreRel σn σl →
        ∃ vl σl', LN.ApplyKont κl dl σl vl σl' ∧ ValueRel v vl ∧ StoreRel σn' σl') := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- ═══════════════════════ P_exp ═══════════════════════
  · intro e ρn σn v σn' h_eval Γ ρl σl henv hst hsc hwf
    match e, h_eval with
    | .tail ce l, .eval_tail h_cexp =>
      have hsc' : ce.fvs ⊆ Γ := (by simpa only [Exp.fvs] using hsc)
      have hwf' : WFCExp ce := by rw [WFExp] at hwf; exact hwf
      obtain ⟨vl, σl', hev, hvr, hsr⟩ := (sim_forward_allN _).2.1 h_cexp henv hst hsc' hwf'
      exact ⟨vl, σl', by simp only [toLNExp]; exact .eval_tail hev, hvr, hsr⟩
    | .letE y ce e' l, .eval_let h_cexp h_cont =>
      have hsc_split := List.append_subset.mp (by simpa only [Exp.fvs] using hsc)
      have hsc_ce : ce.fvs ⊆ Γ := hsc_split.1
      rw [WFExp] at hwf
      have hsc_e : e'.fvs ⊆ y :: Γ := by
        intro x hx
        by_cases hxy : x = y
        · subst hxy; exact List.mem_cons_self ..
        · refine List.mem_cons_of_mem _ (hsc_split.2 ?_)
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨hx, hxy⟩
      obtain ⟨vl, σl', hev, hvr, hsr⟩ := (sim_forward_allN _).2.1 h_cexp henv hst hsc_ce hwf.1
      have hfr : FrameRel (Frame.letFrame ⟨[y], e', ρn, List.nodup_singleton _⟩)
          (LN.Frame.letFrame (toLNExp (y :: Γ) e') ρl) := .letFrame henv rfl hsc_e hwf.2
      obtain ⟨vl', σl'', hcont, hvr', hsr'⟩ :=
        (sim_forward_allN _).2.2.1 h_cont hfr hvr hsr
      exact ⟨vl', σl'', by simp only [toLNExp]; exact .eval_let hev hcont, hvr', hsr'⟩
  -- ═══════════════════════ P_cexp ═══════════════════════
  · intro ce ρn σn v σn' h_eval Γ ρl σl henv hst hsc hwf
    match h_eval with
    | .eval_atomic (ae := ae) hatom =>
      have hsc' : ae.fvs ⊆ Γ := (by simpa only [CExp.fvs] using hsc)
      have hwf' : WFAExp ae := by rw [WFCExp] at hwf; exact hwf
      obtain ⟨dl, hevl, hrel⟩ := evalAtomic_forward henv hst hsc' hwf' hatom
      exact ⟨_, _, by simp only [toLNCExp]; exact .eval_atomic hevl, .den hrel, hst⟩
    | .eval_opApp (x := x) (op := op) (a_v := a_v) hρ =>
      have hxΓ : x ∈ Γ := hsc (by simp [CExp.fvs])
      have hlk := henv.lookup x hxΓ
      have hρl : ρl.lookup (Γ.idxOf x) = some a_v := by rw [← hlk]; exact hρ
      refine ⟨_, _, ?_, .suspended .nil, hst⟩
      simp only [toLNCExp]
      exact .eval_opApp (by simp only [LN.evalAddr]; exact hρl)
    | .eval_fun (f := f) (xs := xs) (e1 := e1) hfresh hnd hvf hσ' =>
      subst hvf; subst hσ'
      have hfresh_l : σl _ = none := hst.none hfresh
      have hbody : e1.fvs ⊆ f :: xs ++ Γ := by
        intro y hy
        simp only [CExp.fvs] at hsc
        by_cases hyf : y = f
        · subst hyf; exact List.mem_cons_self ..
        · by_cases hyxs : y ∈ xs
          · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hyxs))
          · refine List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (hsc ?_)))
            rw [List.mem_filter]
            exact ⟨hy, by simp [hyxs, hyf]⟩
      rw [WFCExp] at hwf
      refine ⟨_, _, ?_, .den (.closure (.recF henv rfl rfl hbody hwf.2.1 hwf.2.2)),
        hst.extend (.closure (.recF henv rfl rfl hbody hwf.2.1 hwf.2.2))⟩
      · simp only [toLNCExp]; exact .eval_fun hfresh_l rfl rfl
    | .eval_match (ae := ae) (bs := bs) (c := c) (xs := xs') (e := e) hatom hd hfind hxs hbody =>
      subst hxs; subst hd
      have hsc_split := List.append_subset.mp (by simpa only [CExp.fvs] using hsc)
      rw [WFCExp] at hwf
      obtain ⟨dl, hevl, hrel⟩ := evalAtomic_forward henv hst hsc_split.1 hwf.1 hatom
      -- DenotableRel (conLabel c) dl forces dl = conLabel c
      cases hrel with
      | con _ =>
        have hfindl := findBranch_forward (Γ := Γ) hfind
        have hsc_e : e.fvs ⊆ Γ := by
          have := findBranch_scope hfind hsc_split.2
          simpa using this
        have hbwf := (findBranch_wf hfind hwf.2).1
        obtain ⟨vl, σl', hev, hvr, hsr⟩ := (sim_forward_allN _).1 hbody henv hst hsc_e hbwf
        refine ⟨vl, σl', ?_, hvr, hsr⟩
        simp only [toLNCExp]
        refine .eval_match hevl rfl ?_ hev
        simpa using hfindl
    | .eval_match_succ (ae := ae) (bs := bs) (a_inner := a_inner) (x_bind := x_bind) (e := e)
        (a_fresh := a_fresh) (d_inner := d_inner) hatom hfind hinner hfresh hσ hρ hbody =>
      subst hσ; subst hρ
      have hsc_split := List.append_subset.mp (by simpa only [CExp.fvs] using hsc)
      rw [WFCExp] at hwf
      obtain ⟨dl, hevl, hrel⟩ := evalAtomic_forward henv hst hsc_split.1 hwf.1 hatom
      cases hrel with
      | succ =>
        have hfindl := findBranch_forward (Γ := Γ) hfind
        have hsc_e : e.fvs ⊆ x_bind :: Γ := by
          have := findBranch_scope hfind hsc_split.2; simpa using this
        have hbwf := (findBranch_wf hfind hwf.2).1
        obtain ⟨dinl, hinnerl, hdrel⟩ := hst.some hinner
        have hfresh_l : σl a_fresh = none := hst.none hfresh
        obtain ⟨vl, σl', hev, hvr, hsr⟩ :=
          (sim_forward_allN _).1 hbody (henv.push x_bind a_fresh) (hst.extend hdrel) hsc_e hbwf
        refine ⟨vl, σl', ?_, hvr, hsr⟩
        simp only [toLNCExp]
        exact .eval_match_succ hevl (by simpa using hfindl) hinnerl hfresh_l rfl rfl hev
    | .eval_funApp_clos (f := f) (aes := aes) (xs := xs) (e_body := e_body) (ρ_lam := ρ_lam)
        (ds := ds) (as_v := as_v) hfun harity hargs hfreshs hnd_as hlen hσ hρ hbody =>
      subst hσ; subst hρ
      have hsc_split := List.append_subset.mp (by simpa only [CExp.fvs] using hsc)
      have hsc_f : f.fvs ⊆ Γ := hsc_split.1
      have hsc_args : aexpListFvs aes ⊆ Γ := hsc_split.2
      rw [WFCExp] at hwf
      obtain ⟨dfl, hfunl, hfrel⟩ := evalAtomic_forward henv hst hsc_f hwf.1 hfun
      obtain ⟨dsl, hargsl, hdsrel⟩ := evalArgs_forward henv hst hsc_args hwf.2 hargs
      have hfreshl := fresh_forward hst hfreshs hdsrel
      have hlen_aesl : as_v.length = (toLNAExpList Γ aes).length := by
        rw [toLNAExpList_length, ← harity]; exact hlen
      have hstore : StoreRel ((List.zip as_v ds).foldl (fun s (p : VAddr × Denotable) => s.extend p.1 p.2) σn)
          ((List.zip as_v dsl).foldl (fun s (p : VAddr × LN.Denotable) => s.extend p.1 p.2) σl) :=
        hst.extendManyZip hdsrel
      cases hfrel with
      | closure hcrel =>
        cases hcrel with
        | lam henv_lam harity' hbodyl hbodysc hbodywf =>
          subst harity'; subst hbodyl
          have hnd : xs.Nodup := by assumption
          have hlen' : xs.length = as_v.length := hlen.symm
          have henv_new := henv_lam.pushMany (xs := xs) (as := as_v) hlen' hnd
          obtain ⟨vl, σl', hev, hvr, hsr⟩ :=
            (sim_forward_allN _).1 hbody henv_new hstore hbodysc hbodywf
          refine ⟨vl, σl', ?_, hvr, hsr⟩
          simp only [toLNCExp]
          exact .eval_funApp_clos hfunl (by rw [toLNAExpList_length]; exact harity)
            hargsl hfreshl hnd_as hlen_aesl rfl rfl hev
        | @recF Γlam _ _ frec a_f ρn' hnd ρll _ _ henv_lam harity' hbodyl hbodysc hf hbodywf =>
          subst harity'; subst hbodyl
          have hlen' : xs.length = as_v.length := hlen.symm
          have henv_new := henv_lam.pushManySelf (as := as_v) (a_f := a_f) hlen' hnd hf
          obtain ⟨vl, σl', hev, hvr, hsr⟩ :=
            (sim_forward_allN _).1 hbody henv_new hstore hbodysc hbodywf
          refine ⟨vl, σl', ?_, hvr, hsr⟩
          simp only [toLNCExp]
          exact .eval_funApp_clos hfunl (by rw [toLNAExpList_length]; exact harity)
            hargsl hfreshl hnd_as hlen_aesl rfl rfl hev

    | .eval_funApp_kont (f := f) (ae := ae) hfun harg happly hhandle =>
      have hsc_split := List.append_subset.mp (by simpa only [CExp.fvs] using hsc)
      have hsc_f : f.fvs ⊆ Γ := hsc_split.1
      have hsc_ae : ae.fvs ⊆ Γ := by
        have := hsc_split.2; simpa only [aexpListFvs, List.append_nil] using this
      rw [WFCExp] at hwf
      have hwf_ae : WFAExp ae := by rw [WFAExpList] at hwf; exact hwf.2.1
      obtain ⟨dfl, hfunl, hfrel⟩ := evalAtomic_forward henv hst hsc_f hwf.1 hfun
      obtain ⟨dl, hargl, hdrel⟩ := evalAtomic_forward henv hst hsc_ae hwf_ae harg
      cases hfrel with
      | kont henv_h hhr hkr =>
        obtain ⟨vl', σl', happlyl, hvr', hsr'⟩ :=
          (sim_forward_allN _).2.2.2.2 happly hkr hdrel hst
        obtain ⟨vl'', σl'', hhdll, hvr'', hsr''⟩ :=
          (sim_forward_allN _).2.2.2.1 hhandle henv_h hhr hvr' hsr'
        refine ⟨vl'', σl'', ?_, hvr'', hsr''⟩
        simp only [toLNCExp, toLNAExpList]
        exact .eval_funApp_kont hfunl hargl happlyl hhdll
    | .eval_handler (h := hn) (e_body := e) (l_h := l) hbody hhandle =>
      have hsc_split := List.append_subset.mp (by simpa only [CExp.fvs] using hsc)
      rw [WFCExp] at hwf
      have hhr : HandlerRel Γ hn (toLNHandler Γ hn) := handlerRel_of_scope hsc_split.1 hwf.1
      obtain ⟨vl', σl', hev, hvr', hsr'⟩ := (sim_forward_allN _).1 hbody henv hst hsc_split.2 hwf.2
      obtain ⟨vl'', σl'', hhdl, hvr'', hsr''⟩ :=
        (sim_forward_allN _).2.2.2.1 hhandle henv hhr hvr' hsr'
      refine ⟨vl'', σl'', ?_, hvr'', hsr''⟩
      simp only [toLNCExp]
      exact .eval_handler hev hhdl
  -- ═══════════════════════ P_continue ═══════════════════════
  · intro frn frl v σn v' σn' h_cont vl σl hfr hvr hst
    match h_cont with
    | .continue_let (a_v := a_v) (d := dn) hfresh hσlet hbody =>
      cases hfr with
      | letFrame henv hel hesc hewf =>
        rename_i Γ y e _ _ _ _
        subst hel; subst hσlet
        cases hvr with
        | den hdr =>
          have hfresh_l : σl a_v = none := hst.none hfresh
          obtain ⟨vl', σl', hev, hvr', hsr'⟩ :=
            (sim_forward_allN _).1 hbody (henv.push y a_v) (hst.extend hdr) hesc hewf
          exact ⟨vl', σl', .continue_let hfresh_l rfl hev, hvr', hsr'⟩
    | .continue_op =>
      cases hfr with
      | letFrame henv hel hesc hewf =>
        cases hvr with
        | suspended hkr =>
          exact ⟨_, _, .continue_op, .suspended (.cons (.letFrame henv hel hesc hewf) hkr), hst⟩
  -- ═══════════════════════ P_handle ═══════════════════════
  · intro hn ρn v σn v' σn' h_handle Γ hl ρl vl σl henv hhr hvr hst
    match h_handle with
    | .handle_return (a_v := a_v) (d := dn) hret hfresh hσret hbody =>
      subst hσret
      cases hvr with
      | den hdr =>
        -- extract returnClause translation + scoping from HandlerRel
        obtain ⟨⟨xret, eret⟩, ops⟩ := hn
        cases hhr with
        | mk hretl hopsl hretsc hopssc hretwf hopswf =>
          -- hret : (xret', eret') = ⟨(xret,eret),ops⟩.returnClause = (xret, eret)
          obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hret.symm
          have hfresh_l : σl a_v = none := hst.none hfresh
          obtain ⟨vl', σl', hev, hvr', hsr'⟩ :=
            (sim_forward_allN _).1 hbody (henv.push xret a_v) (hst.extend hdr) hretsc hretwf
          refine ⟨vl', σl', ?_, hvr', hsr'⟩
          exact .handle_return hretl.symm hfresh_l rfl hev
    | .handle_capture_op (op := op) (as_v := as_v) (κ := κ) hhas hv' =>
      subst hv'
      cases hvr with
      | suspended hkr =>
        have hhasl : hl.hasOp op = false := by rw [hasOp_eq hhr]; exact hhas
        exact ⟨_, _, .handle_capture_op hhasl rfl,
          .suspended (.cons (.handlerFrame henv hhr) hkr), hst⟩
    | .handle_op (op := op) (x := x) (e_op := e_op) (a_v' := a_v') (a_vk := a_vk)
        (a_arg := a_arg) (d_arg := d_arg) (κ := κ) hfind hfresh' hfreshk hne harg hσop hbody =>
      subst hσop
      cases hvr with
      | @suspended _ _ _ κl hkr =>
        have hfindl := findOp_forward hhr hfind
        have hfresh'_l : σl a_v' = none := hst.none hfresh'
        have hfreshk_l : σl a_vk = none := hst.none hfreshk
        obtain ⟨dargl, hargl, hdargrel⟩ := hst.some harg
        have hkont_rel : DenotableRel (Denotable.kontClosure hn ρn κ)
            (LN.Denotable.kontClosure hl ρl κl) := .kont henv hhr hkr
        -- named store: (σ.extend a_v' d_arg).extend a_vk kont
        -- LN store:    (σl.extend a_vk kont).extend a_v' d_argl  (commuting, a_v'≠a_vk)
        have hstore : StoreRel ((σn.extend a_v' d_arg).extend a_vk (Denotable.kontClosure hn ρn κ))
            ((σl.extend a_vk (LN.Denotable.kontClosure hl ρl κl)).extend a_v' dargl) := by
          have h0 := (hst.extend (a := a_v') hdargrel).extend (a := a_vk) hkont_rel
          rwa [LN.Store.extend_comm _ hne] at h0
        -- e_op scoping + well-formedness from HandlerRel op data
        obtain ⟨⟨xret, eret⟩, ops⟩ := hn
        have hmem := findOp_mem hfind
        have hopsc : e_op.fvs ⊆ x :: "resume" :: Γ := by
          cases hhr with
          | mk _ _ _ hopssc _ _ => exact hopssc op x e_op hmem
        -- x ≠ "resume" and WFExp e_op come from the per-op WF carried by HandlerRel
        have hopwf : x ≠ "resume" ∧ WFExp e_op := by
          cases hhr with
          | mk _ _ _ _ _ hopswf => exact hopswf op x e_op hmem
        have hxr : x ≠ "resume" := hopwf.1
        have henv_new : EnvRel (x :: "resume" :: Γ)
            ((ρn.extend x a_v').extend "resume" a_vk) ((ρl.push a_vk).push a_v') := by
          have h1 := (henv.push "resume" a_vk).push x a_v'
          have heq : (ρn.extend "resume" a_vk).extend x a_v'
              = (ρn.extend x a_v').extend "resume" a_vk := by
            funext k; simp only [Env.extend]
            by_cases hkx : k = x <;> by_cases hkr2 : k = "resume" <;> simp_all
          rwa [heq] at h1
        obtain ⟨vl', σl', hev, hvr', hsr'⟩ :=
          (sim_forward_allN _).1 hbody henv_new hstore hopsc hopwf.2
        refine ⟨vl', σl', ?_, hvr', hsr'⟩
        exact .handle_op hfindl hfresh'_l hfreshk_l hne hargl rfl hev
  -- ═══════════════════════ P_apply ═══════════════════════
  · intro κn d σn v σn' h_apply κl dl σl hkr hdr hst
    match h_apply with
    | .apply_continue =>
      cases hkr with
      | nil => exact ⟨_, _, .apply_continue, .den hdr, hst⟩
    | .apply_restore (clo := clo) happly_inner hcont =>
      cases hkr with
      | cons hfr hkr_inner =>
        obtain ⟨vl', σl', happlyl, hvr', hsr'⟩ :=
          (sim_forward_allN _).2.2.2.2 happly_inner hkr_inner hdr hst
        obtain ⟨vl'', σl'', hcontl, hvr'', hsr''⟩ :=
          (sim_forward_allN _).2.2.1 hcont hfr hvr' hsr'
        cases hfr with
        | letFrame _ _ _ _ =>
          exact ⟨vl'', σl'', .apply_restore happlyl hcontl, hvr'', hsr''⟩
    | .apply_restore_handle happly_inner hhandle =>
      cases hkr with
      | cons hfr hkr_inner =>
        cases hfr with
        | handlerFrame henv_h hhr =>
          obtain ⟨vl', σl', happlyl, hvr', hsr'⟩ :=
            (sim_forward_allN _).2.2.2.2 happly_inner hkr_inner hdr hst
          obtain ⟨vl'', σl'', hhdll, hvr'', hsr''⟩ :=
            (sim_forward_allN _).2.2.2.1 hhandle henv_h hhr hvr' hsr'
          exact ⟨vl'', σl'', .apply_restore_handle happlyl hhdll, hvr'', hsr''⟩
  termination_by n

/-- Forward: named eval ⇒ LN eval of the translation. -/
theorem sim_forward {e : Exp} {ρn σn v σn'} (h : EvalExp e ρn σn v σn') (hwf : WFExp e) :
    ∀ {Γ ρl σl}, EnvRel Γ ρn ρl → StoreRel σn σl → e.fvs ⊆ Γ →
      ∃ vl σl', LN.EvalExp (toLNExp Γ e) ρl σl vl σl' ∧ ValueRel v vl ∧ StoreRel σn' σl' := by
  obtain ⟨n, hn⟩ := eval_exp_to_N h
  intro Γ ρl σl henv hst hsc
  exact (sim_forward_allN n).1 hn henv hst hsc hwf

/-- Backward height-indexed 5-conjunction. -/
private theorem sim_backward_allN (n : Nat) :
    -- P_exp
    (∀ {e Γ ρn ρl σn σl vl σl'}, LN.EvalExpN n (toLNExp Γ e) ρl σl vl σl' →
      EnvRel Γ ρn ρl → StoreRel σn σl → e.fvs ⊆ Γ → WFExp e →
        ∃ v σn', EvalExp e ρn σn v σn' ∧ ValueRel v vl ∧ StoreRel σn' σl') ∧
    -- P_cexp
    (∀ {ce Γ ρn ρl σn σl vl σl'}, LN.EvalCExpN n (toLNCExp Γ ce) ρl σl vl σl' →
      EnvRel Γ ρn ρl → StoreRel σn σl → ce.fvs ⊆ Γ → WFCExp ce →
        ∃ v σn', EvalCExp ce ρn σn v σn' ∧ ValueRel v vl ∧ StoreRel σn' σl') ∧
    -- P_continue
    (∀ {frn frl vl σl vl' σl'}, LN.ContinueFrameN n frl vl σl vl' σl' →
      ∀ {v σn}, FrameRel frn frl → ValueRel v vl → StoreRel σn σl →
        ∃ v' σn', ContinueFrame frn v σn v' σn' ∧ ValueRel v' vl' ∧ StoreRel σn' σl') ∧
    -- P_handle
    (∀ {hl ρl vl σl vl' σl'}, LN.HandleValueN n hl ρl vl σl vl' σl' →
      ∀ {Γ hn ρn v σn}, EnvRel Γ ρn ρl → HandlerRel Γ hn hl → ValueRel v vl → StoreRel σn σl →
        ∃ v' σn', HandleValue hn ρn v σn v' σn' ∧ ValueRel v' vl' ∧ StoreRel σn' σl') ∧
    -- P_apply
    (∀ {κl dl σl vl σl'}, LN.ApplyKontN n κl dl σl vl σl' →
      ∀ {κn dn σn}, KontRel κn κl → DenotableRel dn dl → StoreRel σn σl →
        ∃ v σn', ApplyKont κn dn σn v σn' ∧ ValueRel v vl ∧ StoreRel σn' σl') := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- ═══════════════════════ P_exp ═══════════════════════
  · intro e Γ ρn ρl σn σl vl σl' h_eval henv hst hsc hwf
    match e, h_eval with
    | .tail ce l, h_eval =>
      simp only [toLNExp] at h_eval
      match h_eval with
      | .eval_tail h_cexp =>
        have hsc' : ce.fvs ⊆ Γ := (by simpa only [Exp.fvs] using hsc)
        have hwf' : WFCExp ce := by rw [WFExp] at hwf; exact hwf
        obtain ⟨v, σn', hev, hvr, hsr⟩ := (sim_backward_allN _).2.1 h_cexp henv hst hsc' hwf'
        exact ⟨v, σn', .eval_tail hev, hvr, hsr⟩
    | .letE y ce e' l, h_eval =>
      simp only [toLNExp] at h_eval
      match h_eval with
      | .eval_let h_cexp h_cont =>
        have hsc_split := List.append_subset.mp (by simpa only [Exp.fvs] using hsc)
        have hsc_ce : ce.fvs ⊆ Γ := hsc_split.1
        rw [WFExp] at hwf
        have hsc_e : e'.fvs ⊆ y :: Γ := by
          intro x hx
          by_cases hxy : x = y
          · subst hxy; exact List.mem_cons_self ..
          · refine List.mem_cons_of_mem _ (hsc_split.2 ?_)
            simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hx, hxy⟩
        obtain ⟨v, σn', hev, hvr, hsr⟩ := (sim_backward_allN _).2.1 h_cexp henv hst hsc_ce hwf.1
        have hfr : FrameRel (Frame.letFrame ⟨[y], e', ρn, List.nodup_singleton _⟩)
            (LN.Frame.letFrame (toLNExp (y :: Γ) e') ρl) := .letFrame henv rfl hsc_e hwf.2
        obtain ⟨v', σn'', hcont, hvr', hsr'⟩ :=
          (sim_backward_allN _).2.2.1 h_cont hfr hvr hsr
        exact ⟨v', σn'', .eval_let hev hcont, hvr', hsr'⟩
  -- ═══════════════════════ P_cexp ═══════════════════════
  · intro ce Γ ρn ρl σn σl vl σl' h_eval henv hst hsc hwf
    match ce, h_eval with
    | .atomic ae, h_eval =>
      simp only [toLNCExp] at h_eval
      match h_eval with
      | .eval_atomic hatom =>
        have hsc' : ae.fvs ⊆ Γ := (by simpa only [CExp.fvs] using hsc)
        have hwf' : WFAExp ae := by rw [WFCExp] at hwf; exact hwf
        obtain ⟨dn, hatomn, hrel⟩ := evalAtomic_backward henv hst hsc' hwf' hatom
        exact ⟨_, _, .eval_atomic hatomn, .den hrel, hst⟩
    | .opApp op x, h_eval =>
      simp only [toLNCExp] at h_eval
      match h_eval with
      | .eval_opApp (a_v := a_v) hρ =>
        have hxΓ : x ∈ Γ := hsc (by simp [CExp.fvs])
        have hlk := henv.lookup x hxΓ
        have hρn : ρn x = some a_v := by
          rw [hlk]; simpa only [LN.evalAddr] using hρ
        exact ⟨_, _, .eval_opApp hρn, .suspended .nil, hst⟩
    | .funDef f xs e1, h_eval =>
      simp only [toLNCExp] at h_eval
      match h_eval with
      | .eval_fun (a_v := a_v) hfresh hvf hσ' =>
        subst hvf; subst hσ'
        have hfresh_n : σn a_v = Option.none := hst.none' hfresh
        have hbody : e1.fvs ⊆ f :: xs ++ Γ := by
          intro y hy
          simp only [CExp.fvs] at hsc
          by_cases hyf : y = f
          · subst hyf; exact List.mem_cons_self ..
          · by_cases hyxs : y ∈ xs
            · exact List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inl hyxs))
            · refine List.mem_cons_of_mem _ (List.mem_append.mpr (Or.inr (hsc ?_)))
              rw [List.mem_filter]; exact ⟨hy, by simp [hyxs, hyf]⟩
        rw [WFCExp] at hwf
        have hnd : xs.Nodup := hwf.1
        have hf : f ∉ xs := hwf.2.1
        refine ⟨_, _, .eval_fun hfresh_n hnd rfl rfl, ?_, ?_⟩
        · exact .den (.closure (.recF henv rfl rfl hbody hf hwf.2.2))
        · exact hst.extend (.closure (.recF henv rfl rfl hbody hf hwf.2.2))
    | .matchE ae bs, h_eval =>
      simp only [toLNCExp] at h_eval
      match h_eval with
      | .eval_match (c := c) hatom hd hfind hbody =>
        subst hd
        have hsc_split := List.append_subset.mp (by simpa only [CExp.fvs] using hsc)
        rw [WFCExp] at hwf
        obtain ⟨dn, hatomn, hrel⟩ := evalAtomic_backward henv hst hsc_split.1 hwf.1 hatom
        cases hrel with
        | con hcne =>
          obtain ⟨xs', e, hfindn, hel⟩ := findBranch_backward hfind
          have hbwf := findBranch_wf hfindn hwf.2
          -- a matched non-`succ` branch binds no variables
          have hxs : xs' = [] := hbwf.2.2 hcne
          subst hxs; subst hel
          have hsc_e : e.fvs ⊆ Γ := by
            have := findBranch_scope hfindn hsc_split.2; simpa using this
          obtain ⟨v', σn', hev, hvr, hsr⟩ :=
            (sim_backward_allN _).1 hbody henv hst hsc_e hbwf.1
          exact ⟨v', σn', .eval_match hatomn rfl hfindn rfl hev, hvr, hsr⟩
      | .eval_match_succ (a_inner := a_inner) (d_inner := d_innerl) hatom hfind hinner hfresh hσ hρ hbody =>
        subst hσ; subst hρ
        have hsc_split := List.append_subset.mp (by simpa only [CExp.fvs] using hsc)
        rw [WFCExp] at hwf
        obtain ⟨dn, hatomn, hrel⟩ := evalAtomic_backward henv hst hsc_split.1 hwf.1 hatom
        cases hrel with
        | succ =>
          obtain ⟨xs', e, hfindn, hel⟩ := findBranch_backward hfind
          have hbwf := findBranch_wf hfindn hwf.2
          -- the `succ` branch binds exactly one variable
          obtain ⟨x_bind, hxs⟩ : ∃ x_bind, xs' = [x_bind] := hbwf.2.1 rfl
          subst hxs; subst hel
          have hsc_e : e.fvs ⊆ x_bind :: Γ := by
            have := findBranch_scope hfindn hsc_split.2; simpa using this
          obtain ⟨dinn, hinnern, hdrel⟩ := hst.some' hinner
          have hfresh_n : σn _ = Option.none := hst.none' hfresh
          obtain ⟨v', σn', hev, hvr, hsr⟩ :=
            (sim_backward_allN _).1 hbody (henv.push x_bind _) (hst.extend hdrel) hsc_e hbwf.1
          exact ⟨v', σn', .eval_match_succ hatomn hfindn hinnern hfresh_n rfl rfl hev, hvr, hsr⟩
    | .funApp f aes, h_eval =>
      simp only [toLNCExp] at h_eval
      have hsc_split := List.append_subset.mp (by simpa only [CExp.fvs] using hsc)
      have hsc_f : f.fvs ⊆ Γ := hsc_split.1
      have hsc_args : aexpListFvs aes ⊆ Γ := hsc_split.2
      rw [WFCExp] at hwf
      have hwf_f : WFAExp f := hwf.1
      have hwf_args : WFAExpList aes := hwf.2
      -- Closure-application handler, packaged as an existential to reuse across
      -- argument-list shapes.
      have closCase :
          (∃ arity e_bodyl ρ_laml selfAddr dsl as_v n',
            n' < n ∧
            LN.evalAtomic (toLNAExp Γ f) ρl σl =
              some (LN.Denotable.closure ⟨arity, e_bodyl, ρ_laml, selfAddr⟩) ∧
            arity = (toLNAExpList Γ aes).length ∧
            List.Forall₂ (fun ae d => LN.evalAtomic ae ρl σl = some d) (toLNAExpList Γ aes) dsl ∧
            List.Forall₂ (fun a (_ : LN.Denotable) => σl a = none) as_v dsl ∧
            as_v.Nodup ∧ as_v.length = (toLNAExpList Γ aes).length ∧
            LN.EvalExpN n' e_bodyl
              (match selfAddr with
                | none => LN.Env.pushMany ρ_laml as_v
                | some a_f => (LN.Env.pushMany ρ_laml as_v).push a_f)
              ((List.zip as_v dsl).foldl (fun s (p : VAddr × LN.Denotable) => s.extend p.1 p.2) σl)
              vl σl') →
          ∃ v σn', EvalCExp (CExp.funApp f aes) ρn σn v σn' ∧ ValueRel v vl ∧
            StoreRel σn' σl' := by
        rintro ⟨arity, e_bodyl, ρ_laml, selfAddr, dsl, as_v, n', hlt,
          hfun, harity, hargs, hfreshs, hnd_as, hlen, hbody⟩
        obtain ⟨dfn, hfunn, hfrel⟩ := evalAtomic_backward henv hst hsc_f hwf_f hfun
        obtain ⟨ds, hargsn, hdsrel⟩ := evalArgs_backward henv hst hsc_args hwf_args hargs
        have hfreshn := fresh_backward hst hfreshs hdsrel
        have hstore := hst.extendManyZip (as := as_v) hdsrel
        cases hfrel with
        | @closure cn _ hcrel =>
          cases hcrel with
          | @lam Γlam xs body ρlamn hnd _ _ _ henv_lam harity' hbodyl hbodysc hbodywf =>
            subst harity'; subst hbodyl
            have hlen_named : xs.length = aes.length := by
              rw [← toLNAExpList_length Γ aes]; exact harity
            have hlen' : xs.length = as_v.length := by
              rw [hlen_named]; rw [toLNAExpList_length] at hlen; omega
            have henv_new := henv_lam.pushMany (xs := xs) (as := as_v) hlen' hnd
            obtain ⟨v', σn', hev, hvr, hsr⟩ :=
              (sim_backward_allN _).1 hbody henv_new hstore hbodysc hbodywf
            refine ⟨v', σn', ?_, hvr, hsr⟩
            have hlen_as : as_v.length = xs.length := by rw [hlen']
            exact .eval_funApp_clos hfunn hlen_named hargsn hfreshn hnd_as hlen_as rfl rfl hev
          | @recF Γlam xs body frec a_f ρlamn hnd _ _ _ henv_lam harity' hbodyl hbodysc hf hbodywf =>
            subst harity'; subst hbodyl
            have hlen_named : xs.length = aes.length := by
              rw [← toLNAExpList_length Γ aes]; exact harity
            have hlen' : xs.length = as_v.length := by
              rw [hlen_named]; rw [toLNAExpList_length] at hlen; omega
            have henv_new := henv_lam.pushManySelf (as := as_v) (a_f := a_f) hlen' hnd hf
            obtain ⟨v', σn', hev, hvr, hsr⟩ :=
              (sim_backward_allN _).1 hbody henv_new hstore hbodysc hbodywf
            refine ⟨v', σn', ?_, hvr, hsr⟩
            have hlen_as : as_v.length = xs.length := by rw [hlen']
            exact .eval_funApp_clos hfunn hlen_named hargsn hfreshn hnd_as hlen_as rfl rfl hev
      -- Concretise the argument-list shape so the `kont` rule can be inverted.
      cases aes with
      | nil =>
        simp only [toLNAExpList] at h_eval
        match h_eval with
        | .eval_funApp_clos hfun harity hargs hfreshs hnd_as hlen hσ hρ hbody =>
          subst hσ; subst hρ
          exact closCase ⟨_, _, _, _, _, _, _, Nat.lt_succ_self _, hfun, by simp only [toLNAExpList]; exact harity,
            by simp only [toLNAExpList]; exact hargs, hfreshs, hnd_as, by simp only [toLNAExpList]; exact hlen, hbody⟩
      | cons ae rest =>
        cases rest with
        | nil =>
          simp only [toLNAExpList] at h_eval
          match h_eval with
          | .eval_funApp_clos hfun harity hargs hfreshs hnd_as hlen hσ hρ hbody =>
            subst hσ; subst hρ
            exact closCase ⟨_, _, _, _, _, _, _, Nat.lt_succ_self _, hfun, by simp only [toLNAExpList]; exact harity,
              by simp only [toLNAExpList]; exact hargs, hfreshs, hnd_as, by simp only [toLNAExpList]; exact hlen, hbody⟩
          | .eval_funApp_kont hfun harg happly hhandle =>
            obtain ⟨dfn, hfunn, hfrel⟩ := evalAtomic_backward henv hst hsc_f hwf_f hfun
            have hsc_ae : ae.fvs ⊆ Γ := by
              have := hsc_args; simpa only [aexpListFvs, List.append_nil] using this
            have hwf_ae : WFAExp ae := by rw [WFAExpList] at hwf_args; exact hwf_args.1
            obtain ⟨dn, hargn, hdrel⟩ := evalAtomic_backward henv hst hsc_ae hwf_ae harg
            cases hfrel with
            | kont henv_h hhr hkr =>
              obtain ⟨v', σn', happlyn, hvr', hsr'⟩ :=
                (sim_backward_allN _).2.2.2.2 happly hkr hdrel hst
              obtain ⟨v'', σn'', hhdln, hvr'', hsr''⟩ :=
                (sim_backward_allN _).2.2.2.1 hhandle henv_h hhr hvr' hsr'
              exact ⟨v'', σn'', .eval_funApp_kont hfunn hargn happlyn hhdln, hvr'', hsr''⟩
        | cons b rest' =>
          simp only [toLNAExpList] at h_eval
          match h_eval with
          | .eval_funApp_clos hfun harity hargs hfreshs hnd_as hlen hσ hρ hbody =>
            subst hσ; subst hρ
            exact closCase ⟨_, _, _, _, _, _, _, Nat.lt_succ_self _, hfun, by simp only [toLNAExpList]; exact harity,
              by simp only [toLNAExpList]; exact hargs, hfreshs, hnd_as, by simp only [toLNAExpList]; exact hlen, hbody⟩
    | .handler hn e l, h_eval =>
      simp only [toLNCExp] at h_eval
      match h_eval with
      | .eval_handler hbody hhandle =>
        have hsc_split := List.append_subset.mp (by simpa only [CExp.fvs] using hsc)
        rw [WFCExp] at hwf
        have hhr : HandlerRel Γ hn (toLNHandler Γ hn) := handlerRel_of_scope hsc_split.1 hwf.1
        obtain ⟨v', σn', hev, hvr', hsr'⟩ :=
          (sim_backward_allN _).1 hbody henv hst hsc_split.2 hwf.2
        obtain ⟨v'', σn'', hhdl, hvr'', hsr''⟩ :=
          (sim_backward_allN _).2.2.2.1 hhandle henv hhr hvr' hsr'
        exact ⟨v'', σn'', .eval_handler hev hhdl, hvr'', hsr''⟩
  -- ═══════════════════════ P_continue ═══════════════════════
  · intro frn frl vl σl vl' σl' h_cont v σn hfr hvr hst
    cases hfr with
    | letFrame henv hel hesc hewf =>
      rename_i Γ y e _ _ _ _
      subst hel
      match h_cont with
      | .continue_let (a_v := a_v) (d := dl) hfresh hσlet hbody =>
        subst hσlet
        cases hvr with
        | den hdr =>
          have hfresh_n : σn a_v = none := hst.none' hfresh
          obtain ⟨v', σn', hev, hvr', hsr'⟩ :=
            (sim_backward_allN _).1 hbody (henv.push y a_v) (hst.extend hdr) hesc hewf
          exact ⟨v', σn', .continue_let hfresh_n rfl hev, hvr', hsr'⟩
      | .continue_op =>
        cases hvr with
        | suspended hkr =>
          exact ⟨_, _, .continue_op, .suspended (.cons (.letFrame henv rfl hesc hewf) hkr), hst⟩
    | handlerFrame henv hhr => cases h_cont
  -- ═══════════════════════ P_handle ═══════════════════════
  · intro hl ρl vl σl vl' σl' h_handle Γ hn ρn v σn henv hhr hvr hst
    match h_handle with
    | .handle_return (a_v := a_v) (d := dl) hret hfresh hσret hbody =>
      subst hσret
      cases hvr with
      | den hdr =>
        obtain ⟨⟨xret, eret⟩, ops⟩ := hn
        cases hhr with
        | mk hretl hopsl hretsc hopssc hretwf hopswf =>
          subst hret
          have hfresh_n : σn a_v = Option.none := hst.none' hfresh
          rw [hretl] at hbody
          obtain ⟨v', σn', hev, hvr', hsr'⟩ :=
            (sim_backward_allN _).1 hbody (henv.push xret a_v) (hst.extend hdr) hretsc hretwf
          exact ⟨v', σn', .handle_return rfl hfresh_n rfl hev, hvr', hsr'⟩
    | .handle_capture_op (op := op) (as_v := as_v) (κ := κl) hhas hv' =>
      subst hv'
      cases hvr with
      | @suspended _ _ κn _ hkr =>
        have hhas_n : hn.hasOp op = false := by rw [← hasOp_eq hhr]; exact hhas
        exact ⟨_, _, .handle_capture_op hhas_n rfl,
          .suspended (.cons (.handlerFrame henv hhr) hkr), hst⟩
    | .handle_op (op := op) (e_op := e_opl) (a_v' := a_v') (a_vk := a_vk)
        (a_arg := a_arg) (d_arg := d_argl) (κ := κl) hfind hfresh' hfreshk hne harg hσop hbody =>
      subst hσop
      cases hvr with
      | @suspended _ _ κn _ hkr =>
        obtain ⟨x, e_op, hfind_n, hel⟩ := findOp_backward hhr hfind
        subst hel
        have hfresh'_n : σn a_v' = Option.none := hst.none' hfresh'
        have hfreshk_n : σn a_vk = Option.none := hst.none' hfreshk
        obtain ⟨d_arg, hargn, hdargrel⟩ := hst.some' harg
        have hkont_rel : DenotableRel (Denotable.kontClosure hn ρn κn)
            (LN.Denotable.kontClosure hl ρl κl) := .kont henv hhr hkr
        -- named store: (σn.extend a_v' d_arg).extend a_vk kont
        -- LN store:    (σl.extend a_vk kont).extend a_v' d_argl
        have hstore : StoreRel ((σn.extend a_v' d_arg).extend a_vk (Denotable.kontClosure hn ρn κn))
            ((σl.extend a_vk (LN.Denotable.kontClosure hl ρl κl)).extend a_v' d_argl) := by
          have h0 := (hst.extend (a := a_v') hdargrel).extend (a := a_vk) hkont_rel
          rwa [LN.Store.extend_comm _ hne] at h0
        obtain ⟨⟨xret, eret⟩, ops⟩ := hn
        have hmem := findOp_mem hfind_n
        have hopsc : e_op.fvs ⊆ x :: "resume" :: Γ := by
          cases hhr with
          | mk _ _ _ hopssc _ _ => exact hopssc op x e_op hmem
        have hopwf : x ≠ "resume" ∧ WFExp e_op := by
          cases hhr with
          | mk _ _ _ _ _ hopswf => exact hopswf op x e_op hmem
        have hxr : x ≠ "resume" := hopwf.1
        have henv_new : EnvRel (x :: "resume" :: Γ)
            ((ρn.extend x a_v').extend "resume" a_vk) ((ρl.push a_vk).push a_v') := by
          have h1 := (henv.push "resume" a_vk).push x a_v'
          have heq : (ρn.extend "resume" a_vk).extend x a_v'
              = (ρn.extend x a_v').extend "resume" a_vk := by
            funext k; simp only [Env.extend]
            by_cases hkx : k = x <;> by_cases hkr2 : k = "resume" <;> simp_all
          rwa [heq] at h1
        obtain ⟨v', σn', hev, hvr', hsr'⟩ :=
          (sim_backward_allN _).1 hbody henv_new hstore hopsc hopwf.2
        refine ⟨v', σn', ?_, hvr', hsr'⟩
        exact .handle_op hfind_n hfresh'_n hfreshk_n hne hargn rfl hev
  -- ═══════════════════════ P_apply ═══════════════════════
  · intro κl dl σl vl σl' h_apply κn dn σn hkr hdr hst
    cases hkr with
    | nil =>
      cases h_apply with
      | apply_continue => exact ⟨_, _, .apply_continue, .den hdr, hst⟩
    | cons hfr hkr_inner =>
      cases hfr with
      | letFrame henv hel hesc hewf =>
        match h_apply with
        | .apply_restore happly_inner hcont =>
          obtain ⟨v', σn', happlyn, hvr', hsr'⟩ :=
            (sim_backward_allN _).2.2.2.2 happly_inner hkr_inner hdr hst
          obtain ⟨v'', σn'', hcontn, hvr'', hsr''⟩ :=
            (sim_backward_allN _).2.2.1 hcont (.letFrame henv hel hesc hewf) hvr' hsr'
          exact ⟨v'', σn'', .apply_restore happlyn hcontn, hvr'', hsr''⟩
      | handlerFrame henv_h hhr =>
        match h_apply with
        | .apply_restore_handle happly_inner hhandle =>
          obtain ⟨v', σn', happlyn, hvr', hsr'⟩ :=
            (sim_backward_allN _).2.2.2.2 happly_inner hkr_inner hdr hst
          obtain ⟨v'', σn'', hhdln, hvr'', hsr''⟩ :=
            (sim_backward_allN _).2.2.2.1 hhandle henv_h hhr hvr' hsr'
          exact ⟨v'', σn'', .apply_restore_handle happlyn hhdln, hvr'', hsr''⟩
  termination_by n

/-- Backward: LN eval of the translation ⇒ named eval. -/
theorem sim_backward {e : Exp} {Γ ρn ρl σn σl vl σl'}
    (henv : EnvRel Γ ρn ρl) (hst : StoreRel σn σl) (hsc : e.fvs ⊆ Γ) (hwf : WFExp e)
    (h : LN.EvalExp (toLNExp Γ e) ρl σl vl σl') :
    ∃ v σn', EvalExp e ρn σn v σn' ∧ ValueRel v vl ∧ StoreRel σn' σl' := by
  obtain ⟨n, hn⟩ := LN.eval_exp_to_N h
  exact (sim_backward_allN n).1 hn henv hst hsc hwf

end DMCFA.Bridge
