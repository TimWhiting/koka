/-
  Abstract Big-Step Components

  The abstract semantics finitizes the timestamped semantics by truncating
  timestamps and introducing non-determinism via powerset stores.

  Key design: abstract components reuse the same types as timestamped components
  (TVAddr, TEnv, TClosure, etc.) — an "abstract address" is simply a timestamped
  address whose timestamp happens to be short. The only structural difference is
  the store, which maps addresses to *sets* of storables rather than single values.

  Parameterized by (m h : Nat) controlling context sensitivity:
  - m: maximum length of t_k (call-stack depth)
  - h: maximum length of t_mk (handler-nesting depth)
-/

import DMCFA.TimestampedComponents

namespace DMCFA

/-! ## Timestamp Truncation -/

/-- Truncate a list to at most n elements (keep the first n) -/
def List.trunc (n : Nat) (l : List α) : List α := l.take n

@[simp] theorem List.trunc_length_le (n : Nat) (l : List α) :
    (List.trunc n l).length ≤ n := by
  simp [List.trunc, List.length_take]

/-- Truncate a continuation timestamp to length m -/
def truncKTime (m : Nat) (tk : KTime) : KTime := List.trunc m tk

/-- Truncate a meta-continuation timestamp to length h,
    also truncating embedded KTimes to length m -/
def truncMKTime (m h : Nat) (tmk : MKTime) : MKTime :=
  List.trunc h (tmk.map (fun (l, tk) => (l, truncKTime m tk)))

/-- Truncate a full timestamp -/
def truncTime (m h : Nat) (t : Time) : Time :=
  ⟨truncKTime m t.tk, truncMKTime m h t.tmk⟩

/-- Extend t_k with label l, then truncate to m -/
def extKTime (m : Nat) (l : Label) (tk : KTime) : KTime :=
  truncKTime m (l :: tk)

/-- Extend t_mk with (l, tk), truncating tk to m and result to h.
    Used for eval_handler and apply_restore_handle where tk is stored directly. -/
def extMKTime (m h : Nat) (l : Label) (tk : KTime) (tmk : MKTime) : MKTime :=
  truncMKTime m h ((l, truncKTime m tk) :: tmk)

/-- Extend t_mk with (l, l::tk), truncating to m and h.
    Used for eval_funApp_kont where the concrete stores (l, l::t_k)::t_mk. -/
def extMKTimeApp (m h : Nat) (l : Label) (tk : KTime) (tmk : MKTime) : MKTime :=
  truncMKTime m h ((l, extKTime m l tk) :: tmk)

/-! ## Abstract Store -/

/-- Abstract store maps addresses to *sets* of storables.
    Multiple concrete values can map to the same abstract address after truncation. -/
def AStore := TAddr → Set TStorable

/-- Empty abstract store -/
def AStore.empty : AStore := fun _ => ∅

/-- Join two abstract stores (pointwise union) -/
def AStore.join (σ₁ σ₂ : AStore) : AStore :=
  fun a => σ₁ a ∪ σ₂ a

instance : Union AStore := ⟨AStore.join⟩

/-- Weak update: add a storable to the set at address a -/
def AStore.update (σ : AStore) (a : TAddr) (s : TStorable) : AStore :=
  fun a' => if a' = a then σ a ∪ {s} else σ a'

/-- Weak update with a set of storables -/
def AStore.updateSet (σ : AStore) (a : TAddr) (ss : Set TStorable) : AStore :=
  fun a' => if a' = a then σ a ∪ ss else σ a'

/-- Ordering on abstract stores: σ₁ ⊑ σ₂ iff σ₁(a) ⊆ σ₂(a) for all a -/
def AStore.le (σ₁ σ₂ : AStore) : Prop :=
  ∀ a, σ₁ a ⊆ σ₂ a

instance : LE AStore := ⟨AStore.le⟩

@[simp] theorem AStore.le_def (σ₁ σ₂ : AStore) :
    σ₁ ≤ σ₂ ↔ ∀ a, σ₁ a ⊆ σ₂ a := Iff.rfl

/-! ## Abstract Atomic Evaluation -/

/-- Abstract atomic evaluation: returns a *set* of denotables.
    Non-deterministic: variable lookup returns all values at the address. -/
def evalAbsAtomic (ae : AExp) (ρ : TEnv) (σ : AStore) : Set TDenotable :=
  match ae with
  | .var x =>
      match Finmap.lookup x ρ with
      | none => ∅
      | some a => { d | .denotable d ∈ σ (.val a) }
  | .lam xs body =>
      if h : xs.Nodup then {.closure ⟨xs, body, ρ, h⟩} else ∅
  | .con c => {.conLabel c}
  | .succE x =>
      match Finmap.lookup x ρ with
      | none => ∅
      | some a => { d | d = .succVal a ∧ (σ (.val a)).Nonempty }

end DMCFA
