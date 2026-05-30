/-
  Timestamp Ordering and Invariants (v2)

  Replaces TimeOrder.lean with a cleaner approach:
  - Eliminates EnteredScope, ChildrenPreserved
  - Eliminates CallLabelsTracked, HandlerLabelsTracked
  - Adds IsDescendant, EnteredDescendants, SiblingsFresh

  Key insight: Use the program's label structure (WellLabeled/WellNamed) to give
  deterministic bounds on what gets allocated, plus IsDescendant/EnteredDescendants/
  SiblingsFresh to handle cross-timestamp cases.
-/

import DMCFA.TimestampedComponents
import DMCFA.UniqueLabels
import Mathlib.Data.Finset.Basic

namespace DMCFA

/-! ## Entered Timestamps -/

/-- Set of timestamps that have been "entered" (had allocations made at them).
    This grows monotonically during evaluation. -/
abbrev EnteredTimes := Finset Time

/-! ## Store Invariants -/

/-- All addresses in the store have their timestamp in the entered set -/
def OrderInvariant (σ : TStore) (entered : EnteredTimes) : Prop :=
  ∀ a, σ a ≠ none → a.time ∈ entered

/-- Within a single timestamp, no two val addresses share a variable name -/
def NamesDistinct (σ : TStore) : Prop :=
  ∀ (a₁ a₂ : TVAddr), a₁.time = a₂.time → a₁.name = a₂.name →
    σ (.val a₁) ≠ none → σ (.val a₂) ≠ none → a₁ = a₂

/-- Whether a frame content is a let-frame -/
def TFrameContent.isLetFrame : TFrameContent → Bool
  | .letFrame _ => true
  | .handlerFrame _ _ => false

/-- Kont addresses of the same frame kind at the same timestamp with same label+op are equal -/
@[simp] def KontAddrDistinct (σ : TStore) : Prop :=
  ∀ (k₁ k₂ : TKAddr), k₁.frame.time = k₂.frame.time →
    k₁.frame.label = k₂.frame.label →
    k₁.frame.content.isLetFrame = k₂.frame.content.isLetFrame →
    σ (.kont k₁) ≠ none → σ (.kont k₂) ≠ none → k₁ = k₂

/-! ## Well-Labeled/Well-Named Store -/

/-- Whether a storable has well-formed (well-labeled ∧ well-named) bodies -/
def WellFormedStorable : TStorable → Prop
  | .denotable (.closure ⟨xs, body, _, _⟩) => WellFormedProgram body ∧ Disjoint xs.toFinset body.topAllocVars ∧ xs.Nodup
  | .denotable (.kontClosure h _ _) => WellFormedSubHandler h
  | _ => True

/-- All closures/handlers in the store have well-formed bodies -/
def WellFormedStore (σ : TStore) : Prop :=
  ∀ a, match σ a with
  | some (.denotable (.closure ⟨xs, body, _, _⟩)) => WellFormedProgram body ∧ Disjoint xs.toFinset body.topAllocVars ∧ xs.Nodup
  | some (.denotable (.kontClosure h _ _)) => WellFormedSubHandler h
  | _ => True

/-- Well-formedness for TValue -/
def WellFormedValue : TValue → Prop
  | .den (.closure ⟨xs, body, _, _⟩) => WellFormedProgram body ∧ Disjoint xs.toFinset body.topAllocVars ∧ xs.Nodup
  | .den (.kontClosure h _ _) => WellFormedSubHandler h
  | _ => True

/-- Sub-eval at a different time didn't allocate at time t -/
def StorePreservation (σ σ' : TStore) (t : Time) : Prop :=
  ∀ a, a.time = t → σ' a = σ a

theorem StorePreservation.refl : StorePreservation σ σ t := fun _ _ => rfl

theorem StorePreservation.trans (h1 : StorePreservation σ₁ σ₂ t) (h2 : StorePreservation σ₂ σ₃ t) :
    StorePreservation σ₁ σ₃ t := fun a ha => by rw [h2 a ha, h1 a ha]

theorem StorePreservation.extend_ne (h : StorePreservation σ σ' t) (a : TAddr) (s : TStorable)
    (hne : a.time ≠ t) : StorePreservation σ (σ'.extend a s) t := by
  intro a' ha'
  simp [TStore.extend]
  split
  · next heq => subst heq; exact absurd ha' hne
  · exact h a' ha'

/-- StorePreservation through foldl of val extensions at a different time -/
theorem storePreservation_foldl_val_ne {t_new t' : Time} (h_ne : t_new ≠ t')
    (pairs : List (Var × TDenotable)) :
    StorePreservation σ
      (pairs.foldl (fun s xd => s.extend (.val ⟨xd.1, t_new⟩) (.denotable xd.2)) σ) t' := by
  induction pairs generalizing σ with
  | nil => exact StorePreservation.refl
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    exact (StorePreservation.extend_ne StorePreservation.refl _ _
      (by simp [TAddr.time]; exact h_ne)).trans ih

/-- Combined store invariant -/
structure StoreInvariant (σ : TStore) (entered : EnteredTimes) : Prop where
  order : OrderInvariant σ entered
  names : NamesDistinct σ
  konts : KontAddrDistinct σ
  wf_store : WellFormedStore σ
  call_parent : ∀ l tk tmk, (⟨l :: tk, tmk⟩ : Time) ∈ entered → (⟨tk, tmk⟩ : Time) ∈ entered
  handler_parent : ∀ l tk tmk, (⟨[], (l, tk) :: tmk⟩ : Time) ∈ entered → (⟨tk, tmk⟩ : Time) ∈ entered

/-! ## Well-Formed Store Lemmas -/

theorem wellFormedStore_empty : WellFormedStore TStore.empty := by
  intro a; simp [TStore.empty]

theorem wellFormedStore_extend (h : WellFormedStore σ) (a : TAddr) (s : TStorable)
    (h_wf : WellFormedStorable s) :
    WellFormedStore (σ.extend a s) := by
  intro a'
  by_cases heq : a' = a
  · subst heq; simp [TStore.extend]
    match s, h_wf with
    | .denotable (.closure ⟨_, body, _, _⟩), h_wf => exact h_wf
    | .denotable (.kontClosure h _ _), h_wf => exact h_wf
    | .denotable (.conLabel _), _ => trivial
    | .denotable (.succVal _), _ => trivial
    | .kontLink _, _ => trivial
  · simp [TStore.extend, heq]; exact h a'

/-! ## Well-Formed Kont Chains -/

/-- Well-formedness of a frame's content -/
def WellFormedFrameContent : TFrameContent → Prop
  | .letFrame ⟨_, body, _, _⟩ => WellFormedProgram body
  | .handlerFrame hdl _ => WellFormedSubHandler hdl

/-- A kont chain in the store is well-formed: each frame carries WF content,
    and the chain terminates. -/
inductive WellFormedKontChain (σ : TStore) : Option TKAddr → Prop where
  | nil : WellFormedKontChain σ none
  | cons :
      σ (.kont a_κ) = some (.kontLink a_next) →
      WellFormedFrameContent a_κ.frame.content →
      WellFormedKontChain σ a_next →
      WellFormedKontChain σ (some a_κ)

/-- Extract frame content WF from a chain -/
theorem WellFormedKontChain.head_wf (h : WellFormedKontChain σ (some a_κ)) :
    WellFormedFrameContent a_κ.frame.content := by
  cases h with | cons _ hwf _ => exact hwf

/-- Extract the lookup from a chain -/
theorem WellFormedKontChain.head_lookup (h : WellFormedKontChain σ (some a_κ)) :
    ∃ a_next, σ (.kont a_κ) = some (.kontLink a_next) := by
  cases h with | cons hlk _ _ => exact ⟨_, hlk⟩

/-- Extract the tail chain -/
theorem WellFormedKontChain.tail (h : WellFormedKontChain σ (some a_κ))
    (hlk : σ (.kont a_κ) = some (.kontLink a_next)) :
    WellFormedKontChain σ a_next := by
  cases h with
  | cons hlk' _ htail =>
    rw [hlk] at hlk'; cases hlk'; exact htail

/-- WellFormedKontChain preserved under store extension at a val address -/
theorem WellFormedKontChain.extend_val (h : WellFormedKontChain σ oa_κ)
    (av : TVAddr) (s : TStorable) :
    WellFormedKontChain (σ.extend (.val av) s) oa_κ := by
  induction h with
  | nil => exact .nil
  | cons hlk hwf _ ih =>
    exact .cons (by simp [TStore.extend]; exact hlk) hwf ih

/-- WellFormedKontChain preserved under store extension at a fresh kont address -/
theorem WellFormedKontChain.extend_kont_fresh (h : WellFormedKontChain σ oa_κ)
    (k : TKAddr) (s : TStorable) (h_fresh : σ (.kont k) = none) :
    WellFormedKontChain (σ.extend (.kont k) s) oa_κ := by
  induction h with
  | nil => exact .nil
  | cons hlk hwf _ ih =>
    refine .cons ?_ hwf ih
    simp only [TStore.extend]
    split
    · next heq => simp [TAddr.kont.injEq] at heq; subst heq; rw [h_fresh] at hlk; simp at hlk
    · exact hlk

/-! ## Freshness from Invariant -/

/-- A timestamp not in `entered` has no addresses in σ -/
theorem fresh_of_not_entered (hinv : OrderInvariant σ entered)
    (h_not : t ∉ entered) :
    fresh σ t := by
  intro a ha heq
  exact h_not (heq ▸ hinv a ha)

/-! ## Timestamp Entry Lemmas -/

/-- A function-call timestamp is distinct from the parent -/
theorem call_timestamp_distinct (l : Label) (t : Time) :
    (⟨l :: t.tk, t.tmk⟩ : Time) ≠ t := by
  intro h
  have := congr_arg Time.tk h
  simp at this

/-- A handler-body timestamp is distinct from the parent -/
theorem handler_timestamp_distinct (l : Label) (t : Time) :
    (⟨[], (l, t.tk) :: t.tmk⟩ : Time) ≠ t := by
  intro h
  have := congr_arg Time.tmk h
  simp at this

/-! ## Invariant Preservation under Store Extension -/

/-- OrderInvariant preserved when extending at an address whose timestamp is entered -/
theorem order_invariant_extend (hinv : OrderInvariant σ entered)
    (h_time : a.time ∈ entered) (s : TStorable) :
    OrderInvariant (σ.extend a s) (entered) := by
  intro a' ha'
  simp only [TStore.extend] at ha'
  split at ha'
  · next heq => subst heq; exact h_time
  · exact hinv a' ha'

/-- OrderInvariant preserved when extending at a new timestamp and adding it to entered -/
theorem order_invariant_extend_new (hinv : OrderInvariant σ entered)
    (s : TStorable) :
    OrderInvariant (σ.extend a s) (entered ∪ {a.time}) := by
  intro a' ha'
  simp only [TStore.extend] at ha'
  split at ha'
  · next heq => subst heq; simp
  · exact Finset.mem_union_left _ (hinv a' ha')

/-- TVAddr extensionality: same name and time means equal -/
theorem TVAddr.ext_iff (a₁ a₂ : TVAddr) : a₁ = a₂ ↔ a₁.name = a₂.name ∧ a₁.time = a₂.time := by
  constructor
  · intro h; subst h; exact ⟨rfl, rfl⟩
  · intro ⟨hn, ht⟩; cases a₁; cases a₂; simp_all

/-- NamesDistinct preserved when extending with a name not yet used at that timestamp -/
theorem names_distinct_extend_val (hnames : NamesDistinct σ)
    (av : TVAddr) (s : TStorable):
    NamesDistinct (σ.extend (.val av) s) := by
  intro a₁ a₂ h_time h_name ha₁ ha₂
  have same_is_eq : ∀ a : TVAddr, a.time = av.time → a.name = av.name → a = av :=
    fun a ht hn => (TVAddr.ext_iff a av).mpr ⟨hn, ht⟩
  by_cases h1 : a₁ = av <;> by_cases h2 : a₂ = av
  · rw [h1, h2]
  · exfalso; apply h2; rw [h1] at h_time h_name
    exact (TVAddr.ext_iff a₂ av).mpr ⟨h_name.symm, h_time.symm⟩
  · exfalso; apply h1; rw [h2] at h_time h_name
    exact (TVAddr.ext_iff a₁ av).mpr ⟨h_name, h_time⟩
  · have lift : ∀ a : TVAddr, a ≠ av →
        (σ.extend (.val av) s) (.val a) ≠ none → σ (.val a) ≠ none := by
      intro a hne h; simp only [TStore.extend] at h
      have : TAddr.val a ≠ TAddr.val av := fun heq => hne (TAddr.val.inj heq)
      simp [this] at h; exact h
    exact hnames a₁ a₂ h_time h_name (lift a₁ h1 ha₁) (lift a₂ h2 ha₂)

/-- KontAddrDistinct preserved under val extension -/
theorem kont_distinct_extend_val (hkonts : KontAddrDistinct σ)
    (av : TVAddr) (s : TStorable) :
    KontAddrDistinct (σ.extend (.val av) s) := by
  unfold KontAddrDistinct
  intro k₁ k₂ h_time h_label h_kind hk₁ hk₂
  simp only [TStore.extend] at hk₁ hk₂
  split at hk₁ <;> split at hk₂
  · all_goals simp_all
  · all_goals simp_all
  · all_goals simp_all
  · exact hkonts k₁ k₂ h_time h_label h_kind hk₁ hk₂

/-- KontAddrDistinct preserved under kont extension when no same-kind conflicting address exists -/
theorem kont_distinct_extend_kont (hkonts : KontAddrDistinct σ)
    (ak : TKAddr) (s : TStorable)
    (h_no_conflict : ∀ k : TKAddr, k.frame.time = ak.frame.time →
      k.frame.label = ak.frame.label →
      k.frame.content.isLetFrame = ak.frame.content.isLetFrame →
      σ (.kont k) = none) :
    KontAddrDistinct (σ.extend (.kont ak) s) := by
  intro k₁ k₂ h_time h_label h_kind hk₁ hk₂
  have lift : ∀ k : TKAddr, k ≠ ak →
      (σ.extend (.kont ak) s) (.kont k) ≠ none → σ (.kont k) ≠ none := by
    intro k hne h; simp only [TStore.extend] at h
    have : TAddr.kont k ≠ TAddr.kont ak := fun heq => hne (TAddr.kont.inj heq)
    simp [this] at h; exact h
  by_cases h1 : k₁ = ak <;> by_cases h2 : k₂ = ak
  · rw [h1, h2]
  · exfalso
    rw [h1] at h_time h_label h_kind
    have := h_no_conflict k₂ h_time.symm h_label.symm h_kind.symm
    exact lift k₂ h2 hk₂ this
  · exfalso
    rw [h2] at h_time h_label h_kind
    have := h_no_conflict k₁ h_time h_label h_kind
    exact lift k₁ h1 hk₁ this
  · exact hkonts k₁ k₂ h_time h_label h_kind (lift k₁ h1 hk₁) (lift k₂ h2 hk₂)

/-! ## Combined Invariant Preservation -/

/-- StoreInvariant preserved under val extension at current timestamp -/
theorem store_invariant_extend_val (hinv : StoreInvariant σ entered)
    (av : TVAddr) (s : TStorable)
    (h_time : av.time ∈ entered)
    (h_wf : WellFormedStorable s) :
    StoreInvariant (σ.extend (.val av) s) entered := by
  exact {
    order := order_invariant_extend hinv.order (by simp [TAddr.time]; exact h_time) s
    names := names_distinct_extend_val hinv.names av s
    konts := kont_distinct_extend_val hinv.konts av s
    wf_store := wellFormedStore_extend hinv.wf_store _ s h_wf
    call_parent := hinv.call_parent
    handler_parent := hinv.handler_parent
  }

/-- StoreInvariant preserved under val extension at a NEW timestamp
    with parent already entered -/
theorem store_invariant_extend_val_new (hinv : StoreInvariant σ entered)
    (av : TVAddr) (s : TStorable)
    (h_wf : WellFormedStorable s)
    (h_cp : ∀ l tk tmk, av.time = ⟨l :: tk, tmk⟩ → (⟨tk, tmk⟩ : Time) ∈ entered)
    (h_hp : ∀ l tk tmk, av.time = ⟨[], (l, tk) :: tmk⟩ → (⟨tk, tmk⟩ : Time) ∈ entered) :
    StoreInvariant (σ.extend (.val av) s) (entered ∪ {av.time}) := by
  exact {
    order := order_invariant_extend_new hinv.order s
    names := names_distinct_extend_val hinv.names av s
    konts := kont_distinct_extend_val hinv.konts av s
    wf_store := wellFormedStore_extend hinv.wf_store _ s h_wf
    call_parent := fun l tk tmk h => by
      simp only [Finset.mem_union, Finset.mem_singleton] at h ⊢
      rcases h with h | h
      · exact Or.inl (hinv.call_parent l tk tmk h)
      · exact Or.inl (h_cp l tk tmk (by rw [h])  )
    handler_parent := fun l tk tmk h => by
      simp only [Finset.mem_union, Finset.mem_singleton] at h ⊢
      rcases h with h | h
      · exact Or.inl (hinv.handler_parent l tk tmk h)
      · exact Or.inl (h_hp l tk tmk (by rw [h]))
  }

/-- StoreInvariant preserved under foldl of val extensions at a given timestamp -/
theorem store_invariant_foldl_extend_val
    {entered : EnteredTimes} {t_new : Time}
    (hinv : StoreInvariant σ entered)
    (h_t : t_new ∈ entered)
    (pairs : List (Var × TDenotable))
    (h_wf_pairs : ∀ (q : Var × TDenotable), q ∈ pairs → WellFormedStorable (.denotable q.2))
    : StoreInvariant (pairs.foldl
      (fun s (xd : Var × TDenotable) => s.extend (.val ⟨xd.1, t_new⟩) (.denotable xd.2)) σ)
      entered := by
  induction pairs generalizing σ with
  | nil => exact hinv
  | cons p ps ih =>
    obtain ⟨x, d⟩ := p
    simp only [List.foldl_cons]
    apply ih
    · exact store_invariant_extend_val hinv ⟨x, t_new⟩ (.denotable d) h_t
        (h_wf_pairs ⟨x, d⟩ (.head _))
    · intro q hq; exact h_wf_pairs q (List.mem_cons_of_mem _ hq)

/-- StoreInvariant preserved under kont extension at current timestamp -/
theorem store_invariant_extend_kont (hinv : StoreInvariant σ entered)
    (ak : TKAddr) (s : TStorable)
    (h_time : ak.frame.time ∈ entered)
    (h_no_conflict : ∀ k : TKAddr, k.frame.time = ak.frame.time →
      k.frame.label = ak.frame.label →
      k.frame.content.isLetFrame = ak.frame.content.isLetFrame →
      σ (.kont k) = none)
    (h_wf : WellFormedStorable s) :
    StoreInvariant (σ.extend (.kont ak) s) entered := by
  exact {
    order := order_invariant_extend hinv.order (by simp [TAddr.time]; exact h_time) s
    names := by
      intro a₁ a₂ ht hn ha₁ ha₂
      simp only [TStore.extend] at ha₁ ha₂
      split at ha₁ <;> split at ha₂ <;> simp_all
      exact hinv.names a₁ a₂ ht hn ha₁ ha₂
    konts := kont_distinct_extend_kont hinv.konts ak s h_no_conflict
    wf_store := wellFormedStore_extend hinv.wf_store _ s h_wf
    call_parent := hinv.call_parent
    handler_parent := hinv.handler_parent
  }

/-! ## Empty Store Invariant -/

/-- Empty store satisfies the invariant trivially -/
theorem store_invariant_empty : StoreInvariant TStore.empty ∅ := by
  exact {
    order := fun a ha => by simp [TStore.empty] at ha
    names := fun a₁ a₂ _ _ ha₁ _ => by simp [TStore.empty] at ha₁
    konts := fun k₁ k₂ _ _ _ hk₁ _ => by simp [TStore.empty] at hk₁
    wf_store := wellFormedStore_empty
    call_parent := fun _ _ _ h => by simp at h
    handler_parent := fun _ _ _ h => by simp at h
  }

/-! ## Key Address Freshness Theorems -/

/-- If timestamp is not entered, then any val address at that timestamp is fresh -/
theorem val_addr_fresh_of_time_not_entered (hinv : OrderInvariant σ entered)
    (h_not : t ∉ entered) (x : Var) :
    σ (.val ⟨x, t⟩) = none := by
  by_contra h
  push_neg at h
  have := hinv (.val ⟨x, t⟩) h
  simp [TAddr.time] at this
  exact h_not this

/-- If timestamp is not entered, then any kont address at that timestamp is fresh -/
theorem kont_addr_fresh_of_time_not_entered (hinv : OrderInvariant σ entered)
    (h_not : t ∉ entered) (k : TKAddr) (h_time : k.frame.time = t) :
    σ (.kont k) = none := by
  by_contra h
  push_neg at h
  have := hinv (.kont k) h
  simp [TAddr.time] at this
  rw [h_time] at this
  exact h_not this

/-! ## Within-Segment Freshness -/

/-- All val addresses at time t with names NOT in `used` are none in σ -/
def ValFreshExcept (σ : TStore) (t : Time) (used : Finset Var) : Prop :=
  ∀ x, x ∉ used → σ (.val ⟨x, t⟩) = none

/-- All kont addresses at time t with (label,op) NOT in `used` are none in σ -/
def KontFreshExcept (σ : TStore) (t : Time) (used : Finset Label) : Prop :=
  ∀ k : TKAddr, k.frame.time = t → (k.frame.label) ∉ used → σ (.kont k) = none

/-- Let-frame kont addresses at time t with (label,op) NOT in `used` are none in σ -/
def LetKontFresh (σ : TStore) (t : Time) (used : Finset Label) : Prop :=
  ∀ k : TKAddr, k.frame.time = t → k.frame.content.isLetFrame →
    (k.frame.label) ∉ used → σ (.kont k) = none

/-- Handler-frame kont addresses at time t with (label,op) NOT in `used` are none in σ -/
def HandlerKontFresh (σ : TStore) (t : Time) (used : Finset Label) : Prop :=
  ∀ k : TKAddr, k.frame.time = t → ¬k.frame.content.isLetFrame →
    (k.frame.label) ∉ used → σ (.kont k) = none

/-- KontFreshExcept implies both LetKontFresh and HandlerKontFresh -/
theorem KontFreshExcept.toLetKontFresh (h : KontFreshExcept σ t used) :
    LetKontFresh σ t used :=
  fun k hk _ hlo => h k hk hlo

theorem KontFreshExcept.toHandlerKontFresh (h : KontFreshExcept σ t used) :
    HandlerKontFresh σ t used :=
  fun k hk _ hlo => h k hk hlo

/-! ### LetKontFresh / HandlerKontFresh lemmas -/

/-- LetKontFresh is monotone in the used set -/
theorem LetKontFresh.mono (h : LetKontFresh σ t S₁) (h_sub : S₁ ⊆ S₂) :
    LetKontFresh σ t S₂ :=
  fun k hk hlet hlo => h k hk hlet (fun hm => hlo (h_sub hm))

/-- HandlerKontFresh is monotone in the used set -/
theorem HandlerKontFresh.mono (h : HandlerKontFresh σ t S₁) (h_sub : S₁ ⊆ S₂) :
    HandlerKontFresh σ t S₂ :=
  fun k hk hlet hlo => h k hk hlet (fun hm => hlo (h_sub hm))

/-- LetKontFresh preserved under val extension -/
theorem letKontFresh_extend_val (h : LetKontFresh σ t used)
    (av : TVAddr) (s : TStorable) :
    LetKontFresh (σ.extend (.val av) s) t used := by
  intro k hk hlet hlo; simp [TStore.extend]; exact h k hk hlet hlo

/-- HandlerKontFresh preserved under val extension -/
theorem handlerKontFresh_extend_val (h : HandlerKontFresh σ t used)
    (av : TVAddr) (s : TStorable) :
    HandlerKontFresh (σ.extend (.val av) s) t used := by
  intro k hk hlet hlo; simp [TStore.extend]; exact h k hk hlet hlo

/-- LetKontFresh preserved under let-frame kont extension (adds to used) -/
theorem letKontFresh_extend_kont_let (h : LetKontFresh σ t used)
    (clo : TClosure) (ak_time : Time) (ak_label : Label)
    (s : TStorable) :
    LetKontFresh (σ.extend (.kont ⟨⟨.letFrame clo, ak_time, ak_label⟩, ak_op⟩) s) t
      (insert (ak_label) used) := by
  intro k hk hlet hlo
  simp only [Finset.mem_insert, not_or] at hlo
  have hne : (TAddr.kont k) ≠ TAddr.kont ⟨⟨.letFrame clo, ak_time, ak_label⟩, ak_op⟩ := by
    intro heq
    have := TAddr.kont.inj heq; subst this
    grind
  simp [TStore.extend, hne]
  exact h k hk hlet hlo.2

/-- LetKontFresh preserved under handler-frame kont extension (no change to used) -/
theorem letKontFresh_extend_kont_handler (h : LetKontFresh σ t used)
    (hdl : Handler) (ρ : TEnv) (ak_time : Time) (ak_label : Label)
    (s : TStorable) :
    LetKontFresh (σ.extend (.kont ⟨⟨.handlerFrame hdl ρ, ak_time, ak_label⟩, ak_op⟩) s) t
      used := by
  intro k hk hlet hlo
  have hne : (TAddr.kont k) ≠ TAddr.kont ⟨⟨.handlerFrame hdl ρ, ak_time, ak_label⟩, ak_op⟩ := by
    intro heq
    have := TAddr.kont.inj heq; subst this
    simp [TFrameContent.isLetFrame] at hlet
  simp [TStore.extend, hne]
  exact h k hk hlet hlo

/-- HandlerKontFresh preserved under handler-frame kont extension (adds to used) -/
theorem handlerKontFresh_extend_kont_handler (h : HandlerKontFresh σ t used)
    (hdl : Handler) (ρ : TEnv) (ak_time : Time) (ak_label : Label)
    (s : TStorable) :
    HandlerKontFresh (σ.extend (.kont ⟨⟨.handlerFrame hdl ρ, ak_time, ak_label⟩, ak_op⟩) s) t
      (insert (ak_label) used) := by
  intro k hk hlet hlo
  simp only [Finset.mem_insert, not_or] at hlo
  have hne : (TAddr.kont k) ≠ TAddr.kont ⟨⟨.handlerFrame hdl ρ, ak_time, ak_label⟩, ak_op⟩ := by
    intro heq
    have := TAddr.kont.inj heq; subst this
    grind
  simp [TStore.extend, hne]
  exact h k hk hlet hlo.2

/-- HandlerKontFresh preserved under let-frame kont extension (no change to used) -/
theorem handlerKontFresh_extend_kont_let (h : HandlerKontFresh σ t used)
    (clo : TClosure) (ak_time : Time) (ak_label : Label)
    (s : TStorable) :
    HandlerKontFresh (σ.extend (.kont ⟨⟨.letFrame clo, ak_time, ak_label⟩, ak_op⟩) s) t
      used := by
  intro k hk hlet hlo
  have hne : (TAddr.kont k) ≠ TAddr.kont ⟨⟨.letFrame clo, ak_time, ak_label⟩, ak_op⟩ := by
    intro heq
    have := TAddr.kont.inj heq; subst this
    simp [TFrameContent.isLetFrame] at hlet
  simp [TStore.extend, hne]
  exact h k hk hlet hlo

/-- LetKontFresh from full freshness -/
theorem letKontFresh_of_fresh (h : fresh σ t) : LetKontFresh σ t ∅ := by
  intro k hk _ _
  by_contra h_ne; push_neg at h_ne
  exact h (.kont k) h_ne (by simp [TAddr.time]; exact hk)

/-- HandlerKontFresh from full freshness -/
theorem handlerKontFresh_of_fresh (h : fresh σ t) : HandlerKontFresh σ t ∅ := by
  intro k hk _ _
  by_contra h_ne; push_neg at h_ne
  exact h (.kont k) h_ne (by simp [TAddr.time]; exact hk)

/-- LetKontFresh from not-entered -/
theorem letKontFresh_of_not_entered (hinv : OrderInvariant σ entered)
    (h_not : t ∉ entered) : LetKontFresh σ t ∅ :=
  letKontFresh_of_fresh (fresh_of_not_entered hinv h_not)

/-- HandlerKontFresh from not-entered -/
theorem handlerKontFresh_of_not_entered (hinv : OrderInvariant σ entered)
    (h_not : t ∉ entered) : HandlerKontFresh σ t ∅ :=
  handlerKontFresh_of_fresh (fresh_of_not_entered hinv h_not)

/-- StorePreservation preserves LetKontFresh -/
theorem StorePreservation.letKontFresh (h : StorePreservation σ σ' t)
    (hfe : LetKontFresh σ t used) : LetKontFresh σ' t used := by
  intro k htime hlet hk; rw [h (.kont k) htime]; exact hfe k htime hlet hk

/-- StorePreservation preserves HandlerKontFresh -/
theorem StorePreservation.handlerKontFresh (h : StorePreservation σ σ' t)
    (hfe : HandlerKontFresh σ t used) : HandlerKontFresh σ' t used := by
  intro k htime hlet hk; rw [h (.kont k) htime]; exact hfe k htime hlet hk

/-- Let-kont no-conflict: from LetKontFresh, derive all let-frame konts at (l,op) are none -/
theorem let_kont_no_conflict_of_letKontFresh
    (h : LetKontFresh σ t used)
    (ak_label : Label)
    (h_not : (ak_label) ∉ used) :
    ∀ k : TKAddr, k.frame.time = t →
      k.frame.content.isLetFrame →
      k.frame.label = ak_label → σ (.kont k) = none := by
  intro k hkt hlet hkl
  apply h k hkt hlet
  rwa [hkl]

/-- Handler-kont no-conflict: from HandlerKontFresh, derive all handler-frame konts at (l,op) are none -/
theorem handler_kont_no_conflict_of_handlerKontFresh
    (h : HandlerKontFresh σ t used)
    (ak_label : Label)
    (h_not : (ak_label) ∉ used) :
    ∀ k : TKAddr, k.frame.time = t →
      ¬k.frame.content.isLetFrame →
      k.frame.label = ak_label → σ (.kont k) = none := by
  intro k hkt hlet hkl
  apply h k hkt hlet
  rwa [hkl]

/-- LetKontFresh foldl val extensions -/
theorem letKontFresh_foldl_val (h : LetKontFresh σ t used)
    (pairs : List (Var × TDenotable)) :
    LetKontFresh (pairs.foldl
      (fun s (xd : Var × TDenotable) => s.extend (.val ⟨xd.1, t⟩) (.denotable xd.2)) σ)
      t used := by
  induction pairs generalizing σ with
  | nil => exact h
  | cons p ps ih =>
    simp only [List.foldl]
    exact ih (letKontFresh_extend_val h ⟨p.1, t⟩ (.denotable p.2))

/-- HandlerKontFresh foldl val extensions -/
theorem handlerKontFresh_foldl_val (h : HandlerKontFresh σ t used)
    (pairs : List (Var × TDenotable)) :
    HandlerKontFresh (pairs.foldl
      (fun s (xd : Var × TDenotable) => s.extend (.val ⟨xd.1, t⟩) (.denotable xd.2)) σ)
      t used := by
  induction pairs generalizing σ with
  | nil => exact h
  | cons p ps ih =>
    simp only [List.foldl]
    exact ih (handlerKontFresh_extend_val h ⟨p.1, t⟩ (.denotable p.2))

/-- From LetKontFresh, get the kind-specific no-conflict for store_invariant_extend_kont
    when inserting a let-frame kont -/
theorem let_kont_no_conflict_for_insert
    (h : LetKontFresh σ t used)
    (clo : TClosure) (ak_label : Label)
    (h_not : (ak_label) ∉ used) :
    ∀ k : TKAddr, k.frame.time = t →
      k.frame.label = ak_label →
      k.frame.content.isLetFrame = (TFrameContent.letFrame clo).isLetFrame →
      σ (.kont k) = none := by
  intro k hkt hkl hkind
  apply h k hkt
  · simp [TFrameContent.isLetFrame] at hkind; exact hkind
  · rwa [hkl]

/-- From HandlerKontFresh, get the kind-specific no-conflict for store_invariant_extend_kont
    when inserting a handler-frame kont -/
theorem handler_kont_no_conflict_for_insert
    (h : HandlerKontFresh σ t used)
    (hdl : Handler) (ρ : TEnv) (ak_label : Label)
    (h_not : (ak_label) ∉ used) :
    ∀ k : TKAddr, k.frame.time = t →
      k.frame.label = ak_label →
      k.frame.content = (TFrameContent.handlerFrame hdl ρ) →
      σ (.kont k) = none := by
  intro k hkt hkl hkind
  apply h k hkt
  · simp [TFrameContent.isLetFrame]; simp [hkind]
  · rwa [hkl]

/-! ### Monotonicity and trivial lookups -/

/-- ValFreshExcept is monotone in the used set: larger set → easier to satisfy -/
theorem ValFreshExcept.mono (h : ValFreshExcept σ t S₁) (h_sub : S₁ ⊆ S₂) :
    ValFreshExcept σ t S₂ :=
  fun x hx => h x (fun hm => hx (h_sub hm))

/-- KontFreshExcept is monotone in the used set -/
theorem KontFreshExcept.mono (h : KontFreshExcept σ t S₁) (h_sub : S₁ ⊆ S₂) :
    KontFreshExcept σ t S₂ :=
  fun k hk hlo => h k hk (fun hm => hlo (h_sub hm))

theorem ValFreshExcept.lookup (h : ValFreshExcept σ t used) (hx : x ∉ used) :
    σ (.val ⟨x, t⟩) = none := h x hx

theorem KontFreshExcept.lookup (h : KontFreshExcept σ t used)
    (k : TKAddr) (hk : k.frame.time = t) (hlo : (k.frame.label) ∉ used) :
    σ (.kont k) = none := h k hk hlo

/-! ### StorePreservation → FreshExcept -/

theorem StorePreservation.valFreshExcept (h : StorePreservation σ σ' t)
    (hfe : ValFreshExcept σ t usedVal) : ValFreshExcept σ' t usedVal := by
  intro x hx; rw [h (.val ⟨x, t⟩) rfl]; exact hfe.lookup hx

theorem StorePreservation.kontFreshExcept (h : StorePreservation σ σ' t)
    (hfe : KontFreshExcept σ t usedKont) : KontFreshExcept σ' t usedKont := by
  intro k htime hk; rw [h (.kont k) htime]; exact hfe k htime hk

/-! ### From full freshness -/

theorem valFreshExcept_of_fresh (h : fresh σ t) : ValFreshExcept σ t ∅ := by
  intro x _
  by_contra h_ne; push_neg at h_ne
  exact h (.val ⟨x, t⟩) h_ne rfl

theorem kontFreshExcept_of_fresh (h : fresh σ t) : KontFreshExcept σ t ∅ := by
  intro k hk _
  by_contra h_ne; push_neg at h_ne
  exact h (.kont k) h_ne (by simp [TAddr.time]; exact hk)

/-! ### Val extension at same time: adds name to used set -/

theorem valFreshExcept_extend_val_same (h : ValFreshExcept σ t used) (y : Var) (s : TStorable) :
    ValFreshExcept (σ.extend (.val ⟨y, t⟩) s) t (insert y used) := by
  intro x hx
  simp only [Finset.mem_insert, not_or] at hx
  have hne : (TAddr.val ⟨x, t⟩) ≠ TAddr.val ⟨y, t⟩ := by
    intro heq; exact hx.1 (congrArg TVAddr.name (TAddr.val.inj heq))
  simp [TStore.extend, hne]
  exact h x hx.2

/-! ### Val extension at different time: preserves -/

theorem valFreshExcept_extend_val_diff (h : ValFreshExcept σ t used)
    (y : Var) (t' : Time) (h_ne : t' ≠ t) (s : TStorable) :
    ValFreshExcept (σ.extend (.val ⟨y, t'⟩) s) t used := by
  intro x hx
  have hne : (TAddr.val ⟨x, t⟩) ≠ TAddr.val ⟨y, t'⟩ := by
    intro heq
    exact h_ne (congrArg TVAddr.time (TAddr.val.inj heq)).symm
  simp [TStore.extend, hne]
  exact h x hx

/-! ### Kont extension: preserves val freshness -/

theorem valFreshExcept_extend_kont (h : ValFreshExcept σ t used)
    (k : TKAddr) (s : TStorable) :
    ValFreshExcept (σ.extend (.kont k) s) t used := by
  intro x hx
  simp [TStore.extend]
  exact h x hx

/-! ### Val extension: preserves kont freshness -/

theorem kontFreshExcept_extend_val (h : KontFreshExcept σ t used)
    (av : TVAddr) (s : TStorable) :
    KontFreshExcept (σ.extend (.val av) s) t used := by
  intro k hk hlo
  simp [TStore.extend]
  exact h k hk hlo

/-! ### Kont extension at same time: adds to used set -/

theorem kontFreshExcept_extend_kont_same (h : KontFreshExcept σ t used)
    (ak : TKAddr) (h_time : ak.frame.time = t) (s : TStorable) :
    KontFreshExcept (σ.extend (.kont ak) s) t (insert (ak.frame.label) used) := by
  intro k hk hlo
  simp only [Finset.mem_insert, not_or] at hlo
  have hne : (TAddr.kont k) ≠ TAddr.kont ak := by
    intro heq
    have := TAddr.kont.inj heq; subst this
    grind
  simp [TStore.extend, hne]
  exact h k hk hlo.2

/-! ### Kont extension at different time: preserves -/

theorem kontFreshExcept_extend_kont_diff (h : KontFreshExcept σ t used)
    (ak : TKAddr) (h_time : ak.frame.time ≠ t) (s : TStorable) :
    KontFreshExcept (σ.extend (.kont ak) s) t used := by
  intro k hk hlo
  have hne : (TAddr.kont k) ≠ TAddr.kont ak := by
    intro heq
    have := TAddr.kont.inj heq; subst this
    exact h_time (hk ▸ rfl)
  simp [TStore.extend, hne]
  exact h k hk hlo

/-! ### Foldl of val extensions at same time -/

theorem valFreshExcept_foldl_same (h : ValFreshExcept σ t used)
    (pairs : List (Var × TDenotable)) :
    ∀ x, x ∉ used → x ∉ (pairs.map Prod.fst) →
      (pairs.foldl (fun s (xd : Var × TDenotable) =>
        s.extend (.val ⟨xd.1, t⟩) (.denotable xd.2)) σ) (.val ⟨x, t⟩) = none := by
  induction pairs generalizing σ used with
  | nil => intro x hx _; exact h x hx
  | cons p ps ih =>
    intro x hx hx_not
    simp only [List.map_cons, List.mem_cons, not_or] at hx_not
    simp only [List.foldl]
    apply ih (valFreshExcept_extend_val_same h p.1 (.denotable p.2))
    · simp [Finset.mem_insert]; exact ⟨hx_not.1, hx⟩
    · exact hx_not.2

theorem kontFreshExcept_foldl_val (h : KontFreshExcept σ t used)
    (pairs : List (Var × TDenotable)) :
    KontFreshExcept (pairs.foldl
      (fun s (xd : Var × TDenotable) => s.extend (.val ⟨xd.1, t⟩) (.denotable xd.2)) σ)
      t used := by
  induction pairs generalizing σ with
  | nil => exact h
  | cons p ps ih =>
    simp only [List.foldl]
    exact ih (kontFreshExcept_extend_val h ⟨p.1, t⟩ (.denotable p.2))

/-! ### Kont no-conflict from KontFreshExcept -/

theorem kont_no_conflict_of_kontFreshExcept
    (h : KontFreshExcept σ t used)
    (ak : TKAddr) (h_time : ak.frame.time = t)
    (h_not : (ak.frame.label) ∉ used) :
    ∀ k : TKAddr, k.frame.time = ak.frame.time →
      k.frame.label = ak.frame.label → σ (.kont k) = none := by
  intro k hkt hkl
  apply h k (hkt ▸ h_time)
  rwa [hkl]

/-! ### From not-entered (combining OrderInvariant + ValFreshExcept) -/

theorem valFreshExcept_of_not_entered (hinv : OrderInvariant σ entered)
    (h_not : t ∉ entered) : ValFreshExcept σ t ∅ :=
  valFreshExcept_of_fresh (fresh_of_not_entered hinv h_not)

theorem kontFreshExcept_of_not_entered (hinv : OrderInvariant σ entered)
    (h_not : t ∉ entered) : KontFreshExcept σ t ∅ :=
  kontFreshExcept_of_fresh (fresh_of_not_entered hinv h_not)

/-! ## Store lookup helpers for WellFormedStore -/

/-- If a denotable is in a WellFormedStore, its storable is WellFormedStorable -/
theorem wellFormedStorable_of_store_lookup (h_wf : WellFormedStore σ)
    (h_lookup : σ a = some (.denotable d)) :
    WellFormedStorable (.denotable d) := by
  have := h_wf a
  rw [h_lookup] at this
  match d with
  | .closure ⟨_, body, _, _⟩ => exact this
  | .kontClosure h _ _ => exact this
  | .conLabel _ => trivial
  | .succVal _ => trivial

/-- Closure body from store is well-formed -/
theorem wellFormedProgram_of_store_closure (h_wf : WellFormedStore σ)
    (h_lookup : σ a = some (.denotable (.closure ⟨xs, body, env, h_nd⟩))) :
    WellFormedProgram body := by
  have := h_wf a; rw [h_lookup] at this; exact this.1

/-- KontClosure handler from store is well-formed -/
theorem wellFormedSubHandler_of_store_kontClosure (h_wf : WellFormedStore σ)
    (h_lookup : σ a = some (.denotable (.kontClosure h env ak))) :
    WellFormedSubHandler h := by
  have := h_wf a; rw [h_lookup] at this; exact this

/-- Convert WellFormedValue (.den d) to WellFormedStorable (.denotable d) -/
theorem WellFormedValue.to_wellFormedStorable {d : TDenotable}
    (h : WellFormedValue (.den d)) : WellFormedStorable (.denotable d) := by
  cases d with
  | closure c => cases c; exact h
  | kontClosure => exact h
  | conLabel => trivial
  | succVal => trivial

/-- Convert WellFormedStorable (.denotable d) to WellFormedValue (.den d) -/
theorem WellFormedValue.of_wellFormedStorable {d : TDenotable}
    (h : WellFormedStorable (.denotable d)) : WellFormedValue (.den d) := by
  cases d with
  | closure c => cases c; exact h
  | kontClosure => exact h
  | conLabel => trivial
  | succVal => trivial

/-- WellFormedValue for suspended values is trivially true -/
theorem WellFormedValue.suspended (op : OpName) (addrs : List TVAddr) (oa : Option TKAddr) :
    WellFormedValue (.suspended op addrs oa) := trivial

/-! ## NEW: IsDescendant, EnteredDescendants, SiblingsFresh -/

/-- t' is a descendant of t in the timestamp tree -/
inductive IsDescendant : Time → Time → Prop where
  | refl : IsDescendant t t
  | call (l : Label) : IsDescendant t' {tk := l :: t.tk, tmk := t.tmk} → IsDescendant t' t
  | handler (l : Label) : IsDescendant t' {tk := [], tmk := (l, t.tk) :: t.tmk} → IsDescendant t' t

/-- Transitivity of IsDescendant -/
theorem IsDescendant.trans {t₁ t₂ t₃ : Time}
    (h1 : IsDescendant t₁ t₂) (h2 : IsDescendant t₂ t₃) :
    IsDescendant t₁ t₃ := by
  induction h2 generalizing t₁ with
  | refl => exact h1
  | call l _ ih => exact .call l (ih h1)
  | handler l _ ih => exact .handler l (ih h1)

/-- All newly-entered timestamps are descendants of t_eval -/
def EnteredDescendants (entered entered' : EnteredTimes) (t_eval : Time) : Prop :=
  ∀ t ∈ entered', t ∉ entered → IsDescendant t t_eval

/-- New call/handler children of t are bounded by the expression's labels -/
def SiblingsFresh (entered entered' : EnteredTimes) (t : Time) (labels : Finset Label) : Prop :=
  (∀ l, ({tk := [l] ++ t.tk, tmk := t.tmk} : Time) ∈ entered' →
    ({tk := [l] ++ t.tk, tmk := t.tmk} : Time) ∈ entered ∨ l ∈ labels) ∧
  (∀ l, ({tk := [], tmk := (l, t.tk) :: t.tmk} : Time) ∈ entered' →
    ({tk := [], tmk := (l, t.tk) :: t.tmk} : Time) ∈ entered ∨ l ∈ labels)

/-! ### EnteredDescendants lemmas -/

theorem enteredDescendants_refl (entered : EnteredTimes) (t : Time) :
    EnteredDescendants entered entered t := by
  intro t ht hnt; exact absurd ht hnt

theorem enteredDescendants_trans
    (h12 : EnteredDescendants entered₁ entered₂ t)
    (h23 : EnteredDescendants entered₂ entered₃ t) :
    EnteredDescendants entered₁ entered₃ t := by
  intro t' ht' hnt'
  by_cases h : t' ∈ entered₂
  · exact h12 t' h hnt'
  · exact h23 t' ht' h



/-- Entering a call child: all timestamps in `entered ∪ {t_child}` where
    t_child = ⟨l :: t.tk, t.tmk⟩ that are new to `entered` are descendants of t -/
theorem enteredDescendants_enter_call (entered : EnteredTimes) (t : Time) (l : Label) :
    EnteredDescendants entered (entered ∪ {⟨l :: t.tk, t.tmk⟩}) t := by
  intro t' ht' hnt'
  simp only [Finset.mem_union, Finset.mem_singleton] at ht'
  rcases ht' with ht' | ht'
  · exact absurd ht' hnt'
  · subst ht'; exact .call l .refl

/-- Entering a handler child -/
theorem enteredDescendants_enter_handler (entered : EnteredTimes) (t : Time) (l : Label) :
    EnteredDescendants entered (entered ∪ {⟨[], (l, t.tk) :: t.tmk⟩}) t := by
  intro t' ht' hnt'
  simp only [Finset.mem_union, Finset.mem_singleton] at ht'
  rcases ht' with ht' | ht'
  · exact absurd ht' hnt'
  · subst ht'; exact .handler l .refl

/-- If all new entries in entered₂ are descendants of a call child ⟨l::t.tk, t.tmk⟩,
    then they are also descendants of t -/
theorem enteredDescendants_of_call_child
    (h : EnteredDescendants entered₁ entered₂ ⟨l :: t.tk, t.tmk⟩) :
    EnteredDescendants entered₁ entered₂ t := by
  intro t' ht' hnt'
  exact .call l (h t' ht' hnt')

/-- If all new entries in entered₂ are descendants of a handler child,
    then they are also descendants of t -/
theorem enteredDescendants_of_handler_child
    (h : EnteredDescendants entered₁ entered₂ ⟨[], (l, t.tk) :: t.tmk⟩) :
    EnteredDescendants entered₁ entered₂ t := by
  intro t' ht' hnt'
  exact .handler l (h t' ht' hnt')

/-! ### SiblingsFresh lemmas -/

theorem siblingsFresh_refl (entered : EnteredTimes) (t : Time) (labels : Finset Label) :
    SiblingsFresh entered entered t labels := by
  exact ⟨fun _ h => Or.inl h, fun _ h => Or.inl h⟩

theorem siblingsFresh_mono (h : SiblingsFresh entered entered' t S₁) (h_sub : S₁ ⊆ S₂) :
    SiblingsFresh entered entered' t S₂ := by
  constructor
  · intro l hl
    rcases h.1 l hl with h | h
    · exact Or.inl h
    · exact Or.inr (h_sub h)
  · intro l hl
    rcases h.2 l hl with h | h
    · exact Or.inl h
    · exact Or.inr (h_sub h)

-- Note: siblingsFresh_mono_entered is NOT true in general without additional info.
-- Use siblingsFresh_trans instead.

theorem siblingsFresh_trans
    (h12 : SiblingsFresh entered₁ entered₂ t labels₁)
    (h23 : SiblingsFresh entered₂ entered₃ t labels₂) :
    SiblingsFresh entered₁ entered₃ t (labels₁ ∪ labels₂) := by
  constructor
  · intro l hl
    rcases h23.1 l hl with h | h
    · rcases h12.1 l h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Finset.mem_union_left _ h')
    · exact Or.inr (Finset.mem_union_right _ h)
  · intro l hl
    rcases h23.2 l hl with h | h
    · rcases h12.2 l h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Finset.mem_union_left _ h')
    · exact Or.inr (Finset.mem_union_right _ h)

/-! ### Helper lemmas about descendant structure -/

/-- tmk of a descendant extends tmk of ancestor by prepending. -/
theorem IsDescendant.tmk_suffix (h : IsDescendant t' t) : ∃ pfx, t'.tmk = pfx ++ t.tmk := by
  match h with
  | .refl => exact ⟨[], by simp⟩
  | .call _ h' => exact h'.tmk_suffix
  | .handler l h' =>
    obtain ⟨pfx, hpfx⟩ := h'.tmk_suffix
    exact ⟨pfx ++ [⟨l, _⟩], by rw [List.append_assoc]; exact hpfx⟩

/-- Recursive weight for tmk component. -/
private def tmkWeight : List (Label × KTime) → Nat
  | [] => 0
  | (_, tk) :: rest => tk.length + 1 + tmkWeight rest

/-- Weight function: each IsDescendant step adds exactly 1. -/
private def timeWeight (t : Time) : Nat := t.tk.length + tmkWeight t.tmk

theorem IsDescendant.weight_le (h : IsDescendant t' t) : timeWeight t ≤ timeWeight t' := by
  match h with
  | .refl => omega
  | .call l h' =>
    have ih := h'.weight_le
    simp only [timeWeight, List.length_cons] at ih ⊢; omega
  | .handler l h' =>
    have ih := h'.weight_le
    simp only [timeWeight, tmkWeight] at ih ⊢; omega

theorem IsDescendant.eq_of_weight_eq (h : IsDescendant t' t)
    (hw : timeWeight t' = timeWeight t) : t' = t := by
  match h with
  | .refl => rfl
  | .call l h' =>
    exfalso
    have h1 := h'.weight_le
    simp only [timeWeight, List.length_cons] at h1 hw; omega
  | .handler l h' =>
    exfalso
    have h1 := h'.weight_le
    simp only [timeWeight, tmkWeight] at h1 hw; omega

/-! ### Key structural lemmas about descendants and siblings -/

/-- A descendant of ⟨l :: tk₀, tmk₀⟩ with tk = l' :: tk₀ and tmk = tmk₀ must have l' = l. -/
theorem call_child_not_sibling
    (h : IsDescendant t' ⟨l :: tk₀, tmk₀⟩)
    (h_tk : t'.tk = [l'] ++ tk₀) (h_tmk : t'.tmk = tmk₀) : l' = l := by
  have hw : timeWeight t' = timeWeight ⟨l :: tk₀, tmk₀⟩ := by
    simp only [timeWeight, h_tk, h_tmk, List.length_cons, List.length_append, List.length_nil]; omega
  obtain rfl := h.eq_of_weight_eq hw
  simp at h_tk; exact h_tk.symm

/-- A descendant of ⟨[], (l, tk₀) :: tmk₀⟩ cannot have tmk = tmk₀. -/
theorem handler_child_not_call_sibling
    (h : IsDescendant t' ⟨[], (l, tk₀) :: tmk₀⟩)
    (h_tmk : t'.tmk = tmk₀) : False := by
  obtain ⟨pfx, hpfx⟩ := h.tmk_suffix
  rw [h_tmk] at hpfx
  have := congrArg List.length hpfx
  simp [List.length_append] at this
  omega

/-- A descendant of ⟨l :: tk₀, tmk₀⟩ cannot have tk = [] and tmk = (l', tk₀) :: tmk₀. -/
theorem call_child_not_handler_sibling
    (h : IsDescendant t' ⟨l :: tk₀, tmk₀⟩)
    (h_tk : t'.tk = []) (h_tmk : t'.tmk = (l', tk₀) :: tmk₀) : False := by
  have hw : timeWeight t' = timeWeight ⟨l :: tk₀, tmk₀⟩ := by
    simp only [timeWeight, tmkWeight, h_tk, h_tmk, List.length_nil, List.length_cons]; omega
  obtain rfl := h.eq_of_weight_eq hw
  simp at h_tk

/-- A descendant of ⟨[], (l, tk₀) :: tmk₀⟩ with tk = [] and tmk = (l', tk₀) :: tmk₀ has l' = l. -/
theorem handler_child_not_handler_sibling
    (h : IsDescendant t' ⟨[], (l, tk₀) :: tmk₀⟩)
    (h_tk : t'.tk = []) (h_tmk : t'.tmk = (l', tk₀) :: tmk₀) : l' = l := by
  have hw : timeWeight t' = timeWeight ⟨[], (l, tk₀) :: tmk₀⟩ := by
    simp only [timeWeight, tmkWeight, h_tk, h_tmk, List.length_nil]
  obtain rfl := h.eq_of_weight_eq hw
  injection h_tmk with h1 _
  injection h1 with h2 _
  exact h2.symm

/-! ### SiblingsFresh from EnteredDescendants -/

/-- Key lemma: if all new entries are descendants of a call child ⟨l :: t.tk, t.tmk⟩,
    then the only new sibling at t that could appear is the one with label l. -/
theorem siblingsFresh_of_enteredDescendants_call
    (h_ed : EnteredDescendants entered entered' ⟨l :: t.tk, t.tmk⟩) :
    SiblingsFresh entered entered' t {l} := by
  constructor
  · intro l' hl'
    by_cases h_old : ({tk := [l'] ++ t.tk, tmk := t.tmk} : Time) ∈ entered
    · exact Or.inl h_old
    · have h_desc := h_ed _ hl' h_old
      have : l' = l := call_child_not_sibling h_desc (by simp) rfl
      exact Or.inr (by simp [this])
  · intro l' hl'
    by_cases h_old : ({tk := [], tmk := (l', t.tk) :: t.tmk} : Time) ∈ entered
    · exact Or.inl h_old
    · have h_desc := h_ed _ hl' h_old
      exact absurd (call_child_not_handler_sibling h_desc rfl rfl) False.elim

/-- Key lemma: if all new entries are descendants of a handler child,
    then the only new handler sibling at t that could appear is the one with label l. -/
theorem siblingsFresh_of_enteredDescendants_handler
    (h_ed : EnteredDescendants entered entered' ⟨[], (l, t.tk) :: t.tmk⟩) :
    SiblingsFresh entered entered' t {l} := by
  constructor
  · intro l' hl'
    by_cases h_old : ({tk := [l'] ++ t.tk, tmk := t.tmk} : Time) ∈ entered
    · exact Or.inl h_old
    · have h_desc := h_ed _ hl' h_old
      exact absurd (handler_child_not_call_sibling h_desc rfl) False.elim
  · intro l' hl'
    by_cases h_old : ({tk := [], tmk := (l', t.tk) :: t.tmk} : Time) ∈ entered
    · exact Or.inl h_old
    · have h_desc := h_ed _ hl' h_old
      have : l' = l := handler_child_not_handler_sibling h_desc rfl rfl
      exact Or.inr (by simp [this])

/-! ### Conversion: SiblingsFresh → direct freshness hypotheses -/

/-- From h_call_fresh (all labels in allLabels are fresh in entered) and SiblingsFresh
    (all new siblings are bounded by usedLabels), derive freshness for labels in allLabels
    that are not in usedLabels -/
theorem call_not_entered_of_siblingsFresh
    (h_sf : SiblingsFresh entered entered' t usedLabels)
    (h_fresh : ({tk := l :: t.tk, tmk := t.tmk} : Time) ∉ entered)
    (h_l_notin : l ∉ usedLabels) :
    ({tk := l :: t.tk, tmk := t.tmk} : Time) ∉ entered' := by
  intro h_in
  rcases h_sf.1 l (by simpa using h_in) with h | h
  · exact h_fresh h
  · exact h_l_notin h

/-- From h_call_fresh and SiblingsFresh, derive call freshness for labels ∪ new_labels -/
theorem call_fresh_after_siblings
    (h_call_fresh : ∀ l ∈ allLabels, ({tk := l :: t.tk, tmk := t.tmk} : Time) ∉ entered)
    (h_sf : SiblingsFresh entered entered' t usedLabels)
    (h_disj : Disjoint usedLabels allLabels) :
    ∀ l ∈ allLabels, ({tk := l :: t.tk, tmk := t.tmk} : Time) ∉ entered' := by
  intro l hl h_in
  rcases h_sf.1 l (by simpa using h_in) with h | h
  · exact h_call_fresh l hl h
  · exact Finset.disjoint_right.mp h_disj hl h

/-- Similarly for handler freshness -/
theorem handler_fresh_after_siblings
    (h_handler_fresh : ∀ l ∈ allLabels, ({tk := [], tmk := (l, t.tk) :: t.tmk} : Time) ∉ entered)
    (h_sf : SiblingsFresh entered entered' t usedLabels)
    (h_disj : Disjoint usedLabels allLabels) :
    ∀ l ∈ allLabels, ({tk := [], tmk := (l, t.tk) :: t.tmk} : Time) ∉ entered' := by
  intro l hl h_in
  rcases h_sf.2 l (by simpa using h_in) with h | h
  · exact h_handler_fresh l hl h
  · exact Finset.disjoint_right.mp h_disj hl h

/-! ### Monotonicity helpers -/

theorem store_invariant_enter_call (hinv : StoreInvariant σ entered)
    (h_t_entered : t ∈ entered) (l : Label) :
    StoreInvariant σ (entered ∪ {⟨l :: t.tk, t.tmk⟩}) := by
  exact {
    order := fun a ha => Finset.mem_union_left _ (hinv.order a ha)
    names := hinv.names
    konts := hinv.konts
    wf_store := hinv.wf_store
    call_parent := fun l' tk' tmk' h => by
      simp only [Finset.mem_union, Finset.mem_singleton] at h ⊢
      rcases h with h | h
      · exact Or.inl (hinv.call_parent l' tk' tmk' h)
      · have htk : l' :: tk' = l :: t.tk := congr_arg Time.tk h
        have htmk : tmk' = t.tmk := congr_arg Time.tmk h
        rw [List.cons_eq_cons] at htk
        obtain ⟨h1, h2⟩ := htk
        subst h1; subst h2; subst htmk
        exact Or.inl h_t_entered
    handler_parent := fun l' tk' tmk' h => by
      simp only [Finset.mem_union, Finset.mem_singleton] at h ⊢
      rcases h with h | h
      · exact Or.inl (hinv.handler_parent l' tk' tmk' h)
      · have : ([] : List Label) = l :: t.tk := congr_arg Time.tk h
        exact absurd this (by simp)
  }

theorem store_invariant_enter_handler (hinv : StoreInvariant σ entered)
    (h_t_entered : t ∈ entered) (l : Label) :
    StoreInvariant σ (entered ∪ {⟨[], (l, t.tk) :: t.tmk⟩}) := by
  exact {
    order := fun a ha => Finset.mem_union_left _ (hinv.order a ha)
    names := hinv.names
    konts := hinv.konts
    wf_store := hinv.wf_store
    call_parent := fun l' tk' tmk' h => by
      simp only [Finset.mem_union, Finset.mem_singleton] at h ⊢
      rcases h with h | h
      · exact Or.inl (hinv.call_parent l' tk' tmk' h)
      · have : l' :: tk' = ([] : List Label) := congr_arg Time.tk h
        exact absurd this (by simp)
    handler_parent := fun l' tk' tmk' h => by
      simp only [Finset.mem_union, Finset.mem_singleton] at h ⊢
      rcases h with h | h
      · exact Or.inl (hinv.handler_parent l' tk' tmk' h)
      · have htk : ([] : List Label) = [] := congr_arg Time.tk h
        have htmk : (l', tk') :: tmk' = (l, t.tk) :: t.tmk := congr_arg Time.tmk h
        rw [List.cons_eq_cons] at htmk
        obtain ⟨hlk, htmk'⟩ := htmk
        have : tk' = t.tk := congr_arg Prod.snd hlk
        subst this; subst htmk'
        exact Or.inl h_t_entered
  }

/-! ### Cross-tmk ancestry lemmas -/

/-- IsDescendant implies tmk suffix (convenience wrapper) -/
theorem IsDescendant.tmk_isSuffix (h : IsDescendant t' t) : t.tmk <:+ t'.tmk := by
  obtain ⟨pfx, hpfx⟩ := h.tmk_suffix
  exact ⟨pfx, hpfx.symm⟩

/-- If t ∈ entered and (l, tk₀) :: tmk₀ is a suffix of t.tmk, then ⟨tk₀, tmk₀⟩ ∈ entered.
    This follows from the call_parent and handler_parent rules by well-founded descent. -/
theorem StoreInvariant.tmk_suffix_entered (hinv : StoreInvariant σ entered)
    (h_entered : t ∈ entered) (h_suffix : ((l, tk₀) :: tmk₀) <:+ t.tmk) :
    (⟨tk₀, tmk₀⟩ : Time) ∈ entered := by
  -- Well-founded induction on timeWeight t
  generalize hweight : timeWeight t = w
  induction w using Nat.strongRecOn generalizing t with
  | _ w ih =>
  obtain ⟨t_tk, t_tmk⟩ := t
  cases htk : t_tk with
  | cons l_h tk_rest =>
    have h_parent := hinv.call_parent l_h tk_rest t_tmk (htk ▸ h_entered)
    have h_wt : timeWeight ⟨tk_rest, t_tmk⟩ < w := by
      rw [← hweight, htk]; simp [timeWeight, List.length_cons]
    exact ih _ h_wt h_parent h_suffix rfl
  | nil =>
    obtain ⟨pfx, hpfx⟩ := h_suffix
    simp at hpfx
    cases pfx with
    | nil =>
      simp at hpfx
      exact hinv.handler_parent l tk₀ tmk₀ (hpfx ▸ htk ▸ h_entered)
    | cons p pfx_rest =>
      simp at hpfx
      have h_parent := hinv.handler_parent p.1 p.2 (pfx_rest ++ (l, tk₀) :: tmk₀)
        (by rw [Prod.mk.eta]; exact hpfx ▸ htk ▸ h_entered)
      have h_wt : timeWeight ⟨p.2, pfx_rest ++ (l, tk₀) :: tmk₀⟩ < w := by
        rw [← hweight, htk, ← hpfx]; simp [timeWeight, tmkWeight]
      exact ih _ h_wt h_parent ⟨pfx_rest, rfl⟩ rfl

/-- Precondition helper: if t_handle ∉ entered, then tmk_apply is not a suffix of any
    entered timestamp's tmk -/
theorem StoreInvariant.tmk_fresh_of_call_fresh (hinv : StoreInvariant σ entered)
    {t : Time} (l : Label) (h_call_fresh : (⟨l :: t.tk, t.tmk⟩ : Time) ∉ entered) :
    ∀ t' ∈ entered, ¬ ((l, l :: t.tk) :: t.tmk) <:+ t'.tmk := by
  intro t' ht' hsuf
  exact h_call_fresh (hinv.tmk_suffix_entered ht' hsuf)

/-- Extending tk preserves descendant: ⟨tk, tmk⟩ is a descendant of ⟨[], tmk⟩ -/
theorem IsDescendant.of_call_chain (tmk : MKTime) :
    ∀ (tk : KTime), IsDescendant ⟨tk, tmk⟩ ⟨[], tmk⟩ := by
  intro tk
  induction tk with
  | nil => exact .refl
  | cons l tk_rest ih => exact (IsDescendant.call l .refl).trans ih

/-- Extending tmk preserves descendant: ⟨[], pfx ++ tmk₀⟩ is a descendant of ⟨[], tmk₀⟩ -/
theorem IsDescendant.of_tmk_prefix (tmk₀ : MKTime) :
    ∀ (pfx : MKTime), IsDescendant ⟨[], pfx ++ tmk₀⟩ ⟨[], tmk₀⟩ := by
  intro pfx
  induction pfx with
  | nil => exact .refl
  | cons entry pfx_rest ih =>
    obtain ⟨l, tk₀⟩ := entry
    exact (IsDescendant.handler l .refl).trans ((of_call_chain _ tk₀).trans ih)

/-- If tmk₀ is a suffix of t.tmk, then t is a descendant of ⟨[], tmk₀⟩ -/
theorem IsDescendant.of_tmk_suffix {t : Time} {tmk₀ : MKTime}
    (h : tmk₀ <:+ t.tmk) : IsDescendant t ⟨[], tmk₀⟩ := by
  obtain ⟨pfx, hpfx⟩ := h
  have h1 : IsDescendant t ⟨[], t.tmk⟩ := of_call_chain t.tmk t.tk
  rw [← hpfx] at h1
  exact h1.trans (of_tmk_prefix tmk₀ pfx)

end DMCFA
