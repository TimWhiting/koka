/-
  Abstraction Function and Abstract Soundness

  Defines α mapping timestamped components to abstract (truncated) components,
  and proves that the abstract semantics is sound with respect to the naive
  timestamped semantics:

    If (e, ρ, σ, t) ⇓et (v, σ') and α(σ) ⊑ σ_a,
    then (e, α(ρ), σ_a, α(t)) ⇓ea (v̂, σ_a') with α(v) ∈ v̂ and α(σ') ⊑ σ_a'.

  The proof is by mutual induction on the timestamped derivation.
-/

import DMCFA.AbstractSemantics
import DMCFA.NaiveSemantics

namespace DMCFA

/-! ## Abstraction on Components -/

/-- Abstract a timestamp by truncating -/
def absTime (m h : Nat) (t : Time) : Time := truncTime m h t

/-- Abstract a value address by truncating its timestamp -/
def absTVAddr (m h : Nat) (a : TVAddr) : TVAddr :=
  ⟨a.name, absTime m h a.time⟩

/-! ## Finmap.mapVal for constant-type Finmap -/

private theorem nodupKeys_map_snd {α : Type*} {β : Type*}
    (f : β → β) (s : Multiset ((_ : α) × β)) (h : s.NodupKeys) :
    (s.map (fun ⟨k, v⟩ => (⟨k, f v⟩ : (_ : α) × β))).NodupKeys := by
  rw [← Multiset.nodup_keys] at h ⊢
  have : (s.map (fun ⟨k, v⟩ => (⟨k, f v⟩ : (_ : α) × β))).keys = s.keys := by
    simp [Multiset.keys, Multiset.map_map, Function.comp]
  rwa [this]

/-- Map a function over the values of a constant-type Finmap -/
noncomputable def Finmap.mapVal {α : Type*} {β : Type*} [DecidableEq α]
    (f : β → β) (m : Finmap (fun _ : α => β)) : Finmap (fun _ : α => β) :=
  ⟨m.entries.map (fun ⟨k, v⟩ => ⟨k, f v⟩), nodupKeys_map_snd f m.entries m.nodupKeys⟩

theorem Finmap.lookup_mapVal {α : Type*} {β : Type*} [DecidableEq α]
    (f : β → β) (m : Finmap (fun _ : α => β)) (k : α) :
    Finmap.lookup k (Finmap.mapVal f m) = (Finmap.lookup k m).map f := by
  cases h : Finmap.lookup k m with
  | none =>
    simp only [Option.map_none]
    rw [Finmap.lookup_eq_none] at h ⊢
    intro hk; apply h
    simp only [Finmap.mem_def, Finmap.mapVal, Multiset.keys, Multiset.map_map] at hk ⊢
    simpa [Function.comp] using hk
  | some v =>
    simp only [Option.map_some]
    rw [Finmap.lookup_eq_some_iff] at h ⊢
    simp only [Finmap.mapVal]
    exact Multiset.mem_map.mpr ⟨⟨k, v⟩, h, rfl⟩

theorem Finmap.mapVal_insert {α : Type*} {β : Type*} [DecidableEq α]
    (f : β → β) (m : Finmap (fun _ : α => β)) (k : α) (v : β) :
    Finmap.mapVal f (m.insert k v) = (Finmap.mapVal f m).insert k (f v) := by
  apply Finmap.ext_lookup
  intro a
  simp only [Finmap.lookup_mapVal]
  by_cases h : a = k
  · subst h; simp [Finmap.lookup_insert]
  · rw [Finmap.lookup_insert_of_ne _ h, Finmap.lookup_insert_of_ne _ h, Finmap.lookup_mapVal]

/-! ## Abstract Environment -/

/-- Abstract environment: pointwise abstraction of addresses -/
noncomputable def absTEnv (m h : Nat) (ρ : TEnv) : TEnv :=
  Finmap.mapVal (absTVAddr m h) ρ

/-- Abstraction commutes with env lookup -/
theorem absTEnv_lookup (m h : Nat) (ρ : TEnv) (x : Var) :
    Finmap.lookup x (absTEnv m h ρ) = (Finmap.lookup x ρ).map (absTVAddr m h) :=
  Finmap.lookup_mapVal (absTVAddr m h) ρ x

/-- Abstraction commutes with env extend -/
theorem absTEnv_extend (m h : Nat) (ρ : TEnv) (x : Var) (a : TVAddr) :
    absTEnv m h (ρ.extend x a) = (absTEnv m h ρ).extend x (absTVAddr m h a) := by
  simp only [absTEnv, TEnv.extend]
  exact Finmap.mapVal_insert (absTVAddr m h) ρ x a

/-- Abstract a frame content -/
noncomputable def absTFrameContent (m h : Nat) : TFrameContent → TFrameContent
  | .letFrame ⟨xs, body, ρ, h_nd⟩ => .letFrame ⟨xs, body, absTEnv m h ρ, h_nd⟩
  | .handlerFrame hdl ρ => .handlerFrame hdl (absTEnv m h ρ)

/-- Abstract a timed frame -/
noncomputable def absTimedFrame (m h : Nat) (ψ : TimedFrame) : TimedFrame :=
  ⟨absTFrameContent m h ψ.content, absTime m h ψ.time, ψ.label⟩

/-- Abstract a continuation address -/
noncomputable def absTKAddr (m h : Nat) (a : TKAddr) : TKAddr :=
  ⟨absTimedFrame m h a.frame, a.op⟩

/-- Abstract a unified address -/
noncomputable def absTAddr (m h : Nat) (a : TAddr) : TAddr :=
  match a with
  | .val va => .val (absTVAddr m h va)
  | .kont ka => .kont (absTKAddr m h ka)

mutual

/-- Abstract a denotable -/
noncomputable def absTDenotable (m h : Nat) : TDenotable → TDenotable
  | .closure ⟨xs, body, ρ, h_nd⟩ => .closure ⟨xs, body, absTEnv m h ρ, h_nd⟩
  | .kontClosure hdl ρ a_κ => .kontClosure hdl (absTEnv m h ρ) (a_κ.map (absTKAddr m h))
  | .conLabel c => .conLabel c
  | .succVal a => .succVal (absTVAddr m h a)

/-- Abstract a value -/
noncomputable def absTValue (m h : Nat) : TValue → TValue
  | .den d => .den (absTDenotable m h d)
  | .suspended op as_v a_κ =>
      .suspended op (as_v.map (absTVAddr m h)) (a_κ.map (absTKAddr m h))

end

/-- Abstract a storable -/
noncomputable def absTStorable (m h : Nat) : TStorable → TStorable
  | .denotable d => .denotable (absTDenotable m h d)
  | .kontLink next => .kontLink (next.map (absTKAddr m h))

/-- Abstract a concrete (timestamped) store into an abstract store.
    Collects all values at addresses that truncate to the same abstract address. -/
noncomputable def absStore (m h : Nat) (σ : TStore) : AStore :=
  fun â => { s' | ∃ a s, σ a = some s ∧ absTAddr m h a = â ∧ s' = absTStorable m h s }

/-! ## Store ordering -/

/-- α(σ) ⊑ σ_a: the abstraction of the concrete store is contained in the abstract store -/
def storeAbstracts (m h : Nat) (σ : TStore) (σ_a : AStore) : Prop :=
  absStore m h σ ≤ σ_a

/-! ## Key Properties -/

/-- List.take is idempotent under cons -/
private theorem take_cons_take (n : Nat) (x : α) (xs : List α) :
    List.take n (x :: xs) = List.take n (x :: List.take n xs) := by
  cases n with
  | zero => simp [List.take]
  | succ n' => simp [List.take, List.take_take]

/-- Timestamp abstraction commutes with t_k extension:
    α(l :: t_k, t_mk) = (⌊l :: α(t_k)⌋_m, α(t_mk)) -/
theorem absTime_extKTime (m h : Nat) (l : Label) (t : Time) :
    absTime m h ⟨l :: t.tk, t.tmk⟩ = ⟨extKTime m l (truncKTime m t.tk), truncMKTime m h t.tmk⟩ := by
  simp only [absTime, truncTime, truncKTime, extKTime, List.trunc]
  congr 1
  exact take_cons_take m l t.tk

/-- absTime commutes with MKTime extension (for eval_handler) -/
theorem absTime_extMKTime (m h : Nat) (l : Label) (t : Time) :
    absTime m h ⟨[], (l, t.tk) :: t.tmk⟩ = ⟨[], extMKTime m h l t.tk t.tmk⟩ := by
  simp only [absTime, truncTime, truncKTime, List.trunc, extMKTime, truncMKTime, List.map_cons,
             List.take_nil]
  congr 2
  rw [List.take_take]; simp

/-- Core: take n (map f (take n xs)) = take n (map f xs) -/
private theorem List.take_map_take (n : Nat) (f : α → β) (xs : List α) :
    List.take n (List.map f (List.take n xs)) = List.take n (List.map f xs) := by
  simp [List.map_take, List.take_take]

private theorem mktime_map_idem (m : Nat) (x : Label × KTime) :
    (fun x : Label × KTime => (x.1, List.take m x.2)) ((fun x : Label × KTime => (x.1, List.take m x.2)) x) =
    (fun x : Label × KTime => (x.1, List.take m x.2)) x := by
  simp [List.take_take]

private theorem list_map_idem {f : α → α} (hf : ∀ x, f (f x) = f x) (xs : List α) :
    List.map f (List.map f xs) = List.map f xs := by
  rw [List.map_map]; congr 1; ext x; exact hf x

/-- Idempotency for the composed truncation function on MKTime entries -/
private theorem take_map_trunc_idem (m h : Nat) (tmk : MKTime) :
    List.take h (List.map (fun x : Label × KTime => (x.1, List.take m x.2))
      (List.take h (List.map (fun x => (x.1, List.take m x.2)) tmk))) =
    List.take h (List.map (fun x => (x.1, List.take m x.2)) tmk) := by
  rw [List.map_take, List.take_take]; simp
  show List.take h (List.map _ tmk) = List.take h (List.map _ tmk)
  congr 2; funext x; exact mktime_map_idem m x

/-- truncMKTime is idempotent -/
theorem truncMKTime_idem (m h : Nat) (tmk : MKTime) :
    truncMKTime m h (truncMKTime m h tmk) = truncMKTime m h tmk := by
  simp only [truncMKTime, truncKTime, List.trunc]
  exact take_map_trunc_idem m h tmk

/-- extMKTime is idempotent under truncation -/
theorem extMKTime_trunc (m h : Nat) (l : Label) (tk : KTime) (tmk : MKTime) :
    extMKTime m h l (truncKTime m tk) (truncMKTime m h tmk) = extMKTime m h l tk tmk := by
  simp only [extMKTime, truncMKTime, truncKTime, List.trunc, List.map_cons,
             List.take_take, Nat.min_self, List.map_take]
  rw [list_map_idem (mktime_map_idem m)]
  exact (take_cons_take h _ _).symm

/-- extMKTimeApp is idempotent under truncation -/
theorem extMKTimeApp_trunc (m h : Nat) (l : Label) (tk : KTime) (tmk : MKTime) :
    extMKTimeApp m h l (truncKTime m tk) (truncMKTime m h tmk) = extMKTimeApp m h l tk tmk := by
  -- Use extMKTime_trunc's proof strategy but adapted for extMKTimeApp
  -- extMKTimeApp m h l (truncKTime m tk) (truncMKTime m h tmk) = extMKTimeApp m h l tk tmk
  -- Both sides unfold to truncMKTime m h ((l, extKTime m l _) :: _)
  -- LHS has extKTime m l (truncKTime m tk) and truncMKTime m h tmk
  -- RHS has extKTime m l tk and tmk
  -- extKTime m l (truncKTime m tk) = truncKTime m (l :: truncKTime m tk) = truncKTime m (l :: tk) = extKTime m l tk
  -- by take_cons_take
  -- And truncMKTime m h (truncMKTime m h tmk) = truncMKTime m h tmk by truncMKTime_idem
  have h1 : extKTime m l (truncKTime m tk) = extKTime m l tk := by
    simp [extKTime, truncKTime, List.trunc, take_cons_take, List.take_take]
  have h2 : truncMKTime m h (truncMKTime m h tmk) = truncMKTime m h tmk := truncMKTime_idem m h tmk
  simp only [extMKTimeApp, h1]
  simp only [truncMKTime, truncKTime, List.trunc, List.map_cons]
  have h3 : List.map (fun x : Label × KTime => (x.1, List.take m x.2))
        (List.take h (List.map (fun x => (x.1, List.take m x.2)) tmk)) =
      List.take h (List.map (fun x => (x.1, List.take m x.2)) tmk) :=
    (by rw [List.map_take, list_map_idem (mktime_map_idem m)])
  rw [h3]; exact (take_cons_take h _ _).symm

/-- Concrete tmk_apply abstracts to extMKTimeApp -/
theorem truncMKTime_app (m h : Nat) (l : Label) (tk : KTime) (tmk : MKTime) :
    truncMKTime m h ((l, l :: tk) :: tmk) = extMKTimeApp m h l tk tmk := by
  simp only [extMKTimeApp, extKTime, truncMKTime, truncKTime, List.trunc, List.map_cons]
  -- Goal: take h ((l, take m (l :: tk)) :: map f tmk) = take h ((l, take m (take m (l :: tk))) :: map f tmk)
  -- Just need take m (l :: tk) = take m (take m (l :: tk)) by take_take
  congr 2; simp [List.take_take]

/-- absTime components: tk and tmk of absTime -/
@[simp] theorem absTKAddr_frame_content (m h : Nat) (a : TKAddr) :
    (absTKAddr m h a).frame.content = absTFrameContent m h a.frame.content := rfl

@[simp] theorem absTKAddr_frame_time_tk (m h : Nat) (a : TKAddr) :
    (absTKAddr m h a).frame.time.tk = truncKTime m a.frame.time.tk := rfl

@[simp] theorem absTKAddr_frame_time_tmk (m h : Nat) (a : TKAddr) :
    (absTKAddr m h a).frame.time.tmk = truncMKTime m h a.frame.time.tmk := rfl

@[simp] theorem absTKAddr_frame_label (m h : Nat) (a : TKAddr) :
    (absTKAddr m h a).frame.label = a.frame.label := rfl

/-- truncMKTime on (l, tk) :: tmk equals extMKTime (for apply_restore_handle) -/
theorem truncMKTime_restore (m h : Nat) (l : Label) (tk : KTime) (tmk : MKTime) :
    truncMKTime m h ((l, tk) :: tmk) = extMKTime m h l tk tmk := by
  simp only [extMKTime, truncMKTime, truncKTime, List.trunc, List.map_cons,
             List.take_take, Nat.min_self]

@[simp] theorem absTime_tk (m h : Nat) (t : Time) : (absTime m h t).tk = truncKTime m t.tk := rfl
@[simp] theorem absTime_tmk (m h : Nat) (t : Time) : (absTime m h t).tmk = truncMKTime m h t.tmk := rfl

/-- Store abstraction is monotonic under extension:
    if α(σ) ⊑ σ_a and σ' = σ[a ↦ s], then α(σ') ⊑ σ_a ⊔ [α(a) ↦ {α(s)}] -/
theorem storeAbstracts_extend (m h : Nat) (σ : TStore) (σ_a : AStore)
    (a : TAddr) (s : TStorable)
    (h_abs : storeAbstracts m h σ σ_a) :
    storeAbstracts m h (σ.extend a s) (σ_a.update (absTAddr m h a) (absTStorable m h s)) := by
  intro â x h_mem
  obtain ⟨a_c, s_c, h_lookup, h_addr, h_val⟩ := h_mem
  subst h_val; subst h_addr
  simp only [AStore.update]
  by_cases heq : a_c = a
  · -- a_c = a: new entry
    subst heq; simp [TStore.extend] at h_lookup; subst h_lookup
    rw [if_pos rfl]; exact Set.mem_union_right _ rfl
  · -- a_c ≠ a: old entry
    have h_old : σ a_c = some s_c := by
      unfold TStore.extend at h_lookup; rw [if_neg heq] at h_lookup; exact h_lookup
    have : absTStorable m h s_c ∈ absStore m h σ (absTAddr m h a_c) :=
      ⟨a_c, s_c, h_old, rfl, rfl⟩
    have h_in_old := h_abs _ this
    by_cases hâ : absTAddr m h a_c = absTAddr m h a
    · rw [if_pos hâ]; rw [hâ] at h_in_old; exact Set.mem_union_left _ h_in_old
    · rw [if_neg hâ]; exact h_in_old

/-- Non-deterministic lookup is sound: if σ(a) = some s and α(σ) ⊑ σ_a,
    then α(s) ∈ σ_a(α(a)) -/
theorem absStore_lookup (m h : Nat) (σ : TStore) (σ_a : AStore)
    (a : TAddr) (s : TStorable)
    (h_abs : storeAbstracts m h σ σ_a)
    (h_lookup : σ a = some s) :
    absTStorable m h s ∈ σ_a (absTAddr m h a) :=
  h_abs _ ⟨a, s, h_lookup, rfl, rfl⟩

/-- Denotable lookup from storable lookup -/
theorem absStore_lookup_den (m h : Nat) (σ : TStore) (σ_a : AStore)
    (a : TVAddr) (d : TDenotable)
    (h_abs : storeAbstracts m h σ σ_a)
    (h_lookup : σ (.val a) = some (.denotable d)) :
    .denotable (absTDenotable m h d) ∈ σ_a (.val (absTVAddr m h a)) := by
  have := absStore_lookup m h σ σ_a (.val a) (.denotable d) h_abs h_lookup
  simp only [absTAddr, absTStorable] at this
  exact this

/-- absTFrameContent on letFrame unfolds -/
@[simp] theorem absTFrameContent_letFrame (m h : Nat) (clo : TClosure) :
    absTFrameContent m h (.letFrame clo) =
      .letFrame ⟨clo.params, clo.body, absTEnv m h clo.env, clo.params_nodup⟩ := rfl

/-- absTFrameContent on handlerFrame unfolds -/
@[simp] theorem absTFrameContent_handlerFrame (m h : Nat) (hdl : Handler) (ρ : TEnv) :
    absTFrameContent m h (.handlerFrame hdl ρ) = .handlerFrame hdl (absTEnv m h ρ) := rfl

/-- absTKAddr unfolds structurally -/
@[simp] theorem absTKAddr_mk (m h : Nat) (ψ : TimedFrame) (op : OpName) :
    absTKAddr m h ⟨ψ, op⟩ = ⟨absTimedFrame m h ψ, op⟩ := rfl

/-- absTimedFrame unfolds structurally -/
@[simp] theorem absTimedFrame_mk (m h : Nat) (fc : TFrameContent) (t : Time) (l : Label) :
    absTimedFrame m h ⟨fc, t, l⟩ = ⟨absTFrameContent m h fc, absTime m h t, l⟩ := rfl

/-- absTAddr on kont addresses unfolds structurally -/
@[simp] theorem absTAddr_kont (m h : Nat) (a : TKAddr) :
    absTAddr m h (.kont a) = .kont (absTKAddr m h a) := rfl

/-- absTStorable on kontLink unfolds structurally -/
@[simp] theorem absTStorable_kontLink (m h : Nat) (next : Option TKAddr) :
    absTStorable m h (.kontLink next) = .kontLink (next.map (absTKAddr m h)) := rfl

/-- Kont lookup abstraction -/
theorem absStore_kont_lookup (m h : Nat) (σ : TStore) (σ_a : AStore)
    (a : TKAddr) (next : Option TKAddr)
    (h_abs : storeAbstracts m h σ σ_a)
    (h_lookup : σ (.kont a) = some (.kontLink next)) :
    .kontLink (next.map (absTKAddr m h)) ∈ σ_a (.kont (absTKAddr m h a)) := by
  have := absStore_lookup m h σ σ_a (.kont a) (.kontLink next) h_abs h_lookup
  simp only [absTAddr, absTStorable, absTKAddr] at this
  exact this

/-- Atomic evaluation correspondence: if evalTAtomic returns d with α(σ) ⊑ σ_a,
    then α(d) ∈ evalAbsAtomic with abstracted env/store -/
theorem abs_evalTAtomic (m h : Nat) (ae : AExp) (ρ : TEnv) (σ : TStore) (σ_a : AStore)
    (d : TDenotable)
    (h_eval : evalTAtomic ae ρ σ = some d)
    (h_abs : storeAbstracts m h σ σ_a) :
    absTDenotable m h d ∈ evalAbsAtomic ae (absTEnv m h ρ) σ_a := by
  cases ae with
  | var x =>
    simp only [evalTAtomic] at h_eval
    cases h_ρ : Finmap.lookup x ρ with
    | none => simp [h_ρ] at h_eval
    | some a =>
      simp [h_ρ] at h_eval
      cases h_σ : σ (.val a) with
      | none => simp [h_σ] at h_eval
      | some s =>
        simp [h_σ] at h_eval
        cases s with
        | denotable d' =>
          simp at h_eval; subst h_eval
          simp only [evalAbsAtomic]
          rw [absTEnv_lookup]; rw [h_ρ]; simp
          -- Goal: absTDenotable m h d' ∈ { d | .denotable d ∈ σ_a (.val (absTVAddr m h a)) }
          show .denotable (absTDenotable m h d') ∈ σ_a (.val (absTVAddr m h a))
          exact absStore_lookup_den m h σ σ_a a d' h_abs h_σ
        | kontLink => simp at h_eval
  | lam xs body =>
    simp only [evalTAtomic] at h_eval
    split at h_eval
    · rename_i h_nd; injection h_eval with h_eval; subst h_eval
      simp only [evalAbsAtomic, absTDenotable, h_nd, dite_true]
      exact Set.mem_singleton _
    · simp at h_eval
  | con c =>
    simp only [evalTAtomic] at h_eval
    injection h_eval with h_eval; subst h_eval
    simp [evalAbsAtomic, absTDenotable]
  | succE x =>
    simp only [evalTAtomic] at h_eval
    cases h_ρ : Finmap.lookup x ρ with
    | none => simp [h_ρ] at h_eval
    | some a =>
      simp [h_ρ] at h_eval
      cases h_σ : σ (.val a) with
      | none => simp [h_σ] at h_eval
      | some s =>
        simp [h_σ] at h_eval
        cases s with
        | denotable _ =>
          simp at h_eval; subst h_eval
          simp only [evalAbsAtomic, absTDenotable]
          rw [absTEnv_lookup]; simp [h_ρ]
          exact Set.nonempty_of_mem (absStore_lookup m h σ σ_a (.val a) _ h_abs h_σ)
        | kontLink => simp at h_eval

/-! ## Abstract Soundness Theorem

  If (e, ρ, σ, t) ⇓et (v, σ') and α(σ) ⊑ σ_a,
  then (e, α(ρ), σ_a, α(t)) ⇓ea (v̂, σ_a')
  with α(v) ∈ v̂ and α(σ') ⊑ σ_a'.

  Proved by mutual induction on the naive timestamped derivation.
-/

theorem abstract_soundness (m h n : Nat) :
    -- P_exp
    (∀ (e : Exp) (ρ : TEnv) (σ : TStore) (t : Time) (v : TValue) (σ' : TStore),
       TEvalExpN n e ρ σ t v σ' →
       ∀ (σ_a : AStore), storeAbstracts m h σ σ_a →
       ∃ σ_a', AbsEvalExp m h e (absTEnv m h ρ) σ_a (absTime m h t)
                (absTValue m h v) σ_a' ∧
              storeAbstracts m h σ' σ_a') ∧
    -- P_cexp
    (∀ (ce : CExp) (ρ : TEnv) (σ : TStore) (t : Time) (l : Label) (v : TValue) (σ' : TStore),
       TEvalCExpN n ce ρ σ t l v σ' →
       ∀ (σ_a : AStore), storeAbstracts m h σ σ_a →
       ∃ σ_a', AbsEvalCExp m h ce (absTEnv m h ρ) σ_a (absTime m h t) l
                (absTValue m h v) σ_a' ∧
              storeAbstracts m h σ' σ_a') ∧
    -- P_continue
    (∀ (l : Label) (fc : TFrameContent) (t : Time) (v : TValue) (σ : TStore)
        (v' : TValue) (σ' : TStore),
       TContinueFrameN n l fc t v σ v' σ' →
       ∀ (σ_a : AStore), storeAbstracts m h σ σ_a →
       ∃ σ_a', AbsContinueFrame m h (absTFrameContent m h fc) (absTValue m h v) σ_a (absTime m h t)
                (absTValue m h v') σ_a' ∧
              storeAbstracts m h σ' σ_a') ∧
    -- P_handle
    (∀ (l : Label) (hdl : Handler) (ρ : TEnv) (v : TValue) (σ : TStore)
        (t : Time) (v' : TValue) (σ' : TStore),
       THandleValueN n l hdl ρ v σ t v' σ' →
       ∀ (σ_a : AStore), storeAbstracts m h σ σ_a →
       ∃ σ_a', AbsHandleValue m h l hdl (absTEnv m h ρ) (absTValue m h v) σ_a (absTime m h t)
                (absTValue m h v') σ_a' ∧
              storeAbstracts m h σ' σ_a') ∧
    -- P_apply
    (∀ (a_κ : Option TKAddr) (d : TDenotable) (σ : TStore)
        (tmk : MKTime) (v : TValue) (σ' : TStore),
       TApplyKontN n a_κ d σ tmk v σ' →
       ∀ (σ_a : AStore), storeAbstracts m h σ σ_a →
       ∃ σ_a', AbsApplyKont m h (a_κ.map (absTKAddr m h)) (absTDenotable m h d) σ_a
                (truncMKTime m h tmk) (absTValue m h v) σ_a' ∧
              storeAbstracts m h σ' σ_a') := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  -- P_exp
  · intro e ρ σ t v σ' h_eval σ_a h_abs
    cases h_eval with
    | eval_let h_ce h_cont =>
      obtain ⟨σ_a₁, h_abs_ce, h_abs₁⟩ := (ih _ (by omega)).2.1 _ _ _ _ _ _ _ h_ce σ_a h_abs
      obtain ⟨σ_a₂, h_abs_cont, h_abs₂⟩ := (ih _ (by omega)).2.2.1 _ _ _ _ _ _ _ h_cont σ_a₁ h_abs₁
      exact ⟨σ_a₂, .eval_let h_abs_ce h_abs_cont, h_abs₂⟩
    | eval_tail h_ce =>
      obtain ⟨σ_a', h_abs_ce, h_abs'⟩ := (ih _ (by omega)).2.1 _ _ _ _ _ _ _ h_ce σ_a h_abs
      exact ⟨σ_a', .eval_tail h_abs_ce, h_abs'⟩
  -- P_cexp
  · intro ce ρ σ t l v σ' h_eval σ_a h_abs
    cases h_eval with
    | eval_atomic h_ae =>
      exact ⟨σ_a, .eval_atomic (abs_evalTAtomic m h _ _ _ σ_a _ h_ae h_abs), h_abs⟩
    | eval_funApp_clos h_f h_len h_args h_tnew h_σnew h_ρnew h_body =>
      subst h_tnew; subst h_σnew; subst h_ρnew
      rename_i xs e_body ρ_lam _h_nd aes ds n_body
      -- foldl store abstraction: storeAbstracts preserved through zip extend
      have h_foldl_abs : storeAbstracts m h
          ((xs.zip ds).foldl (fun s (p : Var × TDenotable) =>
            s.extend (.val ⟨p.1, ⟨l :: t.tk, t.tmk⟩⟩) (.denotable p.2)) σ)
          ((xs.zip ds).foldl (fun s (p : Var × TDenotable) =>
            s.update (.val ⟨p.1, absTime m h ⟨l :: t.tk, t.tmk⟩⟩) (.denotable (absTDenotable m h p.2))) σ_a) := by
        suffices ∀ (pairs : List (Var × TDenotable)) (σ₀ : TStore) (σ_a₀ : AStore),
            storeAbstracts m h σ₀ σ_a₀ →
            storeAbstracts m h
              (pairs.foldl (fun s p => s.extend (.val ⟨p.1, ⟨l :: t.tk, t.tmk⟩⟩) (.denotable p.2)) σ₀)
              (pairs.foldl (fun s p => s.update (.val ⟨p.1, absTime m h ⟨l :: t.tk, t.tmk⟩⟩)
                (.denotable (absTDenotable m h p.2))) σ_a₀) from
          this (xs.zip ds) σ σ_a h_abs
        intro pairs; induction pairs with
        | nil => exact fun _ _ h => h
        | cons p tl ih => intro σ₀ σ_a₀ h₀; simp only [List.foldl_cons]; exact ih _ _ (storeAbstracts_extend m h σ₀ σ_a₀ _ _ h₀)
      -- env foldl abstraction
      have h_foldl_env : absTEnv m h (xs.foldl (fun r x => r.extend x ⟨x, ⟨l :: t.tk, t.tmk⟩⟩) ρ_lam) =
          xs.foldl (fun r x => r.extend x ⟨x, absTime m h ⟨l :: t.tk, t.tmk⟩⟩) (absTEnv m h ρ_lam) := by
        suffices ∀ (vars : List Var) (ρ₀ : TEnv),
            absTEnv m h (vars.foldl (fun r x => r.extend x ⟨x, ⟨l :: t.tk, t.tmk⟩⟩) ρ₀) =
            vars.foldl (fun r x => r.extend x ⟨x, absTime m h ⟨l :: t.tk, t.tmk⟩⟩) (absTEnv m h ρ₀) from
          this xs ρ_lam
        intro vars; induction vars with
        | nil => exact fun _ => rfl
        | cons x tl ih =>
          intro ρ₀; simp only [List.foldl_cons]
          rw [ih (ρ₀.extend x ⟨x, _⟩), absTEnv_extend]; rfl
      -- Forall₂ for abstract args
      have h_args_abs : List.Forall₂ (fun ae d => d ∈ evalAbsAtomic ae (absTEnv m h ρ) σ_a) aes
          (ds.map (absTDenotable m h)) := by
        have : ∀ (aes' : List AExp) (ds' : List TDenotable),
            List.Forall₂ (fun ae d => evalTAtomic ae ρ σ = some d) aes' ds' →
            List.Forall₂ (fun ae d => d ∈ evalAbsAtomic ae (absTEnv m h ρ) σ_a) aes'
              (ds'.map (absTDenotable m h)) := by
          intro aes' ds' hf; induction hf with
          | nil => exact .nil
          | cons h_hd _ ih_f2 => exact .cons (abs_evalTAtomic m h _ _ _ σ_a _ h_hd h_abs) ih_f2
        exact this aes ds h_args
      -- IH on body
      obtain ⟨σ_a', h_abs_body, h_abs'⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ h_body _ h_foldl_abs
      rw [h_foldl_env, absTime_extKTime] at h_abs_body
      refine ⟨σ_a', ?_, h_abs'⟩
      -- Align: foldl over (xs.zip ds) with absTDenotable in lambda
      -- vs foldl over (xs.zip (ds.map absTDenotable)) without extra map
      have h_store_eq : ∀ (σ₀ : AStore),
          (xs.zip (ds.map (absTDenotable m h))).foldl
          (fun s (p : Var × TDenotable) => s.update (TAddr.val ⟨p.1, ⟨extKTime m l (truncKTime m t.tk), truncMKTime m h t.tmk⟩⟩) (TStorable.denotable p.2)) σ₀ =
          (xs.zip ds).foldl
          (fun s (p : Var × TDenotable) => s.update (TAddr.val ⟨p.1, ⟨extKTime m l (truncKTime m t.tk), truncMKTime m h t.tmk⟩⟩) (TStorable.denotable (absTDenotable m h p.2))) σ₀ := by
        intro σ₀
        rw [List.zip_map_right, List.foldl_map]
        simp [Prod.map, id]
      rw [← h_store_eq] at h_abs_body
      exact AbsEvalCExp.eval_funApp_clos
        (abs_evalTAtomic m h _ _ _ σ_a _ h_f h_abs)
        h_len h_args_abs rfl rfl rfl h_abs_body
    | eval_opApp h_lookup =>
      refine ⟨σ_a, ?_, h_abs⟩
      have h_abs_l : ∀ x a, Finmap.lookup x ρ = some a →
          Finmap.lookup x (absTEnv m h ρ) = some (absTVAddr m h a) := by
        intro x a hxa; rw [absTEnv_lookup]; rw [hxa]; simp
      exact .eval_opApp (h_abs_l _ _ h_lookup)
    | eval_funApp_kont h_f h_ae h_tmk h_apply h_thandle h_handle =>
      subst h_tmk; subst h_thandle
      obtain ⟨σ_a₁, h_abs_apply, h_abs₁⟩ := (ih _ (by omega)).2.2.2.2 _ _ _ _ _ _ h_apply σ_a h_abs
      obtain ⟨σ_a₂, h_abs_handle, h_abs₂⟩ := (ih _ (by omega)).2.2.2.1 _ _ _ _ _ _ _ _ h_handle σ_a₁ h_abs₁
      refine ⟨σ_a₂, ?_, h_abs₂⟩
      rw [truncMKTime_app] at h_abs_apply
      rw [absTime_extKTime] at h_abs_handle
      exact AbsEvalCExp.eval_funApp_kont
        (abs_evalTAtomic m h _ _ _ σ_a _ h_f h_abs)
        (abs_evalTAtomic m h _ _ _ σ_a _ h_ae h_abs)
        (extMKTimeApp_trunc m h l t.tk t.tmk ▸ h_abs_apply)
        h_abs_handle
    | eval_fun h_av h_nd h_vf h_σ' =>
      subst h_av; subst h_vf; subst h_σ'
      refine ⟨_, ?_, storeAbstracts_extend m h σ σ_a _ _ h_abs⟩
      simp only [absTValue, absTDenotable, absTStorable, absTAddr, absTVAddr]
      rw [absTEnv_extend]
      exact .eval_fun rfl h_nd rfl rfl
    | eval_match h_ae h_d h_br h_xs h_body =>
      subst h_d; subst h_xs
      obtain ⟨σ_a', h_abs_body, h_abs'⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ h_body σ_a h_abs
      exact ⟨σ_a', .eval_match (abs_evalTAtomic m h _ _ _ σ_a _ h_ae h_abs) rfl h_br rfl h_abs_body, h_abs'⟩
    | eval_match_succ h_ae h_findBr h_σ_inner h_xs h_afresh h_σnew h_ρnew h_body =>
      subst h_xs; subst h_afresh; subst h_σnew; subst h_ρnew
      -- Simplify the foldl on singleton list
      simp only [List.zip_cons_cons, List.zip_nil_right, List.foldl_cons, List.foldl_nil] at h_body ⊢
      obtain ⟨σ_a', h_abs_body, h_abs'⟩ :=
        (ih _ (by omega)).1 _ _ _ _ _ _ h_body _
          (storeAbstracts_extend m h σ σ_a (.val (TVAddr.mk _ _)) _ h_abs)
      rw [absTEnv_extend] at h_abs_body
      refine ⟨σ_a', ?_, h_abs'⟩
      exact .eval_match_succ (abs_evalTAtomic m h _ _ _ σ_a _ h_ae h_abs)
        rfl h_findBr (absStore_lookup_den m h σ σ_a _ _ h_abs h_σ_inner) rfl rfl rfl h_abs_body
    | eval_handler h_tbody h_body h_handle =>
      subst h_tbody
      obtain ⟨σ_a₁, h_abs_body, h_abs₁⟩ := (ih _ (by omega)).1 _ _ _ _ _ _ h_body σ_a h_abs
      obtain ⟨σ_a₂, h_abs_handle, h_abs₂⟩ := (ih _ (by omega)).2.2.2.1 _ _ _ _ _ _ _ _ h_handle σ_a₁ h_abs₁
      refine ⟨σ_a₂, ?_, h_abs₂⟩
      rw [absTime_extMKTime] at h_abs_body
      exact .eval_handler (extMKTime_trunc m h _ t.tk t.tmk ▸ h_abs_body) h_abs_handle
  -- P_continue
  · intro l fc t v σ v' σ' h_eval σ_a h_abs
    cases h_eval with
    | continue_let h_a h_body =>
      subst h_a
      obtain ⟨σ_a', h_abs_body, h_abs'⟩ : ∃ σ_a', _ ∧ storeAbstracts m h _ σ_a' :=
        (ih _ (by omega)).1 _ _ _ _ _ _ h_body _ (storeAbstracts_extend m h σ σ_a
          (.val (TVAddr.mk _ _)) (.denotable _) h_abs)
      rw [absTEnv_extend] at h_abs_body
      exact ⟨σ_a', .continue_let rfl h_abs_body, h_abs'⟩
    | continue_op h_ψ h_aκ h_σ' =>
      subst h_ψ; subst h_aκ; subst h_σ'
      simp only [absTValue, absTFrameContent_letFrame]
      exact ⟨_, .continue_op rfl rfl rfl, storeAbstracts_extend m h σ σ_a _ _ h_abs⟩
  -- P_handle
  · intro l hdl ρ v σ t v' σ' h_eval σ_a h_abs
    cases h_eval with
    | handle_return h_ret h_av h_body =>
      subst h_av
      obtain ⟨σ_a', h_abs_body, h_abs'⟩ : ∃ σ_a', _ ∧ storeAbstracts m h _ σ_a' :=
        (ih _ (by omega)).1 _ _ _ _ _ _ h_body _
          (storeAbstracts_extend m h σ σ_a (.val (TVAddr.mk _ _)) (.denotable _) h_abs)
      rw [absTEnv_extend] at h_abs_body
      exact ⟨σ_a', .handle_return h_ret rfl rfl h_abs_body, h_abs'⟩
    | handle_op h_findop h_ax h_ar h_asv h_lookup h_dkont h_σop h_body_eval =>
      subst h_ax; subst h_ar; subst h_asv; subst h_dkont; subst h_σop
      obtain ⟨σ_a', h_abs_body, h_abs'⟩ :=
        (ih _ (by omega)).1 _ _ _ _ _ _ h_body_eval _
          (storeAbstracts_extend m h _ _
            (.val (TVAddr.mk "resume" t)) (.denotable (.kontClosure hdl ρ _))
            (storeAbstracts_extend m h σ σ_a _ (.denotable _) h_abs))
      rw [absTEnv_extend, absTEnv_extend] at h_abs_body
      refine ⟨σ_a', ?_, h_abs'⟩
      exact .handle_op h_findop rfl h_abs_body
    | handle_capture_op h_hasop h_ψ h_aκ h_σ' =>
      subst h_ψ; subst h_aκ; subst h_σ'
      simp only [absTValue]
      exact ⟨_, .handle_capture_op h_hasop rfl rfl rfl, storeAbstracts_extend m h σ σ_a _ _ h_abs⟩
  -- P_apply
  · intro a_κ d σ tmk v σ' h_eval σ_a h_abs
    cases h_eval with
    | apply_continue =>
      exact ⟨σ_a, .apply_continue, h_abs⟩
    | apply_restore h_lookup h_clo h_apply h_t_restored h_cont =>
      rename_i clo a_κ
      obtain ⟨σ_a₁, h_abs_apply, h_abs₁⟩ := (ih _ (by omega)).2.2.2.2 _ _ _ _ _ _ h_apply σ_a h_abs
      rw [h_t_restored] at h_cont
      obtain ⟨σ_a₂, h_abs_cont, h_abs₂⟩ := (ih _ (by omega)).2.2.1 _ _ _ _ _ _ _ h_cont σ_a₁ h_abs₁
      have h_kont_in := absStore_kont_lookup m h σ σ_a _ _ h_abs h_lookup
      refine ⟨σ_a₂, ?_, h_abs₂⟩
      have h_fc : (absTKAddr m h a_κ).frame.content = absTFrameContent m h (.letFrame clo) := by
        simp [absTKAddr, absTimedFrame, h_clo]
      rw [← h_fc] at h_abs_cont
      exact .apply_restore h_kont_in h_abs_apply h_abs_cont
    | apply_restore_handle h_lookup h_content h_tmk' h_apply h_t_restored h_handle =>
      rename_i hdl_h ρ_h a_κ
      subst h_tmk'; rw [h_t_restored] at h_handle
      obtain ⟨σ_a₁, h_abs_apply, h_abs₁⟩ := (ih _ (by omega)).2.2.2.2 _ _ _ _ _ _ h_apply σ_a h_abs
      obtain ⟨σ_a₂, h_abs_handle, h_abs₂⟩ := (ih _ (by omega)).2.2.2.1 _ _ _ _ _ _ _ _ h_handle σ_a₁ h_abs₁
      have h_kont_in := absStore_kont_lookup m h σ σ_a _ _ h_abs h_lookup
      refine ⟨σ_a₂, ?_, h_abs₂⟩
      rw [truncMKTime_restore] at h_abs_apply
      rw [← extMKTime_trunc] at h_abs_apply
      have h_content' : (absTKAddr m h a_κ).frame.content = .handlerFrame hdl_h (absTEnv m h ρ_h) := by
        simp [absTKAddr, absTimedFrame, h_content]
      exact .apply_restore_handle h_kont_in h_content' h_abs_apply h_abs_handle

end DMCFA
