/-
  Correspondence relations between untyped (Semantics.lean) and
  timestamped (TSemantics.lean) semantic domains.

  The simulation maps each untyped VAddr to a TVAddr via an injective
  witness function α. All relations are parameterized by α and the
  timestamped store tσ (needed for continuation correspondence).
-/

import DMCFA.Components
import DMCFA.TimestampedComponents

namespace DMCFA

/-! ## Environment Correspondence -/

/-- Environments correspond: every binding in ρ has a corresponding binding in tρ -/
def EnvCorr (α : VAddr → TVAddr) (ρ : Env) (tρ : TEnv) : Prop :=
  ∀ x a, ρ x = some a → Finmap.lookup x tρ = some (α a)

/-- Reverse direction: every timestamped env entry comes from a concrete one -/
def EnvReflects (α : VAddr → TVAddr) (ρ : Env) (tρ : TEnv) : Prop :=
  ∀ x ta, Finmap.lookup x tρ = some ta → ∃ a, ρ x = some a ∧ α a = ta

/-! ## Closure Correspondence -/

/-- Closure correspondence (bidirectional env) -/
structure ClosureCorr (α : VAddr → TVAddr) (clo : Closure) (tclo : TClosure) : Prop where
  params_eq : clo.params = tclo.params
  body_eq : clo.body = tclo.body
  env_corr : EnvCorr α clo.env tclo.env
  env_reflects : EnvReflects α clo.env tclo.env

/-! ## Frame Correspondence -/

/-- Frame content correspondence -/
inductive FrameCorr (α : VAddr → TVAddr) : Frame → TFrameContent → Prop where
  | letFrame : ClosureCorr α clo tclo →
      FrameCorr α (.letFrame clo) (.letFrame tclo)
  | handlerFrame : EnvCorr α ρ tρ → EnvReflects α ρ tρ →
      FrameCorr α (.handlerFrame h ρ) (.handlerFrame h tρ)

/-! ## Continuation Correspondence -/

/-- Continuation correspondence: Kont (stack) ↔ Option TKAddr (linked list in tσ) -/
inductive KontCorr (α : VAddr → TVAddr) (tσ : TStore) : Kont → Option TKAddr → Prop where
  | nil : KontCorr α tσ [] none
  | cons :
      tσ (.kont a_κ) = some (.kontLink a_next) →
      FrameCorr α frame a_κ.frame.content →
      KontCorr α tσ rest a_next →
      KontCorr α tσ (frame :: rest) (some a_κ)

/-! ## Denotable Correspondence -/

/-- Denotable correspondence (parameterized by tσ for kontClosure's KontCorr) -/
inductive DenotableCorr (α : VAddr → TVAddr) (tσ : TStore) :
    Denotable → TDenotable → Prop where
  | closure : ClosureCorr α clo tclo →
      DenotableCorr α tσ (.closure clo) (.closure tclo)
  | kontClosure :
      EnvCorr α ρ tρ → EnvReflects α ρ tρ →
      KontCorr α tσ κ ta_κ →
      DenotableCorr α tσ (.kontClosure h ρ κ) (.kontClosure h tρ ta_κ)
  | conLabel : DenotableCorr α tσ (.conLabel c) (.conLabel c)
  | succVal : DenotableCorr α tσ (.succVal a) (.succVal (α a))

/-! ## Value Correspondence -/

/-- Value correspondence -/
inductive ValueCorr (α : VAddr → TVAddr) (tσ : TStore) :
    Value → TValue → Prop where
  | den : DenotableCorr α tσ d td →
      ValueCorr α tσ (.den d) (.den td)
  | suspended :
      as_v.length = tas_v.length →
      (∀ i (h1 : i < as_v.length) (h2 : i < tas_v.length),
        tas_v[i] = α (as_v[i])) →
      KontCorr α tσ κ ta_κ →
      ValueCorr α tσ (.suspended op as_v κ) (.suspended op tas_v ta_κ)

/-! ## Store Correspondence -/

/-- Store correspondence: val entries in untyped store correspond to val entries in tσ -/
def StoreCorr (α : VAddr → TVAddr) (tσ : TStore) (σ : Store) : Prop :=
  ∀ a d, σ a = some d →
    ∃ td, tσ (.val (α a)) = some (.denotable td) ∧ DenotableCorr α tσ d td

/-- Store reflects: every occupied val address in tσ is an α-image of a live untyped address.
    Together with StoreCorr, this makes α a bijection between Dom(σ) and val-Dom(tσ). -/
def StoreReflects (α : VAddr → TVAddr) (tσ : TStore) (σ : Store) : Prop :=
  ∀ ta, tσ (.val ta) ≠ none → ∃ a, σ a ≠ none ∧ α a = ta

/-- From StoreReflects: if no live address maps to ta, then ta is fresh in tσ -/
theorem StoreReflects.val_fresh {α : VAddr → TVAddr} {tσ : TStore} {σ : Store}
    (h : StoreReflects α tσ σ) {ta : TVAddr}
    (h_no_preimage : ∀ a, σ a ≠ none → α a ≠ ta) :
    tσ (.val ta) = none := by
  by_contra h_ne
  push_neg at h_ne
  obtain ⟨a, ha, hα⟩ := h ta h_ne
  exact h_no_preimage a ha hα

/-- StoreReflects preserved when extending both stores with corresponding entries -/
theorem StoreReflects.extend_val {α : VAddr → TVAddr} {tσ : TStore} {σ : Store}
    (h : StoreReflects α tσ σ) (a : VAddr) (s : TStorable) (d : Denotable) :
    StoreReflects (fun a' => if a' = a then α a else α a')
      (tσ.extend (.val (α a)) s) (σ.extend a d) := by
  intro ta h_ne
  simp only [TStore.extend] at h_ne
  split at h_ne
  · rename_i heq
    exact ⟨a, by simp [Store.extend], by simp [TAddr.val.inj heq]⟩
  · rename_i hne
    obtain ⟨a', ha', hα⟩ := h ta h_ne
    refine ⟨a', ?_, ?_⟩
    · simp [Store.extend]; split <;> [exact nofun; exact ha']
    · dsimp only; split
      · rename_i heq; subst heq; exfalso; apply hne; rw [hα]
      · exact hα

/-! ## Extension of α -/

/-- α' extends α: agrees on all addresses in the old store's domain -/
def AlphaExtends (α α' : VAddr → TVAddr) (σ : Store) : Prop :=
  ∀ a, σ a ≠ none → α' a = α a

/-! ## Basic lemmas -/

section Lemmas

variable {α : VAddr → TVAddr}

theorem EnvCorr.extend (h : EnvCorr α ρ tρ) (x : Var) (a : VAddr) :
    EnvCorr α (ρ.extend x a) (tρ.insert x (α a)) := by
  intro y b hy; simp only [Env.extend] at hy
  split at hy
  · injection hy with hy; subst_vars; simp
  · rename_i hne; rw [Finmap.lookup_insert_of_ne _ hne]; exact h _ _ hy

theorem EnvCorr.empty : EnvCorr α Env.empty TEnv.empty := by
  intro x a h; simp [Env.empty] at h

theorem EnvReflects.extend (h : EnvReflects α ρ tρ) (x : Var) (a : VAddr) :
    EnvReflects α (ρ.extend x a) (tρ.insert x (α a)) := by
  intro y ta hy
  by_cases heq : y = x
  · subst heq; simp at hy; subst hy; exact ⟨a, by simp [Env.extend], rfl⟩
  · rw [Finmap.lookup_insert_of_ne _ heq] at hy
    obtain ⟨a', ha', hα⟩ := h y ta hy
    exact ⟨a', by simp [Env.extend, heq]; exact ha', hα⟩

theorem EnvReflects.empty : EnvReflects α Env.empty TEnv.empty := by
  intro x ta h; simp [TEnv.empty] at h

theorem StoreCorr.empty : StoreCorr α TStore.empty Store.empty := by
  intro a d h; simp [Store.empty] at h

theorem StoreReflects.empty : StoreReflects α TStore.empty Store.empty := by
  intro ta h; simp [TStore.empty] at h

/-- EnvCorr transfers across α extension when all env addresses are in σ's domain -/
theorem EnvCorr.of_alpha_extends {α α' : VAddr → TVAddr} {ρ : Env} {tρ : TEnv} {σ : Store}
    (h : EnvCorr α ρ tρ) (h_ext : AlphaExtends α α' σ)
    (h_scope : ∀ x a, ρ x = some a → σ a ≠ none) :
    EnvCorr α' ρ tρ := by
  intro x a hρ
  have := h_ext a (h_scope x a hρ)
  rw [show α' a = α a from this]
  exact h x a hρ

/-- EnvReflects transfers across α extension when all env addresses are in σ's domain -/
theorem EnvReflects.of_alpha_extends {α α' : VAddr → TVAddr} {ρ : Env} {tρ : TEnv} {σ : Store}
    (h : EnvReflects α ρ tρ) (h_ext : AlphaExtends α α' σ)
    (h_scope : ∀ x a, ρ x = some a → σ a ≠ none) :
    EnvReflects α' ρ tρ := by
  intro x ta htρ
  obtain ⟨a, hρ, hα⟩ := h x ta htρ
  exact ⟨a, hρ, by rw [h_ext a (h_scope x a hρ)]; exact hα⟩

/-- All addresses in an environment are in the store (well-scopedness) -/
def EnvScoped (ρ : Env) (σ : Store) : Prop :=
  ∀ x a, ρ x = some a → σ a ≠ none

/-- A frame's environment addresses are all live in the store -/
def FrameScoped (f : Frame) (σ : Store) : Prop :=
  match f with
  | .letFrame clo => EnvScoped clo.env σ
  | .handlerFrame _ ρ => EnvScoped ρ σ

/-- All frames in a continuation have scoped environments -/
def KontScoped (κ : Kont) (σ : Store) : Prop :=
  ∀ f ∈ κ, FrameScoped f σ

/-- A denotable's transitive addresses are all live in the store -/
def DenotableScoped (d : Denotable) (σ : Store) : Prop :=
  match d with
  | .closure clo => EnvScoped clo.env σ
  | .kontClosure _ ρ κ => EnvScoped ρ σ ∧ KontScoped κ σ
  | .conLabel _ => True
  | .succVal a => σ a ≠ none

/-- A value's transitive addresses are all live in the store -/
def ValueScoped (v : Value) (σ : Store) : Prop :=
  match v with
  | .den d => DenotableScoped d σ
  | .suspended _ as_v κ => (∀ a ∈ as_v, σ a ≠ none) ∧ KontScoped κ σ

/-- All denotables in the store have scoped addresses (concrete store well-formedness) -/
def StoreScoped (σ : Store) : Prop :=
  ∀ a d, σ a = some d → DenotableScoped d σ

theorem EnvScoped.empty : EnvScoped Env.empty Store.empty := by
  intro x a h; simp [Env.empty] at h

theorem StoreScoped.empty : StoreScoped Store.empty := by
  intro a d h; simp [Store.empty] at h

theorem denotableScoped_mono {d : Denotable} {σ σ' : Store}
    (h : DenotableScoped d σ) (h_mono : ∀ a, σ a ≠ none → σ' a ≠ none) :
    DenotableScoped d σ' := by
  cases d with
  | closure clo => exact fun x a hxa => h_mono _ (h x a hxa)
  | kontClosure h_hdl ρ κ =>
    constructor
    · exact fun x a hxa => h_mono _ (h.1 x a hxa)
    · intro f hf
      have hfs := h.2 f hf
      cases f with
      | letFrame clo => exact fun x a hxa => h_mono _ (hfs x a hxa)
      | handlerFrame _ ρ' => exact fun x a hxa => h_mono _ (hfs x a hxa)
  | conLabel _ => trivial
  | succVal a => exact h_mono _ h

theorem storeScoped_extend {σ : Store} {a : VAddr} {d : Denotable}
    (h : StoreScoped σ) (h_new : DenotableScoped d (σ.extend a d)) :
    StoreScoped (σ.extend a d) := by
  intro a' d' hσ'
  simp only [Store.extend] at hσ'
  split at hσ'
  · injection hσ' with hσ'; subst hσ'; exact h_new
  · have h_mono : ∀ a'', σ a'' ≠ none → (σ.extend a d) a'' ≠ none := by
      intro a'' ha''
      simp [Store.extend]; split
      · exact nofun
      · exact ha''
    exact denotableScoped_mono (h a' d' hσ') h_mono

theorem envScoped_mono {ρ : Env} {σ σ' : Store}
    (h : EnvScoped ρ σ) (h_mono : ∀ a, σ a ≠ none → σ' a ≠ none) :
    EnvScoped ρ σ' :=
  fun x a hxa => h_mono _ (h x a hxa)

/-! ## Monotonicity: correspondence under store growth -/

/-- KontCorr is monotone in the store -/
theorem KontCorr.mono {α : VAddr → TVAddr} {tσ tσ' : TStore} {κ : Kont} {ta_κ : Option TKAddr}
    (h : KontCorr α tσ κ ta_κ) (hext : ∀ a, tσ a ≠ none → tσ' a = tσ a) :
    KontCorr α tσ' κ ta_κ := by
  induction h with
  | nil => exact KontCorr.nil
  | cons hlookup hframe _hrest ih =>
    refine KontCorr.cons ?_ hframe ih
    rw [hext _ (by rw [hlookup]; exact nofun)]
    exact hlookup

/-- DenotableCorr is monotone in the store -/
theorem DenotableCorr.mono {α : VAddr → TVAddr} {tσ tσ' : TStore} {d : Denotable} {td : TDenotable}
    (h : DenotableCorr α tσ d td) (hext : ∀ a, tσ a ≠ none → tσ' a = tσ a) :
    DenotableCorr α tσ' d td := by
  cases h with
  | closure hclo => exact DenotableCorr.closure hclo
  | kontClosure henv henvR hkont => exact DenotableCorr.kontClosure henv henvR (hkont.mono hext)
  | conLabel => exact DenotableCorr.conLabel
  | succVal => exact DenotableCorr.succVal

/-- ValueCorr is monotone in the store -/
theorem ValueCorr.mono {α : VAddr → TVAddr} {tσ tσ' : TStore} {v : Value} {tv : TValue}
    (h : ValueCorr α tσ v tv) (hext : ∀ a, tσ a ≠ none → tσ' a = tσ a) :
    ValueCorr α tσ' v tv := by
  cases h with
  | den hd => exact ValueCorr.den (hd.mono hext)
  | suspended hlen hmap hkont => exact ValueCorr.suspended hlen hmap (hkont.mono hext)

/-! ## Alpha+Store extension with scoping -/

/-- EnvCorr preserved under α change when env is scoped -/
theorem EnvCorr.of_alpha_scoped {α α' : VAddr → TVAddr} {ρ : Env} {tρ : TEnv}
    (h : EnvCorr α ρ tρ) {σ_c : Store}
    (h_ext_α : ∀ a, σ_c a ≠ none → α' a = α a)
    (h_scope : EnvScoped ρ σ_c) :
    EnvCorr α' ρ tρ := by
  intro x a hxa
  rw [h_ext_α a (h_scope x a hxa)]
  exact h x a hxa

/-- ClosureCorr preserved under α change when closure env is scoped -/
theorem ClosureCorr.of_alpha_scoped {α α' : VAddr → TVAddr} {clo : Closure} {tclo : TClosure}
    (h : ClosureCorr α clo tclo) {σ_c : Store}
    (h_ext_α : ∀ a, σ_c a ≠ none → α' a = α a)
    (h_scope : EnvScoped clo.env σ_c) :
    ClosureCorr α' clo tclo :=
  ⟨h.params_eq, h.body_eq, h.env_corr.of_alpha_scoped h_ext_α h_scope,
   h.env_reflects.of_alpha_extends h_ext_α h_scope⟩

/-- FrameCorr preserved under α change when frame env is scoped -/
theorem FrameCorr.of_alpha_scoped {α α' : VAddr → TVAddr} {f : Frame} {fc : TFrameContent}
    (h : FrameCorr α f fc) {σ_c : Store}
    (h_ext_α : ∀ a, σ_c a ≠ none → α' a = α a)
    (h_scope : FrameScoped f σ_c) :
    FrameCorr α' f fc := by
  cases h with
  | letFrame hclo => exact .letFrame (hclo.of_alpha_scoped h_ext_α h_scope)
  | handlerFrame henv henvR =>
    exact .handlerFrame (henv.of_alpha_scoped h_ext_α h_scope) (henvR.of_alpha_extends h_ext_α h_scope)

/-- KontCorr preserved under α+tσ change when kont is scoped -/
theorem KontCorr.of_alpha_tσ_scoped {α α' : VAddr → TVAddr} {tσ tσ' : TStore}
    {κ : Kont} {ta_κ : Option TKAddr}
    (h : KontCorr α tσ κ ta_κ) {σ_c : Store}
    (h_ext_α : ∀ a, σ_c a ≠ none → α' a = α a)
    (h_ext_tσ : ∀ a, tσ a ≠ none → tσ' a = tσ a)
    (h_scope : KontScoped κ σ_c) :
    KontCorr α' tσ' κ ta_κ := by
  induction h with
  | nil => exact .nil
  | cons hlookup hframe _hrest ih =>
    have h_head := h_scope _ (.head _)
    have h_tail : KontScoped _ σ_c := fun f hf => h_scope f (.tail _ hf)
    refine .cons ?_ (hframe.of_alpha_scoped h_ext_α h_head) (ih h_tail)
    rw [h_ext_tσ _ (by rw [hlookup]; exact nofun)]; exact hlookup

/-- KontCorr preserved when extending tσ with a fresh kont address -/
theorem KontCorr.extend_kont {α : VAddr → TVAddr} {tσ : TStore}
    {κ : Kont} {ta_κ : Option TKAddr}
    (h : KontCorr α tσ κ ta_κ)
    (a_new : TKAddr) (s : TStorable) (h_fresh : tσ (.kont a_new) = none) :
    KontCorr α (tσ.extend (.kont a_new) s) κ ta_κ := by
  induction h with
  | nil => exact .nil
  | cons hlookup hframe _hrest ih =>
    refine .cons ?_ hframe ih
    have hne : (TAddr.kont ‹_›) ≠ TAddr.kont a_new := by
      intro heq; cases heq; rw [hlookup] at h_fresh; exact absurd h_fresh nofun
    rw [TStore.extend_ne _ _ _ _ hne]; exact hlookup

/-- StoreReflects preserved when extending tσ with a kont address -/
theorem StoreReflects.extend_kont {α : VAddr → TVAddr} {tσ : TStore} {σ : Store}
    (h : StoreReflects α tσ σ)
    (a_new : TKAddr) (s : TStorable) :
    StoreReflects α (tσ.extend (.kont a_new) s) σ := by
  intro ta' h_ne
  have hne : TAddr.val ta' ≠ TAddr.kont a_new := by intro h; cases h
  have h_old : tσ (.val ta') ≠ none := by
    intro h; exact h_ne (by rw [TStore.extend_ne _ _ _ _ hne]; exact h)
  exact h ta' h_old

/-- DenotableCorr transfers across α/tσ extension when d is scoped in σ -/
theorem DenotableCorr.of_alpha_extends_fresh
    {α α' : VAddr → TVAddr} {tσ tσ' : TStore} {σ : Store}
    {d : Denotable} {td : TDenotable}
    (h : DenotableCorr α tσ d td)
    (h_ext_α : ∀ a, σ a ≠ none → α' a = α a)
    (h_ext_tσ : ∀ a, tσ a ≠ none → tσ' a = tσ a)
    (h_scoped : DenotableScoped d σ) :
    DenotableCorr α' tσ' d td := by
  cases h with
  | closure hclo => exact .closure (hclo.of_alpha_scoped h_ext_α h_scoped)
  | kontClosure henv henvR hkont =>
    exact .kontClosure (henv.of_alpha_scoped h_ext_α h_scoped.1)
      (henvR.of_alpha_extends h_ext_α h_scoped.1)
      (hkont.of_alpha_tσ_scoped h_ext_α h_ext_tσ h_scoped.2)
  | conLabel => exact .conLabel
  | succVal =>
    have := h_ext_α _ h_scoped
    conv => rhs; rw [← this]
    exact .succVal

/-- DenotableCorr preserved when extending tσ with a kont address -/
theorem DenotableCorr.extend_kont {α : VAddr → TVAddr} {tσ : TStore} {σ : Store}
    {d : Denotable} {td : TDenotable}
    (h : DenotableCorr α tσ d td)
    (a_new : TKAddr) (s : TStorable) (h_fresh : tσ (.kont a_new) = none)
    (h_scoped : DenotableScoped d σ) :
    DenotableCorr α (tσ.extend (.kont a_new) s) d td := by
  have h_ext_tσ : ∀ a, tσ a ≠ none → (tσ.extend (.kont a_new) s) a = tσ a :=
    fun a ha => TStore.extend_ne _ _ _ _ (by intro heq; subst heq; exact absurd h_fresh ha)
  exact h.of_alpha_extends_fresh (fun _ _ => rfl) h_ext_tσ h_scoped

/-- StoreCorr preserved when extending tσ with a kont address -/
theorem StoreCorr.extend_kont {α : VAddr → TVAddr} {tσ : TStore} {σ : Store}
    (h : StoreCorr α tσ σ) (h_ss : StoreScoped σ)
    (a_new : TKAddr) (s : TStorable) (h_fresh : tσ (.kont a_new) = none) :
    StoreCorr α (tσ.extend (.kont a_new) s) σ := by
  intro a d' hσ'
  obtain ⟨td', htσ', hd⟩ := h a d' hσ'
  have hne : TAddr.val (α a) ≠ TAddr.kont a_new := by intro h; cases h
  exact ⟨td', by rw [TStore.extend_ne _ _ _ _ hne]; exact htσ',
         hd.extend_kont a_new s h_fresh (h_ss a d' hσ')⟩

/-- StoreScoped preserved when extending with a scoped denotable -/
theorem StoreScoped.extend_val {σ : Store} {a_v : VAddr} {d : Denotable}
    (h : StoreScoped σ) (h_d : DenotableScoped d (σ.extend a_v d)) :
    StoreScoped (σ.extend a_v d) := by
  intro a d' hσ'
  simp only [Store.extend] at hσ'
  split at hσ'
  · injection hσ' with hσ'; subst hσ'; exact h_d
  · exact denotableScoped_mono (h a d' hσ') (fun a' ha' => by
      simp [Store.extend]; split <;> [exact nofun; exact ha'])

/-- StoreCorr is monotone in the timestamped store (when it grows) -/
theorem StoreCorr.mono {α : VAddr → TVAddr} {tσ tσ' : TStore} {σ : Store}
    (h : StoreCorr α tσ σ) (hext : ∀ a, tσ a ≠ none → tσ' a = tσ a) :
    StoreCorr α tσ' σ := by
  intro a d hσ
  obtain ⟨td, htσ, hd⟩ := h a d hσ
  have hne : tσ (.val (α a)) ≠ none := by rw [htσ]; exact nofun
  exact ⟨td, by rw [hext _ hne, htσ], hd.mono hext⟩

/-- StoreCorr preserved when extending both stores correspondingly.
    Requires α to be injective on the store domain and the timestamped address to be fresh. -/
theorem StoreCorr.extend_val {α : VAddr → TVAddr} {tσ : TStore} {σ : Store}
    (h : StoreCorr α tσ σ)
    (a : VAddr) (d : Denotable) (td : TDenotable)
    (hd : DenotableCorr α (tσ.extend (.val (α a)) (.denotable td)) d td)
    (h_fresh : σ a = none)
    (h_inj : ∀ a', σ a' ≠ none → α a' ≠ α a)
    (h_tfresh : tσ (.val (α a)) = none) :
    StoreCorr α (tσ.extend (.val (α a)) (.denotable td)) (σ.extend a d) := by
  intro a' d' hσ'
  simp only [Store.extend] at hσ'
  split at hσ'
  · rename_i heq; subst heq; injection hσ' with hσ'; subst hσ'
    exact ⟨td, TStore.extend_same _ _ _, hd⟩
  · rename_i hne
    obtain ⟨td', htσ', hd'⟩ := h a' d' hσ'
    have hne' : TAddr.val (α a') ≠ TAddr.val (α a) := by
      intro heq; apply h_inj a' (by rw [hσ']; exact nofun)
      exact TAddr.val.inj heq
    have hext : ∀ addr, tσ addr ≠ none → (tσ.extend (.val (α a)) (.denotable td)) addr = tσ addr :=
      fun addr haddr => TStore.extend_ne _ _ _ _ (by
        intro heq; subst heq; exact absurd h_tfresh haddr)
    exact ⟨td', by rw [TStore.extend_ne _ _ _ _ hne']; exact htσ', hd'.mono hext⟩

/-- AlphaExtends is reflexive -/
theorem AlphaExtends.refl : AlphaExtends α α σ := by
  intro a _; rfl

/-- AlphaExtends is transitive (when σ ⊆ σ') -/
theorem AlphaExtends.trans {α α' α'' : VAddr → TVAddr} {σ σ' : Store}
    (h1 : AlphaExtends α α' σ)
    (h2 : AlphaExtends α' α'' σ')
    (h_ext : ∀ a, σ a ≠ none → σ' a ≠ none) :
    AlphaExtends α α'' σ := by
  intro a ha
  rw [h2 a (h_ext a ha), h1 a ha]

end Lemmas

end DMCFA
