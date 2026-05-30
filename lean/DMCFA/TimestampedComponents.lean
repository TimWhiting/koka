/-
  Timestamped Semantic Components for the concrete big-step machine.

  Timestamps distinguish allocations: each address is (variable, timestamp),
  making distinct dynamic allocations receive distinct addresses.
  Based on the timestamped-correctness-formal paper.
-/

import DMCFA.Syntax
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finmap

namespace DMCFA

/-! ## Timestamps -/

/-- Call-site trace (stack of labels) -/
abbrev KTime := List Label

/-- Meta-continuation trace (stack of delimiters) -/
abbrev MKTime := List (Label × KTime)

/-- Complete timestamp: call-stack trace + meta-continuation trace -/
structure Time where
  tk : KTime
  tmk : MKTime
  deriving DecidableEq, Repr

instance : Inhabited Time := ⟨⟨[], []⟩⟩

/-- Initial (empty) timestamp -/
def Time.empty : Time := ⟨[], []⟩

/-! ## Timestamped Addresses -/

/-- Timestamped value address: (variable_name, timestamp) -/
structure TVAddr where
  name : Var
  time : Time
  deriving DecidableEq, Repr

/-! ## Timestamped Environment -/

/-- Environment maps variables to timestamped value addresses.
    Uses Finmap for decidable equality (needed by TClosure/TFrameContent/TimedFrame). -/
abbrev TEnv := Finmap (fun _ : Var => TVAddr)

-- Use Finmap.lookup for environment lookup: ρ.lookup x
-- (TEnv.lookup is just Finmap.lookup since TEnv = Finmap ...)

def TEnv.empty : TEnv := ∅

def TEnv.extend (ρ : TEnv) (x : Var) (a : TVAddr) : TEnv :=
  ρ.insert x a

def TEnv.extendMany (ρ : TEnv) (bindings : List (Var × TVAddr)) : TEnv :=
  bindings.foldl (fun ρ' (x, a) => ρ'.extend x a) ρ

/-! ## Timestamped Closures and Frames -/

/-- Timestamped closure -/
structure TClosure where
  params : List Var
  body : Exp
  env : TEnv
  params_nodup : params.Nodup

/-- Frame content: either a let-continuation or a handler frame -/
inductive TFrameContent where
  | letFrame : TClosure → TFrameContent
  | handlerFrame : Handler → TEnv → TFrameContent

-- DecidableEq now available since Syntax.lean defines instances for mutual inductives.
instance : DecidableEq TClosure := fun a b =>
  match decEq a.params b.params, decEq a.body b.body, decEq a.env b.env with
  | .isTrue h1, .isTrue h2, .isTrue h3 => .isTrue (by cases a; cases b; simp at *; exact ⟨h1, h2, h3⟩)
  | .isFalse h, _, _ => .isFalse (fun h' => h (by subst h'; rfl))
  | _, .isFalse h, _ => .isFalse (fun h' => h (by subst h'; rfl))
  | _, _, .isFalse h => .isFalse (fun h' => h (by subst h'; rfl))

instance : DecidableEq TFrameContent := fun a b => by
  cases a <;> cases b
  · rename_i c1 c2; exact if h : c1 = c2 then .isTrue (h ▸ rfl) else .isFalse (fun | rfl => h rfl)
  · exact .isFalse nofun
  · exact .isFalse nofun
  · rename_i h1 ρ1 h2 ρ2
    exact match decEq h1 h2, decEq ρ1 ρ2 with
    | .isTrue h1, .isTrue h2 => .isTrue (h1 ▸ h2 ▸ rfl)
    | .isFalse h, _ => .isFalse (fun | rfl => h rfl)
    | _, .isFalse h => .isFalse (fun | rfl => h rfl)

/-- Timed frame: frame content paired with capture timestamp and introduction label -/
structure TimedFrame where
  content : TFrameContent
  time : Time
  label : Label            -- the label of the expression site that created this frame
  deriving DecidableEq

/-! ## Continuation Addresses and Unified Store -/

/-- Continuation address: identifies a point in the continuation chain -/
structure TKAddr where
  frame : TimedFrame
  op : OpName
  deriving DecidableEq

/-- Unified address type: store maps both value and kont addresses -/
inductive TAddr where
  | val : TVAddr → TAddr
  | kont : TKAddr → TAddr
  deriving DecidableEq

@[simp, grind ->] def TAddr.time : TAddr → Time
  | .val a => a.time
  | .kont a => a.frame.time

@[simp, grind ->] def TAddr.tmk : TAddr → MKTime
  | .val a => a.time.tmk
  | .kont a => a.frame.time.tmk

/-! ## Denotables and Store -/

/-- Denotables: values that can be stored at value addresses -/
inductive TDenotable where
  | closure : TClosure → TDenotable
  | kontClosure : Handler → TEnv → Option TKAddr → TDenotable  -- kont is an optional ADDRESS
  | conLabel : ConLabel → TDenotable
  | succVal : TVAddr → TDenotable

instance : Inhabited TDenotable := ⟨TDenotable.conLabel ConLabel.unit⟩

/-- What the store maps to -/
inductive TStorable where
  | denotable : TDenotable → TStorable
  | kontLink : Option TKAddr → TStorable     -- points to next frame in chain (none = end)

/-- Unified store: maps TAddr to TStorable -/
abbrev TStore := TAddr → Option TStorable

def TStore.empty : TStore := fun _ => none

/-- Store domain -/
def TStore.dom (σ : TStore) : Set TAddr := { a | σ a ≠ none }

def TStore.extend (σ : TStore) (a : TAddr) (s : TStorable) : TStore :=
  fun a' => if a' = a then some s else σ a'

/-! ## Values -/

/-- Timestamped values -/
inductive TValue where
  | den : TDenotable → TValue
  | suspended : OpName → List TVAddr → Option TKAddr → TValue  -- kont is an optional ADDRESS

/-! ## Prefix Orderings -/

/-- t1 is a prefix of t2 (t2 extends t1) -/
def MKTime.isPrefixOf (t1 t2 : MKTime) : Prop := ∃ suffix, t2 = suffix ++ t1

/-- Single-step extension of MKTime -/
def MKTime.isExtOf (t1 t2 : MKTime) : Prop :=
  ∃ l tk, t2 = (l, tk) :: t1

/-! ## Freshness Definitions -/

/-- Core freshness: no address in σ has timestamp t -/
def fresh (σ : TStore) (t : Time) : Prop :=
  ∀ a, σ a ≠ none → a.time ≠ t

/-- Meta-kont freshness: no address in σ has tmk equal to or extending given tmk -/
def fresh_mk (σ : TStore) (tmk : MKTime) : Prop :=
  ∀ a, σ a ≠ none → ¬ MKTime.isPrefixOf tmk a.tmk

/-- Store extension: σ' extends σ (preserves all mappings) -/
def store_extends (σ σ' : TStore) : Prop :=
  ∀ a, σ a ≠ none → σ' a = σ a

/-! ## Continuation Chains -/

/-- Continuation chain: sequence of timed frames reachable from an Option TKAddr through the store -/
inductive Chain (σ : TStore) : Option TKAddr → List TimedFrame → Prop where
  | «end» : Chain σ none []
  | link : σ (.kont a) = some (.kontLink next) →
           Chain σ next rest →
           Chain σ (some a) (a.frame :: rest)

/-- Well-ordered chain -/
def WellOrderedChain : List TimedFrame → Prop
  | [] => True
  | [_] => True
  | ψ₁ :: ψ₂ :: rest =>
      match ψ₂.content with
      | .letFrame _ =>
          (ψ₁.time.tmk = ψ₂.time.tmk ∧
           ψ₁.time.tk.length ≤ ψ₂.time.tk.length) ∧
          WellOrderedChain (ψ₂ :: rest)
      | .handlerFrame _ _ =>
          ψ₁.time.tmk.length < ψ₂.time.tmk.length ∧
          WellOrderedChain (ψ₂ :: rest)

/-- Store well-formedness: all reachable continuation chains are well-ordered and acyclic -/
def wf_kont (σ : TStore) : Prop :=
  ∀ a : TKAddr, σ (.kont a) ≠ none →
    ∃ chain, Chain σ (some a) chain ∧ WellOrderedChain chain ∧ chain.Nodup

/-! ## Helper Lemmas -/

@[simp]
theorem TStore.extend_same (σ : TStore) (a : TAddr) (s : TStorable) :
    (σ.extend a s) a = some s := by
  simp [TStore.extend]

theorem TStore.extend_ne (σ : TStore) (a a' : TAddr) (s : TStorable) (h : a' ≠ a) :
    (σ.extend a s) a' = σ a' := by
  simp [TStore.extend, h]

@[simp]
theorem TEnv.lookup_extend_same (ρ : TEnv) (x : Var) (a : TVAddr) :
    Finmap.lookup x (ρ.extend x a) = some a := by
  simp [TEnv.extend]

theorem TEnv.lookup_extend_ne (ρ : TEnv) (x y : Var) (a : TVAddr) (h : y ≠ x) :
    Finmap.lookup y (ρ.extend x a) = Finmap.lookup y ρ := by
  simp [TEnv.extend, Finmap.lookup_insert_of_ne _ h]

@[simp]
theorem TEnv.lookup_empty (x : Var) :
    Finmap.lookup x TEnv.empty = none := by
  simp [TEnv.empty]

/-- fresh_mk implies fresh for any tk -/
theorem fresh_mk_implies_fresh (h : fresh_mk σ tmk) (tk : KTime) :
    fresh σ ⟨tk, tmk⟩ := by
  intro a ha heq
  have := h a ha
  apply this
  refine ⟨[], ?_⟩
  cases a with
  | val v => simp [TAddr.tmk]; simp [TAddr.time] at heq; rw [heq]
  | kont k => simp [TAddr.tmk]; simp [TAddr.time] at heq; rw [heq]

/-- fresh_mk is preserved under extension of the MKTime -/
theorem fresh_mk_extend (h : fresh_mk σ tmk) (l : Label) (tk : KTime) :
    fresh_mk σ ((l, tk) :: tmk) := by
  intro a ha hpre
  apply h a ha
  obtain ⟨suffix, hsuf⟩ := hpre
  exact ⟨suffix ++ [(l, tk)], by rw [hsuf, List.append_assoc]; rfl⟩

/-- store_extends is reflexive -/
theorem store_extends_refl : store_extends σ σ := by
  intro a _; rfl

/-- store_extends is transitive -/
theorem store_extends_trans (h1 : store_extends σ₁ σ₂) (h2 : store_extends σ₂ σ₃) :
    store_extends σ₁ σ₃ := by
  intro a ha
  have h1a := h1 a ha
  have : σ₂ a ≠ none := by rw [h1a]; exact ha
  rw [h2 a this, h1a]

/-- Freshness is monotone: if σ' extends σ and t is fresh in σ', it's fresh in σ -/
theorem fresh_of_store_extends (hext : store_extends σ σ') (hfresh : fresh σ' t) :
    fresh σ t := by
  intro a ha heq
  have : σ' a ≠ none := by
    rw [hext a ha]; exact ha
  exact hfresh a this heq

/-! ## Store Extension Lemmas -/

/-- Extending the store at a fresh address produces a store extension -/
theorem store_extends_extend (σ : TStore) (a : TAddr) (s : TStorable)
    (hfresh : σ a = none) :
    store_extends σ (σ.extend a s) := by
  intro a' ha'
  by_cases h : a' = a
  · subst h; exact absurd hfresh ha'
  · simp [TStore.extend, h]

/-- Composing two store extensions -/
theorem store_extends_extend_extend (σ : TStore) (a₁ a₂ : TAddr) (s₁ s₂ : TStorable)
    (h₁ : σ a₁ = none) (h₂ : (σ.extend a₁ s₁) a₂ = none) :
    store_extends σ ((σ.extend a₁ s₁).extend a₂ s₂) :=
  store_extends_trans (store_extends_extend σ a₁ s₁ h₁) (store_extends_extend _ a₂ s₂ h₂)

/-- Extending with val preserves kont chain lookups -/
theorem TStore.extend_val_kont (σ : TStore) (av : TVAddr) (s : TStorable) (ak : TKAddr) :
    (σ.extend (.val av) s) (.kont ak) = σ (.kont ak) := by
  simp [TStore.extend]

/-! ## Chain Preservation Lemmas -/

/-- Chain preserved under val extension -/
theorem chain_extend_val (h : Chain σ oa chain) (av : TVAddr) (s : TStorable) :
    Chain (σ.extend (.val av) s) oa chain := by
  induction h with
  | «end» => exact Chain.end
  | link hlookup _hchain ih =>
    exact Chain.link (by rw [TStore.extend_val_kont]; exact hlookup) ih

/-- Chain preserved under unrelated kont extension (ak must be fresh in σ) -/
theorem chain_extend_kont_ne (h : Chain σ oa chain) (ak : TKAddr) (s : TStorable)
    (hfresh : σ (.kont ak) = none) :
    Chain (σ.extend (.kont ak) s) oa chain := by
  induction h with
  | «end» => exact Chain.end
  | link hlookup _hchain ih =>
    apply Chain.link ?_ ih
    simp only [TStore.extend]
    split
    · next heq => rw [TAddr.kont.inj heq] at hlookup; simp [hfresh] at hlookup
    · exact hlookup

/-! ## wf_kont Preservation Lemmas -/

/-- wf_kont preserved under val allocation (kont structure unchanged) -/
theorem wf_kont_extend_val (h : wf_kont σ) (av : TVAddr) (s : TStorable) :
    wf_kont (σ.extend (.val av) s) := by
  intro a ha
  rw [TStore.extend_val_kont] at ha
  obtain ⟨chain, hchain, hord, hnodup⟩ := h a ha
  exact ⟨chain, chain_extend_val hchain av s, hord, hnodup⟩

/-- wf_kont preserved under two val allocations -/
theorem wf_kont_extend_val_val (h : wf_kont σ) (av₁ av₂ : TVAddr) (s₁ s₂ : TStorable) :
    wf_kont ((σ.extend (.val av₁) s₁).extend (.val av₂) s₂) :=
  wf_kont_extend_val (wf_kont_extend_val h av₁ s₁) av₂ s₂

/-- wf_kont preserved under kontLink allocation -/
theorem wf_kont_extend_kontLink (h : wf_kont σ) (a : TKAddr) (next : Option TKAddr)
    (hfresh : σ (.kont a) = none)
    (hchain_ok : ∃ chain, Chain σ next chain ∧ WellOrderedChain (a.frame :: chain) ∧ (a.frame :: chain).Nodup) :
    wf_kont (σ.extend (.kont a) (.kontLink next)) := by
  intro a' ha'
  by_cases heq : a' = a
  · subst heq
    obtain ⟨chain, hchain_next, hord, hnodup⟩ := hchain_ok
    exact ⟨a'.frame :: chain,
           Chain.link (TStore.extend_same σ (.kont a') (.kontLink next))
             (chain_extend_kont_ne hchain_next a' (.kontLink next) hfresh),
           hord, hnodup⟩
  · have hne : (.kont a' : TAddr) ≠ .kont a := fun h => heq (TAddr.kont.inj h)
    rw [TStore.extend_ne _ _ _ _ hne] at ha'
    obtain ⟨chain, hchain, hord, hnodup⟩ := h a' ha'
    exact ⟨chain, chain_extend_kont_ne hchain a (.kontLink next) hfresh, hord, hnodup⟩

/-! ## Store extension under foldl -/

/-- wf_kont preserved through foldl of val extensions -/
theorem wf_kont_foldl_val (h : wf_kont σ) (bindings : List (Var × TDenotable)) :
    wf_kont (bindings.foldl (fun s (x, d) => s.extend (.val ⟨x, t⟩) (.denotable d)) σ) := by
  induction bindings generalizing σ with
  | nil => exact h
  | cons hd tl ih =>
    exact ih (wf_kont_extend_val h _ _)

end DMCFA
