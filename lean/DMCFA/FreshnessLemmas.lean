/-
  FreshnessLemmas: Reusable definitions and lemmas for the freshness simulation proof.

  Contains:
  - Descendant relation and structural properties
  - DescendantVia (first-step labeled descent) and disjointness lemmas
  - Store scoping, freshness definitions, WriteBound
  - PairwiseChain (kont chain tracking with frame labels + vars)
  - WellFormedValue6, StoreChainWF, FreshInvariant6
-/

import DMCFA.TimestampedSemantics
import DMCFA.FreshSemantics
import DMCFA.TimeOrder
import DMCFA.UniqueLabels
import DMCFA.TmkPreservation

set_option maxHeartbeats 800000

namespace DMCFA

/-! ## List Helper Lemmas -/

/-- Two suffixes of the same list with equal length must be equal. -/
theorem suffix_eq_of_length_eq {α : Type*} (xs ys zs : List α)
    (hsuf_xs : List.IsSuffix xs zs) (hsuf_ys : List.IsSuffix ys zs)
    (hlen : xs.length = ys.length) : xs = ys := by
  obtain ⟨px, hpx⟩ := hsuf_xs
  obtain ⟨py, hpy⟩ := hsuf_ys
  have h_eq : px ++ xs = py ++ ys := hpx.trans hpy.symm
  have h_len : px.length = py.length := by
    have : (px ++ xs).length = (py ++ ys).length := by rw [h_eq]
    simp only [List.length_append] at this hlen
    omega
  exact (List.append_inj h_eq h_len).2

/-! ## Timestamp Descendant Relation -/

/-- Time t₂ is a descendant of t₁: reached by a sequence of
    call extensions (prepend to tk) and handler extensions (prepend to tmk).
    The handler constructor is relaxed: tk can be anything in the descendant,
    because kont restoration may change tk. The structural property is that
    tmk grows by prepending (l, t₁.tk) where t₁ is the handler entry time. -/
inductive Descendant : Time → Time → Prop where
  /-- Every time is a descendant of itself -/
  | refl : Descendant t t
  /-- Function call: extend tk by prepending a label -/
  | call {t₁ t₂ : Time} (l : Label) :
      Descendant t₁ t₂ → Descendant t₁ ⟨l :: t₂.tk, t₂.tmk⟩
  /-- Handler entry: extend tmk, tk resets to [] (actual handler body entry point) -/
  | handler {t₁ t₂ : Time} (l : Label) :
      Descendant t₁ t₂ → Descendant t₁ ⟨[], (l, t₂.tk) :: t₂.tmk⟩
  /-- Kont application: extend tmk, tk can be anything (kont restoration) -/
  | appKont {t₁ t₂ : Time} (l : Label) (tk : KTime) :
      Descendant t₁ t₂ → Descendant t₁ ⟨tk, (l, t₂.tk) :: t₂.tmk⟩

/-! ## Structural Properties of Descendant -/

/-- Descendants never shrink tmk: t₁.tmk is always a suffix of t₂.tmk -/
theorem Descendant.tmk_suffix {t₁ t₂ : Time} (h : Descendant t₁ t₂) :
    t₁.tmk <:+ t₂.tmk := by
  induction h with
  | refl => exact List.suffix_refl _
  | call l _ ih => exact ih
  | handler l _ ih => exact ih.trans (List.suffix_cons _ _)
  | appKont l tk _ ih => exact ih.trans (List.suffix_cons _ _)

/-- At the same tmk level, descendants never shrink tk -/
theorem Descendant.tk_suffix_of_same_tmk {t₁ t₂ : Time} (h : Descendant t₁ t₂)
    (htmk : t₁.tmk = t₂.tmk) : t₁.tk <:+ t₂.tk := by
  match h with
  | Descendant.refl => exact List.suffix_refl _
  | Descendant.call l h_prev =>
    have ih := tk_suffix_of_same_tmk h_prev htmk
    exact ih.trans (List.suffix_cons _ _)
  | Descendant.handler l h_prev | Descendant.appKont l _ h_prev =>
    exfalso
    have hsuf := Descendant.tmk_suffix h_prev
    rw [htmk] at hsuf
    obtain ⟨px, hpx⟩ := hsuf
    have hlen := congr_arg List.length hpx
    simp only [List.length_append, List.length_cons] at hlen
    omega

/-- Descendant is transitive -/
theorem Descendant.trans {t₁ t₂ t₃ : Time}
    (h₁ : Descendant t₁ t₂) (h₂ : Descendant t₂ t₃) : Descendant t₁ t₃ := by
  induction h₂ generalizing t₁ with
  | refl => exact h₁
  | call l _ ih => exact .call l (ih h₁)
  | handler l _ ih => exact .handler l (ih h₁)
  | appKont l tk _ ih => exact .appKont l tk (ih h₁)

/-! ## DescendantVia: first-step labeled descent -/

/-- DescendantVia t l t' means t' is a descendant of t where the FIRST step
    from t uses label l — either a call (l :: t.tk) or handler entry ((l, t.tk) :: t.tmk).
    This is the key ingredient for proving that writes through one label don't
    affect freshness at a different label's descendants. -/
def DescendantVia (t : Time) (l : Label) (t' : Time) : Prop :=
  Descendant ⟨l :: t.tk, t.tmk⟩ t' ∨
  ∃ tk, Descendant ⟨tk, (l, t.tk) :: t.tmk⟩ t'

/-- DescendantVia implies Descendant (by prepending one call/handler step) -/
theorem DescendantVia.toDescendant {t t' : Time} {l : Label}
    (h : DescendantVia t l t') : Descendant t t' := by
  rcases h with hc | ⟨tk, hh⟩
  · exact (Descendant.call l .refl).trans hc
  · exact (Descendant.appKont l tk .refl).trans hh

/-- DescendantVia target is never the base time itself -/
theorem DescendantVia.ne {t t' : Time} {l : Label}
    (h : DescendantVia t l t') : t' ≠ t := by
  rcases h with hc | ⟨tk, hh⟩
  · intro heq; subst heq
    have := hc.tk_suffix_of_same_tmk rfl
    obtain ⟨px, hpx⟩ := this
    have hlen := congr_arg List.length hpx; simp at hlen; omega
  · intro heq; subst heq
    have := hh.tmk_suffix
    obtain ⟨px, hpx⟩ := this
    have hlen := congr_arg List.length hpx; simp at hlen; omega

/-- Every non-self descendant decomposes into a DescendantVia -/
theorem Descendant.toDescendantVia {t₁ t₂ : Time}
    (h : Descendant t₁ t₂) (hne : t₂ ≠ t₁) : ∃ l, DescendantVia t₁ l t₂ := by
  induction h with
  | refl => exact absurd rfl hne
  | @call t_mid l _ ih =>
    by_cases heq : t_mid = t₁
    · subst heq; exact ⟨l, Or.inl .refl⟩
    · obtain ⟨l', hdv⟩ := ih heq
      rcases hdv with hc | ⟨tk, hh⟩
      · exact ⟨l', Or.inl (.call l hc)⟩
      · exact ⟨l', Or.inr ⟨_, .call l hh⟩⟩
  | @handler t_mid l _ ih =>
    by_cases heq : t_mid = t₁
    · subst heq; exact ⟨l, Or.inr ⟨[], .refl⟩⟩
    · obtain ⟨l', hdv⟩ := ih heq
      rcases hdv with hc | ⟨tk', hh⟩
      · exact ⟨l', Or.inl (.handler l hc)⟩
      · exact ⟨l', Or.inr ⟨_, .handler l hh⟩⟩
  | @appKont t_mid l tk _ ih =>
    by_cases heq : t_mid = t₁
    · subst heq; exact ⟨l, Or.inr ⟨tk, .refl⟩⟩
    · obtain ⟨l', hdv⟩ := ih heq
      rcases hdv with hc | ⟨tk', hh⟩
      · exact ⟨l', Or.inl (.appKont l tk hc)⟩
      · exact ⟨l', Or.inr ⟨_, .appKont l tk hh⟩⟩

/-! ## Disjointness of Descendant Regions -/

/-- Key structural lemma: descending from a call extension ⟨l :: tk, tmk⟩,
    the first handler entry above tmk in the result must have its second
    component as a suffix-extension of l :: tk. -/
theorem Descendant.call_first_tmk_entry {l : Label} {tk : KTime} {tmk : MKTime} {t : Time}
    (h : Descendant ⟨l :: tk, tmk⟩ t)
    {lh : Label} {tkh : KTime} (hsuf : (lh, tkh) :: tmk <:+ t.tmk) :
    l :: tk <:+ tkh := by
  induction h with
  | refl =>
    obtain ⟨px, hpx⟩ := hsuf
    have hlen := congr_arg List.length hpx
    simp only [List.length_append, List.length_cons] at hlen; omega
  | @call _ _ _ ih => exact ih hsuf
  | @handler t₂ l' h_sub ih | @appKont t₂ l' _ h_sub ih =>
    obtain ⟨px, hpx⟩ := hsuf
    cases px with
    | nil =>
      have heq := List.cons.inj hpx
      have htmk : tmk = t₂.tmk := heq.2
      have htkh : tkh = t₂.tk := (Prod.ext_iff.mp heq.1).2
      rw [htkh]
      exact h_sub.tk_suffix_of_same_tmk htmk
    | cons p ps =>
      exact ih ⟨ps, (List.cons.inj hpx).2⟩

/-- Helper: extract a tmk entry immediately above a suffix from a nonempty prefix. -/
private theorem tmk_entry_of_nonempty_prefix {tmk : MKTime} {t_tmk : MKTime}
    {p : Label × KTime} {ps : List (Label × KTime)}
    (hpx : (p :: ps) ++ tmk = t_tmk) :
    ∃ (lh : Label) (tkh : KTime), (lh, tkh) :: tmk <:+ t_tmk := by
  induction ps generalizing p t_tmk with
  | nil => exact ⟨p.1, p.2, ⟨[], by simp [← hpx]⟩⟩
  | cons q qs ih =>
    obtain ⟨lh, tkh, hsuf⟩ := ih (p := q) (t_tmk := q :: qs ++ tmk) rfl
    exact ⟨lh, tkh, hsuf.trans ⟨[p], by simp [← hpx]⟩⟩

/-- General version: any Descendant from ⟨tk, tmk⟩ to t, if t.tmk has an entry
    above tmk, then tk is a suffix of the entry's tk component. -/
theorem Descendant.general_first_tmk_entry {tk : KTime} {tmk : MKTime} {t : Time}
    (h : Descendant ⟨tk, tmk⟩ t)
    {lh : Label} {tkh : KTime} (hsuf : (lh, tkh) :: tmk <:+ t.tmk) :
    tk <:+ tkh := by
  induction h with
  | refl =>
    obtain ⟨px, hpx⟩ := hsuf
    have hlen := congr_arg List.length hpx
    simp only [List.length_append, List.length_cons] at hlen; omega
  | @call _ _ _ ih => exact ih hsuf
  | @handler t₂ l' h_sub ih | @appKont t₂ l' _ h_sub ih =>
    obtain ⟨px, hpx⟩ := hsuf
    cases px with
    | nil =>
      have heq := List.cons.inj hpx
      have htmk : tmk = t₂.tmk := heq.2
      have htkh : tkh = t₂.tk := (Prod.ext_iff.mp heq.1).2
      rw [htkh]
      exact h_sub.tk_suffix_of_same_tmk htmk
    | cons p ps =>
      exact ih ⟨ps, (List.cons.inj hpx).2⟩

/-- Corollary: descendants of ⟨l :: tk, tmk⟩ can never have (l', tk) :: tmk as tmk suffix.
    The first handler entry above tmk has second component with l :: tk as suffix,
    but |l :: tk| > |tk|, so the suffix match fails. -/
theorem Descendant.no_shorter_tmk_entry {l : Label} {tk : KTime} {tmk : MKTime} {t : Time}
    (h : Descendant ⟨l :: tk, tmk⟩ t)
    {l' : Label} (hsuf : (l', tk) :: tmk <:+ t.tmk) : False := by
  have := h.call_first_tmk_entry hsuf
  -- l :: tk <:+ tk, but |l :: tk| = |tk| + 1 > |tk|
  obtain ⟨px, hpx⟩ := this
  have hlen := congr_arg List.length hpx
  simp only [List.length_append, List.length_cons] at hlen; omega

/-- Two Descendants from the same tmk but possibly different tks always have
    comparable starting tks (one is a suffix of the other). -/
theorem Descendant.tk_suffix_comparable {tk₁ tk₂ : KTime} {tmk : MKTime} {t : Time}
    (h₁ : Descendant ⟨tk₁, tmk⟩ t) (h₂ : Descendant ⟨tk₂, tmk⟩ t) :
    tk₁ <:+ tk₂ ∨ tk₂ <:+ tk₁ := by
  by_cases htmk : t.tmk = tmk
  · exact List.suffix_or_suffix_of_suffix
      (h₁.tk_suffix_of_same_tmk htmk.symm)
      (h₂.tk_suffix_of_same_tmk htmk.symm)
  · have htmk₁ := h₁.tmk_suffix
    obtain ⟨px, hpx⟩ := htmk₁
    cases px with
    | nil => exact absurd hpx.symm htmk
    | cons p ps =>
      obtain ⟨lh, tkh, hsuf_entry⟩ := tmk_entry_of_nonempty_prefix hpx
      exact List.suffix_or_suffix_of_suffix
        (h₁.general_first_tmk_entry hsuf_entry)
        (h₂.general_first_tmk_entry hsuf_entry)

/-- Call disjointness: a time cannot be a descendant of two different
    call extensions from the same base. -/
theorem Descendant.call_disjoint {tk : KTime} {tmk : MKTime} {l₁ l₂ : Label} {t : Time}
    (h₁ : Descendant ⟨l₁ :: tk, tmk⟩ t) (h₂ : Descendant ⟨l₂ :: tk, tmk⟩ t)
    (hne : l₁ ≠ l₂) : False := by
  by_cases htmk : t.tmk = tmk
  · have hsuf₁ := h₁.tk_suffix_of_same_tmk htmk.symm
    have hsuf₂ := h₂.tk_suffix_of_same_tmk htmk.symm
    have hlen : (l₁ :: tk).length = (l₂ :: tk).length := by simp
    have heq := suffix_eq_of_length_eq (l₁ :: tk) (l₂ :: tk) t.tk hsuf₁ hsuf₂ hlen
    exact hne (List.cons.inj heq).1
  · have htmk₁ := h₁.tmk_suffix
    obtain ⟨px, hpx⟩ := htmk₁
    cases px with
    | nil => exact htmk hpx.symm
    | cons p ps =>
      obtain ⟨lh, tkh, hsuf_entry⟩ := tmk_entry_of_nonempty_prefix hpx
      have hk₁ := h₁.call_first_tmk_entry hsuf_entry
      have hk₂ := h₂.call_first_tmk_entry hsuf_entry
      have hlen : (l₁ :: tk).length = (l₂ :: tk).length := by simp
      have heq := suffix_eq_of_length_eq (l₁ :: tk) (l₂ :: tk) tkh hk₁ hk₂ hlen
      exact hne (List.cons.inj heq).1

/-- Handler disjointness: a time cannot be a descendant of two different
    handler extensions from the same base. -/
theorem Descendant.handler_disjoint {tk₁ tk₂ : KTime} {tk_base : KTime}
    {tmk : MKTime} {l₁ l₂ : Label} {t : Time}
    (h₁ : Descendant ⟨tk₁, (l₁, tk_base) :: tmk⟩ t)
    (h₂ : Descendant ⟨tk₂, (l₂, tk_base) :: tmk⟩ t)
    (hne : l₁ ≠ l₂) : False := by
  have hsuf₁ := h₁.tmk_suffix
  have hsuf₂ := h₂.tmk_suffix
  have hlen : ((l₁, tk_base) :: tmk).length = ((l₂, tk_base) :: tmk).length := by simp
  have heq := suffix_eq_of_length_eq ((l₁, tk_base) :: tmk) ((l₂, tk_base) :: tmk) t.tmk hsuf₁ hsuf₂ hlen
  have hp := (List.cons.inj heq).1
  exact hne (Prod.ext_iff.mp hp).1

/-- Cross-mode disjointness: a call-descendant of ⟨l₁ :: tk, tmk⟩ cannot have
    (l₂, tk) :: tmk as a suffix of its tmk. -/
theorem Descendant.call_handler_disjoint {tk : KTime} {tmk : MKTime}
    {l₁ l₂ : Label} {t : Time}
    (h_call : Descendant ⟨l₁ :: tk, tmk⟩ t)
    (h_handler_tmk : (l₂, tk) :: tmk <:+ t.tmk) : False := by
  have h_suf := h_call.call_first_tmk_entry h_handler_tmk
  obtain ⟨px, hpx⟩ := h_suf
  have hlen := congr_arg List.length hpx
  simp only [List.length_append, List.length_cons] at hlen; omega

/-- DescendantVia disjointness: two different first-step labels from the same
    base time produce disjoint descendant regions. -/
theorem DescendantVia.disjoint {t t' : Time} {l₁ l₂ : Label}
    (h₁ : DescendantVia t l₁ t') (h₂ : DescendantVia t l₂ t')
    (hne : l₁ ≠ l₂) : False := by
  rcases h₁ with hc₁ | ⟨tk₁, hh₁⟩ <;> rcases h₂ with hc₂ | ⟨tk₂, hh₂⟩
  · exact Descendant.call_disjoint hc₁ hc₂ hne
  · exact Descendant.call_handler_disjoint hc₁ hh₂.tmk_suffix
  · exact Descendant.call_handler_disjoint hc₂ hh₁.tmk_suffix
  · exact Descendant.handler_disjoint hh₁ hh₂ hne

/-! ## Store Scoping Invariant -/

/-! ## Handler Labels -/

/-- Whether a CExp is a handler expression -/
def CExp.isHandlerCExp : CExp → Bool
  | .handler _ _ _ => true
  | _ => false

mutual

/-- Labels of letEs whose CExp is a handler expression.
    Only these labels need HandlerDescFresh — all others only need CallDescFresh.
    Recursively includes handler labels within CExp sub-expressions (match branches, handler bodies). -/
def Exp.handlerLabels : Exp → Finset Label
  | .letE _y ce e l => (if ce.isHandlerCExp then {l} else ∅) ∪ CExp.handlerLabels ce ∪ e.handlerLabels
  | .tail ce l => (if ce.isHandlerCExp then {l} else ∅) ∪ CExp.handlerLabels ce
termination_by e => sizeOf e

def CExp.handlerLabels : CExp → Finset Label
  | .atomic _ => ∅
  | .funApp _ _ => ∅
  | .opApp _ _ => ∅
  | .funDef _f _xs e => Exp.handlerLabels e
  | .matchE _ae bs => branchListHandlerLabels bs
  | .handler h e l_h => {l_h} ∪ Handler.handlerLabels h ∪ Exp.handlerLabels e
termination_by ce => sizeOf ce

def Branch.handlerLabels : Branch → Finset Label
  | .branch _ _ e => Exp.handlerLabels e
termination_by b => sizeOf b

def Handler.handlerLabels : Handler → Finset Label
  | ⟨(_, e_ret), ops⟩ => Exp.handlerLabels e_ret ∪ opClauseListHandlerLabels ops
termination_by h => sizeOf h

def branchListHandlerLabels : List Branch → Finset Label
  | [] => ∅
  | b :: bs => Branch.handlerLabels b ∪ branchListHandlerLabels bs
termination_by bs => sizeOf bs

def opClauseListHandlerLabels : List (OpName × Var × Exp) → Finset Label
  | [] => ∅
  | (_, _, e) :: ops => Exp.handlerLabels e ∪ opClauseListHandlerLabels ops
termination_by ops => sizeOf ops

end

mutual

private theorem branchListHandlerLabels_subset_branchListLabels :
    ∀ (bs : List Branch), branchListHandlerLabels bs ⊆ branchListLabels bs
  | [] => by simp [branchListHandlerLabels]
  | b :: bs => by
    simp only [branchListHandlerLabels, branchListLabels]
    exact Finset.union_subset_union (Branch.handlerLabels_subset_allLabels b)
      (branchListHandlerLabels_subset_branchListLabels bs)
termination_by bs => sizeOf bs

private theorem opClauseListHandlerLabels_subset_opClauseListLabels :
    ∀ (ops : List (OpName × Var × Exp)), opClauseListHandlerLabels ops ⊆ opClauseListLabels ops
  | [] => by simp [opClauseListHandlerLabels]
  | (_, _, e) :: ops => by
    simp only [opClauseListHandlerLabels, opClauseListLabels]
    exact Finset.union_subset_union (Exp.handlerLabels_subset_allLabels e)
      (opClauseListHandlerLabels_subset_opClauseListLabels ops)
termination_by ops => sizeOf ops

private theorem Branch.handlerLabels_subset_allLabels : ∀ (b : Branch), b.handlerLabels ⊆ b.allLabels
  | .branch _ _ e => by
    simp only [Branch.handlerLabels, Branch.allLabels]
    exact Exp.handlerLabels_subset_allLabels e
termination_by b => sizeOf b

theorem Handler.handlerLabels_subset_allLabels : ∀ (h : Handler), h.handlerLabels ⊆ h.allLabels
  | ⟨(_, e_ret), ops⟩ => by
    simp only [Handler.handlerLabels, Handler.allLabels]
    exact Finset.union_subset_union
      (Exp.handlerLabels_subset_allLabels e_ret)
      (opClauseListHandlerLabels_subset_opClauseListLabels ops)
termination_by h => sizeOf h

theorem CExp.handlerLabels_subset_allLabels : ∀ (ce : CExp), ce.handlerLabels ⊆ ce.allLabels
  | .atomic _ => by simp [CExp.handlerLabels]
  | .funApp _ _ => by simp [CExp.handlerLabels]
  | .opApp _ _ => by simp [CExp.handlerLabels]
  | .funDef _f _xs e => by
    simp only [CExp.handlerLabels, CExp.allLabels]
    exact Exp.handlerLabels_subset_allLabels e
  | .matchE _ae bs => by
    simp only [CExp.handlerLabels, CExp.allLabels]
    exact branchListHandlerLabels_subset_branchListLabels bs
  | .handler h e l_h => by
    intro x hx
    simp only [CExp.handlerLabels, Finset.mem_union, Finset.mem_singleton] at hx
    rw [CExp.allLabels_handler]; simp only [Finset.mem_union, Finset.mem_singleton]
    rcases hx with (rfl | hx) | hx
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (Or.inr (Handler.handlerLabels_subset_allLabels h hx))
    · exact Or.inr (Exp.handlerLabels_subset_allLabels e hx)
termination_by ce => sizeOf ce

theorem Exp.handlerLabels_subset_allLabels : ∀ (e : Exp), e.handlerLabels ⊆ e.allLabels
  | .letE _y ce e l => by
    intro x hx
    simp only [Exp.handlerLabels, Finset.mem_union] at hx
    simp only [Exp.allLabels, Finset.mem_union, Finset.mem_singleton]
    rcases hx with (hx | hx) | hx
    · split at hx <;> simp_all
    · exact Or.inl (Or.inr (CExp.handlerLabels_subset_allLabels ce hx))
    · exact Or.inr (Exp.handlerLabels_subset_allLabels e hx)
  | .tail ce _l => by
    intro x hx
    simp only [Exp.handlerLabels, Finset.mem_union] at hx
    simp only [Exp.allLabels, Finset.mem_union, Finset.mem_singleton]
    rcases hx with hx | hx
    · split at hx <;> simp_all
    · exact Or.inr (CExp.handlerLabels_subset_allLabels ce hx)
termination_by e => sizeOf e

end

/-- The store is "scoped" at time t: every non-none address is at a
    timestamp that is a descendant of t. -/
def ScopedStore (σ : TStore) (t : Time) : Prop :=
  ∀ a, σ a ≠ none → Descendant t a.time

/-! ## PairwiseChain: Kont chain with label + var tracking -/

/-- Kont chain with frame content well-formedness, label AND var tracking.
    Label sets track BODY labels only (not frame labels).
    same_tk accumulates both labels and vars; diff_tk and handler_frame reset. -/
inductive PairwiseChain : TStore → Option TKAddr → Finset Label → Finset Var → Prop where
  | none : PairwiseChain σ none ∅ ∅
  /-- Let-frame with same tk as next frame (or next is none) -/
  | same_tk :
      σ (.kont a_κ) = some (.kontLink a_next) →
      a_κ.frame.content = .letFrame clo →
      WellFormedProgram clo.body →
      (∀ y, clo.params = [y] → y ∉ clo.body.topAllocVars) →
      -- CExp-side labels from the original letE
      (ceLabels : Finset Label) →
      sameTkLabels ⊆ ceLabels →
      Disjoint ceLabels clo.body.allLabels →
      a_κ.frame.label ∉ ceLabels →
      a_κ.frame.label ∉ clo.body.allLabels →
      -- Inner frame label in ceLabels (pairwise: next frame was from CExp evaluation)
      (∀ a', a_next = some a' → a'.frame.label ∈ ceLabels) →
      -- tk and var constraints
      (∀ a', a_next = some a' → a_κ.frame.time.tk = a'.frame.time.tk) →
      (∀ y, clo.params = [y] → Disjoint ({y} ∪ clo.body.topAllocVars) sameTkVars) →
      PairwiseChain σ a_next sameTkLabels sameTkVars →
      PairwiseChain σ (some a_κ) ({a_κ.frame.label} ∪ clo.body.allLabels ∪ sameTkLabels)
        (clo.params.toFinset ∪ clo.body.topAllocVars ∪ sameTkVars)
  /-- Let-frame with inner chain at deeper tk — resets label/var accumulation.
      The bridging label `l_bridge` created the depth (may differ from frame.label
      when depth comes from a nested call within match/handler bodies). -/
  | diff_tk :
      σ (.kont a_κ) = some (.kontLink a_next) →
      a_κ.frame.content = .letFrame clo →
      WellFormedProgram clo.body →
      (∀ y, clo.params = [y] → y ∉ clo.body.topAllocVars) →
      a_κ.frame.label ∉ clo.body.allLabels →
      (l_bridge : Label) →
      l_bridge ∉ clo.body.allLabels →
      (∀ a', a_next = some a' → (l_bridge :: a_κ.frame.time.tk) <:+ a'.frame.time.tk) →
      a_next ≠ none →
      PairwiseChain σ a_next _innerLabels _innerVars →
      PairwiseChain σ (some a_κ) ({a_κ.frame.label} ∪ {l_bridge} ∪ clo.body.allLabels)
        (clo.params.toFinset ∪ clo.body.topAllocVars)
  /-- Handler frame — resets label/var accumulation (inner chain at deeper tmk).
      frame.label ∉ hdl.handlerLabels (enclosing label disjoint from handler's handler labels). -/
  | handler_frame :
      σ (.kont a_κ) = some (.kontLink a_next) →
      a_κ.frame.content = .handlerFrame hdl ρ →
      WellFormedSubHandler hdl →
      a_κ.frame.label ∉ hdl.handlerLabels →
      PairwiseChain σ a_next _innerLabels _innerVars →
      PairwiseChain σ (some a_κ) ({a_κ.frame.label} ∪ hdl.allLabels) hdl.topAllocVars

/-- PairwiseChain preserved by val extend (val extends don't touch konts) -/
theorem PairwiseChain.extend_val (h : PairwiseChain σ oa_κ used usedVars) (a_v : TVAddr) (s : TStorable) :
    PairwiseChain (σ.extend (.val a_v) s) oa_κ used usedVars := by
  induction h with
  | none => exact .none
  | same_tk h_lk h_content h_wfp h_y_notin ceLabels h_sub h_disj_ce h_lnb_ce h_lnb h_inner_label h_tk h_disj_vars _ ih =>
    exact .same_tk (by rw [TStore.extend_ne _ _ _ _ (by simp)]; exact h_lk)
      h_content h_wfp h_y_notin ceLabels h_sub h_disj_ce h_lnb_ce h_lnb h_inner_label h_tk h_disj_vars ih
  | diff_tk h_lk h_content h_wfp h_y_notin h_lnb l_bridge h_l_bridge_notin h_tk h_ne _ ih =>
    exact .diff_tk (by rw [TStore.extend_ne _ _ _ _ (by simp)]; exact h_lk)
      h_content h_wfp h_y_notin h_lnb l_bridge h_l_bridge_notin h_tk h_ne ih
  | handler_frame h_lk h_content h_wfh h_lnb _ ih =>
    exact .handler_frame (by rw [TStore.extend_ne _ _ _ _ (by simp)]; exact h_lk)
      h_content h_wfh h_lnb ih

/-- PairwiseChain preserved by kont extend at a fresh address -/
theorem PairwiseChain.extend_kont (h : PairwiseChain σ oa_κ used usedVars) (ak : TKAddr) (s : TStorable)
    (h_fresh : σ (.kont ak) = Option.none) :
    PairwiseChain (σ.extend (.kont ak) s) oa_κ used usedVars := by
  induction h with
  | none => exact .none
  | same_tk h_lk h_content h_wfp h_y_notin ceLabels h_sub h_disj_ce h_lnb_ce h_lnb h_inner_label h_tk h_disj_vars _ ih =>
    refine .same_tk ?_ h_content h_wfp h_y_notin ceLabels h_sub h_disj_ce h_lnb_ce h_lnb h_inner_label h_tk h_disj_vars ih
    rw [TStore.extend_ne]; exact h_lk
    intro heq; cases heq; rw [h_fresh] at h_lk; cases h_lk
  | diff_tk h_lk h_content h_wfp h_y_notin h_lnb l_bridge h_l_bridge_notin h_tk h_ne _ ih =>
    refine .diff_tk ?_ h_content h_wfp h_y_notin h_lnb l_bridge h_l_bridge_notin h_tk h_ne ih
    rw [TStore.extend_ne]; exact h_lk
    intro heq; cases heq; rw [h_fresh] at h_lk; cases h_lk
  | handler_frame h_lk h_content h_wfh h_lnb _ ih =>
    refine .handler_frame ?_ h_content h_wfh h_lnb ih
    rw [TStore.extend_ne]; exact h_lk
    intro heq; cases heq; rw [h_fresh] at h_lk; cases h_lk

/-- PairwiseChain on none always has empty label and var sets -/
theorem PairwiseChain.none_empty (h : PairwiseChain σ Option.none used usedVars) :
    used = ∅ ∧ usedVars = ∅ := by
  cases h; exact ⟨rfl, rfl⟩

/-- When PairwiseChain starts at some a_κ, the frame label is in the used set -/
theorem PairwiseChain.frame_label_mem (h : PairwiseChain σ (some a_κ) used usedVars) :
    a_κ.frame.label ∈ used := by
  cases h with
  | same_tk => simp []
  | diff_tk => simp []
  | handler_frame => simp []

/-- PairwiseChain label and var sets are uniquely determined by σ and oa -/
theorem PairwiseChain.used_unique (h1 : PairwiseChain σ oa used₁ usedVars₁)
    (h2 : PairwiseChain σ oa used₂ usedVars₂) :
    used₁ = used₂ ∧ usedVars₁ = usedVars₂ := by
  induction h1 generalizing used₂ usedVars₂ with
  | none => have ⟨h1, h2⟩ := h2.none_empty; exact ⟨h1.symm, h2.symm⟩
  | same_tk h_lk h_ct _ _ _ _ _ _ _ _ h_tk _ h_inner ih =>
    cases h2 with
    | same_tk h_lk2 h_ct2 _ _ _ _ _ _ _ _ _ _ h_inner2 =>
      rw [h_lk] at h_lk2; cases h_lk2
      rw [h_ct] at h_ct2; cases h_ct2
      have ⟨ih_l, ih_v⟩ := ih h_inner2
      exact ⟨by simp [ih_l], by simp [ih_v]⟩
    | diff_tk h_lk2 h_ct2 _ _ _ _ _ h_tk2 h_ne2 _ =>
      rw [h_lk] at h_lk2; cases h_lk2
      rw [h_ct] at h_ct2; cases h_ct2
      -- same_tk vs diff_tk: suffix contradiction
      cases h_inner with
      | none => exact absurd rfl h_ne2
      | same_tk | diff_tk | handler_frame =>
        exact absurd ((h_tk2 _ rfl).length_le) (by rw [h_tk _ rfl]; simp)
    | handler_frame _ h_ct2 _ _ _ =>
      rw [h_ct] at h_ct2; cases h_ct2
  | diff_tk h_lk h_ct _ _ _ l_bridge1 _ h_tk h_ne h_inner ih =>
    cases h2 with
    | same_tk h_lk2 h_ct2 _ _ _ _ _ _ _ _ h_tk2 _ h_inner2 =>
      rw [h_lk] at h_lk2; cases h_lk2
      rw [h_ct] at h_ct2; cases h_ct2
      cases h_inner2 with
      | none => exact absurd rfl h_ne
      | same_tk | diff_tk | handler_frame =>
        exact absurd ((h_tk _ rfl).length_le) (by rw [h_tk2 _ rfl]; simp)
    | diff_tk h_lk2 h_ct2 _ _ _ l_bridge2 _ h_tk2 h_ne2 h_inner2 =>
      rw [h_lk] at h_lk2; cases h_lk2
      rw [h_ct] at h_ct2; cases h_ct2
      -- diff_tk vs diff_tk: both have a_next ≠ none, same l_bridge
      obtain ⟨a', ha'⟩ := Option.ne_none_iff_exists'.mp h_ne
      have h_suf1 := h_tk a' ha'
      have h_suf2 := h_tk2 a' ha'
      have h_eq := suffix_eq_of_length_eq _ _ _ h_suf1 h_suf2 (by simp)
      have h_lb_eq : l_bridge1 = l_bridge2 := (List.cons.inj h_eq).1
      subst h_lb_eq
      exact ⟨rfl, rfl⟩
    | handler_frame _ h_ct2 _ _ _ =>
      rw [h_ct] at h_ct2; cases h_ct2
  | handler_frame h_lk h_ct _ _ _ ih =>
    cases h2 with
    | same_tk _ h_ct2 _ _ _ _ _ _ _ _ _ _ =>
      rw [h_ct] at h_ct2; cases h_ct2
    | diff_tk _ h_ct2 _ _ _ _ _ _ _ _ =>
      rw [h_ct] at h_ct2; cases h_ct2
    | handler_frame h_lk2 h_ct2 _ _ _ =>
      rw [h_lk] at h_lk2; cases h_lk2
      rw [h_ct] at h_ct2; cases h_ct2
      exact ⟨rfl, rfl⟩

/-! ## WellFormedValue6, StoreChainWF, FreshInvariant6 -/

/-- WellFormedValue with chain info for kontClosures and suspended values -/
structure WellFormedValue6 (σ : TStore) (v : TValue) : Prop where
  wfv : WellFormedValue v
  kontChain : ∀ hdl ρ oa, v = .den (.kontClosure hdl ρ oa) → ∃ used usedVars, PairwiseChain σ oa used usedVars
  suspChain : ∀ op args oa, v = .suspended op args oa → ∃ used usedVars, PairwiseChain σ oa used usedVars

/-- Store chain well-formedness: every kontClosure in the store has a well-formed chain -/
def StoreChainWF (σ : TStore) : Prop :=
  ∀ a, match σ a with
  | some (.denotable (.kontClosure _ _ oa_κ)) => ∃ used usedVars, PairwiseChain σ oa_κ used usedVars
  | _ => True

theorem StoreChainWF.extend_val (h : StoreChainWF σ) (a_v : TVAddr) (s : TStorable)
    (h_chain : ∀ hdl ρ oa, s = .denotable (.kontClosure hdl ρ oa) →
      ∃ used usedVars, PairwiseChain σ oa used usedVars) :
    StoreChainWF (σ.extend (.val a_v) s) := by
  intro a
  by_cases heq : a = .val a_v
  · subst heq; simp [TStore.extend]
    cases s with
    | denotable d =>
      cases d with
      | kontClosure hdl ρ oa =>
        obtain ⟨used, usedVars, hc⟩ := h_chain hdl ρ oa rfl
        exact ⟨used, usedVars, hc.extend_val a_v _⟩
      | _ => exact True.intro
    | kontLink => exact True.intro
  · rw [TStore.extend_ne _ _ _ _ heq]
    have := h a
    cases hσ : σ a with
    | none => simp
    | some val =>
      simp [hσ] at this ⊢
      cases val with
      | denotable d =>
        cases d with
        | kontClosure _ _ oa =>
          obtain ⟨used, usedVars, hc⟩ := this
          exact ⟨used, usedVars, hc.extend_val a_v s⟩
        | _ => exact True.intro
      | kontLink => exact True.intro

theorem StoreChainWF.extend_kont_link (h : StoreChainWF σ) (ak : TKAddr) (next : Option TKAddr)
    (h_fresh : σ (.kont ak) = none) :
    StoreChainWF (σ.extend (.kont ak) (.kontLink next)) := by
  intro a
  by_cases heq : a = .kont ak
  · subst heq; simp [TStore.extend]
  · rw [TStore.extend_ne _ _ _ _ heq]
    have := h a
    cases hσ : σ a with
    | none => simp
    | some val =>
      simp [hσ] at this ⊢
      cases val with
      | denotable d =>
        cases d with
        | kontClosure _ _ oa =>
          obtain ⟨used, usedVars, hc⟩ := this
          exact ⟨used, usedVars, hc.extend_kont ak (.kontLink next) h_fresh⟩
        | _ => exact True.intro
      | kontLink => exact True.intro

/-- Combined store invariant -/
structure FreshInvariant (σ : TStore) : Prop where
  names : NamesDistinct σ
  konts : KontAddrDistinct σ
  wf_store : WellFormedStore σ
  chain_wf : StoreChainWF σ

/-! ## Freshness Definitions -/

/-- All addresses at time t are fresh -/
def TimeFresh (σ : TStore) (t : Time) : Prop :=
  ∀ a, a.time = t → σ a = none

/-- Call-descendant fresh: no address at any descendant of (l :: t.tk, t.tmk) -/
def CallDescFresh (σ : TStore) (t : Time) (l : Label) : Prop :=
  ∀ a, Descendant ⟨l :: t.tk, t.tmk⟩ a.time → σ a = none

/-- Handler-descendant fresh: no address at any descendant of (tk, (l, t.tk) :: t.tmk) -/
def HandlerDescFresh (σ : TStore) (t : Time) (l : Label) : Prop :=
  ∀ a tk, Descendant ⟨tk, (l, t.tk) :: t.tmk⟩ a.time → σ a = none

/-- DescendantVia-fresh: unifies CallDescFresh and HandlerDescFresh -/
def DescFresh (σ : TStore) (t : Time) (l : Label) : Prop :=
  ∀ a, DescendantVia t l a.time → σ a = none

theorem DescFresh.toCallDescFresh (h : DescFresh σ t l) : CallDescFresh σ t l :=
  fun a ha => h a (Or.inl ha)

theorem DescFresh.toHandlerDescFresh (h : DescFresh σ t l) : HandlerDescFresh σ t l :=
  fun a tk ha => h a (Or.inr ⟨tk, ha⟩)

theorem DescFresh.of_cdf_hdf (hc : CallDescFresh σ t l) (hh : HandlerDescFresh σ t l) :
    DescFresh σ t l := by
  intro a ha; rcases ha with hc' | ⟨tk, hh'⟩
  · exact hc a hc'
  · exact hh a tk hh'

theorem DescFresh.of_allDescFresh (h : ∀ a, Descendant t a.time → a.time ≠ t → σ a = none)
    (l : Label) : DescFresh σ t l :=
  fun a hvia => h a hvia.toDescendant hvia.ne

theorem DescFresh.extend_val {σ : TStore} {t : Time} {l : Label}
    (h : DescFresh σ t l) {x : Var} {s : TStorable} :
    DescFresh (σ.extend (.val ⟨x, t⟩) s) t l := by
  intro a ha
  have hne : (.val ⟨x, t⟩ : TAddr) ≠ a := by
    intro heq; subst heq; simp [TAddr.time] at ha
    exact ha.ne rfl
  rw [TStore.extend_ne _ _ _ _ (Ne.symm hne)]
  exact h a ha

theorem DescFresh.foldl_val {σ : TStore} {t : Time} {l : Label}
    (h : DescFresh σ t l) {pairs : List (Var × TDenotable)} :
    DescFresh (pairs.foldl (fun s (x, d) =>
      s.extend (.val ⟨x, t⟩) (.denotable d)) σ) t l := by
  induction pairs generalizing σ with
  | nil => exact h
  | cons p ps ih =>
    simp only [List.foldl_cons]
    exact ih h.extend_val

/-! ## Freshness from Scoping -/

theorem fresh_of_not_descendant (hinv : ScopedStore σ t)
    (hnd : ¬ Descendant t t') :
    σ (.val ⟨x, t'⟩) = none := by
  by_contra h
  exact hnd (hinv (.val ⟨x, t'⟩) h)

/-! ## Descendant Preservation Through Store Extension -/

theorem ScopedStore.extend_at_descendant
    (h : ScopedStore σ t_root) (hd : Descendant t_root t_write)
    (addr : TAddr) (s : TStorable) (ha : addr.time = t_write) :
    ScopedStore (σ.extend addr s) t_root := by
  intro a h_ne
  by_cases heq : a = addr
  · subst heq; rw [ha]; exact hd
  · rw [TStore.extend_ne σ addr a s heq] at h_ne
    exact h a h_ne

theorem ScopedStore.foldl_extend_val
    (h : ScopedStore σ t_root)
    (hd : Descendant t_root t_alloc)
    (pairs : List (Var × TDenotable)) :
    ScopedStore (pairs.foldl (fun s (x, d) =>
      s.extend (.val ⟨x, t_alloc⟩) (.denotable d)) σ) t_root := by
  induction pairs generalizing σ with
  | nil => exact h
  | cons p ps ih =>
    simp only [List.foldl_cons]
    exact ih (h.extend_at_descendant hd (.val ⟨p.1, t_alloc⟩) (.denotable p.2) rfl)

/-! ## Shared Utility Lemmas -/

theorem Descendant.of_tk_suffix {tk₁ tk₂ : KTime} {tmk : MKTime}
    (h : tk₁ <:+ tk₂) : Descendant ⟨tk₁, tmk⟩ ⟨tk₂, tmk⟩ := by
  obtain ⟨pfx, hpfx⟩ := h; subst hpfx
  induction pfx with
  | nil => exact .refl
  | cons l ls ih => exact .call l ih

theorem Descendant.of_tmk_suffix {tmk₁ tmk₂ : MKTime} (h : tmk₁ <:+ tmk₂) (tk : KTime) :
    ∃ tk₀, Descendant ⟨tk₀, tmk₁⟩ ⟨tk, tmk₂⟩ := by
  obtain ⟨entries, hentries⟩ := h; subst hentries
  induction entries generalizing tk with
  | nil => exact ⟨tk, .refl⟩
  | cons entry rest ih =>
    obtain ⟨l, k⟩ := entry
    obtain ⟨tk₀, hd⟩ := ih k
    exact ⟨tk₀, .appKont l tk hd⟩

/-- If tmk is a strict suffix of t.tmk, extract the entry immediately above tmk.
    That is: t.tmk = pfx ++ (l_e, tk_e) :: tmk for some pfx, l_e, tk_e. -/
theorem tmk_strict_suffix_entry {tmk : MKTime} {t_tmk : MKTime}
    (h_suf : tmk <:+ t_tmk) (h_ne : t_tmk ≠ tmk) :
    ∃ l_e tk_e, (l_e, tk_e) :: tmk <:+ t_tmk := by
  obtain ⟨pfx, h_pfx⟩ := h_suf
  have h_pfx_ne : pfx ≠ [] := fun h => h_ne (by rw [← h_pfx, h]; simp)
  induction pfx using List.reverseRecOn with
  | nil => exact absurd rfl h_pfx_ne
  | append_singleton init last =>
    obtain ⟨l_e, tk_e⟩ := last
    exact ⟨l_e, tk_e, init, by rw [← h_pfx, List.append_assoc]; rfl⟩

theorem not_descendant_of_call_ext {t : Time} {l : Label} :
    ¬ Descendant ⟨l :: t.tk, t.tmk⟩ t := by
  intro hd; exact absurd (hd.tk_suffix_of_same_tmk rfl) (by
    intro ⟨pfx, hp⟩; have := congr_arg List.length hp; simp at this; omega)

theorem not_descendant_of_handler_ext {t : Time} {l : Label} {tk : KTime} :
    ¬ Descendant ⟨tk, (l, t.tk) :: t.tmk⟩ t := by
  intro hd; exact absurd hd.tmk_suffix (by
    intro ⟨pfx, hp⟩; have := congr_arg List.length hp; simp at this; omega)

@[simp] theorem val_extend_preserves_kont {σ : TStore} {x : Var} {t_w : Time} {s : TStorable}
    (k : TKAddr) : (σ.extend (.val ⟨x, t_w⟩) s) (.kont k) = σ (.kont k) :=
  TStore.extend_ne _ _ _ _ (by simp)

theorem val_extend_preserves_non_desc {σ : TStore} {x : Var} {t_w : Time} {s : TStorable}
    {a : TAddr} (hnd : ¬ Descendant t_w a.time) :
    (σ.extend (.val ⟨x, t_w⟩) s) a = σ a := by
  apply TStore.extend_ne
  intro heq; subst heq; exact hnd (by simp [TAddr.time]; exact .refl)

@[simp] theorem val_extend_preserves_val_ne {σ : TStore} {x y : Var} {t : Time} {s : TStorable}
    (hne : x ≠ y) : (σ.extend (.val ⟨y, t⟩) s) (.val ⟨x, t⟩) = σ (.val ⟨x, t⟩) :=
  TStore.extend_ne _ _ _ _ (by simp [hne])

@[simp] theorem kont_extend_preserves_val {σ : TStore} {k : TKAddr} {s : TStorable}
    (x : Var) (t_v : Time) : (σ.extend (.kont k) s) (.val ⟨x, t_v⟩) = σ (.val ⟨x, t_v⟩) :=
  TStore.extend_ne _ _ _ _ (by simp)

theorem kont_extend_preserves_non_desc {σ : TStore} {k : TKAddr} {s : TStorable}
    {a : TAddr} (hnd : ¬ Descendant ⟨k.frame.time.tk, k.frame.time.tmk⟩ a.time) :
    (σ.extend (.kont k) s) a = σ a := by
  apply TStore.extend_ne
  intro heq; subst heq; simp [TAddr.time] at hnd; exact hnd .refl

theorem foldl_val_preserves_val_notin {σ : TStore} {t_w : Time}
    {pairs : List (Var × TDenotable)} {x : Var}
    (hx : x ∉ pairs.map Prod.fst) :
    (pairs.foldl (fun s (xd : Var × TDenotable) =>
      s.extend (.val ⟨xd.1, t_w⟩) (.denotable xd.2)) σ) (.val ⟨x, t_w⟩) = σ (.val ⟨x, t_w⟩) := by
  induction pairs generalizing σ with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons, List.map_cons, List.mem_cons, not_or] at hx ⊢
    rw [ih hx.2]; exact val_extend_preserves_val_ne hx.1

theorem foldl_val_preserves_non_desc {σ : TStore} {t_w : Time}
    {pairs : List (Var × TDenotable)} {a : TAddr} (hnd : ¬ Descendant t_w a.time) :
    (pairs.foldl (fun s (x, d) =>
      s.extend (.val ⟨x, t_w⟩) (.denotable d)) σ) a = σ a := by
  induction pairs generalizing σ with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rw [ih]; exact val_extend_preserves_non_desc hnd

theorem foldl_val_preserves_kont {σ : TStore} {t_w : Time}
    {pairs : List (Var × TDenotable)} (k : TKAddr) :
    (pairs.foldl (fun s (x, d) =>
      s.extend (.val ⟨x, t_w⟩) (.denotable d)) σ) (.kont k) = σ (.kont k) := by
  induction pairs generalizing σ with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.foldl_cons]
    rw [ih]; exact val_extend_preserves_kont k

theorem CallDescFresh.extend_val {σ : TStore} {t : Time} {l : Label}
    (h : CallDescFresh σ t l) {x : Var} {s : TStorable} :
    CallDescFresh (σ.extend (.val ⟨x, t⟩) s) t l := by
  intro a ha
  have : (.val ⟨x, t⟩ : TAddr) ≠ a := by
    intro heq; subst heq; simp [TAddr.time] at ha
    exact not_descendant_of_call_ext ha
  rw [TStore.extend_ne _ _ _ _ (Ne.symm this)]
  exact h a ha

theorem HandlerDescFresh.extend_val {σ : TStore} {t : Time} {l : Label}
    (h : HandlerDescFresh σ t l) {x : Var} {s : TStorable} :
    HandlerDescFresh (σ.extend (.val ⟨x, t⟩) s) t l := by
  intro a tk ha
  have : (.val ⟨x, t⟩ : TAddr) ≠ a := by
    intro heq; subst heq; simp [TAddr.time] at ha
    exact not_descendant_of_handler_ext ha
  rw [TStore.extend_ne _ _ _ _ (Ne.symm this)]
  exact h a tk ha

theorem CallDescFresh.foldl_val {σ : TStore} {t : Time} {l : Label}
    (h : CallDescFresh σ t l) {pairs : List (Var × TDenotable)} :
    CallDescFresh (pairs.foldl (fun s (x, d) =>
      s.extend (.val ⟨x, t⟩) (.denotable d)) σ) t l := by
  induction pairs generalizing σ with
  | nil => exact h
  | cons p ps ih =>
    simp only [List.foldl_cons]
    exact ih h.extend_val

theorem HandlerDescFresh.foldl_val {σ : TStore} {t : Time} {l : Label}
    (h : HandlerDescFresh σ t l) {pairs : List (Var × TDenotable)} :
    HandlerDescFresh (pairs.foldl (fun s (x, d) =>
      s.extend (.val ⟨x, t⟩) (.denotable d)) σ) t l := by
  induction pairs generalizing σ with
  | nil => exact h
  | cons p ps ih =>
    simp only [List.foldl_cons]
    exact ih h.extend_val

/-! ## FreshInvariant Lemmas -/

theorem FreshInvariant.pairwiseChain_of_lookup (h : FreshInvariant σ)
    {a : TAddr} {hdl : Handler} {ρ : TEnv} {oa : Option TKAddr}
    (h_lookup : σ a = some (.denotable (.kontClosure hdl ρ oa))) :
    ∃ used usedVars, PairwiseChain σ oa used usedVars := by
  have := h.chain_wf a; simp [h_lookup] at this; exact this

theorem FreshInvariant.extend_val (h : FreshInvariant σ) (a_v : TVAddr) (s : TStorable)
    (h_wf : WellFormedStorable s)
    (h_s_chain : ∀ hdl ρ oa, s = .denotable (.kontClosure hdl ρ oa) →
      ∃ used usedVars, PairwiseChain σ oa used usedVars) :
    FreshInvariant (σ.extend (.val a_v) s) :=
  ⟨names_distinct_extend_val h.names a_v s,
   kont_distinct_extend_val h.konts a_v s,
   wellFormedStore_extend h.wf_store _ s h_wf,
   h.chain_wf.extend_val a_v s h_s_chain⟩

theorem FreshInvariant.extend_kont (h : FreshInvariant σ) (a_k : TKAddr) (next : Option TKAddr)
    (h_no_conflict : ∀ k : TKAddr, k.frame.time = a_k.frame.time →
      k.frame.label = a_k.frame.label →
      k.frame.content.isLetFrame = a_k.frame.content.isLetFrame →
      σ (.kont k) = none) :
    FreshInvariant (σ.extend (.kont a_k) (.kontLink next)) := by
  have h_fresh := h_no_conflict a_k rfl rfl rfl
  refine ⟨?_, ?_, wellFormedStore_extend h.wf_store _ _ trivial, ?_⟩
  · intro a₁ a₂ ht hn ha₁ ha₂
    have lift : ∀ a : TVAddr, (σ.extend (.kont a_k) (.kontLink next)) (.val a) ≠ none → σ (.val a) ≠ none := by
      intro a h; rw [TStore.extend_ne _ _ _ _ (by simp)] at h; exact h
    exact h.names a₁ a₂ ht hn (lift a₁ ha₁) (lift a₂ ha₂)
  · exact kont_distinct_extend_kont h.konts a_k _ h_no_conflict
  · exact h.chain_wf.extend_kont_link a_k next h_fresh

/-! ## evalTAtomic Helpers -/

theorem pairwiseChain_of_evalTAtomic
    (h_chain : StoreChainWF σ)
    (h_eval : evalTAtomic ae ρ σ = some (.kontClosure hdl ρ' oa)) :
    ∃ used usedVars, PairwiseChain σ oa used usedVars := by
  unfold evalTAtomic at h_eval
  split at h_eval
  case h_1 x =>
    cases h_bind : Finmap.lookup x ρ with
    | none => rw [h_bind] at h_eval; simp at h_eval
    | some a =>
      rw [h_bind] at h_eval; simp at h_eval
      cases h_store : σ (TAddr.val a) with
      | none => rw [h_store] at h_eval; simp at h_eval
      | some s =>
        rw [h_store] at h_eval; simp at h_eval
        cases s with
        | denotable dd =>
          simp at h_eval; subst h_eval
          have := h_chain (.val a); simp [h_store] at this; exact this
        | kontLink => simp at h_eval
  case h_2 xs body => simp at h_eval
  case h_3 => simp at h_eval
  case h_4 x =>
    cases h_bind : Finmap.lookup x ρ with
    | none => simp [h_bind] at h_eval
    | some a => simp [h_bind] at h_eval; cases h_store : σ (.val a) with
      | none => simp [h_store] at h_eval
      | some s => simp [h_store] at h_eval; cases s with
        | denotable d => simp at h_eval
        | kontLink => simp at h_eval

theorem wellFormedStorable_of_evalTAtomic
    (h_wf_store : WellFormedStore σ)
    (h_wf_ae : ∀ (xs : List Var) (body : Exp), ae = AExp.lam xs body →
      WellFormedProgram body ∧ Disjoint xs.toFinset body.topAllocVars ∧ xs.Nodup)
    (h_eval : evalTAtomic ae ρ σ = some d) :
    WellFormedStorable (TStorable.denotable d) := by
  unfold evalTAtomic at h_eval
  split at h_eval
  case h_1 x =>
    cases h_bind : Finmap.lookup x ρ with
    | none => rw [h_bind] at h_eval; simp at h_eval
    | some a =>
      rw [h_bind] at h_eval; simp at h_eval
      cases h_store : σ (TAddr.val a) with
      | none => rw [h_store] at h_eval; simp at h_eval
      | some s =>
        rw [h_store] at h_eval; simp at h_eval
        cases s with
        | denotable dd =>
          simp at h_eval; subst h_eval
          exact wellFormedStorable_of_store_lookup h_wf_store h_store
        | kontLink => simp at h_eval
  case h_2 xs body =>
    split_ifs at h_eval with h_nd
    · simp at h_eval; subst h_eval; exact h_wf_ae xs body rfl
  case h_3 c =>
    simp at h_eval; subst h_eval; trivial
  case h_4 x =>
    cases h_bind : Finmap.lookup x ρ with
    | none => rw [h_bind] at h_eval; simp at h_eval
    | some a =>
      rw [h_bind] at h_eval; simp at h_eval
      cases h_store : σ (TAddr.val a) with
      | none => rw [h_store] at h_eval; simp at h_eval
      | some s =>
        rw [h_store] at h_eval; simp at h_eval
        cases s with
        | denotable _ => simp at h_eval; subst h_eval; trivial
        | kontLink => simp at h_eval

/-! ## WriteBound -/

/-- WriteBound tracks WHAT was written at time t (vars/labels) and WHERE
    descendant writes went (through descLabels via DescendantVia). -/
def WriteBound (σ σ' : TStore) (t : Time) (vars : Finset Var)
    (letLabels : Finset Label) (handlerLabels : Finset Label)
    (descLabels : Finset Label) : Prop :=
  ∀ a, σ' a ≠ σ a →
    (a.time = t →
      (∃ x, a = .val ⟨x, t⟩ ∧ x ∈ vars) ∨
      (∃ k, a = .kont k ∧ k.frame.content.isLetFrame = true ∧ k.frame.label ∈ letLabels) ∨
      (∃ k, a = .kont k ∧ k.frame.content.isLetFrame = false ∧ k.frame.label ∈ handlerLabels)) ∧
    (a.time ≠ t → ∃ l ∈ descLabels, DescendantVia t l a.time)

theorem WriteBound.descendant (h : WriteBound σ σ' t vars letLabels handlerLabels descLabels)
    {a : TAddr} (ha : σ' a ≠ σ a) : Descendant t a.time := by
  by_cases heq : a.time = t
  · rw [heq]; exact .refl
  · obtain ⟨_, hdv⟩ := h a ha; obtain ⟨l, _, hlv⟩ := hdv heq; exact hlv.toDescendant

theorem WriteBound.val_fresh (h : WriteBound σ σ' t vars letLabels handlerLabels descLabels)
    {x : Var} (hx : x ∉ vars) (hfresh : σ (.val ⟨x, t⟩) = none) :
    σ' (.val ⟨x, t⟩) = none := by
  by_contra h_ne; push Not at h_ne
  have ⟨h_at_t, _⟩ := h (.val ⟨x, t⟩) (by rw [ne_eq]; intro heq; rw [heq] at h_ne; exact h_ne hfresh)
  rcases h_at_t rfl with ⟨x', hx_eq, hx_mem⟩ | ⟨k, hk_eq, _⟩ | ⟨k, hk_eq, _⟩
  · cases hx_eq; exact hx hx_mem
  · cases hk_eq
  · cases hk_eq

theorem WriteBound.let_kont_fresh (h : WriteBound σ σ' t vars letLabels handlerLabels descLabels)
    {k : TKAddr} (hk : k.frame.time = t) (hlet : k.frame.content.isLetFrame = true)
    (hl : k.frame.label ∉ letLabels) (hfresh : σ (.kont k) = none) :
    σ' (.kont k) = none := by
  by_contra h_ne; push Not at h_ne
  have ⟨h_at_t, _⟩ := h (.kont k) (by rw [ne_eq]; intro heq; rw [heq] at h_ne; exact h_ne hfresh)
  rcases h_at_t hk with ⟨x, hx_eq, _⟩ | ⟨k', hk_eq, _, hk_mem⟩ | ⟨k', hk_eq, hk_handler, _⟩
  · cases hx_eq
  · cases hk_eq; exact hl hk_mem
  · cases hk_eq; rw [hlet] at hk_handler; cases hk_handler

theorem WriteBound.kont_fresh (h : WriteBound σ σ' t vars letLabels handlerLabels descLabels)
    {k : TKAddr} (hk : k.frame.time = t) (hl_let : k.frame.label ∉ letLabels)
    (hl_handler : k.frame.label ∉ handlerLabels) (hfresh : σ (.kont k) = none) :
    σ' (.kont k) = none := by
  by_contra h_ne; push Not at h_ne
  have ⟨h_at_t, _⟩ := h (.kont k) (by rw [ne_eq]; intro heq; rw [heq] at h_ne; exact h_ne hfresh)
  rcases h_at_t hk with ⟨x, hx_eq, _⟩ | ⟨k', hk_eq, _, hk_mem⟩ | ⟨k', hk_eq, _, hk_mem⟩
  · cases hx_eq
  · cases hk_eq; exact hl_let hk_mem
  · cases hk_eq; exact hl_handler hk_mem

theorem WriteBound.callDescFresh (h : WriteBound σ σ' t vars letLabels handlerLabels descLabels)
    {l : Label} (hl : l ∉ descLabels) (h_cdf : CallDescFresh σ t l) :
    CallDescFresh σ' t l := by
  intro a ha
  by_contra h_ne; push Not at h_ne
  have h_changed : σ' a ≠ σ a := by rw [h_cdf a ha]; exact h_ne
  have h_ne_t : a.time ≠ t := fun heq => by subst heq; exact not_descendant_of_call_ext ha
  obtain ⟨_, hdv⟩ := h a h_changed
  obtain ⟨l', hl', hlv⟩ := hdv h_ne_t
  exact DescendantVia.disjoint (Or.inl ha) hlv (fun h => hl (h ▸ hl'))

theorem WriteBound.handlerDescFresh (h : WriteBound σ σ' t vars letLabels handlerLabels descLabels)
    {l : Label} (hl : l ∉ descLabels) (h_hdf : HandlerDescFresh σ t l) :
    HandlerDescFresh σ' t l := by
  intro a tk ha
  by_contra h_ne; push Not at h_ne
  have h_changed : σ' a ≠ σ a := by rw [h_hdf a tk ha]; exact h_ne
  have h_ne_t : a.time ≠ t := fun heq => by subst heq; exact not_descendant_of_handler_ext ha
  obtain ⟨_, hdv⟩ := h a h_changed
  obtain ⟨l', hl', hlv⟩ := hdv h_ne_t
  exact DescendantVia.disjoint (Or.inr ⟨tk, ha⟩) hlv (fun h => hl (h ▸ hl'))

theorem WriteBound.descFresh (h : WriteBound σ σ' t vars letLabels handlerLabels descLabels)
    {l : Label} (hl : l ∉ descLabels) (h_df : DescFresh σ t l) :
    DescFresh σ' t l := by
  intro a ha
  by_contra h_ne; push Not at h_ne
  have h_changed : σ' a ≠ σ a := by rw [h_df a ha]; exact h_ne
  have h_ne_t : a.time ≠ t := fun heq => by subst heq; exact ha.ne rfl
  obtain ⟨_, hdv⟩ := h a h_changed
  obtain ⟨l', hl', hlv⟩ := hdv h_ne_t
  exact DescendantVia.disjoint ha hlv (fun h => hl (h ▸ hl'))

theorem WriteBound.trans (h₁ : WriteBound σ σ₁ t V₁ LL₁ HL₁ DL₁) (h₂ : WriteBound σ₁ σ' t V₂ LL₂ HL₂ DL₂) :
    WriteBound σ σ' t (V₁ ∪ V₂) (LL₁ ∪ LL₂) (HL₁ ∪ HL₂) (DL₁ ∪ DL₂) := by
  intro a ha
  by_cases h_eq : σ₁ a = σ a
  · have ha₂ : σ' a ≠ σ₁ a := by rw [h_eq]; exact ha
    have ⟨hat, hdv⟩ := h₂ a ha₂
    exact ⟨fun h => (hat h).elim3
      (fun ⟨x, hx, hm⟩ => Or.inl ⟨x, hx, Finset.mem_union_right _ hm⟩)
      (fun ⟨k, hk, hlet, hm⟩ => Or.inr (Or.inl ⟨k, hk, hlet, Finset.mem_union_right _ hm⟩))
      (fun ⟨k, hk, hhdl, hm⟩ => Or.inr (Or.inr ⟨k, hk, hhdl, Finset.mem_union_right _ hm⟩)),
     fun hne => let ⟨l, hl, hlv⟩ := hdv hne; ⟨l, Finset.mem_union_right _ hl, hlv⟩⟩
  · have ⟨hat, hdv⟩ := h₁ a h_eq
    exact ⟨fun h => (hat h).elim3
      (fun ⟨x, hx, hm⟩ => Or.inl ⟨x, hx, Finset.mem_union_left _ hm⟩)
      (fun ⟨k, hk, hlet, hm⟩ => Or.inr (Or.inl ⟨k, hk, hlet, Finset.mem_union_left _ hm⟩))
      (fun ⟨k, hk, hhdl, hm⟩ => Or.inr (Or.inr ⟨k, hk, hhdl, Finset.mem_union_left _ hm⟩)),
     fun hne => let ⟨l, hl, hlv⟩ := hdv hne; ⟨l, Finset.mem_union_left _ hl, hlv⟩⟩

theorem WriteBound.mono (h : WriteBound σ σ' t V LL HL DL) (hv : V ⊆ V') (hll : LL ⊆ LL')
    (hhl : HL ⊆ HL') (hdl : DL ⊆ DL') :
    WriteBound σ σ' t V' LL' HL' DL' := by
  intro a ha
  have ⟨hat, hdv⟩ := h a ha
  exact ⟨fun h => (hat h).elim3
    (fun ⟨x, hx, hm⟩ => Or.inl ⟨x, hx, hv hm⟩)
    (fun ⟨k, hk, hlet, hm⟩ => Or.inr (Or.inl ⟨k, hk, hlet, hll hm⟩))
    (fun ⟨k, hk, hhdl, hm⟩ => Or.inr (Or.inr ⟨k, hk, hhdl, hhl hm⟩)),
   fun hne => let ⟨l, hlm, hlv⟩ := hdv hne; ⟨l, hdl hlm, hlv⟩⟩

theorem WriteBound.refl : WriteBound σ σ t V LL HL DL :=
  fun _ h => absurd rfl h

theorem WriteBound.tmk_suffix (h : WriteBound σ σ' t V LL HL DL)
    {a : TAddr} (ha : σ' a ≠ σ a) : t.tmk <:+ a.time.tmk :=
  (h.descendant ha).tmk_suffix

end DMCFA
