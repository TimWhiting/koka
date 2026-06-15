/-
  FreshConcrete: Combined Concrete → TNaive → TStrict Proof

  Transforms the Freshness simulation proof (TNaive → TStrict) into a combined
  proof that also does Concrete → TNaive correspondence. Same mutual induction,
  same freshness threading, but with concrete derivation inputs and
  correspondence outputs added.

  Key structural insights (inherited from Freshness):
  - PairwiseChain includes frame labels → DL ⊆ chainLabels ∪ {frame.label} works for all cases
  - diff_tk carries explicit bridge label (may differ from frame.label)
  - tk_suffix_comparable unifies same/diff tmk suffix arguments
  - P_handle has dual context (Case A: per-label DescFresh, Case B: full timestamp fresh)
  - All predicates output chain bounds (labels, vars, tk suffix, bridge)
-/

import DMCFA.FreshnessLemmas
import DMCFA.Correspondence
import DMCFA.Semantics
import DMCFA.Lemmas
import DMCFA.TimestampedToFresh

set_option maxHeartbeats 800000

namespace DMCFA

/-! ## WellNamed/WellLabeled Decomposition Helpers -/

theorem fc_ne_of_mem_of_not_mem {α : Type*} [DecidableEq α] {x y : α} {S : Finset α}
    (hx : x ∈ S) (hy : y ∉ S) : x ≠ y :=
  fun h => hy (h ▸ hx)

theorem fc_wellNamedProgram_letE_y_notin_body {y : Var} {ce : CExp} {e : Exp} {l : Label}
    (h : WellNamedProgram (.letE y ce e l)) : y ∉ e.topAllocVars := by
  cases h; assumption

/-! ## findOp/findBranch membership helpers -/

private lemma fc_findSome_mem {l : List (OpName × Var × Exp)} {op : OpName} {x : Var} {e : Exp}
    (h : l.findSome? (fun (op', x, e) => if op' = op then some (x, e) else none) = some (x, e)) :
    (op, x, e) ∈ l := by
  induction l with
  | nil => simp [List.findSome?] at h
  | cons p ps ih =>
    obtain ⟨op', x', e'⟩ := p
    simp only [List.findSome?] at h
    split at h
    · next heq => cases h; simp_all
    · exact List.mem_cons_of_mem _ (ih h)

lemma fc_findOp_mem {hdl : Handler} {op : OpName} {x : Var} {e : Exp}
    (hfind : Handler.findOp hdl op = some (x, e)) :
    (op, x, e) ∈ hdl.opClauses := by
  simp only [Handler.findOp] at hfind
  exact fc_findSome_mem hfind

private lemma fc_findBranch_mem {bs : List Branch} {c : ConLabel} {xs : List Var} {e : Exp}
    (h : findBranch bs c = some (xs, e)) :
    ∃ b ∈ bs, b = Branch.branch c xs e := by
  induction bs with
  | nil => simp [findBranch, List.findSome?] at h
  | cons b bs ih =>
    cases b with
    | branch c' xs' e' =>
      simp only [findBranch, List.findSome?] at h
      split at h
      · simp_all
      · next hne =>
        obtain ⟨b, hb_mem, hb_eq⟩ := ih h
        exact ⟨b, List.mem_cons_of_mem _ hb_mem, hb_eq⟩

/-! ## Subset/membership lemmas for match/handler -/

/-- Branch handlerLabels ⊆ branchListHandlerLabels for any branch in the list -/
private lemma fc_branch_handlerLabels_subset_branchListHandlerLabels {b : Branch} {bs : List Branch}
    (h_mem : b ∈ bs) : b.handlerLabels ⊆ branchListHandlerLabels bs := by
  induction bs with
  | nil => simp at h_mem
  | cons hd tl ih =>
    simp only [branchListHandlerLabels]
    cases List.mem_cons.mp h_mem with
    | inl h => subst h; exact Finset.subset_union_left
    | inr h => exact Finset.Subset.trans (ih h) Finset.subset_union_right

lemma fc_match_body_handlerLabels_subset {bs : List Branch} {c : ConLabel} {xs : List Var} {e : Exp}
    (h : findBranch bs c = some (xs, e)) : e.handlerLabels ⊆ (CExp.matchE ae bs).handlerLabels := by
  obtain ⟨b, hb_mem, hb_eq⟩ := fc_findBranch_mem h; subst hb_eq
  simp only [CExp.handlerLabels]
  exact Finset.Subset.trans (by simp [Branch.handlerLabels])
    (fc_branch_handlerLabels_subset_branchListHandlerLabels hb_mem)

lemma fc_match_body_allLabels_subset {bs : List Branch} {c : ConLabel} {xs : List Var} {e : Exp}
    (h : findBranch bs c = some (xs, e)) : e.allLabels ⊆ (CExp.matchE ae bs).allLabels := by
  obtain ⟨b, hb_mem, hb_eq⟩ := fc_findBranch_mem h; subst hb_eq
  simp [CExp.allLabels]
  exact Finset.Subset.trans (by simp [Branch.allLabels])
    (branch_allLabels_subset_branchListLabels hb_mem)

private lemma fc_branch_topAllocVars_subset_list {b : Branch} {bs : List Branch}
    (h_mem : b ∈ bs) : b.topAllocVars ⊆ branchListAllocVars bs := by
  induction bs with
  | nil => simp at h_mem
  | cons hd tl ih =>
    simp only [branchListAllocVars]
    cases List.mem_cons.mp h_mem with
    | inl h => subst h; exact Finset.subset_union_left
    | inr h => exact Finset.Subset.trans (ih h) Finset.subset_union_right

lemma fc_match_body_topAllocVars_subset {bs : List Branch} {c : ConLabel} {xs : List Var} {e : Exp}
    (h : findBranch bs c = some (xs, e)) : e.topAllocVars ⊆ (CExp.matchE ae bs).topAllocVars := by
  obtain ⟨b, hb_mem, hb_eq⟩ := fc_findBranch_mem h; subst hb_eq
  simp only [CExp.topAllocVars]
  exact Finset.Subset.trans (branch_body_topAllocVars_subset c xs e)
    (fc_branch_topAllocVars_subset_list hb_mem)

lemma fc_match_xbind_mem_topAllocVars {bs : List Branch} {c : ConLabel} {x : Var} {e : Exp}
    (h : findBranch bs c = some ([x], e)) : x ∈ (CExp.matchE ae bs).topAllocVars := by
  obtain ⟨b, hb_mem, hb_eq⟩ := fc_findBranch_mem h; subst hb_eq
  simp only [CExp.topAllocVars]
  exact fc_branch_topAllocVars_subset_list hb_mem
    (show x ∈ (Branch.branch c [x] e).topAllocVars by simp [Branch.topAllocVars])

lemma fc_handler_xret_mem_topAllocVars (hdl : Handler) :
    hdl.returnClause.1 ∈ hdl.topAllocVars := by
  cases hdl with | mk ret ops =>
    obtain ⟨x, e⟩ := ret; simp [Handler.topAllocVars]

lemma fc_handler_resume_mem_topAllocVars (hdl : Handler) :
    "resume" ∈ hdl.topAllocVars := by
  cases hdl with | mk ret ops =>
    obtain ⟨x, e⟩ := ret; simp [Handler.topAllocVars]

private lemma fc_x_mem_opClauseListAllocVars {ops : List (OpName × Var × Exp)}
    {op : OpName} {x : Var} {e : Exp}
    (h_mem : (op, x, e) ∈ ops) : x ∈ opClauseListAllocVars ops := by
  induction ops with
  | nil => simp at h_mem
  | cons hd tl ih =>
    obtain ⟨op', x', e'⟩ := hd
    simp only [opClauseListAllocVars]
    cases List.mem_cons.mp h_mem with
    | inl heq =>
      have : x = x' := by
        have := congr_arg (fun p : OpName × Var × Exp => p.2.1) heq; simpa using this
      subst this; exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_insert_self _ _))
    | inr h => exact Finset.mem_union_right _ (ih h)

lemma fc_handler_op_x_mem_topAllocVars {hdl : Handler} {op : OpName} {x : Var} {e : Exp}
    (h_mem : (op, x, e) ∈ hdl.opClauses) : x ∈ hdl.topAllocVars := by
  cases hdl with | mk ret ops =>
    obtain ⟨x_ret, e_ret⟩ := ret; simp only [Handler.topAllocVars]
    exact Finset.mem_union_right _ (fc_x_mem_opClauseListAllocVars h_mem)

lemma fc_handler_op_allLabels_sub {hdl : Handler} {op : OpName} {x : Var} {e : Exp}
    (h_mem : (op, x, e) ∈ hdl.opClauses) : e.allLabels ⊆ hdl.allLabels :=
  handler_op_allLabels_subset h_mem

private lemma fc_e_handlerLabels_subset_opClauseListHandlerLabels
    {ops : List (OpName × Var × Exp)} {op : OpName} {x : Var} {e : Exp}
    (h_mem : (op, x, e) ∈ ops) : e.handlerLabels ⊆ opClauseListHandlerLabels ops := by
  induction ops with
  | nil => simp at h_mem
  | cons hd tl ih =>
    obtain ⟨op', x', e'⟩ := hd
    simp only [opClauseListHandlerLabels]
    cases List.mem_cons.mp h_mem with
    | inl heq =>
      have : e = e' := by have := congr_arg (fun p : OpName × Var × Exp => p.2.2) heq; simpa using this
      subst this; exact Finset.subset_union_left
    | inr h => exact Finset.Subset.trans (ih h) Finset.subset_union_right

lemma fc_handler_op_handlerLabels_sub {hdl : Handler} {op : OpName} {x : Var} {e : Exp}
    (h_mem : (op, x, e) ∈ hdl.opClauses) : e.handlerLabels ⊆ hdl.handlerLabels := by
  cases hdl with | mk ret ops =>
    obtain ⟨x_ret, e_ret⟩ := ret
    simp only [Handler.handlerLabels]
    exact Finset.Subset.trans (fc_e_handlerLabels_subset_opClauseListHandlerLabels h_mem)
      Finset.subset_union_right

private theorem fc_foldl_val_preserves_fi {σ : TStore} {t_w : Time}
    {pairs : List (Var × TDenotable)}
    (hinv : FreshInvariant σ)
    (h_wf : ∀ p ∈ pairs, WellFormedStorable (.denotable p.2))
    (h_chain : ∀ p ∈ pairs, ∀ hdl ρ oa, p.2 = .kontClosure hdl ρ oa →
      ∃ used usedVars, PairwiseChain σ oa used usedVars) :
    FreshInvariant (pairs.foldl (fun s (xd : Var × TDenotable) =>
      s.extend (.val ⟨xd.1, t_w⟩) (.denotable xd.2)) σ) := by
  induction pairs generalizing σ with
  | nil => exact hinv
  | cons p ps ih =>
    simp only [List.foldl_cons]
    exact ih (hinv.extend_val ⟨p.1, t_w⟩ _ (h_wf p (List.Mem.head _))
        (fun hdl ρ oa heq => by
          have := TStorable.denotable.inj heq
          obtain ⟨used, usedVars, hc⟩ := h_chain p (List.Mem.head _) hdl ρ oa this
          exact ⟨used, usedVars, hc⟩))
      (fun q hq => h_wf q (List.Mem.tail _ hq))
      (fun q hq hdl ρ oa heq =>
        let ⟨used, usedVars, hc⟩ := h_chain q (List.Mem.tail _ hq) hdl ρ oa heq
        ⟨used, usedVars, hc.extend_val ⟨p.1, t_w⟩ _⟩)

/-! ## Atomic Correspondence -/

/-- Concrete evalAtomic corresponds to TNaive evalTAtomic under EnvCorr + StoreCorr -/
private theorem fc_evalAtomic_corr {α : VAddr → TVAddr} {ρ : Env} {tρ : TEnv}
    {σ : Store} {tσ : TStore}
    (h_env : EnvCorr α ρ tρ) (h_envR : EnvReflects α ρ tρ) (h_store : StoreCorr α tσ σ)
    {ae : AExp} {d : Denotable} (h_eval : evalAtomic ae ρ σ = some d) :
    ∃ td, evalTAtomic ae tρ tσ = some td ∧ DenotableCorr α tσ d td := by
  cases ae with
  | var x =>
    simp only [evalAtomic] at h_eval
    cases hρ : ρ x with
    | none => simp [hρ] at h_eval
    | some a =>
      simp [hρ] at h_eval
      have htρ := h_env x a hρ
      obtain ⟨td, htσ, hcorr⟩ := h_store a d h_eval
      exact ⟨td, by simp only [evalTAtomic]; simp [htρ, htσ], hcorr⟩
  | lam xs body =>
    simp only [evalAtomic] at h_eval; split_ifs at h_eval with h_nd
    · injection h_eval with h_eval; subst h_eval
      exact ⟨.closure ⟨xs, body, tρ, h_nd⟩, by simp [evalTAtomic, h_nd], DenotableCorr.closure ⟨rfl, rfl, h_env, h_envR⟩⟩
  | con c =>
    simp only [evalAtomic] at h_eval; injection h_eval with h_eval; subst h_eval
    exact ⟨.conLabel c, by simp [evalTAtomic], DenotableCorr.conLabel⟩
  | succE x =>
    simp only [evalAtomic] at h_eval
    cases hρ : ρ x with
    | none => simp [hρ] at h_eval
    | some a =>
      simp [hρ] at h_eval
      cases hσ : σ a with
      | none => simp [hσ] at h_eval
      | some d_inner =>
        simp [hσ] at h_eval; subst h_eval
        have htρ := h_env x a hρ
        obtain ⟨td_inner, htσ, _⟩ := h_store a d_inner hσ
        exact ⟨.succVal (α a), by simp only [evalTAtomic]; simp [htρ, htσ], DenotableCorr.succVal⟩

/-! ## Helper lemmas -/

private theorem fc_mem_snd_of_mem_zip {α β : Type*} {a : α} {b : β}
    {xs : List α} {ys : List β} (h : (a, b) ∈ xs.zip ys) : b ∈ ys := by
  induction xs generalizing ys with
  | nil => simp at h
  | cons _ _ ih =>
    cases ys with
    | nil => simp at h
    | cons y ys => simp at h; exact h.elim (fun ⟨_, h⟩ => h ▸ .head _) (fun h => .tail _ (ih h))

/-! ## Chain Bound Type Alias -/

/-- Chain bound output: PairwiseChain + label bound + tk suffix + bridge label.
    `boundLabels` is the tight set for label disjointness (excludes l_enc).
    `bridgeLabels` is the wider set for bridge membership (includes l_enc). -/
def FCChainBound (σ : TStore) (v : TValue) (t : Time)
    (boundLabels bridgeLabels : Finset Label) (boundVars : Finset Var := ∅) : Prop :=
  ∀ op args oa, v = .suspended op args oa →
    ∃ used usedVars, PairwiseChain σ oa used usedVars ∧
      (∀ a', oa = some a' → a'.frame.time.tk = t.tk → used ⊆ boundLabels) ∧
      (∀ a', oa = some a' → a'.frame.time.tk = t.tk → usedVars ⊆ boundVars) ∧
      (∀ a', oa = some a' → t.tk <:+ a'.frame.time.tk) ∧
      (∀ a', oa = some a' → a'.frame.time.tk ≠ t.tk →
        ∃ l_bridge ∈ bridgeLabels, (l_bridge :: t.tk) <:+ a'.frame.time.tk)

/-! ## Foldl extend utility lemmas for multi-arg allocation -/

/-- Store.extend foldl preserves existing non-none entries -/
private theorem foldl_store_extend_mono (σ : Store) (pairs : List (VAddr × Denotable)) :
    ∀ a, σ a ≠ none → (pairs.foldl (fun s (p : VAddr × Denotable) => s.extend p.1 p.2) σ) a ≠ none := by
  induction pairs generalizing σ with
  | nil => exact fun a h => h
  | cons p ps ih =>
    intro a ha
    apply ih
    simp only [Store.extend]; split
    · exact nofun
    · exact ha

/-- AlphaExtends for foldl-based alpha: α' agrees with α on addresses alive in σ
    (because α' only changes at fresh addresses not in σ) -/
private theorem foldl_alpha_extends (α : VAddr → TVAddr) (σ_c : Store) (t_new : Time)
    (xs : List Var) (as_v : List VAddr)
    (h_fresh : ∀ a ∈ as_v, σ_c a = none)
    (h_len : as_v.length = xs.length) :
    AlphaExtends α
      ((xs.zip as_v).foldl (fun f (p : Var × VAddr) => fun a' => if a' = p.2 then ⟨p.1, t_new⟩ else f a') α)
      σ_c := by
  intro a ha
  -- Generalize: for any β that agrees with α at a, the foldl result agrees too
  suffices ∀ (β : VAddr → TVAddr) (xs' : List Var) (as' : List VAddr),
      (∀ a' ∈ as', σ_c a' = none) → as'.length = xs'.length → β a = α a →
      (xs'.zip as').foldl (fun f (p : Var × VAddr) => fun a'' => if a'' = p.2 then ⟨p.1, t_new⟩ else f a'') β a = α a from
    this α xs as_v h_fresh h_len rfl
  intro β xs' as' h_fr h_ln hβ
  induction xs' generalizing as' β with
  | nil => match as', h_ln with | [], _ => simpa using hβ
  | cons x xs'' ih =>
    match as', h_ln with
    | a_v :: as'', h_ln' =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      exact ih (fun a'' => if a'' = a_v then ⟨x, t_new⟩ else β a'') as''
        (fun a' h' => h_fr a' (.tail _ h'))
        (by simp at h_ln'; exact h_ln')
        (by simp [show a ≠ a_v from fun heq => by subst heq; exact ha (h_fr _ (.head _))]; exact hβ)

/-- EnvScoped for foldl-extended env and store -/
private theorem foldl_envScoped_extend (ρ : Env) (σ : Store)
    (xs : List Var) (as_v : List VAddr) (ds : List Denotable)
    (h_scope : EnvScoped ρ σ)
    (h_len_xv : as_v.length = xs.length)
    (h_len_vd : as_v.length ≤ ds.length) :
    EnvScoped
      ((xs.zip as_v).foldl (fun r (p : Var × VAddr) => r.extend p.1 p.2) ρ)
      ((as_v.zip ds).foldl (fun s (p : VAddr × Denotable) => s.extend p.1 p.2) σ) := by
  induction xs generalizing as_v ds ρ σ with
  | nil =>
    match as_v, h_len_xv with
    | [], _ => exact h_scope
  | cons x xs' ih =>
    match as_v, h_len_xv, ds, h_len_vd with
    | a :: as', h_len', d :: ds', h_len_vd' =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      exact ih (ρ.extend x a) (σ.extend a d) as' ds'
        (fun x' a' hxa' => by
          simp only [Env.extend] at hxa'; split at hxa'
          · injection hxa' with hxa'; subst hxa'
            simp only [Store.extend, ite_true]; exact nofun
          · simp only [Store.extend]; split
            · exact nofun
            · exact h_scope _ _ hxa')
        (by simp at h_len'; exact h_len')
        (by simp at h_len_vd'; omega)

/-- StoreScoped for foldl-extended store -/
private theorem foldl_storeScoped_extend (σ : Store)
    (as_v : List VAddr) (ds : List Denotable)
    (h_ss : StoreScoped σ)
    (_h_fresh : List.Forall₂ (fun a (_ : Denotable) => σ a = none) as_v ds)
    (h_ds_scoped : ∀ d ∈ ds, DenotableScoped d σ) :
    StoreScoped ((as_v.zip ds).foldl (fun s (p : VAddr × Denotable) => s.extend p.1 p.2) σ) := by
  -- Suffices to show: for any σ₀ that is StoreScoped and where all ds are scoped,
  -- foldl extend preserves StoreScoped (regardless of freshness)
  suffices ∀ (σ₀ : Store) (as' : List VAddr) (ds' : List Denotable),
      StoreScoped σ₀ → (∀ d ∈ ds', DenotableScoped d σ₀) →
      StoreScoped ((as'.zip ds').foldl (fun s (p : VAddr × Denotable) => s.extend p.1 p.2) σ₀) from
    this σ as_v ds h_ss (fun d hd => h_ds_scoped d hd)
  intro σ₀ as' ds'
  induction as' generalizing ds' σ₀ with
  | nil => intro h _; exact h
  | cons a_hd as_tl ih =>
    match ds' with
    | [] => intro h _; simp [List.zip]; exact h
    | d_hd :: ds_tl =>
      intro h_ss₀ h_ds
      simp only [List.zip_cons_cons, List.foldl_cons]
      have h_mono : ∀ a', σ₀ a' ≠ none → (σ₀.extend a_hd d_hd) a' ≠ none := by
        intro a' ha'; simp only [Store.extend]; split <;> [exact nofun; exact ha']
      exact ih (σ₀.extend a_hd d_hd) ds_tl
        (storeScoped_extend h_ss₀ (denotableScoped_mono (h_ds d_hd (.head _)) h_mono))
        (fun d' hd' => denotableScoped_mono (h_ds d' (.tail _ hd')) h_mono)

/-- DenotableCorr is preserved when α and tσ are extended at fresh addresses.
    Requires the denotable to be scoped in σ_c (all referenced addresses alive). -/
private theorem fc_denotableCorr_of_alpha_extends_fresh
    {α α' : VAddr → TVAddr} {tσ tσ' : TStore} {σ_c : Store}
    {d : Denotable} {td : TDenotable}
    (h : DenotableCorr α tσ d td)
    (h_ext_α : ∀ a, σ_c a ≠ none → α' a = α a)
    (h_ext_tσ : ∀ a, tσ a ≠ none → tσ' a = tσ a)
    (h_scoped : DenotableScoped d σ_c) :
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

/-- Single-step correspondence: extending α, σ, tσ, ρ, tρ with one (x, a_v, d, td) -/
private theorem single_step_correspondence
    {α : VAddr → TVAddr} {tσ : TStore} {σ : Store}
    {ρ : Env} {tρ : TEnv} {t_new : Time}
    {x : Var} {a_v : VAddr} {d : Denotable} {td : TDenotable}
    (h_env : EnvCorr α ρ tρ)
    (h_envR : EnvReflects α ρ tρ)
    (h_store : StoreCorr α tσ σ)
    (h_refl : StoreReflects α tσ σ)
    (h_ss : StoreScoped σ)
    (h_corr : DenotableCorr α tσ d td)
    (h_fresh_c : σ a_v = none)
    (h_fresh_t : tσ (.val ⟨x, t_new⟩) = none)
    (h_inj : ∀ a, σ a ≠ none → α a ≠ ⟨x, t_new⟩)
    (h_d_scoped : DenotableScoped d σ)
    (h_env_scoped : EnvScoped ρ σ) :
    let α' := fun a => if a = a_v then (⟨x, t_new⟩ : TVAddr) else α a
    let tσ' := tσ.extend (.val ⟨x, t_new⟩) (.denotable td)
    let σ' := σ.extend a_v d
    EnvCorr α' (ρ.extend x a_v) (tρ.extend x ⟨x, t_new⟩) ∧
    EnvReflects α' (ρ.extend x a_v) (tρ.extend x ⟨x, t_new⟩) ∧
    StoreCorr α' tσ' σ' ∧
    StoreReflects α' tσ' σ' ∧
    StoreScoped σ' := by
  have h_ext_α : ∀ a, σ a ≠ none → (fun a' => if a' = a_v then (⟨x, t_new⟩ : TVAddr) else α a') a = α a :=
    fun a ha => if_neg (fun heq => by subst heq; exact absurd h_fresh_c ha)
  have h_ext_tσ : ∀ a, tσ a ≠ none → (tσ.extend (.val ⟨x, t_new⟩) (.denotable td)) a = tσ a :=
    fun a ha => TStore.extend_ne _ _ _ _ (by intro heq; rw [heq] at ha; exact absurd h_fresh_t ha)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- EnvCorr: new binding x→a_v trivial, old bindings via a' ≠ a_v
    intro x' a' hxa'
    simp only [Env.extend] at hxa'
    split at hxa'
    · -- x' = x: ρ.extend x a_v x = some a_v, tρ.extend x ⟨x,t_new⟩ x = some ⟨x,t_new⟩, α' a_v = ⟨x,t_new⟩
      rename_i heq; subst heq; injection hxa' with hxa'; subst hxa'
      simp [TEnv.lookup_extend_same]
    · -- x' ≠ x: use h_env and α' a' = α a' (since a' ∈ σ from h_env_scoped)
      rename_i hne
      have ha_ne : a' ≠ a_v := fun heq => by subst heq; exact absurd h_fresh_c (h_env_scoped _ _ hxa')
      rw [TEnv.lookup_extend_ne _ _ _ _ hne]
      have h_αeq : (fun a => if a = a_v then (⟨x, t_new⟩ : TVAddr) else α a) a' = α a' := if_neg ha_ne
      rw [h_αeq]; exact h_env _ _ hxa'
  · -- EnvReflects
    intro x' ta htρ'
    by_cases heq : x' = x
    · subst heq; simp [TEnv.extend] at htρ'; subst htρ'
      exact ⟨a_v, by simp [Env.extend], if_pos rfl⟩
    · rw [TEnv.lookup_extend_ne _ _ _ _ heq] at htρ'
      obtain ⟨a, hρ, hα⟩ := h_envR x' ta htρ'
      exact ⟨a, by simp [Env.extend, heq]; exact hρ,
             show (if a = a_v then _ else _) = ta by
               rw [if_neg (fun h => by subst h; exact absurd h_fresh_c (h_env_scoped _ _ hρ))]; exact hα⟩
  · -- StoreCorr: new entry a_v→d via DenotableCorr, old entries via h_store
    intro a' d' hσ'
    simp only [Store.extend] at hσ'
    split at hσ'
    · -- a' = a_v: new entry
      rename_i heq; subst heq; injection hσ' with hσ'; subst hσ'

      simp only [ite_true]
      exact ⟨td, TStore.extend_same _ _ _, fc_denotableCorr_of_alpha_extends_fresh h_corr h_ext_α h_ext_tσ h_d_scoped⟩
    · -- a' ≠ a_v: old entry
      rename_i hne
      obtain ⟨td', htσ', hd'⟩ := h_store a' d' hσ'
      have h_α_a' : (fun a => if a = a_v then (⟨x, t_new⟩ : TVAddr) else α a) a' = α a' := if_neg hne
      rw [h_α_a']
      have hne_t : TAddr.val (α a') ≠ TAddr.val ⟨x, t_new⟩ := by
        intro heq; exact h_inj a' (by rw [hσ']; exact nofun) (TAddr.val.inj heq)
      exact ⟨td', by rw [TStore.extend_ne _ _ _ _ hne_t]; exact htσ',
        fc_denotableCorr_of_alpha_extends_fresh hd' h_ext_α h_ext_tσ (h_ss _ _ hσ')⟩
  · -- StoreReflects: new ta=⟨x,t_new⟩ via a_v, old ta via h_refl
    intro ta h_ne
    by_cases heq : ta = ⟨x, t_new⟩
    · subst heq; exact ⟨a_v, by simp [Store.extend], if_pos rfl⟩
    · rw [TStore.extend_ne _ _ _ _ (fun h => heq (TAddr.val.inj h))] at h_ne
      obtain ⟨a', ha', hα'⟩ := h_refl ta h_ne
      exact ⟨a', by simp [Store.extend]; split <;> [exact nofun; exact ha'],
        show (if a' = a_v then _ else _) = ta by
          rw [if_neg (fun h => by subst h; exact absurd h_fresh_c ha')]; exact hα'⟩
  · -- StoreScoped
    exact storeScoped_extend h_ss (denotableScoped_mono h_d_scoped
      (fun a' ha' => by simp [Store.extend]; split <;> [exact nofun; exact ha']))

/-- EnvReflects is preserved by a single extension with a fresh allocation,
    where α is updated to map the fresh concrete address to the fresh timestamped one. -/
private theorem fc_envReflects_extend_alpha
    {α : VAddr → TVAddr} {ρ : Env} {tρ : TEnv} {σ : Store}
    {x : Var} {a_v : VAddr} {ta : TVAddr}
    (h_envR : EnvReflects α ρ tρ)
    (h_fresh : σ a_v = none)
    (h_scope : EnvScoped ρ σ) :
    EnvReflects (fun a => if a = a_v then ta else α a) (ρ.extend x a_v) (tρ.extend x ta) := by
  intro y ta' htρ'
  by_cases heq : y = x
  · subst heq; rw [TEnv.lookup_extend_same] at htρ'
    injection htρ' with htρ'; subst htρ'
    exact ⟨a_v, by simp [Env.extend], if_pos rfl⟩
  · rw [TEnv.lookup_extend_ne _ _ _ _ heq] at htρ'
    obtain ⟨a, hρ, hα⟩ := h_envR y ta' htρ'
    have ha_ne : a ≠ a_v := fun heq_av => by
      subst heq_av; exact absurd h_fresh (h_scope _ _ hρ)
    exact ⟨a, by simp [Env.extend, heq]; exact hρ,
      show (if a = a_v then ta else α a) = ta' by rw [if_neg ha_ne]; exact hα⟩

/-- Combined correspondence through parallel foldl: proves EnvCorr, StoreCorr, StoreReflects
    simultaneously for multi-arg allocation. Induction on xs/as_v/ds/tds in parallel. -/
private theorem foldl_correspondence
    {α : VAddr → TVAddr} {tσ : TStore} {σ_c : Store}
    {ρ_lam : Env} {tρ_lam : TEnv} {t_new : Time}
    (h_env : EnvCorr α ρ_lam tρ_lam)
    (h_envR : EnvReflects α ρ_lam tρ_lam)
    (h_store : StoreCorr α tσ σ_c)
    (h_refl : StoreReflects α tσ σ_c)
    (h_store_scoped : StoreScoped σ_c)
    (xs : List Var) (as_v : List VAddr) (ds : List Denotable) (tds : List TDenotable)
    (h_corrs : List.Forall₂ (fun d td => DenotableCorr α tσ d td) ds tds)
    (h_fresh_c : List.Forall₂ (fun a (_ : Denotable) => σ_c a = none) as_v ds)
    (h_fresh_t : ∀ (x : Var), x ∈ xs → tσ (.val ⟨x, t_new⟩) = none)
    (h_inj_c : ∀ a, σ_c a ≠ none → ∀ x ∈ xs, α a ≠ ⟨x, t_new⟩)
    (h_ds_scoped : ∀ d ∈ ds, DenotableScoped d σ_c)
    (h_env_scoped : EnvScoped ρ_lam σ_c)
    (h_xs_nodup : List.Nodup xs)
    (h_as_nodup : List.Nodup as_v)
    (h_len_xv : as_v.length = xs.length)
    (h_len_xd : ds.length = xs.length) :
    let α' := (xs.zip as_v).foldl (fun f (p : Var × VAddr) => fun a => if a = p.2 then ⟨p.1, t_new⟩ else f a) α
    let tσ_new := (xs.zip tds).foldl (fun s (p : Var × TDenotable) => s.extend (.val ⟨p.1, t_new⟩) (.denotable p.2)) tσ
    let σ_new := (as_v.zip ds).foldl (fun s (p : VAddr × Denotable) => s.extend p.1 p.2) σ_c
    let ρ_new := (xs.zip as_v).foldl (fun r (p : Var × VAddr) => r.extend p.1 p.2) ρ_lam
    let tρ_new := xs.foldl (fun r x => r.extend x ⟨x, t_new⟩) tρ_lam
    EnvCorr α' ρ_new tρ_new ∧
    EnvReflects α' ρ_new tρ_new ∧
    StoreCorr α' tσ_new σ_new ∧
    StoreReflects α' tσ_new σ_new := by
  -- Suffices with generalized state for induction
  suffices ∀ (α₀ : VAddr → TVAddr) (tσ₀ : TStore) (σ₀ : Store) (ρ₀ : Env) (tρ₀ : TEnv)
      (xs' : List Var) (as' : List VAddr) (ds' : List Denotable) (tds' : List TDenotable),
      EnvCorr α₀ ρ₀ tρ₀ → EnvReflects α₀ ρ₀ tρ₀ → StoreCorr α₀ tσ₀ σ₀ → StoreReflects α₀ tσ₀ σ₀ → StoreScoped σ₀ → EnvScoped ρ₀ σ₀ →
      List.Forall₂ (fun d td => DenotableCorr α₀ tσ₀ d td) ds' tds' →
      List.Forall₂ (fun a (_ : Denotable) => σ₀ a = none) as' ds' →
      (∀ x, x ∈ xs' → tσ₀ (.val ⟨x, t_new⟩) = none) →
      (∀ a, σ₀ a ≠ none → ∀ x ∈ xs', α₀ a ≠ ⟨x, t_new⟩) →
      (∀ d ∈ ds', DenotableScoped d σ₀) →
      List.Nodup xs' → List.Nodup as' →
      as'.length = xs'.length → ds'.length = xs'.length →
      let α' := (xs'.zip as').foldl (fun f (p : Var × VAddr) => fun a => if a = p.2 then ⟨p.1, t_new⟩ else f a) α₀
      let tσ' := (xs'.zip tds').foldl (fun s (p : Var × TDenotable) => s.extend (.val ⟨p.1, t_new⟩) (.denotable p.2)) tσ₀
      let σ' := (as'.zip ds').foldl (fun s (p : VAddr × Denotable) => s.extend p.1 p.2) σ₀
      let ρ' := (xs'.zip as').foldl (fun r (p : Var × VAddr) => r.extend p.1 p.2) ρ₀
      let tρ' := xs'.foldl (fun r x => r.extend x ⟨x, t_new⟩) tρ₀
      EnvCorr α' ρ' tρ' ∧ EnvReflects α' ρ' tρ' ∧ StoreCorr α' tσ' σ' ∧ StoreReflects α' tσ' σ' from
    this α tσ σ_c ρ_lam tρ_lam xs as_v ds tds h_env h_envR h_store h_refl h_store_scoped
      h_env_scoped h_corrs h_fresh_c h_fresh_t h_inj_c h_ds_scoped h_xs_nodup h_as_nodup h_len_xv h_len_xd
  intro α₀ tσ₀ σ₀ ρ₀ tρ₀ xs' as' ds' tds'
  induction xs' generalizing as' ds' tds' α₀ tσ₀ σ₀ ρ₀ tρ₀ with
  | nil =>
    intro h_e h_eR h_s h_r _ _ _ _ _ _ _ _ _ h_lv h_ld
    match as', h_lv, ds', h_ld, tds' with
    | [], _, [], _, [] => exact ⟨h_e, h_eR, h_s, h_r⟩
    | [], _, [], _, _ :: _ => intro; contradiction
  | cons x xs_tl ih =>
    intro h_e₀ h_eR₀ h_s₀ h_r₀ h_ss₀ h_es₀ h_corrs₀ h_fresh₀ h_ft₀ h_inj₀ h_ds₀ h_nd_xs₀ h_nd_as₀ h_lv₀ h_ld₀
    match as', h_lv₀, ds', h_ld₀ with
    | a_v :: as_tl, h_lv, d_v :: ds_tl, h_ld =>
      cases h_corrs₀ with | cons h_c_hd h_c_tl =>
      rename_i td_v tds_tl
      cases h_fresh₀ with | cons h_f_hd h_f_tl =>
      simp only [List.zip_cons_cons, List.foldl_cons]
      -- Apply single_step_correspondence
      have h_step := single_step_correspondence h_e₀ h_eR₀ h_s₀ h_r₀ h_ss₀ h_c_hd h_f_hd
        (h_ft₀ x (.head _)) (fun a ha => h_inj₀ a ha x (.head _)) (h_ds₀ d_v (.head _))
        h_es₀
      -- Apply IH on tails with updated correspondence
      have h_nd_xs_tl := (List.nodup_cons.mp h_nd_xs₀).2
      have h_x_notin := (List.nodup_cons.mp h_nd_xs₀).1
      have h_nd_as_tl := (List.nodup_cons.mp h_nd_as₀).2
      have h_av_notin := (List.nodup_cons.mp h_nd_as₀).1
      -- Update h_c_tl through single-step extension
      have h_c_tl' : List.Forall₂ (fun d td => DenotableCorr
          (fun a => if a = a_v then ⟨x, t_new⟩ else α₀ a)
          (tσ₀.extend (.val ⟨x, t_new⟩) (.denotable td_v)) d td) ds_tl tds_tl :=
        (by
          have h_ext_α : ∀ a, σ₀ a ≠ none → (fun a' => if a' = a_v then ⟨x, t_new⟩ else α₀ a') a = α₀ a :=
            fun a ha => if_neg (fun heq => by subst heq; exact absurd h_f_hd ha)
          have h_ext_tσ : ∀ a, tσ₀ a ≠ none → (tσ₀.extend (.val ⟨x, t_new⟩) (.denotable td_v)) a = tσ₀ a :=
            fun a ha => TStore.extend_ne _ _ _ _ (by intro heq; rw [heq] at ha; exact absurd (h_ft₀ x (.head _)) ha)
          -- Update each DenotableCorr in tail through single-step extension
          suffices ∀ (ds₁ : List Denotable) (tds₁ : List TDenotable),
              List.Forall₂ (fun d td => DenotableCorr α₀ tσ₀ d td) ds₁ tds₁ →
              (∀ d ∈ ds₁, DenotableScoped d σ₀) →
              List.Forall₂ (fun d td => DenotableCorr (fun a => if a = a_v then ⟨x, t_new⟩ else α₀ a)
                (tσ₀.extend (.val ⟨x, t_new⟩) (.denotable td_v)) d td) ds₁ tds₁ from
            this ds_tl tds_tl h_c_tl (fun d hd => h_ds₀ d (.tail _ hd))
          intro ds₁ tds₁ hf₂ hds
          induction hf₂ with
          | nil => exact .nil
          | cons h_hd _ ih_f =>
            exact .cons (fc_denotableCorr_of_alpha_extends_fresh h_hd h_ext_α h_ext_tσ (hds _ (.head _)))
              (ih_f (fun d hd => hds d (.tail _ hd))))
      -- Update h_f_tl: fresh addresses in extended store
      have h_f_tl' : List.Forall₂ (fun a (_ : Denotable) => (σ₀.extend a_v d_v) a = none) as_tl ds_tl :=
        (by
          suffices ∀ (as₁ : List VAddr) (ds₁ : List Denotable),
              List.Forall₂ (fun a _ => σ₀ a = none) as₁ ds₁ →
              (∀ a ∈ as₁, a ≠ a_v) →
              List.Forall₂ (fun a _ => (σ₀.extend a_v d_v) a = none) as₁ ds₁ from
            this as_tl ds_tl h_f_tl (fun a ha => by
              intro heq; subst heq; exact h_av_notin ha)
          intro as₁ ds₁ hf hne
          induction hf with
          | nil => exact .nil
          | cons h_hd _ ih_f =>
            exact .cons (by simp [Store.extend, show _ ≠ a_v from hne _ (.head _)]; exact h_hd)
              (ih_f (fun a ha => hne a (.tail _ ha))))
      exact ih (fun a => if a = a_v then ⟨x, t_new⟩ else α₀ a)
        (tσ₀.extend (.val ⟨x, t_new⟩) (.denotable td_v))
        (σ₀.extend a_v d_v) (ρ₀.extend x a_v) (tρ₀.extend x ⟨x, t_new⟩)
        as_tl ds_tl tds_tl
        h_step.1 h_step.2.1 h_step.2.2.1 h_step.2.2.2.1 h_step.2.2.2.2
        (fun x' a' hxa' => by
          simp only [Env.extend] at hxa'; split at hxa'
          · rename_i heq; subst heq; cases hxa'; simp [Store.extend]
          · exact foldl_store_extend_mono σ₀ [(a_v, d_v)] a' (h_es₀ _ _ hxa'))
        h_c_tl' h_f_tl'
        (fun x' hx' => by
          show (tσ₀.extend _ _) (.val ⟨x', t_new⟩) = none
          rw [TStore.extend_ne _ _ _ _ (by
            intro heq; have := TAddr.val.inj heq; simp at this
            exact h_x_notin (this ▸ hx'))]
          exact h_ft₀ x' (.tail _ hx'))
        (fun a ha x' hx' => by
          by_cases heq_a : a = a_v
          · -- a = a_v: α₁ a = ⟨x, t_new⟩ ≠ ⟨x', t_new⟩ since x ∉ xs_tl
            subst heq_a
            simp only [ite_true]
            intro heq; simp at heq; exact h_x_notin (heq ▸ hx')
          · -- a ≠ a_v: α₁ a = α₀ a, use h_inj₀
            simp only [show (a = a_v) = False from propext ⟨heq_a, False.elim⟩, ite_false]
            have ha' : σ₀ a ≠ none := by
              simp only [Store.extend] at ha; rw [if_neg heq_a] at ha; exact ha
            exact h_inj₀ a ha' x' (.tail _ hx'))
        (fun d' hd' => denotableScoped_mono (h_ds₀ d' (.tail _ hd'))
          (fun a' ha' => by simp only [Store.extend]; split <;> [exact nofun; exact ha']))
        h_nd_xs_tl h_nd_as_tl
        (by simp at h_lv; exact h_lv)
        (by simp at h_ld; exact h_ld)

/-- If evalAtomic returns a denotable and the store is scoped, the denotable is scoped -/
private lemma evalAtomic_denotableScoped {ae : AExp} {ρ : Env} {σ : Store} {d : Denotable}
    (h_eval : evalAtomic ae ρ σ = some d) (h_scope : EnvScoped ρ σ) (h_ss : StoreScoped σ) :
    DenotableScoped d σ := by
  cases ae with
  | var x =>
    simp only [evalAtomic] at h_eval
    cases h_ρ : ρ x with
    | none => simp [h_ρ] at h_eval
    | some a =>
      simp [h_ρ] at h_eval
      cases h_σ : σ a with
      | none => simp [h_σ] at h_eval
      | some d' => simp [h_σ] at h_eval; subst h_eval; exact h_ss _ _ h_σ
  | lam xs body =>
    simp only [evalAtomic] at h_eval; split_ifs at h_eval with h_nd
    · cases h_eval; exact h_scope
  | con c => simp only [evalAtomic] at h_eval; cases h_eval; trivial
  | succE x =>
    simp only [evalAtomic] at h_eval
    cases h_ρ : ρ x with
    | none => simp [h_ρ] at h_eval
    | some a =>
      simp [h_ρ] at h_eval
      cases h_σ : σ a with
      | none => simp [h_σ] at h_eval
      | some d' => simp [h_σ] at h_eval; cases h_eval; exact h_scope _ _ h_ρ

/-! ## Generalized completeness: concrete ⟹ fresh-guarded timestamped

  For arbitrary intermediate configurations with corresponding stores:
  if (e, ρ, σ) ⇓e (v, σ') and the program is well-formed, then
  ∃ α' tv tσ', (e, tρ, tσ, t) ⇓et_f (tv, tσ') with v ~α' tv and σ' ~α' tσ'.

  Proved by mutual strong induction on concrete derivation height.
  Simultaneously constructs both a naive timestamped derivation (⇓et)
  and a fresh-guarded derivation (⇓et_f), threading the freshness invariant
  and write bounds needed for continuation restoration. -/

theorem fresh_concrete (isHandlerLabel : Label → Prop)
    (h_handlerLabels_consistent : ∀ (h : Handler), ∀ l ∈ h.handlerLabels, isHandlerLabel l)
    (h_label_kind_sound : ∀ l, isHandlerLabel l →
      ∀ (e : Exp), WellLabeledProgram e → l ∈ e.allLabels → l ∈ e.handlerLabels)
    (n : Nat) :
    -- P_exp: Concrete → TNaive + TStrict + Correspondence + Freshness
    (∀ (e : Exp) (ρ_c : Env) (σ_c : Store) (v_c : Value) (σ_c' : Store),
       EvalExpN n e ρ_c σ_c v_c σ_c' →
       WellFormedProgram e →
       -- Correspondence inputs
       ∀ (α : VAddr → TVAddr) (tρ : TEnv) (tσ : TStore) (t : Time),
       EnvCorr α ρ_c tρ →
       EnvReflects α ρ_c tρ →
       StoreCorr α tσ σ_c →
       StoreReflects α tσ σ_c →
       EnvScoped ρ_c σ_c →
       StoreScoped σ_c →
       -- Freshness inputs (on tσ)
       FreshInvariant tσ →
       (∀ x ∈ e.topAllocVars, tσ (.val ⟨x, t⟩) = none) →
       (∀ l ∈ e.allLabels, ∀ k : TKAddr, k.frame.time = t → k.frame.label = l → tσ (.kont k) = none) →
       (∀ l ∈ e.allLabels, CallDescFresh tσ t l) →
       (∀ l ∈ e.handlerLabels, HandlerDescFresh tσ t l) →
       -- Outputs: existential timestamped quantities + correspondence + freshness
       ∃ (α' : VAddr → TVAddr) (tv : TValue) (tσ' : TStore),
         -- TNaive derivation
         TEvalExpN n e tρ tσ t tv tσ' ∧
         -- TStrict derivation
         TFreshEvalExpN n e tρ tσ t tv tσ' ∧
         -- Correspondence outputs
         ValueCorr α' tσ' v_c tv ∧
         StoreCorr α' tσ' σ_c' ∧
         StoreReflects α' tσ' σ_c' ∧
         AlphaExtends α α' σ_c ∧
         -- Freshness outputs
         WellFormedValue6 tσ' tv ∧
         FreshInvariant tσ' ∧
         WriteBound tσ tσ' t e.topAllocVars e.allLabels e.allLabels e.allLabels ∧
         FCChainBound tσ' tv t e.allLabels e.allLabels e.topAllocVars ∧
         ValueScoped v_c σ_c' ∧
         StoreScoped σ_c') ∧
    -- P_cexp: Concrete → TNaive + TStrict + Correspondence + Freshness
    (∀ (ce : CExp) (ρ_c : Env) (σ_c : Store) (v_c : Value) (σ_c' : Store)
       (l_enc : Label),
       EvalCExpN n ce ρ_c σ_c v_c σ_c' →
       WellLabeledSubCExp ce →
       WellNamedSubCExp ce →
       -- Correspondence inputs
       ∀ (α : VAddr → TVAddr) (tρ : TEnv) (tσ : TStore) (t : Time),
       EnvCorr α ρ_c tρ →
       EnvReflects α ρ_c tρ →
       StoreCorr α tσ σ_c →
       StoreReflects α tσ σ_c →
       EnvScoped ρ_c σ_c →
       StoreScoped σ_c →
       -- Freshness inputs (on tσ)
       FreshInvariant tσ →
       (∀ x ∈ ce.topAllocVars, tσ (.val ⟨x, t⟩) = none) →
       (∀ k : TKAddr, k.frame.time = t → k.frame.label = l_enc → tσ (.kont k) = none) →
       (∀ l ∈ ce.allLabels, ∀ k : TKAddr, k.frame.time = t → k.frame.label = l → tσ (.kont k) = none) →
       l_enc ∉ ce.allLabels →
       (∀ l ∈ ce.allLabels, CallDescFresh tσ t l) →
       CallDescFresh tσ t l_enc →
       (ce.isHandlerCExp → HandlerDescFresh tσ t l_enc) →
       (∀ l ∈ ce.handlerLabels, HandlerDescFresh tσ t l) →
       (isHandlerLabel l_enc → ce.isHandlerCExp = true) →
       -- Outputs
       ∃ (α' : VAddr → TVAddr) (tv : TValue) (tσ' : TStore),
         TEvalCExpN n ce tρ tσ t l_enc tv tσ' ∧
         TFreshEvalCExpN n ce tρ tσ t l_enc tv tσ' ∧
         ValueCorr α' tσ' v_c tv ∧
         StoreCorr α' tσ' σ_c' ∧
         StoreReflects α' tσ' σ_c' ∧
         AlphaExtends α α' σ_c ∧
         WellFormedValue6 tσ' tv ∧
         FreshInvariant tσ' ∧
         WriteBound tσ tσ' t ce.topAllocVars ce.allLabels ({l_enc} ∪ ce.allLabels) ({l_enc} ∪ ce.allLabels) ∧
         FCChainBound tσ' tv t ce.allLabels (({l_enc} : Finset Label) ∪ ce.allLabels) ce.topAllocVars ∧
         ValueScoped v_c σ_c' ∧
         StoreScoped σ_c') ∧
    -- P_continue: Concrete → TNaive + TStrict + Correspondence + Freshness
    (∀ (frame_c : Frame) (v_c : Value) (σ_c : Store) (v_c' : Value) (σ_c' : Store)
       (l_enc : Label) (fc : TFrameContent) (t_f : Time)
       (frameVars : Finset Var) (frameLabels : Finset Label),
       ContinueFrameN n frame_c v_c σ_c v_c' σ_c' →
       -- Correspondence inputs
       ∀ (α : VAddr → TVAddr) (tv : TValue) (tσ : TStore),
       FrameCorr α frame_c fc →
       ValueCorr α tσ v_c tv →
       StoreCorr α tσ σ_c →
       StoreReflects α tσ σ_c →
       (∀ clo, frame_c = .letFrame clo → EnvScoped clo.env σ_c) →
       StoreScoped σ_c →
       ValueScoped v_c σ_c →
       -- Freshness inputs (on tσ)
       WellFormedValue6 tσ tv →
       FreshInvariant tσ →
       (∀ (clo : TClosure), fc = .letFrame clo → WellFormedProgram clo.body) →
       (∀ y (e : Exp) ρ, fc = .letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩ → tσ (.val ⟨y, t_f⟩) = none) →
       (∀ k : TKAddr, k.frame.time = t_f → k.frame.label = l_enc →
         k.frame.content.isLetFrame = true → tσ (.kont k) = none) →
       (∀ y (e : Exp) ρ, fc = .letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩ → y ∉ e.topAllocVars) →
       (∀ y (e : Exp) ρ, fc = .letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩ →
         ∀ x ∈ e.topAllocVars, tσ (.val ⟨x, t_f⟩) = none) →
       (∀ y (e : Exp) ρ, fc = .letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩ →
         ∀ l ∈ e.allLabels, ∀ k : TKAddr, k.frame.time = t_f → k.frame.label = l → tσ (.kont k) = none) →
       (∀ y (e : Exp) ρ, fc = .letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩ →
         ∀ l ∈ e.allLabels, CallDescFresh tσ t_f l) →
       (∀ y (e : Exp) ρ, fc = .letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩ →
         ∀ l ∈ e.handlerLabels, HandlerDescFresh tσ t_f l) →
       (∀ clo, fc = .letFrame clo → l_enc ∉ clo.body.allLabels) →
       -- Chain label disjoint (at same tk)
       (∀ clo, fc = .letFrame clo →
         ∀ op args oa, tv = .suspended op args oa →
           ∀ used usedVars, PairwiseChain tσ oa used usedVars →
             ∀ a', oa = some a' → a'.frame.time.tk = t_f.tk →
               Disjoint clo.body.allLabels used) →
       -- Chain var disjoint (at same tk)
       (∀ clo, fc = .letFrame clo →
         ∀ op args oa, tv = .suspended op args oa →
           ∀ used usedVars, PairwiseChain tσ oa used usedVars →
             ∀ a', oa = some a' → a'.frame.time.tk = t_f.tk →
               ∀ y, clo.params = [y] →
                 Disjoint ({y} ∪ clo.body.topAllocVars) usedVars) →
       -- Chain tk suffix
       (∀ op args oa, tv = .suspended op args oa →
         ∀ a', oa = some a' → t_f.tk <:+ a'.frame.time.tk) →
       -- Bridge label (at different tk)
       (∀ (clo : TClosure), fc = .letFrame clo →
         ∀ op args oa, tv = .suspended op args oa →
           ∀ a', oa = some a' → a'.frame.time.tk ≠ t_f.tk →
             ∃ l_bridge ∈ frameLabels, l_bridge ∉ clo.body.allLabels ∧
               (l_bridge :: t_f.tk) <:+ a'.frame.time.tk) →
       -- CExp-side labels for PairwiseChain construction at continue_op
       (∀ clo, fc = .letFrame clo →
         ∀ op args oa, tv = .suspended op args oa →
           ∃ ceLabels : Finset Label,
             Disjoint ceLabels clo.body.allLabels ∧
             l_enc ∉ ceLabels ∧
             (∀ used usedVars, PairwiseChain tσ oa used usedVars →
               ∀ a', oa = some a' → a'.frame.time.tk = t_f.tk →
                 used ⊆ ceLabels) ∧
             (∀ a', oa = some a' → a'.frame.time.tk = t_f.tk →
               a'.frame.label ∈ ceLabels) ∧
             ceLabels ⊆ frameLabels) →
       -- Frame vars/labels bound
       (∀ y (e : Exp) ρ, fc = .letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩ →
         {y} ∪ e.topAllocVars ⊆ frameVars) →
       (∀ y (e : Exp) ρ, fc = .letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩ →
         e.allLabels ⊆ frameLabels) →
       (∀ (clo : TClosure), fc = .letFrame clo → {l_enc} ⊆ frameLabels) →
       -- Frame bounds (generalized, for continue_op)
       (∀ (clo : TClosure), fc = .letFrame clo → clo.body.allLabels ⊆ frameLabels) →
       (∀ (clo : TClosure), fc = .letFrame clo → clo.params.toFinset ∪ clo.body.topAllocVars ⊆ frameVars) →
       -- Inner chain var bound (for continue_op same_tk)
       (∀ clo, fc = .letFrame clo →
         ∀ op args oa, tv = .suspended op args oa →
           ∀ used usedVars, PairwiseChain tσ oa used usedVars →
             ∀ a', oa = some a' → a'.frame.time.tk = t_f.tk →
               usedVars ⊆ frameVars) →
       -- Outputs
       ∃ (α' : VAddr → TVAddr) (tv' : TValue) (tσ' : TStore),
         TContinueFrameN n l_enc fc t_f tv tσ tv' tσ' ∧
         TFreshContinueFrameN n l_enc fc t_f tv tσ tv' tσ' ∧
         ValueCorr α' tσ' v_c' tv' ∧
         StoreCorr α' tσ' σ_c' ∧
         StoreReflects α' tσ' σ_c' ∧
         AlphaExtends α α' σ_c ∧
         WellFormedValue6 tσ' tv' ∧
         FreshInvariant tσ' ∧
         (∃ frameDescLabels, frameDescLabels ⊆ frameLabels ∧ l_enc ∉ frameDescLabels ∧
           WriteBound tσ tσ' t_f frameVars frameLabels frameLabels frameDescLabels) ∧
         FCChainBound tσ' tv' t_f frameLabels ({l_enc} ∪ frameLabels) frameVars ∧
         ValueScoped v_c' σ_c' ∧
         StoreScoped σ_c') ∧
    -- P_handle: Concrete → TNaive + TStrict + Correspondence + Freshness
    (∀ (hdl : Handler) (ρ_c : Env) (v_c : Value) (σ_c : Store)
       (v_c' : Value) (σ_c' : Store)
       (l_enc : Label) (ρ_handler : TEnv) (t : Time),
       HandleValueN n hdl ρ_c v_c σ_c v_c' σ_c' →
       WellFormedSubHandler hdl →
       -- Correspondence inputs
       ∀ (α : VAddr → TVAddr) (tv : TValue) (tσ : TStore),
       EnvCorr α ρ_c ρ_handler →
       EnvReflects α ρ_c ρ_handler →
       ValueCorr α tσ v_c tv →
       StoreCorr α tσ σ_c →
       StoreReflects α tσ σ_c →
       EnvScoped ρ_c σ_c →
       StoreScoped σ_c →
       ValueScoped v_c σ_c →
       -- Freshness inputs (on tσ)
       WellFormedValue6 tσ tv →
       FreshInvariant tσ →
       (∀ x ∈ hdl.topAllocVars, tσ (.val ⟨x, t⟩) = none) →
       (∀ l ∈ hdl.allLabels, ∀ k : TKAddr, k.frame.time = t → k.frame.label = l → tσ (.kont k) = none) →
       (∀ k : TKAddr, k.frame.time = t → k.frame.label = l_enc → tσ (.kont k) = none) →
       (∀ l ∈ hdl.allLabels, CallDescFresh tσ t l) →
       (∀ l ∈ hdl.handlerLabels, HandlerDescFresh tσ t l) →
       l_enc ∉ hdl.handlerLabels →
       -- Outputs
       ∃ (α' : VAddr → TVAddr) (tv' : TValue) (tσ' : TStore),
         THandleValueN n l_enc hdl ρ_handler tv tσ t tv' tσ' ∧
         TFreshHandleValueN n l_enc hdl ρ_handler tv tσ t tv' tσ' ∧
         ValueCorr α' tσ' v_c' tv' ∧
         StoreCorr α' tσ' σ_c' ∧
         StoreReflects α' tσ' σ_c' ∧
         AlphaExtends α α' σ_c ∧
         WellFormedValue6 tσ' tv' ∧
         FreshInvariant tσ' ∧
         WriteBound tσ tσ' t hdl.topAllocVars hdl.allLabels ({l_enc} ∪ hdl.allLabels) hdl.allLabels ∧
         FCChainBound tσ' tv' t ({l_enc} ∪ hdl.allLabels) ({l_enc} ∪ hdl.allLabels) hdl.topAllocVars ∧
         ValueScoped v_c' σ_c' ∧
         StoreScoped σ_c') ∧
    -- P_apply: Concrete → TNaive + TStrict + Correspondence + Freshness
    (∀ (κ_c : Kont) (d_c : Denotable) (σ_c : Store)
       (v_c : Value) (σ_c' : Store)
       (oa_κ : Option TKAddr) (td : TDenotable) (tmk : MKTime)
       (chainLabels : Finset Label) (chainVars : Finset Var),
       ApplyKontN n κ_c d_c σ_c v_c σ_c' →
       -- Correspondence inputs
       ∀ (α : VAddr → TVAddr) (tσ : TStore),
       KontCorr α tσ κ_c oa_κ →
       DenotableCorr α tσ d_c td →
       StoreCorr α tσ σ_c →
       StoreReflects α tσ σ_c →
       StoreScoped σ_c →
       DenotableScoped d_c σ_c →
       KontScoped κ_c σ_c →
       -- Freshness inputs (on tσ)
       WellFormedStorable (.denotable td) →
       (∀ hdl ρ oa, td = .kontClosure hdl ρ oa → ∃ used usedVars, PairwiseChain tσ oa used usedVars) →
       FreshInvariant tσ →
       (∀ a, tmk <:+ a.time.tmk → tσ a = none) →
       PairwiseChain tσ oa_κ chainLabels chainVars →
       -- Outputs
       ∃ (α' : VAddr → TVAddr) (tv : TValue) (tσ' : TStore),
         TApplyKontN n oa_κ td tσ tmk tv tσ' ∧
         TFreshApplyKontN n oa_κ td tσ tmk tv tσ' ∧
         ValueCorr α' tσ' v_c tv ∧
         StoreCorr α' tσ' σ_c' ∧
         StoreReflects α' tσ' σ_c' ∧
         AlphaExtends α α' σ_c ∧
         WellFormedValue6 tσ' tv ∧
         FreshInvariant tσ' ∧
         (∀ a, tσ' a ≠ tσ a → tmk <:+ a.time.tmk) ∧
         -- CallDescFresh preservation
         (∀ a_κ₀, oa_κ = some a_κ₀ →
           ∃ DL : Finset Label, DL ⊆ chainLabels ∧
             ∀ l, l ∉ DL →
               CallDescFresh tσ ⟨a_κ₀.frame.time.tk, tmk⟩ l →
               CallDescFresh tσ' ⟨a_κ₀.frame.time.tk, tmk⟩ l) ∧
         -- HandlerDescFresh preservation
         (∀ a_κ₀, oa_κ = some a_κ₀ →
           ∃ DL : Finset Label, DL ⊆ ({a_κ₀.frame.label} ∪ chainLabels) ∧
             ∀ l, l ∉ DL →
               HandlerDescFresh tσ ⟨a_κ₀.frame.time.tk, tmk⟩ l →
               HandlerDescFresh tσ' ⟨a_κ₀.frame.time.tk, tmk⟩ l) ∧
         -- Scoped Descendant
         (∀ a_κ₀, oa_κ = some a_κ₀ →
           ∀ a, tσ' a ≠ tσ a →
             Descendant ⟨a_κ₀.frame.time.tk, tmk⟩ a.time) ∧
         -- Same-tk writes bounded by chain vars/labels + frame label
         (∀ a_κ₀, oa_κ = some a_κ₀ →
           ∀ a, tσ' a ≠ tσ a → a.time.tk = a_κ₀.frame.time.tk → a.time.tmk = tmk →
             (∃ x, a = .val ⟨x, a.time⟩ ∧ x ∈ chainVars) ∨
             (∃ k, a = .kont k ∧ k.frame.label ∈ ({a_κ₀.frame.label} ∪ chainLabels))) ∧
         -- ChainBound for result value
         FCChainBound tσ' tv ⟨(match oa_κ with | some a => a.frame.time.tk | none => []), tmk⟩
           ((match oa_κ with | some a => {a.frame.label} | none => {}) ∪ chainLabels)
           ((match oa_κ with | some a => {a.frame.label} | none => {}) ∪ chainLabels) chainVars ∧
         ValueScoped v_c σ_c' ∧
         StoreScoped σ_c') := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    -- P_exp
    · intro e ρ_c σ_c v_c σ_c' h_eval h_wf α tρ tσ t
        h_env h_envR h_store h_refl h_scope h_store_scoped hinv h_var_fresh h_kont_fresh h_cdf h_hdf
      cases h_eval with
      | eval_tail h_ce =>
        rename_i n_sub ce l_tail
        -- Decompose well-formedness
        have h_wl_ce : WellLabeledSubCExp ce := by cases h_wf.wl with | tail _ _ h1 _ => exact h1
        have h_wn_ce : WellNamedSubCExp ce := by cases h_wf.wn with | tail _ _ h1 => exact h1
        have h_l_notin_ce : l_tail ∉ ce.allLabels := by cases h_wf.wl with | tail _ _ _ h2 => exact h2
        -- Use P_cexp IH at smaller height
        obtain ⟨_, ih_cexp, _, _, _⟩ := ih n_sub (by omega)
        obtain ⟨α', tv, tσ', h_tn_ce, h_ts_ce, h_val, h_store', h_refl', h_ext,
                h_wfv, h_fi', h_wb, h_cb, h_val_scoped', h_store_scoped'⟩ :=
          ih_cexp ce ρ_c σ_c v_c σ_c' l_tail h_ce h_wl_ce h_wn_ce
            α tρ tσ t h_env h_envR h_store h_refl h_scope h_store_scoped hinv
            (fun x hx => h_var_fresh x (by simp []; exact hx))
            (fun k hk hlk => h_kont_fresh l_tail (by simp []) k hk hlk)
            (fun l hl k hk hlk => h_kont_fresh l (by simp []; exact Or.inr hl) k hk hlk)
            h_l_notin_ce
            (fun l hl => h_cdf l (by simp []; exact Or.inr hl))
            (h_cdf l_tail (by simp []))
            (fun h_is_handler => h_hdf l_tail (by simp [Exp.handlerLabels, h_is_handler]))
            (fun l hl => h_hdf l (by simp [Exp.handlerLabels]; exact Or.inr hl))
            (fun h_hl => by
              by_contra h_neg
              have h_in_hls := h_label_kind_sound l_tail h_hl _ h_wf.wl
                (by simp [])
              simp only [Exp.handlerLabels, Finset.mem_union] at h_in_hls
              have h_not_true : ¬ (ce.isHandlerCExp = true) := h_neg
              rcases h_in_hls with h1 | h2 <;>
                [simp [h_not_true] at h1;
                 exact h_l_notin_ce (CExp.handlerLabels_subset_allLabels ce h2)])
        -- Build outputs
        have h_cb_out : FCChainBound tσ' tv t (Exp.tail ce l_tail).allLabels (Exp.tail ce l_tail).allLabels (Exp.tail ce l_tail).topAllocVars :=
          fun op args oa hv => by
            obtain ⟨used, usedV, hchain, hbound, hvar_bound, htk_suf, h_bridge⟩ := h_cb op args oa hv
            exact ⟨used, usedV, hchain,
              fun a' hoa htk => (hbound a' hoa htk).trans (by simp []),
              fun a' hoa htk => (hvar_bound a' hoa htk).trans (by simp []),
              htk_suf,
              fun a' hoa h_ne_tk => by
                obtain ⟨l_br, h_mem, h_suf⟩ := h_bridge a' hoa h_ne_tk
                have : l_br ∈ (Exp.tail ce l_tail).allLabels := by
                  simp []
                  exact (Finset.mem_union.mp h_mem).elim
                    (fun h => Or.inl (Finset.mem_singleton.mp h))
                    (fun h => Or.inr h)
                exact ⟨l_br, this, h_suf⟩⟩
        exact ⟨α', tv, tσ',
               .eval_tail h_tn_ce,
               .eval_tail h_ts_ce,
               h_val, h_store', h_refl', h_ext,
               h_wfv, h_fi',
               h_wb.mono (by simp [])
                         (by simp [])
                         (by simp [])
                         (by simp []),
               h_cb_out,
               h_val_scoped',
               h_store_scoped'⟩
      | eval_let h_ce h_cont =>
        rename_i n1 ce vce σ₁ n2 y e_body l_let
        have h_wf_body := wellFormedProgram_letE_body h_wf
        have h_wf_ce := wellFormedProgram_letE_ce h_wf
        have h_l_in := letE_label_mem_allLabels y ce e_body l_let
        have h_l_notin_ce := wellLabeled_label_notin_ce (wellLabeledProgram_letE_wl h_wf.wl)
        have h_wl := wellLabeledProgram_letE_wl h_wf.wl
        have h_ce_body_disj := wellLabeled_letE_disjoint h_wl
        have h_l_notin_body := wellLabeled_label_notin_body h_wl
        -- Step 1: Use P_cexp IH on h_ce
        obtain ⟨_, ih_cexp, _, _, _⟩ := ih n1 (by omega)
        obtain ⟨α₁, tv₁, tσ₁, h_tn_ce, h_ts_ce, hval₁, hstore₁, hrefl₁, hext₁,
                h_wfv₁, hfi₁, h_wb_ce, h_cb_ce, h_val_scoped₁, h_store_scoped₁⟩ :=
          ih_cexp ce ρ_c σ_c vce σ₁ l_let h_ce h_wf_ce.wl h_wf_ce.wn
            α tρ tσ t h_env h_envR h_store h_refl h_scope h_store_scoped hinv
            (fun x hx => h_var_fresh x (by
              show x ∈ Exp.topAllocVars (.letE y ce e_body l_let)
              simp only [Exp.topAllocVars]
              exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)))
            (fun k hk hlk => h_kont_fresh l_let h_l_in k hk hlk)
            (fun l hl k hk hlk => h_kont_fresh l (letE_ce_allLabels_subset y ce e_body l_let hl) k hk hlk)
            h_l_notin_ce
            (fun l hl => h_cdf l (letE_ce_allLabels_subset y ce e_body l_let hl))
            (h_cdf l_let h_l_in)
            (fun h_is_handler => h_hdf l_let (by
              simp [Exp.handlerLabels, h_is_handler]))
            (fun l hl => h_hdf l (by
              simp only [Exp.handlerLabels, Finset.mem_union]
              exact Or.inl (Or.inr hl)))
            (fun h_hl => by
              by_contra h_neg
              have h_in_hls := h_label_kind_sound l_let h_hl _ h_wf.wl h_l_in
              simp only [Exp.handlerLabels, Finset.mem_union] at h_in_hls
              have h_not_true : ¬ (ce.isHandlerCExp = true) := h_neg
              cases h_in_hls with
              | inl h1 => simp [h_not_true] at h1; exact h_l_notin_ce (CExp.handlerLabels_subset_allLabels ce h1)
              | inr h2 => exact h_l_notin_body (Exp.handlerLabels_subset_allLabels e_body h2))
        -- Step 2: Propagate freshness through WriteBound for continuation preconditions
        have h_env₁ : EnvCorr α₁ ρ_c tρ := h_env.of_alpha_extends hext₁ h_scope
        have h_y_fresh_σ₁ : tσ₁ (.val ⟨y, t⟩) = none :=
          h_wb_ce.val_fresh (wellNamedProgram_letE_y_notin_ce h_wf.wn)
            (h_var_fresh y (by simp []))
        have h_body_vf_σ₁ : ∀ x ∈ e_body.topAllocVars, tσ₁ (.val ⟨x, t⟩) = none :=
          fun x hx => h_wb_ce.val_fresh
            (Finset.disjoint_right.mp (wellNamedProgram_letE_disjoint h_wf.wn) hx)
            (h_var_fresh x (by simp []; exact Or.inr (Or.inr hx)))
        have h_body_kf_σ₁ : ∀ l ∈ e_body.allLabels, ∀ k : TKAddr,
            k.frame.time = t → k.frame.label = l → tσ₁ (.kont k) = none :=
          fun l hl k hk hlk => h_wb_ce.kont_fresh hk
            (by rw [hlk]; exact Finset.disjoint_right.mp h_ce_body_disj hl)
            (by rw [hlk]; simp only [Finset.mem_union, Finset.mem_singleton, not_or]
                exact ⟨fun h => h_l_notin_body (h ▸ hl), Finset.disjoint_right.mp h_ce_body_disj hl⟩)
            (h_kont_fresh l (letE_body_allLabels_subset y ce e_body l_let hl) k hk hlk)
        have h_body_cdf_σ₁ : ∀ l ∈ e_body.allLabels, CallDescFresh tσ₁ t l :=
          fun l hl => h_wb_ce.callDescFresh
            (by simp only [Finset.mem_union, Finset.mem_singleton, not_or]
                exact ⟨fun h => h_l_notin_body (h ▸ hl), Finset.disjoint_right.mp h_ce_body_disj hl⟩)
            (h_cdf l (letE_body_allLabels_subset y ce e_body l_let hl))
        have h_body_hdf_σ₁ : ∀ l ∈ e_body.handlerLabels, HandlerDescFresh tσ₁ t l :=
          fun l hl => h_wb_ce.handlerDescFresh
            (by have h_in_body := Exp.handlerLabels_subset_allLabels e_body hl
                simp only [Finset.mem_union, Finset.mem_singleton, not_or]
                exact ⟨fun h => h_l_notin_body (h ▸ h_in_body),
                       Finset.disjoint_right.mp h_ce_body_disj h_in_body⟩)
            (h_hdf l (by simp only [Exp.handlerLabels, Finset.mem_union]; exact Or.inr hl))
        -- Step 3: Use P_continue IH on h_cont
        have h_store_mono : ∀ a, σ_c a ≠ none → σ₁ a ≠ none := by
          intro a h_ne h_eq
          cases h_σ : σ_c a with
          | none => exact h_ne h_σ
          | some d =>
            have := eval_cexp_store_mono (eval_cexpN_to h_ce) a d h_σ
            rw [h_eq] at this; exact absurd this (by simp)
        have h_scope₁ : EnvScoped ρ_c σ₁ :=
          fun x a hxa => h_store_mono a (h_scope x a hxa)
        obtain ⟨_, _, ih_cont, _, _⟩ := ih n2 (by omega)
        obtain ⟨α₂, tv₂, tσ₂, h_tn_cont, h_ts_cont, hval₂, hstore₂, hrefl₂, hext₂,
                h_wfv₂, hfi₂, ⟨contDL, contDL_sub, contDL_excl, h_wb_cont⟩, h_cb_cont, h_val_scoped', h_store_scoped'⟩ :=
          ih_cont (Frame.letFrame ⟨[y], e_body, ρ_c, List.nodup_singleton _⟩) vce σ₁ v_c σ_c' l_let
            (.letFrame ⟨[y], e_body, tρ, List.nodup_singleton _⟩) t
            ({y} ∪ ce.topAllocVars ∪ e_body.topAllocVars) ({l_let} ∪ ce.allLabels ∪ e_body.allLabels)
            h_cont
            α₁ tv₁ tσ₁
            (FrameCorr.letFrame ⟨rfl, rfl, h_env₁, h_envR.of_alpha_extends hext₁ h_scope⟩)
            hval₁ hstore₁ hrefl₁
            (fun clo heq => by cases heq; exact h_scope₁)
            h_store_scoped₁
            h_val_scoped₁
            h_wfv₁ hfi₁
            (fun clo heq => by cases heq; exact h_wf_body)
            (fun _ _ _ heq => by cases heq; exact h_y_fresh_σ₁)
            (fun k hk hl hlet => h_wb_ce.let_kont_fresh hk hlet
              (by rw [hl]; exact h_l_notin_ce)
              (h_kont_fresh l_let h_l_in k hk hl))
            (fun _ _ _ heq => by cases heq; exact fc_wellNamedProgram_letE_y_notin_body h_wf.wn)
            (fun _ _ _ heq => by cases heq; exact h_body_vf_σ₁)
            (fun _ _ _ heq => by cases heq; exact h_body_kf_σ₁)
            (fun _ _ _ heq => by cases heq; exact h_body_cdf_σ₁)
            (fun _ _ _ heq => by cases heq; exact h_body_hdf_σ₁)
            (fun clo heq => by cases heq; exact h_l_notin_body)
            -- Chain label disjoint
            (fun clo_arg heq => by
              cases heq
              intro op args oa hsusp used usedV hchain a' hoa htk
              obtain ⟨used₀, usedV₀, hchain₀, hbound₀, _, _, _⟩ := h_cb_ce op args oa hsusp
              have ⟨h_eq_l, _⟩ := hchain.used_unique hchain₀; subst h_eq_l
              have h_sub := hbound₀ a' hoa htk
              exact Finset.disjoint_left.mpr fun l hl =>
                fun h_in_used => Finset.disjoint_left.mp h_ce_body_disj.symm hl (h_sub h_in_used))
            -- Chain var disjoint
            (fun clo_arg heq => by
              cases heq
              intro op args oa hsusp used usedV hchain a' hoa htk y_param hp
              cases hp
              obtain ⟨used₀, usedV₀, hchain₀, _, hvar_bound₀, _, _⟩ := h_cb_ce op args oa hsusp
              have ⟨_, h_vars_eq⟩ := hchain.used_unique hchain₀; subst h_vars_eq
              have h_usedV_sub := hvar_bound₀ a' hoa htk
              have h_y_notin_ce := wellNamedProgram_letE_y_notin_ce h_wf.wn
              have h_ce_body_var_disj : Disjoint ce.topAllocVars e_body.topAllocVars := by
                cases h_wf.wn; assumption
              exact Finset.disjoint_of_subset_right h_usedV_sub
                (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_singleton_left.mpr h_y_notin_ce,
                  h_ce_body_var_disj.symm⟩))
            -- Chain tk suffix
            (fun op args oa hsusp a' hoa => by
              obtain ⟨_, _, _, _, _, htk_suf, _⟩ := h_cb_ce op args oa hsusp
              exact htk_suf a' hoa)
            -- Bridge label
            (fun clo_arg heq_fc op args oa hsusp a' hoa h_ne_tk => by
              cases heq_fc
              obtain ⟨_, _, _, _, _, _, h_bridge⟩ := h_cb_ce op args oa hsusp
              obtain ⟨l_br, h_l_br_mem, h_l_br_suf⟩ := h_bridge a' hoa h_ne_tk
              have h_l_br_notin : l_br ∉ e_body.allLabels := by
                intro hmem
                cases Finset.mem_union.mp h_l_br_mem with
                | inl h => exact h_l_notin_body (Finset.mem_singleton.mp h ▸ hmem)
                | inr h => exact Finset.disjoint_left.mp h_ce_body_disj h hmem
              exact ⟨l_br, Finset.mem_union_left _ h_l_br_mem, h_l_br_notin, h_l_br_suf⟩)
            -- CExp-side labels
            (fun clo_arg heq_fc op args oa hsusp => by
              cases heq_fc
              exact ⟨ce.allLabels,
                h_ce_body_disj,
                h_l_notin_ce,
                fun used usedVars hchain a' hoa htk => by
                  obtain ⟨used₀, usedV₀, hchain₀, hbound₀, _, _, _⟩ := h_cb_ce op args oa hsusp
                  have ⟨h_eq_l, _⟩ := hchain.used_unique hchain₀; subst h_eq_l
                  exact hbound₀ a' hoa htk,
                fun a' hoa htk => by
                  obtain ⟨used₀, usedV₀, hchain₀, hbound₀, _, _, _⟩ := h_cb_ce op args oa hsusp
                  subst hoa
                  exact hbound₀ a' rfl htk (hchain₀.frame_label_mem),
                Finset.subset_union_right.trans Finset.subset_union_left⟩)
            -- Frame vars/labels bound
            (fun _ _ _ heq => by cases heq; exact Finset.union_subset (Finset.subset_union_left.trans Finset.subset_union_left) Finset.subset_union_right)
            (fun _ _ _ heq => by cases heq; exact Finset.subset_union_right)
            (fun _ heq => by cases heq; exact (Finset.subset_union_left).trans Finset.subset_union_left)
            (fun _ heq => by cases heq; exact Finset.subset_union_right)
            (fun _ heq => by cases heq; exact Finset.union_subset (Finset.subset_union_left.trans Finset.subset_union_left) Finset.subset_union_right)
            -- Inner chain var bound
            (fun _ heq op args oa hsusp used usedVars hpc a' hoa htk => by
              cases heq
              obtain ⟨_, usedV₀, hpc₀, _, hvar_bound₀, _, _⟩ := h_cb_ce op args oa hsusp
              have ⟨_, h_eq⟩ := hpc.used_unique hpc₀; subst h_eq
              exact (hvar_bound₀ a' hoa htk).trans ((Finset.subset_insert _ _).trans Finset.subset_union_left))
        -- Step 4: Compose outputs
        have h_cb_out : FCChainBound tσ₂ tv₂ t (Exp.letE y ce e_body l_let).allLabels (Exp.letE y ce e_body l_let).allLabels (Exp.letE y ce e_body l_let).topAllocVars := by
          intro op args oa hv
          obtain ⟨used, usedV, hchain, hbound, hvar_bound, htk_suf, h_bridge⟩ := h_cb_cont op args oa hv
          refine ⟨used, usedV, hchain,
            fun a' hoa htk => (hbound a' hoa htk).trans (by simp []),
            fun a' hoa htk => (hvar_bound a' hoa htk).trans (by simp []),
            htk_suf,
            fun a' hoa h_ne_tk => ?_⟩
          obtain ⟨l_br, h_mem, h_suf⟩ := h_bridge a' hoa h_ne_tk
          refine ⟨l_br, ?_, h_suf⟩
          simp only [Exp.allLabels]
          rcases Finset.mem_union.mp h_mem with h | h
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
          · exact h
        exact ⟨α₂, tv₂, tσ₂,
               .eval_let h_tn_ce h_tn_cont,
               .eval_let h_ts_ce h_ts_cont,
               hval₂, hstore₂, hrefl₂,
               hext₁.trans hext₂ h_store_mono,
               h_wfv₂, hfi₂,
               (h_wb_ce.trans (h_wb_cont.mono (Finset.Subset.refl _) (Finset.Subset.refl _) (Finset.Subset.refl _) contDL_sub)).mono
                 (by simp [])
                 (by simp [])
                 (by simp [])
                 (by simp []),
               h_cb_out,
               h_val_scoped',
               h_store_scoped'⟩
    -- P_cexp
    · intro ce ρ_c σ_c v_c σ_c' l_enc h_eval h_wl h_wn α tρ tσ t h_env h_envR h_store h_refl h_scope h_store_scoped hinv h_var_fresh h_kont_enc_fresh h_kont_fresh h_l_notin_ce h_cdf h_cdf_enc h_hdf_enc h_hdf_sub h_label_kind
      cases h_eval with
      | eval_atomic h_ae =>
        obtain ⟨td, htd, hcorr⟩ := fc_evalAtomic_corr h_env h_envR h_store h_ae
        exact ⟨α, .den td, tσ, .eval_atomic htd, .eval_atomic htd,
               ValueCorr.den hcorr, h_store, h_refl, AlphaExtends.refl,
               ⟨WellFormedValue.of_wellFormedStorable (wellFormedStorable_of_evalTAtomic hinv.wf_store (fun xs body hlam => ⟨wellFormedSubCExp_atomic_ae ⟨h_wl, h_wn⟩ xs body hlam, wellFormedSubCExp_atomic_ae_disjoint ⟨h_wl, h_wn⟩ xs body hlam, wellNamedSubCExp_atomic_ae_nodup h_wn xs body hlam⟩) htd), (fun hdl ρ' oa h => by cases h; exact pairwiseChain_of_evalTAtomic hinv.chain_wf htd), (fun _ _ _ h => by cases h)⟩,
               hinv, WriteBound.refl, (fun op args oa hv => by cases hv),
               show ValueScoped (.den _) _ from evalAtomic_denotableScoped h_ae h_scope h_store_scoped,
               h_store_scoped⟩
      | eval_opApp h_ρ =>
        -- h_ρ : ρ_c x✝ = some a_v✝; v_c = .suspended op✝ [a_v✝] []; σ_c' = σ_c
        -- ce = CExp.opApp op✝ x✝
        have htρ := h_env _ _ h_ρ
        refine ⟨α, .suspended _ [α _] none, tσ,
               .eval_opApp htρ, .eval_opApp htρ,
               ValueCorr.suspended (by simp) ?_ KontCorr.nil,
               h_store, h_refl, AlphaExtends.refl,
               ⟨trivial, (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h; exact ⟨∅, ∅, .none⟩)⟩,
               hinv, WriteBound.refl,
               (fun op args oa hv => by cases hv; exact ⟨∅, ∅, .none, (fun a' h => by cases h), (fun a' h => by cases h), (fun a' h => by cases h), (fun a' h => by cases h)⟩),
               ⟨fun a ha => by simp at ha; subst ha; exact h_scope _ _ h_ρ,
                fun _ hf => by simp at hf⟩,
               h_store_scoped⟩
        -- Prove the map condition
        intro i h1 h2
        have hi : i = 0 := by simp [List.length] at h1; omega
        subst hi; rfl
      | eval_fun h_fresh_c _h_nd h_vf h_σ'_eq =>
        subst h_σ'_eq; subst h_vf
        -- Try: the inaccessibles in order might be based on their order in the inductive constructor
        -- eval_fun params: f, xs, e1, a_v, v_f, σ'; after subst v_f, σ': f, xs, e1, a_v
        -- But also n=0 is unified. Let's see if there's a 5th inaccessible.
        -- Actually let's check the # of inaccessibles:
        rename_i xs e1 f a_v
        let ta_v : TVAddr := ⟨f, t⟩
        let α' : VAddr → TVAddr := fun a => if a = a_v then ta_v else α a
        let tv_f : TDenotable := .closure ⟨xs, e1, tρ.extend f ta_v, _h_nd⟩
        let tσ' := tσ.extend (.val ta_v) (.denotable tv_f)
        have h_tfresh : tσ (.val ta_v) = none := h_var_fresh f (by simp [])
        have h_wf_ce : WellFormedSubCExp (.funDef f xs e1) := ⟨h_wl, h_wn⟩
        have h_env' : EnvCorr α' (Env.extend ρ_c f a_v) (tρ.extend f ta_v) := by
          intro x a hxa; simp only [Env.extend] at hxa; split at hxa
          · rename_i heq; subst heq; injection hxa with hxa; subst hxa; simp [α', TEnv.lookup_extend_same]
          · rename_i hne; have ha_ne : a ≠ a_v := fun heq => by subst heq; exact absurd h_fresh_c (h_scope _ _ hxa)
            rw [show α' a = α a from if_neg ha_ne, TEnv.lookup_extend_ne _ _ _ _ hne]; exact h_env _ _ hxa
        have h_envR' : EnvReflects α' (Env.extend ρ_c f a_v) (tρ.extend f ta_v) := by
          intro x ta htρ'; by_cases heq : x = f
          · subst heq; simp [TEnv.extend] at htρ'; subst htρ'
            exact ⟨a_v, by simp [Env.extend], if_pos rfl⟩
          · rw [TEnv.lookup_extend_ne _ _ _ _ heq] at htρ'
            obtain ⟨a, hρ, hα⟩ := h_envR x ta htρ'
            exact ⟨a, by simp [Env.extend, heq]; exact hρ,
                   show α' a = ta by rw [show α' a = α a from
                     if_neg (fun h => by subst h; exact absurd h_fresh_c (h_scope _ _ hρ))]; exact hα⟩
        have h_inj : ∀ a', σ_c a' ≠ none → α a' ≠ ta_v := by
          intro a' ha' heq
          rw [Option.ne_none_iff_exists'] at ha'; obtain ⟨d, hd⟩ := ha'
          obtain ⟨_, htσ', _⟩ := h_store a' d hd
          rw [heq] at htσ'; rw [h_tfresh] at htσ'; exact absurd htσ' nofun
        have h_tσ_mono : ∀ addr, tσ addr ≠ none → tσ' addr = tσ addr :=
          fun addr haddr => TStore.extend_ne _ _ _ _ (by intro heq; subst heq; exact absurd h_tfresh haddr)
        have h_store' : StoreCorr α' tσ' (σ_c.extend a_v (.closure ⟨xs, e1, Env.extend ρ_c f a_v, _h_nd⟩)) := by
          intro a d hσ'; simp only [Store.extend] at hσ'
          split at hσ'
          · rename_i heq; subst heq; injection hσ' with hσ'; subst hσ'
            rw [show α' a = ta_v from if_pos rfl]
            exact ⟨tv_f, TStore.extend_same _ _ _, DenotableCorr.closure ⟨rfl, rfl, h_env', h_envR'⟩⟩
          · rename_i hne
            rw [show α' a = α a from if_neg hne]
            have hne' : TAddr.val (α a) ≠ TAddr.val ta_v := by
              intro heq; exact h_inj a (by rw [hσ']; exact nofun) (TAddr.val.inj heq)
            rw [show tσ' (.val (α a)) = tσ (.val (α a)) from TStore.extend_ne _ _ _ _ hne']
            obtain ⟨td, htσ, hd⟩ := h_store a d hσ'
            exact ⟨td, htσ, fc_denotableCorr_of_alpha_extends_fresh hd
              (fun a' ha' => if_neg (fun heq => by subst heq; exact absurd h_fresh_c ha'))
              h_tσ_mono (h_store_scoped _ _ hσ')⟩
        have h_refl' : StoreReflects α' tσ' (σ_c.extend a_v (.closure ⟨xs, e1, Env.extend ρ_c f a_v, _h_nd⟩)) := by
          intro ta h_ne
          simp only [tσ', TStore.extend] at h_ne
          split at h_ne
          · -- ta = ta_v: use a_v
            rename_i heq
            exact ⟨a_v, by simp [Store.extend], by simp [α', TAddr.val.inj heq]⟩
          · -- ta ≠ ta_v: use h_refl
            rename_i hne_ta
            obtain ⟨a, ha, hα⟩ := h_refl ta h_ne
            have ha_ne : a ≠ a_v := by
              intro heq; subst heq; exact absurd h_fresh_c ha
            refine ⟨a, ?_, ?_⟩
            · simp [Store.extend]; split
              · rename_i heq; exact absurd heq ha_ne
              · exact ha
            · simp only [α']; rw [if_neg ha_ne]; exact hα
        exact ⟨α', .den tv_f, tσ',
               .eval_fun rfl _h_nd rfl rfl,
               .eval_fun rfl h_tfresh _h_nd rfl rfl,
               ValueCorr.den (DenotableCorr.closure ⟨rfl, rfl, h_env', h_envR'⟩),
               h_store', h_refl',
               (fun a ha => show α' a = α a from if_neg (fun heq => by subst heq; exact absurd h_fresh_c ha)),
               ⟨⟨wellFormedSubCExp_funDef_body h_wf_ce, wellFormedSubCExp_funDef_disjoint h_wf_ce, wellNamedSubCExp_funDef_nodup h_wn⟩,
                (fun _ _ _ h => by simp at h), (fun _ _ _ h => by simp at h)⟩,
               hinv.extend_val ⟨f, t⟩ _ ⟨wellFormedSubCExp_funDef_body h_wf_ce, wellFormedSubCExp_funDef_disjoint h_wf_ce, wellNamedSubCExp_funDef_nodup h_wn⟩ (fun _ _ _ h => by simp at h),
               (fun a ha => by
                 simp only [tσ'] at ha; constructor
                 · intro hat; by_cases heq : a = .val ⟨f, t⟩
                   · subst heq; left; exact ⟨f, rfl, by simp []⟩
                   · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
                 · intro hne; exfalso; by_cases heq : a = .val ⟨f, t⟩
                   · subst heq; exact hne rfl
                   · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha),
               (fun op args oa hv => by cases hv),
               (show ValueScoped (.den (.closure ⟨xs, e1, Env.extend ρ_c f a_v, _h_nd⟩)) (σ_c.extend a_v (.closure ⟨xs, e1, Env.extend ρ_c f a_v, _h_nd⟩)) from by
                 show EnvScoped (Env.extend ρ_c f a_v) (σ_c.extend a_v _)
                 intro x a hxa; simp only [Env.extend] at hxa; split at hxa
                 · injection hxa with hxa; subst hxa; simp [Store.extend]
                 · have := h_scope _ _ hxa
                   simp only [Store.extend]; split
                   · exact nofun
                   · exact this),
               by -- StoreScoped (σ_c.extend a_v (.closure ⟨xs, e1, Env.extend ρ_c f a_v, _h_nd⟩))
                 apply storeScoped_extend h_store_scoped
                 -- DenotableScoped (.closure ...) (σ_c.extend a_v ...)
                 -- = EnvScoped (Env.extend ρ_c f a_v) (σ_c.extend a_v ...)
                 show EnvScoped (Env.extend ρ_c f a_v) (σ_c.extend a_v _)
                 intro x a hxa; simp only [Env.extend] at hxa; split at hxa
                 · injection hxa with hxa; subst hxa; simp [Store.extend]
                 · have := h_scope _ _ hxa
                   simp only [Store.extend]; split
                   · exact nofun
                   · exact this⟩
      | eval_match h_ae_c h_d_c h_find h_xs h_body_c =>
        subst h_d_c; subst h_xs
        rename_i ae c bs e_m n_body
        obtain ⟨td, htd, hcorr_d⟩ := fc_evalAtomic_corr h_env h_envR h_store h_ae_c
        have htd_eq : td = .conLabel c := by cases hcorr_d; rfl
        have h_bl : e_m.allLabels ⊆ (CExp.matchE ae bs).allLabels := fc_match_body_allLabels_subset h_find
        have h_bv : e_m.topAllocVars ⊆ (CExp.matchE ae bs).topAllocVars := fc_match_body_topAllocVars_subset h_find
        have h_bhl : e_m.handlerLabels ⊆ (CExp.matchE ae bs).handlerLabels := fc_match_body_handlerLabels_subset h_find
        have h_wf_body : WellFormedProgram e_m := by
          obtain ⟨b, hb_mem, hb_eq⟩ := fc_findBranch_mem h_find; subst hb_eq; constructor
          · cases wellLabeledSubCExp_matchE_branches h_wl _ hb_mem with | branch h => exact h
          · cases wellNamedSubCExp_matchE_branches h_wn _ hb_mem with | branch h _ => exact h
        obtain ⟨ih_exp, _, _, _, _⟩ := ih n_body (by omega)
        obtain ⟨α', tv, tσ', h_tn, h_ts, h_val, h_store', h_refl', h_ext, h_wfv, h_fi', h_wb, h_cb, h_val_scoped', h_store_scoped'⟩ :=
          ih_exp e_m ρ_c σ_c v_c σ_c' h_body_c h_wf_body α tρ tσ t h_env h_envR h_store h_refl h_scope h_store_scoped hinv
            (fun x hx => h_var_fresh x (h_bv hx))
            (fun l hl k hk hlk => h_kont_fresh l (h_bl hl) k hk hlk)
            (fun l hl => h_cdf l (h_bl hl))
            (fun l hl => h_hdf_sub l (h_bhl hl))
        exact ⟨α', tv, tσ', .eval_match htd htd_eq h_find rfl h_tn, .eval_match htd htd_eq h_find rfl h_ts,
               h_val, h_store', h_refl', h_ext, h_wfv, h_fi',
               h_wb.mono h_bv h_bl (h_bl.trans Finset.subset_union_right) (h_bl.trans Finset.subset_union_right),
               fun op args oa hv => by
                 obtain ⟨used, usedV, hchain, hbound, hvar_bound, htk_suf, h_bridge⟩ := h_cb op args oa hv
                 exact ⟨used, usedV, hchain,
                   fun a' hoa htk => (hbound a' hoa htk).trans h_bl,
                   fun a' hoa htk => (hvar_bound a' hoa htk).trans h_bv, htk_suf,
                   fun a' hoa h_ne_tk => let ⟨l_br, h_mem, h_suf⟩ := h_bridge a' hoa h_ne_tk; ⟨l_br, Finset.mem_union_right _ (h_bl h_mem), h_suf⟩⟩,
               h_val_scoped',
               h_store_scoped'⟩
      | eval_match_succ h_ae_c h_branch h_inner_c h_fresh_c h_σnew_c h_ρnew_c h_body_c =>
        subst h_σnew_c; subst h_ρnew_c
        rename_i ae a_inner bs x_bind e_m d_inner a_fresh n_body
        -- Step 1: Atomic correspondence → TDenotable.succVal (α a_inner)
        obtain ⟨td_ae, htd_ae, hcorr_ae⟩ := fc_evalAtomic_corr h_env h_envR h_store h_ae_c
        have htd_ae_eq : td_ae = .succVal (α a_inner) := by cases hcorr_ae; rfl
        subst htd_ae_eq
        -- Step 2: Inner store lookup via StoreCorr
        obtain ⟨td_inner, htσ_inner, hcorr_inner⟩ := h_store a_inner d_inner h_inner_c
        -- Step 3: Label/var subsets
        have h_bl : e_m.allLabels ⊆ (CExp.matchE ae bs).allLabels := fc_match_body_allLabels_subset h_branch
        have h_bv : e_m.topAllocVars ⊆ (CExp.matchE ae bs).topAllocVars := fc_match_body_topAllocVars_subset h_branch
        have h_bhl : e_m.handlerLabels ⊆ (CExp.matchE ae bs).handlerLabels := fc_match_body_handlerLabels_subset h_branch
        have h_xbind_in : x_bind ∈ (CExp.matchE ae bs).topAllocVars := fc_match_xbind_mem_topAllocVars h_branch
        -- Step 4: WellFormedProgram for body
        have h_wf_body : WellFormedProgram e_m := by
          obtain ⟨b, hb_mem, hb_eq⟩ := fc_findBranch_mem h_branch; subst hb_eq; constructor
          · cases wellLabeledSubCExp_matchE_branches h_wl _ hb_mem with | branch h => exact h
          · cases wellNamedSubCExp_matchE_branches h_wn _ hb_mem with | branch h _ => exact h
        -- Step 5: Fresh allocation
        let ta_fresh : TVAddr := ⟨x_bind, t⟩
        let α' : VAddr → TVAddr := fun a => if a = a_fresh then ta_fresh else α a
        let tσ' := tσ.extend (.val ta_fresh) (.denotable td_inner)
        have h_tfresh : tσ (.val ta_fresh) = none := h_var_fresh x_bind h_xbind_in
        -- Step 6: x_bind not in body alloc vars
        have h_xbind_notin : x_bind ∉ e_m.topAllocVars := by
          obtain ⟨b, hb_mem, hb_eq⟩ := fc_findBranch_mem h_branch; subst hb_eq
          have h_wnb := wellNamedSubCExp_matchE_branches h_wn _ hb_mem
          cases h_wnb with | branch _ h_vars => exact h_vars x_bind List.mem_cons_self
        -- Step 7: Injectivity
        have h_inj : ∀ a', σ_c a' ≠ none → α a' ≠ ta_fresh := by
          intro a' ha' heq
          rw [Option.ne_none_iff_exists'] at ha'; obtain ⟨d, hd⟩ := ha'
          obtain ⟨_, htσ', _⟩ := h_store a' d hd
          rw [heq] at htσ'; rw [h_tfresh] at htσ'; exact absurd htσ' nofun
        have h_tσ_mono : ∀ addr, tσ addr ≠ none → tσ' addr = tσ addr :=
          fun addr haddr => TStore.extend_ne _ _ _ _ (by intro heq; subst heq; exact absurd h_tfresh haddr)
        -- Step 8: EnvCorr for extended env
        have h_env' : EnvCorr α' (ρ_c.extend x_bind a_fresh) (tρ.extend x_bind ta_fresh) := by
          intro x a hxa; simp only [Env.extend] at hxa; split at hxa
          · rename_i heq; subst heq; injection hxa with hxa; subst hxa; simp [α', TEnv.lookup_extend_same]
          · rename_i hne; have ha_ne : a ≠ a_fresh := fun heq => by subst heq; exact absurd h_fresh_c (h_scope _ _ hxa)
            rw [show α' a = α a from if_neg ha_ne, TEnv.lookup_extend_ne _ _ _ _ hne]; exact h_env _ _ hxa
        -- Step 9: StoreCorr for extended store
        have h_store' : StoreCorr α' tσ' (σ_c.extend a_fresh d_inner) := by
          intro a d hσ'; simp only [Store.extend] at hσ'
          split at hσ'
          · rename_i heq; subst heq; injection hσ' with hσ'; subst hσ'
            rw [show α' a = ta_fresh from if_pos rfl]
            exact ⟨td_inner, TStore.extend_same _ _ _, fc_denotableCorr_of_alpha_extends_fresh hcorr_inner
              (fun a' ha' => if_neg (fun heq => by subst heq; exact absurd h_fresh_c ha'))
              h_tσ_mono (h_store_scoped _ _ h_inner_c)⟩
          · rename_i hne
            rw [show α' a = α a from if_neg hne]
            have hne' : TAddr.val (α a) ≠ TAddr.val ta_fresh := by
              intro heq; exact h_inj a (by rw [hσ']; exact nofun) (TAddr.val.inj heq)
            rw [show tσ' (.val (α a)) = tσ (.val (α a)) from TStore.extend_ne _ _ _ _ hne']
            obtain ⟨td, htσ, hd⟩ := h_store a d hσ'
            exact ⟨td, htσ, fc_denotableCorr_of_alpha_extends_fresh hd
              (fun a' ha' => if_neg (fun heq => by subst heq; exact absurd h_fresh_c ha'))
              h_tσ_mono (h_store_scoped _ _ hσ')⟩
        -- Step 10: StoreReflects for extended store
        have h_refl' : StoreReflects α' tσ' (σ_c.extend a_fresh d_inner) := by
          intro ta h_ne
          simp only [tσ', TStore.extend] at h_ne
          split at h_ne
          · rename_i heq
            exact ⟨a_fresh, by simp [Store.extend], by simp [α', TAddr.val.inj heq]⟩
          · rename_i hne_ta
            obtain ⟨a, ha, hα⟩ := h_refl ta h_ne
            have ha_ne : a ≠ a_fresh := by
              intro heq; subst heq; exact absurd h_fresh_c ha
            refine ⟨a, ?_, ?_⟩
            · simp [Store.extend]; split
              · rename_i heq; exact absurd heq ha_ne
              · exact ha
            · simp only [α']; rw [if_neg ha_ne]; exact hα
        -- Step 11: WellFormed storable for d_inner
        have h_wf_d : WellFormedStorable (.denotable td_inner) :=
          wellFormedStorable_of_store_lookup hinv.wf_store htσ_inner
        -- Step 12: FreshInvariant for extended store
        have hinv_ext := hinv.extend_val ⟨x_bind, t⟩ _ h_wf_d
          (fun hdl' ρ' oa heq => by cases heq; exact hinv.pairwiseChain_of_lookup htσ_inner)
        -- Step 13: Freshness conditions for body
        have h_body_var_fresh : ∀ x ∈ e_m.topAllocVars,
            tσ' (.val ⟨x, t⟩) = none := by
          intro x hx
          have h_ne : x ≠ x_bind := fun heq => h_xbind_notin (heq ▸ hx)
          show (tσ.extend (.val ⟨x_bind, t⟩) (.denotable td_inner)) (.val ⟨x, t⟩) = none
          rw [val_extend_preserves_val_ne h_ne]
          exact h_var_fresh x (h_bv hx)
        have h_body_kont_fresh : ∀ l ∈ e_m.allLabels, ∀ k : TKAddr,
            k.frame.time = t → k.frame.label = l →
            tσ' (.kont k) = none := by
          intro l hl k hk hlk
          show (tσ.extend (.val ⟨x_bind, t⟩) (.denotable td_inner)) (.kont k) = none
          rw [val_extend_preserves_kont]
          exact h_kont_fresh l (h_bl hl) k hk hlk
        have h_cdf_ext : ∀ l ∈ e_m.allLabels, CallDescFresh tσ' t l :=
          fun l hl => (h_cdf l (h_bl hl)).extend_val
        have h_hdf_ext : ∀ l ∈ e_m.handlerLabels, HandlerDescFresh tσ' t l :=
          fun l hl => (h_hdf_sub l (h_bhl hl)).extend_val
        -- Step 14: EnvScoped for extended env/store
        have h_scope' : EnvScoped (ρ_c.extend x_bind a_fresh) (σ_c.extend a_fresh d_inner) := by
          intro x a hxa; simp only [Env.extend] at hxa
          split at hxa
          · rename_i heq; subst heq; injection hxa with hxa; subst hxa
            show (σ_c.extend a_fresh d_inner) a_fresh ≠ none; simp [Store.extend]
          · have hscoped := h_scope x a hxa
            show (σ_c.extend a_fresh d_inner) a ≠ none
            simp only [Store.extend]; split
            · exact nofun
            · exact hscoped
        -- Step 15: Apply IH
        obtain ⟨ih_exp, _, _, _, _⟩ := ih n_body (by omega)
        -- StoreScoped for extended store
        have h_store_scoped_ext : StoreScoped (σ_c.extend a_fresh d_inner) := by
          apply storeScoped_extend h_store_scoped
          exact denotableScoped_mono (h_store_scoped _ _ h_inner_c) (fun a ha => by
            simp only [Store.extend]; split <;> [exact nofun; exact ha])
        obtain ⟨α'', tv, tσ'', h_tn, h_ts, h_val, h_store'', h_refl'', h_ext, h_wfv, h_fi'', h_wb, h_cb, h_val_scoped', h_store_scoped'⟩ :=
          ih_exp e_m (ρ_c.extend x_bind a_fresh) (σ_c.extend a_fresh d_inner) v_c σ_c'
            h_body_c h_wf_body α' (tρ.extend x_bind ta_fresh) tσ' t
            h_env' (fc_envReflects_extend_alpha h_envR h_fresh_c h_scope) h_store' h_refl' h_scope' h_store_scoped_ext hinv_ext
            h_body_var_fresh h_body_kont_fresh h_cdf_ext h_hdf_ext
        -- Step 16: WriteBound for the extension step
        have h_wb_ext : WriteBound tσ tσ' t {x_bind} ∅ ∅ ∅ := by
          intro a ha
          -- ha : tσ' a ≠ tσ a, i.e. (tσ.extend (.val ⟨x_bind, t⟩) (.denotable td_inner)) a ≠ tσ a
          -- The only address where tσ' differs from tσ is .val ⟨x_bind, t⟩
          have ha_eq : a = .val ⟨x_bind, t⟩ := by
            by_contra hne
            exact ha (TStore.extend_ne _ _ _ _ hne)
          subst ha_eq
          constructor
          · intro _; left; exact ⟨x_bind, rfl, Finset.mem_singleton_self _⟩
          · intro hne; exact absurd rfl hne
        -- Step 17: Compose and package result
        have h_alpha_ext : AlphaExtends α α'' σ_c := by
          intro a ha
          have ha_ne : a ≠ a_fresh := fun heq => by subst heq; exact absurd h_fresh_c ha
          have h1 : α' a = α a := if_neg ha_ne
          have ha_ext : (σ_c.extend a_fresh d_inner) a ≠ none := by
            simp only [Store.extend]; split
            · exact nofun
            · exact ha
          have h2 : α'' a = α' a := h_ext a ha_ext
          rw [h2, h1]
        exact ⟨α'', tv, tσ'',
               .eval_match_succ htd_ae h_branch htσ_inner rfl rfl rfl rfl h_tn,
               .eval_match_succ htd_ae h_branch htσ_inner rfl rfl h_tfresh rfl rfl h_ts,
               h_val, h_store'', h_refl'', h_alpha_ext, h_wfv, h_fi'',
               (h_wb_ext.trans h_wb).mono
                 (by intro x hx; simp only [Finset.mem_union, Finset.mem_singleton] at hx ⊢
                     rcases hx with rfl | hx; exact h_xbind_in; exact h_bv hx)
                 (by intro l hl; simp only [Finset.mem_union] at hl
                     rcases hl with hl | hl; simp at hl; exact h_bl hl)
                 (by intro l hl; simp only [Finset.mem_union] at hl
                     rcases hl with hl | hl; simp at hl; exact Finset.mem_union_right _ (h_bl hl))
                 (by intro l hl; simp only [Finset.mem_union] at hl
                     rcases hl with hl | hl; simp at hl; exact Finset.mem_union_right _ (h_bl hl)),
               fun op args oa hv => by
                 obtain ⟨used, usedV, hchain, hbound, hvar_bound, htk_suf, h_bridge⟩ := h_cb op args oa hv
                 exact ⟨used, usedV, hchain,
                   fun a' hoa htk => (hbound a' hoa htk).trans h_bl,
                   fun a' hoa htk => (hvar_bound a' hoa htk).trans h_bv, htk_suf,
                   fun a' hoa h_ne_tk => let ⟨l_br, h_mem, h_suf⟩ := h_bridge a' hoa h_ne_tk; ⟨l_br, Finset.mem_union_right _ (h_bl h_mem), h_suf⟩⟩,
               h_val_scoped',
               h_store_scoped'⟩
      | eval_funApp_clos h_f_c h_len_xs h_args_c h_fresh_as h_inj_as h_len_as h_σnew_c h_ρnew_c h_body_c =>
        subst h_σnew_c; subst h_ρnew_c
        rename_i f_ae xs e_body ρ_lam _h_nd_c aes ds as_v n_body
        -- Step 1: Atomic correspondence for function → closure
        obtain ⟨td_f, htd_f, hcorr_f⟩ := fc_evalAtomic_corr h_env h_envR h_store h_f_c
        -- Decompose the closure correspondence
        cases hcorr_f with
        | closure h_clo_corr =>
          rename_i tclo_lam
          -- Destructure tclo_lam to get free variables for subst
          obtain ⟨txs, te_body, tρ_lam, _tclo_nd⟩ := tclo_lam
          obtain ⟨h_params_eq, h_body_eq, h_env_lam, h_envR_lam⟩ := h_clo_corr
          -- h_params_eq : xs = txs, h_body_eq : e_body = te_body
          simp only [] at h_params_eq h_body_eq h_env_lam
          subst h_params_eq; subst h_body_eq
          -- Step 2: Atomic correspondence for each argument
          have h_args_corr : ∃ tds, List.Forall₂ (fun ae td => evalTAtomic ae tρ tσ = some td) aes tds ∧
              List.Forall₂ (fun d td => DenotableCorr α tσ d td) ds tds := by
            suffices ∀ (aes' : List AExp) (ds' : List Denotable),
                List.Forall₂ (fun ae d => evalAtomic ae ρ_c σ_c = some d) aes' ds' →
                ∃ tds, List.Forall₂ (fun ae td => evalTAtomic ae tρ tσ = some td) aes' tds ∧
                  List.Forall₂ (fun d td => DenotableCorr α tσ d td) ds' tds from
              this aes ds h_args_c
            intro aes' ds' h_f2
            induction h_f2 with
            | nil => exact ⟨[], .nil, .nil⟩
            | @cons ae d _ _ h_eval _ ih_f2 =>
              obtain ⟨td, htd, hcorr⟩ := fc_evalAtomic_corr h_env h_envR h_store h_eval
              obtain ⟨tds', h_targs, h_corrs⟩ := ih_f2
              exact ⟨td :: tds', .cons htd h_targs, .cons hcorr h_corrs⟩
          obtain ⟨tds, h_targs, h_corrs⟩ := h_args_corr
          have h_len_tds : tds.length = ds.length := (List.Forall₂.length_eq h_corrs).symm
          -- Step 3: Set up timestamped time and stores
          let t_new : Time := ⟨l_enc :: t.tk, t.tmk⟩
          let tσ_new := (xs.zip tds).foldl (fun s (x, d) =>
            s.extend (.val ⟨x, t_new⟩) (.denotable d)) tσ
          let tρ_new := xs.foldl (fun r x => r.extend x ⟨x, t_new⟩) tρ_lam
          -- Step 4: WellFormedProgram for body (from closure)
          have h_wf_clo := wellFormedStorable_of_evalTAtomic hinv.wf_store
            (fun xs' body' hlam => by
              cases h_wl with | funApp h_wl_f _ =>
                cases h_wn with | funApp h_wn_f h_disj_f h_nodup_f _ _ _ =>
                  exact ⟨⟨h_wl_f _ _ hlam, h_wn_f _ _ hlam⟩, h_disj_f _ _ hlam, h_nodup_f _ _ hlam⟩) htd_f
          -- After subst: h_wf_clo has xs and e_body directly
          have h_wf_body : WellFormedProgram e_body := h_wf_clo.1
          have h_disj_xs_body : Disjoint xs.toFinset e_body.topAllocVars := h_wf_clo.2.1
          have h_nodup_xs : xs.Nodup := h_wf_clo.2.2
          -- Step 5: Freshness at t_new
          have h_fresh_at_tnew : ∀ (a : TAddr), a.time = t_new → tσ a = none :=
            fun a ha => h_cdf_enc a (ha ▸ .refl)
          have h_fresh_args : ∀ i, (h : i < xs.length) → tσ (.val ⟨xs[i], t_new⟩) = none :=
            fun i _hi => h_fresh_at_tnew (.val ⟨xs[i], t_new⟩) rfl
          -- Step 6: Set up alpha extension for multi-arg
          -- α' maps each as_v[i] → ⟨xs[i], t_new⟩, and agrees with α on old addresses
          let α' : VAddr → TVAddr :=
            (xs.zip as_v).foldl (fun α_acc (x, a) => fun a' => if a' = a then ⟨x, t_new⟩ else α_acc a') α
          -- Step 7: Freshness preservation through foldl (kont preserved, desc preserved)
          have h_body_kont_fresh : ∀ l ∈ e_body.allLabels, ∀ k : TKAddr,
              k.frame.time = t_new → k.frame.label = l →
              tσ_new (.kont k) = none := by
            intro l hl k hk hlk
            show (xs.zip tds).foldl _ tσ (.kont k) = none
            rw [foldl_val_preserves_kont]
            exact h_fresh_at_tnew (.kont k) (by simp [TAddr.time]; exact hk)
          have h_cdf_at_tnew : ∀ l, CallDescFresh tσ t_new l :=
            fun l a ha => h_cdf_enc a ((Descendant.call l .refl).trans ha)
          have h_hdf_at_tnew : ∀ l, HandlerDescFresh tσ t_new l :=
            fun l a tk ha => h_cdf_enc a ((Descendant.appKont l tk .refl).trans ha)
          have h_cdf_new : ∀ l ∈ e_body.allLabels, CallDescFresh tσ_new t_new l :=
            fun l _hl => (h_cdf_at_tnew l).foldl_val
          have h_hdf_new : ∀ l ∈ e_body.handlerLabels, HandlerDescFresh tσ_new t_new l :=
            fun l _hl => (h_hdf_at_tnew l).foldl_val
          -- Step 8: Body variable freshness in tσ_new
          have h_body_var_fresh : ∀ x ∈ e_body.topAllocVars,
              tσ_new (.val ⟨x, t_new⟩) = none := by
            intro x hx
            have hx_notin_fs : x ∉ xs.toFinset := Finset.disjoint_right.mp h_disj_xs_body hx
            have h_len : xs.length ≤ tds.length := by
              rw [h_len_tds, show ds.length = aes.length from
                (List.Forall₂.length_eq h_args_c).symm, ← h_len_xs]
            have hx_notin_map : x ∉ (xs.zip tds).map Prod.fst := by
              rw [List.map_fst_zip h_len]; exact fun h => hx_notin_fs (List.mem_toFinset.mpr h)
            show (xs.zip tds).foldl _ tσ (.val ⟨x, t_new⟩) = none
            rw [foldl_val_preserves_val_notin hx_notin_map]
            exact h_fresh_at_tnew _ rfl
          -- Step 9: tds are well-formed storables
          have h_ds_wf : ∀ d ∈ tds, WellFormedStorable (.denotable d) := by
            have h_wf_aes : ∀ ae ∈ aes, ∀ xs' body', ae = .lam xs' body' →
                WellFormedProgram body' ∧ Disjoint xs'.toFinset body'.topAllocVars ∧ xs'.Nodup :=
              fun ae h_ae xs' body' hlam =>
                ⟨⟨by cases h_wl with | funApp _ h => exact h ae h_ae _ _ hlam,
                  by cases h_wn with | funApp _ _ _ h _ _ => exact h ae h_ae _ _ hlam⟩,
                 by cases h_wn with | funApp _ _ _ _ h _ => exact h ae h_ae _ _ hlam,
                 by cases h_wn with | funApp _ _ _ _ _ h => exact h ae h_ae _ _ hlam⟩
            have : ∀ (aes' : List AExp) (tds' : List TDenotable),
                List.Forall₂ (fun ae d => evalTAtomic ae tρ tσ = some d) aes' tds' →
                (∀ ae ∈ aes', ∀ xs' body', ae = .lam xs' body' →
                  WellFormedProgram body' ∧ Disjoint xs'.toFinset body'.topAllocVars ∧ xs'.Nodup) →
                ∀ d ∈ tds', WellFormedStorable (.denotable d) := by
              intro aes' tds' h_f2 h_wf_a
              induction h_f2 with
              | nil => intro d hd; simp at hd
              | @cons ae₀ d₀ _ _ h_ev _ ih_w =>
                intro d hd
                cases List.mem_cons.mp hd with
                | inl heq =>
                  subst heq
                  exact wellFormedStorable_of_evalTAtomic hinv.wf_store (h_wf_a ae₀ (List.Mem.head _)) h_ev
                | inr h => exact ih_w (fun ae h_ae => h_wf_a ae (List.Mem.tail _ h_ae)) d h
            exact this aes tds h_targs h_wf_aes
          -- Step 10: FreshInvariant for tσ_new
          have hinv_new : FreshInvariant tσ_new :=
            fc_foldl_val_preserves_fi hinv
              (fun ⟨_, d⟩ hp => h_ds_wf d (fc_mem_snd_of_mem_zip hp))
              (fun ⟨_, d⟩ hp hdl ρ oa heq => by
                have h_d_in := fc_mem_snd_of_mem_zip hp
                subst heq
                suffices ∀ (aes' : List AExp) (ds' : List TDenotable),
                    List.Forall₂ (fun ae d => evalTAtomic ae tρ tσ = some d) aes' ds' →
                    (.kontClosure hdl ρ oa) ∈ ds' → ∃ used usedVars, PairwiseChain tσ oa used usedVars from
                  this aes tds h_targs h_d_in
                intro aes' ds' h_f₂ h_mem
                induction h_f₂ with
                | nil => simp at h_mem
                | @cons ae₀ d₀ _ _ h_eval _ ih =>
                  cases List.mem_cons.mp h_mem with
                  | inl heq => subst heq; exact pairwiseChain_of_evalTAtomic hinv.chain_wf h_eval
                  | inr h => exact ih h)
          -- Step 11: Build correspondence for the extended stores (combined lemma)
          have h_corr_combined := foldl_correspondence
            h_env_lam h_envR_lam h_store h_refl h_store_scoped
            xs as_v ds tds h_corrs h_fresh_as
            (fun x hx => h_fresh_at_tnew (.val ⟨x, t_new⟩) rfl)
            (fun a ha x _hx heq => by
              -- α a = ⟨x, t_new⟩ contradicts: tσ (.val ⟨x, t_new⟩) = none but StoreCorr says it's non-none
              have h_tfresh := h_fresh_at_tnew (.val ⟨x, t_new⟩) rfl
              rw [Option.ne_none_iff_exists'] at ha; obtain ⟨d, hd⟩ := ha
              obtain ⟨td, htσ, _⟩ := h_store a d hd
              rw [heq] at htσ; rw [h_tfresh] at htσ; exact absurd htσ nofun)
            (fun d hd => by
              have : ∀ (aes' : List AExp) (ds' : List Denotable),
                  List.Forall₂ (fun ae d => evalAtomic ae ρ_c σ_c = some d) aes' ds' →
                  d ∈ ds' → DenotableScoped d σ_c := by
                intro aes' ds' hf hd'
                induction hf with
                | nil => simp at hd'
                | cons h_ev _ ih => cases hd' with
                  | head => exact evalAtomic_denotableScoped h_ev h_scope h_store_scoped
                  | tail _ h => exact ih h
              exact this aes ds h_args_c hd)
            (evalAtomic_denotableScoped h_f_c h_scope h_store_scoped)
            h_nodup_xs
            h_inj_as
            h_len_as (by have := h_args_c.length_eq; omega)
          have h_env_new := h_corr_combined.1
          have h_envR_new := h_corr_combined.2.1
          have h_store_new := h_corr_combined.2.2.1
          have h_refl_new := h_corr_combined.2.2.2
          -- AlphaExtends: α' agrees with α on old (live) addresses
          have h_alpha_ext : AlphaExtends α α' σ_c :=
            foldl_alpha_extends α σ_c t_new xs as_v
              (fun a ha => by
                have : ∀ (as' : List VAddr) (ds' : List Denotable),
                    List.Forall₂ (fun a _ => σ_c a = none) as' ds' → a ∈ as' → σ_c a = none := by
                  intro as' ds' hf ha'
                  induction hf with
                  | nil => simp at ha'
                  | cons h _ ih => cases ha' with | head => exact h | tail _ h => exact ih h
                exact this as_v ds h_fresh_as ha) h_len_as
          -- EnvScoped for extended env/store
          have h_scope_new : EnvScoped
              ((xs.zip as_v).foldl (fun r (x, a) => r.extend x a) ρ_lam)
              ((as_v.zip ds).foldl (fun s (a, d) => s.extend a d) σ_c) :=
            foldl_envScoped_extend ρ_lam σ_c xs as_v ds
              (evalAtomic_denotableScoped h_f_c h_scope h_store_scoped)
              h_len_as (by have := h_fresh_as.length_eq; omega)
          -- StoreScoped for extended store
          have h_store_scoped_new : StoreScoped
              ((as_v.zip ds).foldl (fun s (a, d) => s.extend a d) σ_c) :=
            foldl_storeScoped_extend σ_c as_v ds h_store_scoped h_fresh_as
              (fun d hd => by
                -- Each d ∈ ds came from evalAtomic, so it's scoped
                have : ∀ (aes' : List AExp) (ds' : List Denotable),
                    List.Forall₂ (fun ae d => evalAtomic ae ρ_c σ_c = some d) aes' ds' →
                    d ∈ ds' → DenotableScoped d σ_c := by
                  intro aes' ds' hf hd'
                  induction hf with
                  | nil => simp at hd'
                  | cons h_ev _ ih => cases hd' with
                    | head => exact evalAtomic_denotableScoped h_ev h_scope h_store_scoped
                    | tail _ h => exact ih h
                exact this aes ds h_args_c hd)
          -- Step 12: Apply P_exp IH on the body
          obtain ⟨ih_exp, _, _, _, _⟩ := ih n_body (by omega)
          obtain ⟨α'', tv, tσ'', h_tn_body, h_ts_body, h_val, h_store'', h_refl'', h_ext_body,
                  h_wfv, h_fi'', h_wb_body, h_cb_body, h_val_scoped', h_store_scoped'⟩ :=
            ih_exp e_body
              ((xs.zip as_v).foldl (fun r (x, a) => r.extend x a) ρ_lam)
              ((as_v.zip ds).foldl (fun s (a, d) => s.extend a d) σ_c)
              v_c σ_c' h_body_c h_wf_body α' tρ_new tσ_new t_new
              h_env_new h_envR_new h_store_new h_refl_new h_scope_new h_store_scoped_new hinv_new
              h_body_var_fresh
              (fun l hl k hk hlk => h_body_kont_fresh l hl k hk hlk)
              h_cdf_new
              h_hdf_new
          -- Step 13: Compose alpha extends
          have h_store_mono : ∀ a, σ_c a ≠ none →
              ((as_v.zip ds).foldl (fun s (a, d) => s.extend a d) σ_c) a ≠ none := by
            intro a ha
            exact foldl_store_extend_mono σ_c (as_v.zip ds) a ha
          have h_alpha_ext_full : AlphaExtends α α'' σ_c :=
            h_alpha_ext.trans h_ext_body h_store_mono
          -- Step 14: WriteBound
          have h_wb : WriteBound tσ tσ'' t (CExp.funApp f_ae aes).topAllocVars
              (CExp.funApp f_ae aes).allLabels
              ({l_enc} ∪ (CExp.funApp f_ae aes).allLabels)
              ({l_enc} ∪ (CExp.funApp f_ae aes).allLabels) := by
            -- All writes at t_new or descendants. CExp.funApp has ∅ allLabels/topAllocVars.
            simp only [CExp.allLabels_funApp, CExp.topAllocVars_funApp]
            intro a ha
            -- a was written: tσ'' a ≠ tσ a. All writes are descendants of t via l_enc.
            have h_desc_tnew : Descendant t_new a.time := by
              by_contra hnd
              have h_fp := foldl_val_preserves_non_desc (σ := tσ) (t_w := t_new) (pairs := xs.zip tds) hnd
              have : tσ'' a ≠ tσ_new a := by
                show tσ'' a ≠ (xs.zip tds).foldl _ tσ a
                rw [h_fp]; exact ha
              exact hnd (h_wb_body.descendant this)
            exact ⟨fun hat => by subst hat; exact absurd h_desc_tnew not_descendant_of_call_ext,
                   fun _ => ⟨l_enc, Finset.mem_singleton_self _, Or.inl h_desc_tnew⟩⟩
          -- Step 15: FCChainBound
          have h_cb : FCChainBound tσ'' tv t (CExp.funApp f_ae aes).allLabels
              (({l_enc} : Finset Label) ∪ (CExp.funApp f_ae aes).allLabels)
              (CExp.funApp f_ae aes).topAllocVars := by
            intro op args oa hv
            obtain ⟨used, usedV, hchain, hbound, hvar_bound, htk_suf, h_bridge⟩ := h_cb_body op args oa hv
            exact ⟨used, usedV, hchain,
              fun a' hoa htk => by
                have hlen := (htk_suf a' hoa).length_le
                simp only [t_new] at hlen; rw [htk] at hlen
                simp [List.length_cons] at hlen; omega,
              fun a' hoa htk => by
                have hlen := (htk_suf a' hoa).length_le
                simp only [t_new] at hlen; rw [htk] at hlen
                simp [List.length_cons] at hlen; omega,
              fun a' hoa => List.IsSuffix.trans ⟨[l_enc], rfl⟩ (htk_suf a' hoa),
              fun a' hoa h_ne_tk =>
                ⟨l_enc, Finset.mem_union_left _ (Finset.mem_singleton_self _), htk_suf a' hoa⟩⟩
          -- Step 16: Package outputs (TNaive and TStrict derivations)
          have h_tn : TEvalCExpN n_body.succ (CExp.funApp f_ae aes) tρ tσ t l_enc tv tσ'' :=
            .eval_funApp_clos htd_f h_len_xs h_targs rfl rfl rfl h_tn_body
          have h_ts : TFreshEvalCExpN n_body.succ (CExp.funApp f_ae aes) tρ tσ t l_enc tv tσ'' :=
            .eval_funApp_clos htd_f h_len_xs h_targs rfl
              (fun i hi => h_fresh_args i hi) rfl rfl h_ts_body
          exact ⟨α'', tv, tσ'',
                 h_tn, h_ts,
                 h_val, h_store'', h_refl'', h_alpha_ext_full,
                 h_wfv, h_fi'', h_wb, h_cb,
                 h_val_scoped', h_store_scoped'⟩
      | eval_funApp_kont h_f_c h_ae_c h_apply_c h_handle_c =>
        rename_i f_ae hdl_kc ρ_h_c κ_c ae_arg d_arg n1 v_mid σ_mid n2
        -- Step 1: Atomic evaluations
        obtain ⟨td_f, htd_f, hcorr_f⟩ := fc_evalAtomic_corr h_env h_envR h_store h_f_c
        obtain ⟨td_arg, htd_arg, hcorr_arg⟩ := fc_evalAtomic_corr h_env h_envR h_store h_ae_c
        -- Step 2: Decompose DenotableCorr for kontClosure
        cases hcorr_f with
        | kontClosure h_env_kc _h_envR_kc h_kont_kc =>
          rename_i tρ_h ta_κ
          -- Step 3: WellFormedStorable for both atomics
          have h_wf_f := wellFormedStorable_of_evalTAtomic hinv.wf_store
            (fun xs body hlam => by subst hlam; simp [evalTAtomic] at htd_f) htd_f
          have h_wf_arg := wellFormedStorable_of_evalTAtomic hinv.wf_store
            (fun xs body hlam => by
              cases h_wl with | funApp _ h_aes =>
                cases h_wn with | funApp _ _ _ h_wn_aes h_disj_aes h_nodup_aes =>
                  exact ⟨⟨h_aes _ (List.Mem.head _) _ _ hlam,
                          h_wn_aes _ (List.Mem.head _) _ _ hlam⟩,
                         h_disj_aes _ (List.Mem.head _) _ _ hlam,
                         h_nodup_aes _ (List.Mem.head _) _ _ hlam⟩) htd_arg
          -- Step 4: Chain data
          obtain ⟨chainUsed, chainVars, h_chain_f⟩ := pairwiseChain_of_evalTAtomic hinv.chain_wf htd_f
          have h_d_chain_arg : ∀ hdl' ρ' oa, td_arg = .kontClosure hdl' ρ' oa →
              ∃ u uv, PairwiseChain tσ oa u uv :=
            fun hdl' ρ' oa heq => by cases heq; exact pairwiseChain_of_evalTAtomic hinv.chain_wf htd_arg
          -- Step 5: Set up times
          let t_handle : Time := ⟨l_enc :: t.tk, t.tmk⟩
          let tmk_apply : MKTime := (l_enc, l_enc :: t.tk) :: t.tmk
          -- Step 6: tmk freshness
          have h_tmk_fresh_apply : ∀ a, tmk_apply <:+ a.time.tmk → tσ a = none := by
            intro a ha
            obtain ⟨tk₀, hd⟩ := Descendant.of_tmk_suffix ha a.time.tk
            exact h_cdf_enc a ((Descendant.appKont l_enc tk₀ .refl).trans hd)
          -- Step 7: Call P_apply IH
          obtain ⟨_, _, _, _, ih_apply⟩ := ih (n1) (by omega)
          obtain ⟨α₁, tv_mid, tσ₁, h_tn_apply, h_ts_apply, hval_mid, hstore₁, hrefl₁, hext₁,
                  h_wfv_mid, hinv₁, h_desc_apply, _h_dfp_apply, _h_hdfp_apply, _h_scope_apply, _h_sametk_apply, h_cb_apply, h_val_scoped_mid, h_store_scoped_apply⟩ :=
            ih_apply κ_c d_arg σ_c v_mid σ_mid ta_κ td_arg tmk_apply chainUsed chainVars
              h_apply_c α tσ h_kont_kc hcorr_arg h_store h_refl h_store_scoped
              (evalAtomic_denotableScoped h_ae_c h_scope h_store_scoped)
              ((evalAtomic_denotableScoped h_f_c h_scope h_store_scoped).2)
              h_wf_arg h_d_chain_arg hinv h_tmk_fresh_apply h_chain_f
          -- Step 8: Freshness preservation through P_apply at t.tmk level
          have h_pres_apply : ∀ a, a.time.tmk = t.tmk → tσ₁ a = tσ a := by
            intro a hat; by_contra h_ne
            have h_suf := h_desc_apply a h_ne
            rw [hat] at h_suf
            obtain ⟨px, hpx⟩ := h_suf
            have hlen := congr_arg List.length hpx
            simp only [tmk_apply, List.length_append, List.length_cons] at hlen; omega
          -- Step 9: Store monotonicity
          have h_store_mono_apply : ∀ a, σ_c a ≠ none → σ_mid a ≠ none := by
            intro a h_ne h_eq
            cases h_σ : σ_c a with
            | none => exact h_ne h_σ
            | some d =>
              have := eval_apply_store_mono (apply_kontN_to h_apply_c) a d h_σ
              rw [h_eq] at this; exact absurd this (by simp)
          -- Step 10: EnvCorr transfer through AlphaExtends
          have h_scope_ρh : EnvScoped ρ_h_c σ_c :=
            (evalAtomic_denotableScoped h_f_c h_scope h_store_scoped).1
          have h_env₁ : EnvCorr α₁ ρ_h_c tρ_h :=
            h_env_kc.of_alpha_extends hext₁ h_scope_ρh
          have h_scope_mid : EnvScoped ρ_h_c σ_mid :=
            fun x a hxa => h_store_mono_apply a (h_scope_ρh x a hxa)
          -- Step 11: Freshness preconditions for P_handle
          have h_var_fresh_σ₁ : ∀ x ∈ hdl_kc.topAllocVars, tσ₁ (.val ⟨x, t_handle⟩) = none := by
            intro x _; rw [h_pres_apply _ rfl]; exact h_cdf_enc (.val ⟨x, t_handle⟩) .refl
          have h_kont_fresh_σ₁ : ∀ l ∈ hdl_kc.allLabels, ∀ k : TKAddr,
              k.frame.time = t_handle → k.frame.label = l → tσ₁ (.kont k) = none := by
            intro l _ k hk _
            rw [h_pres_apply _ (by simp [TAddr.time]; rw [hk])]
            exact h_cdf_enc (.kont k) (by simp [TAddr.time]; exact hk ▸ .refl)
          have h_kont_enc_fresh_σ₁ : ∀ k : TKAddr,
              k.frame.time = t_handle → k.frame.label = l_enc → tσ₁ (.kont k) = none := by
            intro k hk _
            rw [h_pres_apply _ (by simp [TAddr.time]; rw [hk])]
            exact h_cdf_enc (.kont k) (by simp [TAddr.time]; exact hk ▸ .refl)
          have h_cdf_handle_σ₁ : ∀ l ∈ hdl_kc.allLabels, CallDescFresh tσ₁ t_handle l := by
            intro l _ a ha
            by_contra h_ne; push Not at h_ne
            have h_orig := h_cdf_enc a ((Descendant.call l (Descendant.refl (t := t_handle))).trans ha)
            have h_changed : tσ₁ a ≠ tσ a := by rw [h_orig]; exact h_ne
            have h_tmk_suf := h_desc_apply a h_changed
            exact ha.no_shorter_tmk_entry h_tmk_suf
          have h_not_handler_l_enc : ¬ isHandlerLabel l_enc := fun h =>
            by have := h_label_kind h; simp [CExp.isHandlerCExp] at this
          have h_hdf_handle_σ₁ : ∀ l ∈ hdl_kc.handlerLabels, HandlerDescFresh tσ₁ t_handle l := by
            intro l hl a tk ha
            have h_l_ne : l ≠ l_enc := fun h_eq =>
              h_not_handler_l_enc (h_eq ▸ h_handlerLabels_consistent hdl_kc l hl)
            by_contra h_ne; push Not at h_ne
            have h_desc_of_t : Descendant t_handle a.time :=
              (Descendant.appKont l tk Descendant.refl).trans ha
            have h_orig := h_cdf_enc a h_desc_of_t
            have h_changed : tσ₁ a ≠ tσ a := by rw [h_orig]; exact h_ne
            have h_tmk_suf := h_desc_apply a h_changed
            have heq := suffix_eq_of_length_eq
              ((l, l_enc :: t.tk) :: t.tmk)
              ((l_enc, l_enc :: t.tk) :: t.tmk)
              a.time.tmk ha.tmk_suffix h_tmk_suf (by simp)
            exact h_l_ne (Prod.ext_iff.mp (List.cons.inj heq).1).1
          -- Step 12: WellFormedSubHandler from store
          have h_wf_hdl : WellFormedSubHandler hdl_kc := h_wf_f
          -- Step 13: l_enc ∉ hdl_kc.handlerLabels
          have h_l_enc_notin_hdl_hl : l_enc ∉ hdl_kc.handlerLabels :=
            fun h_in => h_not_handler_l_enc (h_handlerLabels_consistent hdl_kc l_enc h_in)
          -- Step 14: Call P_handle IH
          obtain ⟨_, _, _, ih_handle, _⟩ := ih n2 (by omega)
          obtain ⟨α₂, tv_final, tσ₂, h_tn_handle, h_ts_handle, hval_final, hstore₂, hrefl₂, hext₂,
                  h_wfv_final, hinv₂, h_wb_handle, h_cb_handle, h_val_scoped', h_store_scoped'⟩ :=
            ih_handle hdl_kc ρ_h_c v_mid σ_mid v_c σ_c' l_enc tρ_h t_handle
              h_handle_c h_wf_hdl
              α₁ tv_mid tσ₁ h_env₁ (_h_envR_kc.of_alpha_extends hext₁ h_scope_ρh) hval_mid hstore₁ hrefl₁ h_scope_mid h_store_scoped_apply h_val_scoped_mid h_wfv_mid hinv₁
              h_var_fresh_σ₁ h_kont_fresh_σ₁ h_kont_enc_fresh_σ₁ h_cdf_handle_σ₁ h_hdf_handle_σ₁
              h_l_enc_notin_hdl_hl
          -- Step 15: Compose outputs
          -- All writes (both apply and handle) are descendants of t via l_enc
          have h_wb_all_at_t : WriteBound tσ tσ₂ t ∅ ∅ {l_enc} {l_enc} := by
            intro a ha
            have h_desc_t : Descendant t_handle a.time := by
              by_cases h1 : tσ₁ a = tσ a
              · -- Changed only in handle phase
                exact h_wb_handle.descendant (by rw [h1]; exact ha)
              · -- Changed in apply phase
                have h_suf := h_desc_apply a h1
                obtain ⟨tk₀, hd⟩ := Descendant.of_tmk_suffix h_suf a.time.tk
                exact (Descendant.appKont l_enc tk₀ Descendant.refl).trans hd
            constructor
            · intro hat; subst hat; exact absurd h_desc_t not_descendant_of_call_ext
            · intro _; exact ⟨l_enc, Finset.mem_singleton_self _, Or.inl h_desc_t⟩
          exact ⟨α₂, tv_final, tσ₂,
                 .eval_funApp_kont htd_f htd_arg rfl h_tn_apply rfl h_tn_handle,
                 .eval_funApp_kont htd_f htd_arg rfl h_ts_apply rfl h_ts_handle,
                 hval_final, hstore₂, hrefl₂,
                 hext₁.trans hext₂ h_store_mono_apply,
                 h_wfv_final, hinv₂,
                 h_wb_all_at_t.mono
                   (Finset.empty_subset _)
                   (Finset.empty_subset _)
                   (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
                   (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)),
                 by -- FCChainBound
                   intro op args oa hv
                   obtain ⟨used, usedVars, hpc, hsub, hvsub, htk, hbr⟩ := h_cb_handle op args oa hv
                   have h_tk_suf_t : ∀ a', oa = some a' → t.tk <:+ a'.frame.time.tk :=
                     fun a' hoa => (List.suffix_cons l_enc t.tk).trans (htk a' hoa)
                   exact ⟨used, usedVars, hpc,
                     fun a' hoa htk' => by
                       have := (htk' ▸ htk a' hoa).length_le; simp [t_handle] at this; omega,
                     fun a' hoa htk' => by
                       have := (htk' ▸ htk a' hoa).length_le; simp [t_handle] at this; omega,
                     h_tk_suf_t,
                     fun a' hoa h_ne_tk =>
                       ⟨l_enc, by simp, htk a' hoa⟩⟩,
                 h_val_scoped',
                 h_store_scoped'⟩
      | eval_handler h_body_c h_handle_c =>
        rename_i n1 e_body_h v_mid σ_mid n2 hdl l_h
        have h_wf_ce' : WellFormedSubCExp (.handler hdl e_body_h l_h) := ⟨h_wl, h_wn⟩
        have h_wf_body := wellFormedSubCExp_handler_body h_wf_ce'
        have h_wf_handler := wellFormedSubCExp_handler_sub h_wf_ce'
        let t_body : Time := ⟨[], (l_h, t.tk) :: t.tmk⟩
        have h_l_h_in_ce : l_h ∈ (CExp.handler hdl e_body_h l_h).allLabels := by simp []
        have h_l_h_in_ce_hl : l_h ∈ (CExp.handler hdl e_body_h l_h).handlerLabels := by
          simp [CExp.handlerLabels]
        have h_l_h_notin_hdl : l_h ∉ hdl.allLabels := by
          cases h_wl with | handler _ _ h1 _ => exact h1
        have h_l_h_notin_body : l_h ∉ e_body_h.allLabels := by
          cases h_wl with | handler _ _ _ h2 => exact h2
        have h_df_enc : DescFresh tσ t l_h :=
          DescFresh.of_cdf_hdf (h_cdf l_h h_l_h_in_ce) (h_hdf_sub l_h h_l_h_in_ce_hl)
        have h_body_fresh : ∀ (a : TAddr), a.time = t_body → tσ a = none :=
          fun a ha => h_df_enc a (Or.inr ⟨[], by rw [ha]; exact .refl⟩)
        have h_body_var_fresh : ∀ x ∈ e_body_h.topAllocVars, tσ (.val ⟨x, t_body⟩) = none :=
          fun x _ => h_body_fresh (.val ⟨x, t_body⟩) rfl
        have h_body_kont_fresh : ∀ l ∈ e_body_h.allLabels, ∀ k : TKAddr,
            k.frame.time = t_body → k.frame.label = l → tσ (.kont k) = none :=
          fun _ _ k hk _ => h_body_fresh (.kont k) (by simp [TAddr.time]; exact hk)
        have h_body_cdf : ∀ l ∈ e_body_h.allLabels, CallDescFresh tσ t_body l :=
          fun l _ a ha => h_df_enc a (Or.inr ⟨[], (Descendant.call l .refl).trans ha⟩)
        have h_body_hdf : ∀ l ∈ e_body_h.handlerLabels, HandlerDescFresh tσ t_body l :=
          fun l _ a tk ha => h_df_enc a (Or.inr ⟨[], (Descendant.appKont l tk .refl).trans ha⟩)
        -- Step 1: P_exp IH on body
        obtain ⟨ih_exp, _, _, _, _⟩ := ih n1 (by omega)
        obtain ⟨α₁, tv_mid, tσ₁, h_tn_body, h_ts_body, hval_mid, hstore₁, hrefl₁, hext₁,
                h_wfv_mid, hfi₁, h_wb_body, _h_cb_body, h_val_scoped_mid, h_store_scoped_mid⟩ :=
          ih_exp e_body_h ρ_c σ_c v_mid σ_mid h_body_c h_wf_body α tρ tσ t_body
            h_env h_envR h_store h_refl h_scope h_store_scoped hinv
            h_body_var_fresh h_body_kont_fresh h_body_cdf h_body_hdf
        -- Step 2: Preservation at time t (body writes only to descendants of t_body)
        have h_hdl_labels_sub : hdl.allLabels ⊆ (CExp.handler hdl e_body_h l_h).allLabels :=
          handler_allLabels_subset_cexp hdl _ l_h
        have h_hdl_handlerLabels_sub : hdl.handlerLabels ⊆ (CExp.handler hdl e_body_h l_h).handlerLabels :=
          fun l hl => by simp only [CExp.handlerLabels]; exact Finset.mem_union_left _ (Finset.mem_union_right _ hl)
        have h_pres_at_t : ∀ a, a.time = t → tσ₁ a = tσ a := by
          intro a hat
          by_contra h_ne; push Not at h_ne
          have h_desc := h_wb_body.descendant h_ne
          rw [hat] at h_desc
          exact not_descendant_of_handler_ext h_desc
        have h_var_fresh_mid : ∀ x ∈ hdl.topAllocVars, tσ₁ (.val ⟨x, t⟩) = none :=
          fun x hx => by rw [h_pres_at_t _ rfl]; exact h_var_fresh x (by simp [CExp.topAllocVars]; exact hx)
        have h_kont_fresh_mid : ∀ l ∈ hdl.allLabels, ∀ k : TKAddr,
            k.frame.time = t → k.frame.label = l → tσ₁ (.kont k) = none :=
          fun l hl k hk hlk => by rw [h_pres_at_t _ (by simp [TAddr.time]; exact hk)]
                                  exact h_kont_fresh l (h_hdl_labels_sub hl) k hk hlk
        have h_kont_enc_fresh_mid : ∀ k : TKAddr,
            k.frame.time = t → k.frame.label = l_enc → tσ₁ (.kont k) = none :=
          fun k hk hlk => by rw [h_pres_at_t _ (by simp [TAddr.time]; exact hk)]
                             exact h_kont_enc_fresh k hk hlk
        have h_cdf_orig : ∀ l ∈ hdl.allLabels, CallDescFresh tσ t l :=
          fun l hl => h_cdf l (h_hdl_labels_sub hl)
        have h_hdf_orig : ∀ l ∈ hdl.handlerLabels, HandlerDescFresh tσ t l :=
          fun l hl => h_hdf_sub l (h_hdl_handlerLabels_sub hl)
        have h_cdf_mid : ∀ l ∈ hdl.allLabels, CallDescFresh tσ₁ t l := by
          intro l hl a ha
          by_contra h_ne; push Not at h_ne
          have h_orig := h_cdf_orig l hl a ha
          have h_changed : tσ₁ a ≠ tσ a := by rw [h_orig]; exact h_ne
          have h_desc := h_wb_body.descendant h_changed
          exact Descendant.call_handler_disjoint ha h_desc.tmk_suffix
        have h_hdf_mid : ∀ l ∈ hdl.handlerLabels, HandlerDescFresh tσ₁ t l := by
          intro l hl a tk ha
          by_contra h_ne; push Not at h_ne
          have h_orig := h_hdf_orig l hl a tk ha
          have h_changed : tσ₁ a ≠ tσ a := by rw [h_orig]; exact h_ne
          have h_desc := h_wb_body.descendant h_changed
          have hne : l ≠ l_h := fun heq => h_l_h_notin_hdl (heq ▸ Handler.handlerLabels_subset_allLabels hdl hl)
          exact Descendant.handler_disjoint ha h_desc hne
        have h_kont_l_h_fresh : ∀ k : TKAddr, k.frame.time = t → k.frame.label = l_h → tσ₁ (.kont k) = none :=
          fun k hk hlk => by
            rw [h_pres_at_t _ (by simp [TAddr.time]; exact hk)]
            exact h_kont_fresh l_h h_l_h_in_ce k hk hlk
        -- Step 2b: Store monotonicity for correspondence
        have h_store_mono : ∀ a, σ_c a ≠ none → σ_mid a ≠ none := by
          intro a h_ne h_eq
          cases h_σ : σ_c a with
          | none => exact h_ne h_σ
          | some d =>
            have := eval_store_mono (eval_expN_to h_body_c) a d h_σ
            rw [h_eq] at this; exact absurd this (by simp)
        have h_scope_mid : EnvScoped ρ_c σ_mid :=
          fun x a hxa => h_store_mono a (h_scope x a hxa)
        have h_env₁ : EnvCorr α₁ ρ_c tρ := h_env.of_alpha_extends hext₁ h_scope
        -- Step 3: P_handle IH
        obtain ⟨_, _, _, ih_handle, _⟩ := ih n2 (by omega)
        obtain ⟨α₂, tv_final, tσ₂, h_tn_handle, h_ts_handle, hval_final, hstore₂, hrefl₂, hext₂,
                h_wfv_final, hfi₂, h_wb_handle, h_cb_handle, h_val_scoped', h_store_scoped'⟩ :=
          ih_handle hdl ρ_c v_mid σ_mid v_c σ_c' l_h tρ t h_handle_c h_wf_handler
            α₁ tv_mid tσ₁ h_env₁ (h_envR.of_alpha_extends hext₁ h_scope) hval_mid hstore₁ hrefl₁ h_scope_mid h_store_scoped_mid h_val_scoped_mid h_wfv_mid hfi₁
            h_var_fresh_mid h_kont_fresh_mid h_kont_l_h_fresh h_cdf_mid h_hdf_mid
            (fun h => h_l_h_notin_hdl (Handler.handlerLabels_subset_allLabels hdl h))
        -- Step 4: Compose WriteBound
        have h_wb_body_at_t : WriteBound tσ tσ₁ t ∅ ∅ ∅ {l_h} := by
          intro a ha
          have h_desc := h_wb_body.descendant ha
          constructor
          · intro hat; subst hat; exact absurd h_desc not_descendant_of_handler_ext
          · intro hne; exact ⟨l_h, Finset.mem_singleton_self _, Or.inr ⟨[], h_desc⟩⟩
        -- Step 5: Compose outputs
        exact ⟨α₂, tv_final, tσ₂,
               .eval_handler rfl h_tn_body h_tn_handle,
               .eval_handler rfl h_ts_body h_ts_handle,
               hval_final, hstore₂, hrefl₂,
               hext₁.trans hext₂ h_store_mono,
               h_wfv_final, hfi₂,
               WriteBound.mono (h_wb_body_at_t.trans h_wb_handle)
                 (by simp [CExp.topAllocVars, Finset.empty_union])
                 (by simp only [Finset.empty_union]; exact h_hdl_labels_sub)
                 (by simp only [Finset.empty_union]
                     intro l hl
                     rcases Finset.mem_insert.mp hl with rfl | hl'
                     · exact Finset.mem_insert_of_mem h_l_h_in_ce
                     · exact Finset.mem_insert_of_mem (h_hdl_labels_sub hl'))
                 (by intro l hl
                     rcases Finset.mem_insert.mp hl with rfl | hl'
                     · exact Finset.mem_insert_of_mem h_l_h_in_ce
                     · exact Finset.mem_insert_of_mem (h_hdl_labels_sub hl')),
               (by -- ChainBound widening
                 have h_lh_hdl_sub_ce : insert l_h hdl.allLabels ⊆ (CExp.handler hdl e_body_h l_h).allLabels :=
                   fun l hl => by
                     rcases Finset.mem_insert.mp hl with rfl | hl'
                     · exact h_l_h_in_ce
                     · exact h_hdl_labels_sub hl'
                 have h_lh_hdl_sub_enc_ce : insert l_h hdl.allLabels ⊆ insert l_enc (CExp.handler hdl e_body_h l_h).allLabels :=
                   h_lh_hdl_sub_ce.trans (Finset.subset_insert _ _)
                 intro op args oa hv
                 obtain ⟨used, usedVars, hpc, hsub, hvsub, htk, hbr⟩ := h_cb_handle op args oa hv
                 refine ⟨used, usedVars, hpc,
                   fun a' hoa htk' => (hsub a' hoa htk').trans h_lh_hdl_sub_ce,
                   fun a' hoa htk' => (hvsub a' hoa htk').trans (by simp [CExp.topAllocVars]),
                   htk,
                   fun a' hoa hne => ?_⟩
                 · obtain ⟨l, hl, hsuf⟩ := hbr a' hoa hne
                   exact ⟨l, h_lh_hdl_sub_enc_ce hl, hsuf⟩),
               h_val_scoped',
               h_store_scoped'⟩
    -- P_continue
    · intro frame_c v_c σ_c v_c' σ_c' l_enc fc t_f frameVars frameLabels
        h_eval α tv tσ
        h_frame h_val h_store h_refl h_scope_frame h_store_scoped h_val_scoped
        h_wfv hinv h_wf_body h_y_fresh h_kont_fresh
        h_y_notin_body h_body_var_fresh h_body_kont_fresh h_body_cdf h_body_hdf
        h_l_enc_notin_body
        h_chain_disjoint h_chain_var_disjoint h_chain_tk_suf h_chain_bridge
        h_ceLabels_exist
        h_frame_vars_sub h_frame_labels_sub h_frame_enc_sub
        h_frame_body_labels_sub h_frame_body_vars_sub h_inner_vars_sub
      cases h_eval with
      | continue_let h_fresh_c h_σ_eq h_body_c =>
        subst h_σ_eq
        rename_i n_body e_body y_var ρ_c_frame d_c a_v
        cases h_val with
        | den h_den_corr =>
          rename_i td_val
          cases h_frame with
          | letFrame h_clo_corr =>
            rename_i tclo_f
            obtain ⟨tclo_params, tclo_body, tρ_frame⟩ := tclo_f
            have hp := h_clo_corr.params_eq; simp only at hp; subst hp
            have hb := h_clo_corr.body_eq; simp only at hb; subst hb
            have h_env_frame := h_clo_corr.env_corr
            -- Set up timestamped allocation
            let ta_new : TVAddr := ⟨y_var, t_f⟩
            let α' : VAddr → TVAddr := fun a => if a = a_v then ta_new else α a
            let tσ_ext := tσ.extend (.val ta_new) (.denotable td_val)
            have h_tfresh : tσ (.val ta_new) = none := h_y_fresh y_var e_body tρ_frame rfl
            have h_wf_b := h_wf_body ⟨[y_var], e_body, tρ_frame, List.nodup_singleton _⟩ rfl
            -- EnvCorr after extension
            have h_env' : EnvCorr α' (ρ_c_frame.extend y_var a_v) (tρ_frame.extend y_var ta_new) := by
              intro x a hxa; simp only [Env.extend] at hxa; split at hxa
              · rename_i heq; subst heq; injection hxa with hxa; subst hxa; simp [α', TEnv.lookup_extend_same]
              · rename_i hne; have ha_ne : a ≠ a_v := fun heq => by subst heq; exact absurd h_fresh_c (h_scope_frame ⟨[y_var], e_body, ρ_c_frame, List.nodup_singleton _⟩ rfl _ _ hxa)
                rw [show α' a = α a from if_neg ha_ne, TEnv.lookup_extend_ne _ _ _ _ hne]; exact h_env_frame _ _ hxa
            -- Injectivity
            have h_inj : ∀ a', σ_c a' ≠ none → α a' ≠ ta_new := by
              intro a' ha' heq
              rw [Option.ne_none_iff_exists'] at ha'; obtain ⟨d, hd⟩ := ha'
              obtain ⟨_, htσ', _⟩ := h_store a' d hd
              rw [heq] at htσ'; rw [h_tfresh] at htσ'; exact absurd htσ' nofun
            have h_tσ_mono : ∀ addr, tσ addr ≠ none → tσ_ext addr = tσ addr :=
              fun addr haddr => TStore.extend_ne _ _ _ _ (by intro heq; subst heq; exact absurd h_tfresh haddr)
            -- StoreCorr after extension
            have h_store' : StoreCorr α' tσ_ext (σ_c.extend a_v d_c) := by
              intro a d hσ'; simp only [Store.extend] at hσ'
              split at hσ'
              · rename_i heq; subst heq; injection hσ' with hσ'; subst hσ'
                rw [show α' a = ta_new from if_pos rfl]
                exact ⟨td_val, TStore.extend_same _ _ _, fc_denotableCorr_of_alpha_extends_fresh h_den_corr
                  (fun a' ha' => if_neg (fun heq => by subst heq; exact absurd h_fresh_c ha'))
                  h_tσ_mono h_val_scoped⟩
              · rename_i hne
                rw [show α' a = α a from if_neg hne]
                have hne' : TAddr.val (α a) ≠ TAddr.val ta_new := by
                  intro heq; exact h_inj a (by rw [hσ']; exact nofun) (TAddr.val.inj heq)
                rw [show tσ_ext (.val (α a)) = tσ (.val (α a)) from TStore.extend_ne _ _ _ _ hne']
                obtain ⟨td, htσ, hd⟩ := h_store a d hσ'
                exact ⟨td, htσ, fc_denotableCorr_of_alpha_extends_fresh hd
                  (fun a' ha' => if_neg (fun heq => by subst heq; exact absurd h_fresh_c ha'))
                  h_tσ_mono (h_store_scoped _ _ hσ')⟩
            -- StoreReflects after extension
            have h_refl' : StoreReflects α' tσ_ext (σ_c.extend a_v d_c) := by
              intro ta h_ne
              simp only [tσ_ext, TStore.extend] at h_ne
              split at h_ne
              · rename_i heq; exact ⟨a_v, by simp [Store.extend], by simp [α', TAddr.val.inj heq]⟩
              · rename_i hne_ta
                obtain ⟨a, ha, hα⟩ := h_refl ta h_ne
                have ha_ne : a ≠ a_v := by intro heq; subst heq; exact absurd h_fresh_c ha
                refine ⟨a, ?_, ?_⟩
                · simp [Store.extend]; split
                  · rename_i heq; exact absurd heq ha_ne
                  · exact ha
                · simp only [α']; rw [if_neg ha_ne]; exact hα
            -- AlphaExtends
            have h_alpha_ext : AlphaExtends α α' σ_c :=
              fun a ha => show α' a = α a from if_neg (fun heq => by subst heq; exact absurd h_fresh_c ha)
            -- EnvScoped after extension
            have h_scope_ext : EnvScoped (ρ_c_frame.extend y_var a_v) (σ_c.extend a_v d_c) := by
              intro x a hxa; simp only [Env.extend] at hxa; split at hxa
              · injection hxa with hxa; subst hxa; simp [Store.extend]
              · have := h_scope_frame ⟨[y_var], e_body, ρ_c_frame, List.nodup_singleton _⟩ rfl _ _ hxa
                intro h_eq; rw [show σ_c.extend a_v d_c a = σ_c a from by simp [Store.extend, show a ≠ a_v from fun heq => by subst heq; exact absurd h_fresh_c (h_scope_frame ⟨[y_var], e_body, ρ_c_frame, List.nodup_singleton _⟩ rfl _ _ hxa)]] at h_eq
                exact this h_eq
            -- FreshInvariant after val extend
            have hinv_ext := hinv.extend_val ⟨y_var, t_f⟩ _ (h_wfv.wfv.to_wellFormedStorable)
              (fun hdl ρ oa heq => by cases heq; exact h_wfv.2 hdl ρ oa rfl)
            -- Freshness preconditions for body IH (after val extend)
            have h_body_vf_ext : ∀ x ∈ e_body.topAllocVars, tσ_ext (.val ⟨x, t_f⟩) = none := by
              intro x hx
              have h_x_ne_y : x ≠ y_var :=
                ne_of_mem_of_not_mem hx (h_y_notin_body y_var e_body tρ_frame rfl)
              have : TAddr.val ⟨x, t_f⟩ ≠ TAddr.val ta_new := by simp [ta_new, h_x_ne_y]
              rw [show tσ_ext (.val ⟨x, t_f⟩) = tσ (.val ⟨x, t_f⟩) from TStore.extend_ne _ _ _ _ this]
              exact h_body_var_fresh y_var e_body tρ_frame rfl x hx
            have h_body_kf_ext : ∀ l ∈ e_body.allLabels, ∀ k : TKAddr,
                k.frame.time = t_f → k.frame.label = l → tσ_ext (.kont k) = none := by
              intro l hl k hk hlk
              show tσ (.kont k) = none
              exact h_body_kont_fresh y_var e_body tρ_frame rfl l hl k hk hlk
            have h_body_cdf_ext : ∀ l ∈ e_body.allLabels, CallDescFresh tσ_ext t_f l :=
              fun l hl => (h_body_cdf y_var e_body tρ_frame rfl l hl).extend_val
            have h_body_hdf_ext : ∀ l ∈ e_body.handlerLabels, HandlerDescFresh tσ_ext t_f l :=
              fun l hl => (h_body_hdf y_var e_body tρ_frame rfl l hl).extend_val
            -- P_exp IH on body
            obtain ⟨ih_exp, _, _, _, _⟩ := ih n_body (by omega)
            -- StoreScoped for extended store
            have h_store_scoped_ext : StoreScoped (σ_c.extend a_v d_c) := by
              apply storeScoped_extend h_store_scoped
              -- DenotableScoped d_c (σ_c.extend a_v d_c)
              -- h_val_scoped : ValueScoped (.den d_c) σ_c, i.e. DenotableScoped d_c σ_c
              exact denotableScoped_mono h_val_scoped (fun a ha => by
                simp only [Store.extend]; split <;> [exact nofun; exact ha])
            obtain ⟨α₂, tv₂, tσ₂, h_tn_body, h_ts_body, hval₂, hstore₂, hrefl₂, hext₂,
                    h_wfv₂, hfi₂, h_wb_body, h_cb_body, h_val_scoped', h_store_scoped'⟩ :=
              ih_exp e_body (ρ_c_frame.extend y_var a_v) (σ_c.extend a_v d_c) v_c' σ_c'
                h_body_c h_wf_b α' (tρ_frame.extend y_var ta_new) tσ_ext t_f
                h_env' (fc_envReflects_extend_alpha h_clo_corr.env_reflects h_fresh_c
                  (fun x a hxa => h_scope_frame ⟨[y_var], e_body, ρ_c_frame, List.nodup_singleton _⟩ rfl x a hxa))
                h_store' h_refl' h_scope_ext h_store_scoped_ext hinv_ext
                h_body_vf_ext h_body_kf_ext h_body_cdf_ext h_body_hdf_ext
            -- WriteBound for the val extend step
            have h_wb_ext : WriteBound tσ tσ_ext t_f {y_var} ∅ ∅ ∅ := by
              intro a ha; constructor
              · intro hat; by_cases heq : a = .val ⟨y_var, t_f⟩
                · subst heq; left; exact ⟨y_var, rfl, Finset.mem_singleton_self _⟩
                · exact absurd (TStore.extend_ne _ _ _ _ heq) ha
              · intro hne; exfalso; by_cases heq : a = .val ⟨y_var, t_f⟩
                · subst heq; exact hne rfl
                · exact absurd (TStore.extend_ne _ _ _ _ heq) ha
            have h_wb_combined := h_wb_ext.trans h_wb_body
            -- Compose outputs
            exact ⟨α₂, tv₂, tσ₂,
                   .continue_let rfl h_tn_body,
                   .continue_let rfl h_tfresh h_ts_body,
                   hval₂, hstore₂, hrefl₂,
                   h_alpha_ext.trans hext₂ (fun a ha => by
                     intro h_eq; rw [show σ_c.extend a_v d_c a = σ_c a from by
                       simp [Store.extend, show a ≠ a_v from fun heq => by subst heq; exact absurd h_fresh_c ha]] at h_eq
                     exact ha h_eq),
                   h_wfv₂, hfi₂,
                   ⟨e_body.allLabels,
                    h_frame_labels_sub y_var e_body tρ_frame rfl,
                    h_l_enc_notin_body ⟨[y_var], e_body, tρ_frame, List.nodup_singleton _⟩ rfl,
                    h_wb_combined.mono
                      (by intro x hx; simp only [Finset.mem_union, Finset.mem_singleton] at hx
                          exact h_frame_vars_sub y_var e_body tρ_frame rfl (hx.elim
                            (fun h => Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
                            (fun h => Finset.mem_union_right _ h)))
                      (by intro l hl; simp only [Finset.mem_union] at hl
                          rcases hl with hl | hl
                          · simp at hl
                          · exact h_frame_labels_sub y_var e_body tρ_frame rfl hl)
                      (by intro l hl; simp only [Finset.mem_union] at hl
                          rcases hl with hl | hl
                          · simp at hl
                          · exact h_frame_labels_sub y_var e_body tρ_frame rfl hl)
                      (by intro l hl; simp only [Finset.mem_union] at hl
                          rcases hl with hl | hl
                          · simp at hl
                          · exact hl)⟩,
                   fun op args oa hv =>
                     let ⟨used, usedV, hchain, hbound, hvar_bound, htk_suf, h_bridge⟩ := h_cb_body op args oa hv
                     ⟨used, usedV, hchain, fun a' hoa htk =>
                       (hbound a' hoa htk).trans (h_frame_labels_sub y_var e_body tρ_frame rfl),
                       fun a' hoa htk => (hvar_bound a' hoa htk).trans
                         (Finset.subset_union_right.trans (h_frame_vars_sub y_var e_body tρ_frame rfl)),
                       htk_suf,
                       fun a' hoa h_ne_tk =>
                         let ⟨l_br, h_mem, h_suf⟩ := h_bridge a' hoa h_ne_tk
                         ⟨l_br, Finset.mem_union_right {l_enc} ((h_frame_labels_sub y_var e_body tρ_frame rfl) h_mem), h_suf⟩⟩,
                   h_val_scoped',
                   h_store_scoped'⟩
      | continue_op =>
        -- v_c = .suspended op✝ as_v✝ κ✝, frame_c = .letFrame clo✝
        -- v_c' = .suspended op✝ as_v✝ (.letFrame clo✝ :: κ✝), σ_c' = σ_c
        rename_i clo_c op_c as_v_c κ_c
        cases h_val with
        | suspended h_len h_map h_kont_corr =>
          rename_i tas_v a_κ_prev
          cases h_frame with
          | letFrame h_clo_corr =>
            rename_i tclo
            obtain ⟨tclo_params, tclo_body, tρ_frame, tclo_nd⟩ := tclo
            have hp := h_clo_corr.params_eq; simp only at hp; subst hp
            have hb := h_clo_corr.body_eq; simp only at hb; subst hb
            set clo : TClosure := ⟨clo_c.params, clo_c.body, tρ_frame, tclo_nd⟩
            set a_κ : TKAddr := ⟨⟨.letFrame clo, t_f, l_enc⟩, op_c⟩
            have h_fresh_kont : tσ (.kont a_κ) = none := h_kont_fresh a_κ rfl rfl rfl
            let tσ' := tσ.extend (.kont a_κ) (.kontLink a_κ_prev)
            have h_susp_chain := h_wfv.suspChain op_c tas_v a_κ_prev rfl
            have h_wfp := h_wf_body clo rfl
            have h_l_enc_nb := h_l_enc_notin_body clo rfl
            have h_y_notin_clo : ∀ y, clo_c.params = [y] → y ∉ clo_c.body.topAllocVars :=
              fun y hy => h_y_notin_body y clo_c.body tρ_frame (by simp [clo, hy])
            -- FreshInvariant after kont extend
            have hinv' : FreshInvariant tσ' :=
              hinv.extend_kont a_κ a_κ_prev (fun k hk hl hlet => h_kont_fresh k hk hl hlet)
            -- Strict derivation
            have h_strict : TFreshContinueFrameN 0 l_enc (.letFrame clo) t_f
                (.suspended op_c tas_v a_κ_prev) tσ
                (.suspended op_c tas_v (some a_κ)) tσ' :=
              .continue_op rfl rfl h_fresh_kont rfl
            -- Naive derivation
            have h_naive : TContinueFrameN 0 l_enc (.letFrame clo) t_f
                (.suspended op_c tas_v a_κ_prev) tσ
                (.suspended op_c tas_v (some a_κ)) tσ' :=
              .continue_op rfl rfl rfl
            -- tσ monotonicity
            have h_tσ_mono : ∀ addr, tσ addr ≠ none → tσ' addr = tσ addr :=
              fun addr h => TStore.extend_ne _ _ _ _ (fun heq => by subst heq; exact absurd h_fresh_kont h)
            -- KontCorr after extend
            have h_kont_corr' : KontCorr α tσ' (Frame.letFrame clo_c :: κ_c) (some a_κ) :=
              .cons (TStore.extend_same _ _ _) (FrameCorr.letFrame h_clo_corr) (h_kont_corr.mono h_tσ_mono)
            -- ValueCorr after extend
            have h_val' : ValueCorr α tσ' (.suspended op_c as_v_c (Frame.letFrame clo_c :: κ_c))
                (.suspended op_c tas_v (some a_κ)) :=
              .suspended h_len h_map h_kont_corr'
            -- StoreCorr/StoreReflects preserved (kont extend doesn't affect val addresses)
            have h_store' : StoreCorr α tσ' σ_c := by
              intro a d hσ
              obtain ⟨td, htσ, hd⟩ := h_store a d hσ
              have hne : TAddr.val (α a) ≠ TAddr.kont a_κ := by intro h; cases h
              exact ⟨td, by show tσ.extend _ _ _ = _; rw [TStore.extend_ne _ _ _ _ hne]; exact htσ,
                     hd.mono h_tσ_mono⟩
            have h_refl' : StoreReflects α tσ' σ_c := by
              intro ta h_ne
              have hne : TAddr.val ta ≠ TAddr.kont a_κ := by intro h; cases h
              rw [show tσ' (.val ta) = tσ (.val ta) from TStore.extend_ne _ _ _ _ hne] at h_ne
              exact h_refl ta h_ne
            -- WellFormedValue6
            have h_wf_v' : WellFormedValue6 tσ'
                (.suspended op_c tas_v (some a_κ)) := by
              obtain ⟨innerUsed, innerVars, h_inner_chain⟩ := h_susp_chain
              cases a_κ_prev with
              | none =>
                refine ⟨trivial, fun _ _ _ h => ?_, fun _ _ _ h => ?_⟩
                · cases h
                · cases h
                  exact ⟨_, _, .same_tk (TStore.extend_same _ _ _) rfl h_wfp h_y_notin_clo
                    ∅ (by simp) (by simp) (by simp) h_l_enc_nb
                    (fun a' h => by cases h)
                    (fun a' h => by cases h) (fun _ _ => by simp)
                    PairwiseChain.none⟩
              | some a_prev =>
                have h_inner_ext := h_inner_chain.extend_kont a_κ (.kontLink (some a_prev)) h_fresh_kont
                obtain ⟨ceLabels, h_disj_ce, h_lenc_notin_ce, h_same_tk_sub, h_inner_label_mem, h_ce_sub_fl⟩ :=
                  h_ceLabels_exist clo rfl op_c tas_v (some a_prev) rfl
                refine ⟨trivial, fun _ _ _ h => ?_, fun _ _ _ h => ?_⟩
                · cases h
                · cases h
                  by_cases htk_eq : a_prev.frame.time.tk = t_f.tk
                  · -- same_tk
                    have h_used_sub := h_same_tk_sub innerUsed innerVars h_inner_chain a_prev rfl htk_eq
                    exact ⟨_, _, .same_tk (TStore.extend_same _ _ _) rfl h_wfp h_y_notin_clo
                      ceLabels h_used_sub h_disj_ce h_lenc_notin_ce h_l_enc_nb
                      (fun a' heq => by cases heq; exact h_inner_label_mem a_prev rfl htk_eq)
                      (fun a' heq => by cases heq; exact htk_eq.symm)
                      (fun y hy => h_chain_var_disjoint clo rfl op_c tas_v (some a_prev) rfl
                        innerUsed innerVars h_inner_chain a_prev rfl htk_eq y hy)
                      h_inner_ext⟩
                  · -- diff_tk
                    obtain ⟨l_bridge, h_lb_in_fl, h_lb_notin, h_lb_suf⟩ :=
                      h_chain_bridge clo rfl op_c tas_v (some a_prev) rfl a_prev rfl htk_eq
                    exact ⟨_, _, .diff_tk (TStore.extend_same _ _ _) rfl h_wfp h_y_notin_clo h_l_enc_nb
                      l_bridge h_lb_notin
                      (fun a' heq => by cases heq; exact h_lb_suf)
                      (Option.some_ne_none _)
                      h_inner_ext⟩
            -- WriteBound
            have h_wb : WriteBound tσ tσ' t_f ∅ {l_enc} ∅ ∅ := by
              intro a ha; constructor
              · intro hat
                by_cases heq : a = .kont a_κ
                · subst heq; right; left; exact ⟨a_κ, rfl, rfl, Finset.mem_singleton_self _⟩
                · exact absurd (TStore.extend_ne _ _ _ _ heq) ha
              · intro hne; exfalso
                by_cases heq : a = .kont a_κ
                · subst heq; simp [a_κ] at hne
                · exact absurd (TStore.extend_ne _ _ _ _ heq) ha
            -- Package
            exact ⟨α, .suspended op_c tas_v (some a_κ), tσ',
                   h_naive, h_strict,
                   h_val', h_store', h_refl', AlphaExtends.refl,
                   h_wf_v', hinv',
                   ⟨∅, by simp, by simp, h_wb.mono (by simp) (h_frame_enc_sub clo rfl) (by simp) (by simp)⟩,
                   fun op args oa hv => by
                     cases hv
                     obtain ⟨innerUsed, innerVars, h_inner_chain⟩ := h_susp_chain
                     cases a_κ_prev with
                     | none =>
                       obtain ⟨ceLabels, h_disj_ce, h_lenc_notin_ce, h_same_tk_sub, h_inner_label_mem, h_ce_sub_fl⟩ :=
                         h_ceLabels_exist clo rfl op_c tas_v none rfl
                       exact ⟨_, _, .same_tk (TStore.extend_same _ _ _) rfl h_wfp h_y_notin_clo
                         ceLabels (by simp) h_disj_ce h_lenc_notin_ce h_l_enc_nb
                         (fun a' h => by cases h)
                         (fun a' h => by cases h) (fun _ _ => by simp)
                         PairwiseChain.none,
                         fun _ h => by simp only [Finset.union_empty] at *; cases h; intro _; exact Finset.insert_subset_iff.mpr ⟨h_frame_enc_sub clo rfl (Finset.mem_singleton_self l_enc), h_frame_body_labels_sub clo rfl⟩,
                         fun _ h => by simp only [Finset.union_empty] at *; cases h; intro _; exact h_frame_body_vars_sub clo rfl,
                         fun _ h => by cases h; exact List.suffix_refl _,
                         fun a' h h_ne => by cases h; exact absurd rfl h_ne⟩
                     | some a_prev =>
                       have h_inner_ext := h_inner_chain.extend_kont a_κ (.kontLink (some a_prev)) h_fresh_kont
                       obtain ⟨ceLabels, h_disj_ce, h_lenc_notin_ce, h_same_tk_sub, h_inner_label_mem, h_ce_sub_fl⟩ :=
                         h_ceLabels_exist clo rfl op_c tas_v (some a_prev) rfl
                       by_cases htk_eq : a_prev.frame.time.tk = t_f.tk
                       · -- same_tk
                         have h_used_sub := h_same_tk_sub innerUsed innerVars h_inner_chain a_prev rfl htk_eq
                         exact ⟨_, _, .same_tk (TStore.extend_same _ _ _) rfl h_wfp h_y_notin_clo
                           ceLabels h_used_sub h_disj_ce h_lenc_notin_ce h_l_enc_nb
                           (fun a' heq => by cases heq; exact h_inner_label_mem a_prev rfl htk_eq)
                           (fun a' heq => by cases heq; exact htk_eq.symm)
                           (fun y hy => h_chain_var_disjoint clo rfl op_c tas_v (some a_prev) rfl
                             innerUsed innerVars h_inner_chain a_prev rfl htk_eq y hy)
                           h_inner_ext,
                           fun _ h => by cases h; intro _; exact Finset.union_subset (Finset.insert_subset_iff.mpr ⟨h_frame_enc_sub clo rfl (Finset.mem_singleton_self _), h_frame_body_labels_sub clo rfl⟩) (h_used_sub.trans h_ce_sub_fl),
                           fun _ h => by cases h; intro _; exact Finset.union_subset (h_frame_body_vars_sub clo rfl) (h_inner_vars_sub clo rfl op_c tas_v (some a_prev) rfl innerUsed innerVars h_inner_chain a_prev rfl htk_eq),
                           fun _ h => by cases h; exact List.suffix_refl _,
                           fun a' h h_ne => by cases h; exact absurd rfl h_ne⟩
                       · -- diff_tk
                         obtain ⟨l_bridge, h_lb_in_fl, h_lb_notin, h_lb_suf⟩ :=
                           h_chain_bridge clo rfl op_c tas_v (some a_prev) rfl a_prev rfl htk_eq
                         exact ⟨_, _, .diff_tk (TStore.extend_same _ _ _) rfl h_wfp h_y_notin_clo h_l_enc_nb
                           l_bridge h_lb_notin (fun a' heq => by cases heq; exact h_lb_suf)
                           (Option.some_ne_none _) h_inner_ext,
                           fun _ h => by cases h; intro _; exact Finset.union_subset (Finset.union_subset (h_frame_enc_sub clo rfl) (Finset.singleton_subset_iff.mpr h_lb_in_fl)) (h_frame_body_labels_sub clo rfl),
                           fun _ h => by cases h; intro _; exact h_frame_body_vars_sub clo rfl,
                           fun _ h => by cases h; exact List.suffix_refl _,
                           fun a' h h_ne => by cases h; exact absurd rfl h_ne⟩,
                   -- ValueScoped (.suspended op_c as_v_c (Frame.letFrame clo_c :: κ_c)) σ_c
                   ⟨h_val_scoped.1, fun f hf => by
                     rcases List.mem_cons.mp hf with rfl | hf
                     · exact h_scope_frame clo_c rfl
                     · exact h_val_scoped.2 f hf⟩,
                   h_store_scoped⟩
    -- P_handle
    · intro hdl ρ_c v_c σ_c v_c' σ_c' l_enc ρ_handler t
        h_eval h_wf_hdl α tv tσ
        h_env h_envR h_val h_store h_refl h_scope h_store_scoped h_val_scoped
        h_wfv hinv h_var_fresh h_kont_fresh h_kont_enc_fresh h_cdf h_hdf h_lenc_notin
      cases h_eval with
      | handle_return h_ret h_fresh_c h_σ_eq h_body_c =>
        subst h_σ_eq
        -- Decompose ValueCorr: v_c = Value.den d, tv must be TValue.den td
        cases h_val with
        | den h_den_corr =>
          rename_i x_ret e_ret n_body d_val a_v td_val
          -- Same pattern as continue_let: allocate ⟨x_ret, t⟩, call IH P_exp on e_ret
          -- Extract return clause components
          have h_x_ret := congr_arg Prod.fst h_ret
          have h_e_ret := congr_arg Prod.snd h_ret
          simp at h_x_ret h_e_ret
          -- Set up timestamped allocation
          let ta_new : TVAddr := ⟨x_ret, t⟩
          let α' : VAddr → TVAddr := fun a => if a = a_v then ta_new else α a
          let tσ_ext := tσ.extend (.val ta_new) (.denotable td_val)
          have h_tfresh : tσ (.val ta_new) = none := by
            show tσ (.val ⟨x_ret, t⟩) = none
            rw [h_x_ret]; exact h_var_fresh _ (fc_handler_xret_mem_topAllocVars hdl)
          have h_wf_e : WellFormedProgram e_ret := by rw [h_e_ret]; exact wellFormedSubHandler_ret h_wf_hdl
          -- EnvCorr after extension
          have h_env' : EnvCorr α' (ρ_c.extend x_ret a_v) (ρ_handler.extend x_ret ta_new) := by
            intro x a hxa; simp only [Env.extend] at hxa; split at hxa
            · rename_i heq; subst heq; injection hxa with hxa; subst hxa; simp [α', TEnv.lookup_extend_same]
            · rename_i hne; have ha_ne : a ≠ a_v := fun heq => by subst heq; exact absurd h_fresh_c (h_scope _ _ hxa)
              rw [show α' a = α a from if_neg ha_ne, TEnv.lookup_extend_ne _ _ _ _ hne]; exact h_env _ _ hxa
          -- Injectivity
          have h_inj : ∀ a', σ_c a' ≠ none → α a' ≠ ta_new := by
            intro a' ha' heq
            rw [Option.ne_none_iff_exists'] at ha'; obtain ⟨d, hd⟩ := ha'
            obtain ⟨_, htσ', _⟩ := h_store a' d hd
            rw [heq] at htσ'; rw [h_tfresh] at htσ'; exact absurd htσ' nofun
          have h_tσ_mono : ∀ addr, tσ addr ≠ none → tσ_ext addr = tσ addr :=
            fun addr haddr => TStore.extend_ne _ _ _ _ (by intro heq; subst heq; exact absurd h_tfresh haddr)
          -- StoreCorr after extension
          have h_store' : StoreCorr α' tσ_ext (σ_c.extend a_v d_val) := by
            intro a d hσ'; simp only [Store.extend] at hσ'
            split at hσ'
            · rename_i heq; subst heq; injection hσ' with hσ'; subst hσ'
              rw [show α' a = ta_new from if_pos rfl]
              exact ⟨td_val, TStore.extend_same _ _ _, fc_denotableCorr_of_alpha_extends_fresh h_den_corr
                (fun a' ha' => if_neg (fun heq => by subst heq; exact absurd h_fresh_c ha'))
                h_tσ_mono h_val_scoped⟩
            · rename_i hne
              rw [show α' a = α a from if_neg hne]
              have hne' : TAddr.val (α a) ≠ TAddr.val ta_new := by
                intro heq; exact h_inj a (by rw [hσ']; exact nofun) (TAddr.val.inj heq)
              rw [show tσ_ext (.val (α a)) = tσ (.val (α a)) from TStore.extend_ne _ _ _ _ hne']
              obtain ⟨td, htσ, hd⟩ := h_store a d hσ'
              exact ⟨td, htσ, fc_denotableCorr_of_alpha_extends_fresh hd
                (fun a' ha' => if_neg (fun heq => by subst heq; exact absurd h_fresh_c ha'))
                h_tσ_mono (h_store_scoped _ _ hσ')⟩
          -- StoreReflects after extension
          have h_refl' : StoreReflects α' tσ_ext (σ_c.extend a_v d_val) := by
            intro ta h_ne
            simp only [tσ_ext, TStore.extend] at h_ne
            split at h_ne
            · rename_i heq; exact ⟨a_v, by simp [Store.extend], by simp [α', TAddr.val.inj heq]⟩
            · rename_i hne_ta
              obtain ⟨a, ha, hα⟩ := h_refl ta h_ne
              have ha_ne : a ≠ a_v := by intro heq; subst heq; exact absurd h_fresh_c ha
              refine ⟨a, ?_, ?_⟩
              · simp [Store.extend]; split
                · rename_i heq; exact absurd heq ha_ne
                · exact ha
              · simp only [α']; rw [if_neg ha_ne]; exact hα
          -- AlphaExtends
          have h_alpha_ext : AlphaExtends α α' σ_c :=
            fun a ha => show α' a = α a from if_neg (fun heq => by subst heq; exact absurd h_fresh_c ha)
          -- EnvScoped after extension
          have h_scope_ext : EnvScoped (ρ_c.extend x_ret a_v) (σ_c.extend a_v d_val) := by
            intro x a hxa; simp only [Env.extend] at hxa; split at hxa
            · injection hxa with hxa; subst hxa; simp [Store.extend]
            · have := h_scope _ _ hxa
              intro h_eq; rw [show σ_c.extend a_v d_val a = σ_c a from by simp [Store.extend, show a ≠ a_v from fun heq => by subst heq; exact absurd h_fresh_c (h_scope _ _ hxa)]] at h_eq
              exact this h_eq
          -- FreshInvariant after val extend
          have hinv_ext := hinv.extend_val ⟨x_ret, t⟩ _ (h_wfv.wfv.to_wellFormedStorable)
            (fun hdl ρ oa heq => by cases heq; exact h_wfv.2 hdl ρ oa rfl)
          -- Subset lemmas
          have h_ret_labels_sub : e_ret.allLabels ⊆ hdl.allLabels := by
            rw [h_e_ret]; exact handler_ret_allLabels_subset hdl
          have h_ret_vars_sub : e_ret.topAllocVars ⊆ hdl.topAllocVars := by
            rw [h_e_ret]; exact handler_ret_topAllocVars_subset hdl
          have h_xret_in : x_ret ∈ hdl.topAllocVars :=
            h_x_ret ▸ fc_handler_xret_mem_topAllocVars hdl
          have h_xret_notin_ret : x_ret ∉ e_ret.topAllocVars :=
            h_e_ret ▸ h_x_ret ▸ wellNamedSubHandler_xret_notin_ret h_wf_hdl.wn
          -- Freshness preconditions for body IH (after val extend)
          have h_body_vf_ext : ∀ x ∈ e_ret.topAllocVars, tσ_ext (.val ⟨x, t⟩) = none := by
            intro x hx
            have h_x_ne : x ≠ x_ret := ne_of_mem_of_not_mem hx h_xret_notin_ret
            show (tσ.extend (.val ⟨x_ret, t⟩) (.denotable td_val)) (.val ⟨x, t⟩) = none
            rw [val_extend_preserves_val_ne h_x_ne]
            exact h_var_fresh x (h_ret_vars_sub hx)
          have h_body_kf_ext : ∀ l ∈ e_ret.allLabels, ∀ k : TKAddr,
              k.frame.time = t → k.frame.label = l → tσ_ext (.kont k) = none := by
            intro l hl k hk hlk
            show (tσ.extend (.val ⟨x_ret, t⟩) (.denotable td_val)) (.kont k) = none
            rw [val_extend_preserves_kont]
            exact h_kont_fresh l (h_ret_labels_sub hl) k hk hlk
          have h_body_cdf_ext : ∀ l ∈ e_ret.allLabels, CallDescFresh tσ_ext t l :=
            fun l hl => (h_cdf l (h_ret_labels_sub hl)).extend_val
          have h_ret_handlerLabels_sub : e_ret.handlerLabels ⊆ hdl.handlerLabels := by
            rw [h_e_ret]
            cases hdl with | mk ret ops =>
              obtain ⟨_, _⟩ := ret
              unfold Handler.handlerLabels
              exact Finset.subset_union_left
          have h_body_hdf_ext : ∀ l ∈ e_ret.handlerLabels, HandlerDescFresh tσ_ext t l :=
            fun l hl => (h_hdf l (h_ret_handlerLabels_sub hl)).extend_val
          -- P_exp IH on e_ret
          obtain ⟨ih_exp, _, _, _, _⟩ := ih n_body (by omega)
          -- StoreScoped for extended store
          have h_store_scoped_ext : StoreScoped (σ_c.extend a_v d_val) := by
            apply storeScoped_extend h_store_scoped
            -- h_val_scoped : ValueScoped (.den d_val) σ_c = DenotableScoped d_val σ_c
            exact denotableScoped_mono h_val_scoped (fun a ha => by
              simp only [Store.extend]; split <;> [exact nofun; exact ha])
          obtain ⟨α₂, tv₂, tσ₂, h_tn_body, h_ts_body, hval₂, hstore₂, hrefl₂, hext₂,
                  h_wfv₂, hfi₂, h_wb_body, h_cb_body, h_val_scoped', h_store_scoped'⟩ :=
            ih_exp e_ret (ρ_c.extend x_ret a_v) (σ_c.extend a_v d_val) v_c' σ_c'
              h_body_c h_wf_e α' (ρ_handler.extend x_ret ta_new) tσ_ext t
              h_env' (fc_envReflects_extend_alpha h_envR h_fresh_c h_scope) h_store' h_refl' h_scope_ext h_store_scoped_ext hinv_ext
              h_body_vf_ext h_body_kf_ext h_body_cdf_ext h_body_hdf_ext
          -- WriteBound for the val extend step
          have h_wb_ext : WriteBound tσ tσ_ext t {x_ret} ∅ ∅ ∅ := by
            intro a ha
            simp only [tσ_ext] at ha
            constructor
            · intro hat; by_cases heq : a = .val ⟨x_ret, t⟩
              · subst heq; left; exact ⟨x_ret, rfl, Finset.mem_singleton_self _⟩
              · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
            · intro hne; exfalso; by_cases heq : a = .val ⟨x_ret, t⟩
              · subst heq; exact hne rfl
              · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
          have h_wb_combined := h_wb_ext.trans h_wb_body
          -- Compose outputs
          exact ⟨α₂, tv₂, tσ₂,
                 .handle_return h_ret rfl h_tn_body,
                 .handle_return h_ret rfl h_tfresh h_ts_body,
                 hval₂, hstore₂, hrefl₂,
                 h_alpha_ext.trans hext₂ (fun a ha => by
                   intro h_eq; rw [show σ_c.extend a_v d_val a = σ_c a from by
                     simp [Store.extend, show a ≠ a_v from fun heq => by subst heq; exact absurd h_fresh_c ha]] at h_eq
                   exact ha h_eq),
                 h_wfv₂, hfi₂,
                 h_wb_combined.mono
                   (by intro x hx; simp only [Finset.mem_union, Finset.mem_singleton] at hx
                       exact hx.elim (fun h => h ▸ h_xret_in) (fun h => h_ret_vars_sub h))
                   (by intro l hl; simp only [Finset.mem_union] at hl
                       rcases hl with hl | hl
                       · simp at hl
                       · exact h_ret_labels_sub hl)
                   (by intro l hl; simp only [Finset.mem_union] at hl
                       rcases hl with hl | hl
                       · simp at hl
                       · exact Finset.mem_union_right _ (h_ret_labels_sub hl))
                   (by intro l hl; simp only [Finset.mem_union] at hl
                       rcases hl with hl | hl
                       · simp at hl
                       · exact h_ret_labels_sub hl),
                 fun op args oa hv =>
                   let ⟨used, usedV, hchain, hbound, hvar_bound, htk_suf, h_bridge⟩ := h_cb_body op args oa hv
                   ⟨used, usedV, hchain, fun a' hoa htk =>
                     (hbound a' hoa htk).trans (h_ret_labels_sub.trans Finset.subset_union_right),
                     fun a' hoa htk => (hvar_bound a' hoa htk).trans h_ret_vars_sub,
                     htk_suf,
                     fun a' hoa h_ne_tk =>
                       let ⟨l_br, h_mem, h_suf⟩ := h_bridge a' hoa h_ne_tk
                       ⟨l_br, Finset.mem_union_right {l_enc} (h_ret_labels_sub h_mem), h_suf⟩⟩,
                 h_val_scoped',
                 h_store_scoped'⟩
      | handle_op h_find h_fresh_x h_fresh_k h_ne_xk h_lookup h_σ_eq h_body_c =>
        subst h_σ_eq
        cases h_val with
        | suspended h_len h_map h_kont_corr =>
          rename_i x_op e_op a_v' a_vk d_arg n_body op_name a_arg_c κ_c tas_v a_κ_prev
          have h_op_mem := fc_findOp_mem h_find
          -- Get argument denotable from store correspondence
          obtain ⟨td_arg, htσ_arg, h_den_arg⟩ := h_store _ _ h_lookup
          -- tas_v = [α a_arg_c] — now immediate from singleton value pattern
          have h_tasv_eq : tas_v = [α a_arg_c] := by
            have h_tlen1 : tas_v.length = 1 := h_len ▸ rfl
            match tas_v, h_tlen1 with
            | [ta], _ =>
              congr 1; have := h_map 0 (by simp) (by simp); simpa using this
          -- Set up first allocation: ⟨x_op, t⟩ for argument value
          let ta_x : TVAddr := ⟨x_op, t⟩
          have h_tfresh_x : tσ (.val ta_x) = none :=
            h_var_fresh _ (fc_handler_op_x_mem_topAllocVars h_op_mem)
          let ta_resume : TVAddr := ⟨"resume", t⟩
          have h_tfresh_resume : tσ (.val ta_resume) = none :=
            h_var_fresh _ (fc_handler_resume_mem_topAllocVars hdl)
          have h_ne_ta : ta_x ≠ ta_resume := by
            simp [ta_x, ta_resume]
            exact wellNamedSubHandler_x_ne_resume h_wf_hdl.wn _ h_op_mem
          have h_wf_e : WellFormedProgram e_op := wellFormedSubHandler_ops h_wf_hdl _ h_op_mem
          -- First α extension: x_op → a_v'
          let α₁ : VAddr → TVAddr := fun a => if a = a_v' then ta_x else α a
          let tσ₁ := tσ.extend (.val ta_x) (.denotable td_arg)
          -- Injectivity for first extension
          have h_inj₁ : ∀ a', σ_c a' ≠ none → α a' ≠ ta_x := by
            intro a' ha' heq
            rw [Option.ne_none_iff_exists'] at ha'; obtain ⟨d, hd⟩ := ha'
            obtain ⟨_, htσ', _⟩ := h_store a' d hd
            rw [heq] at htσ'; rw [h_tfresh_x] at htσ'; exact absurd htσ' nofun
          have h_tσ₁_mono : ∀ addr, tσ addr ≠ none → tσ₁ addr = tσ addr :=
            fun addr haddr => TStore.extend_ne _ _ _ _ (by intro heq; subst heq; exact absurd h_tfresh_x haddr)
          -- EnvCorr after first extension
          have h_env₁ : EnvCorr α₁ (ρ_c.extend x_op a_v') (ρ_handler.extend x_op ta_x) := by
            intro v a hxa; simp only [Env.extend] at hxa; split at hxa
            · rename_i heq; subst heq; injection hxa with hxa; subst hxa; simp [α₁, TEnv.lookup_extend_same]
            · rename_i hne; have ha_ne : a ≠ a_v' := fun heq => by subst heq; exact absurd h_fresh_x (h_scope _ _ hxa)
              rw [show α₁ a = α a from if_neg ha_ne, TEnv.lookup_extend_ne _ _ _ _ hne]; exact h_env _ _ hxa
          -- StoreCorr after first extension
          have h_store₁ : StoreCorr α₁ tσ₁ (σ_c.extend a_v' d_arg) := by
            intro a d hσ'; simp only [Store.extend] at hσ'
            split at hσ'
            · rename_i heq; subst heq; injection hσ' with hσ'; subst hσ'
              rw [show α₁ a = ta_x from if_pos rfl]
              exact ⟨td_arg, TStore.extend_same _ _ _, fc_denotableCorr_of_alpha_extends_fresh h_den_arg
                (fun a' ha' => if_neg (fun heq => by subst heq; exact absurd h_fresh_x ha'))
                h_tσ₁_mono (h_store_scoped _ _ h_lookup)⟩
            · rename_i hne
              rw [show α₁ a = α a from if_neg hne]
              have hne' : TAddr.val (α a) ≠ TAddr.val ta_x := by
                intro heq; exact h_inj₁ a (by rw [hσ']; exact nofun) (TAddr.val.inj heq)
              rw [show tσ₁ (.val (α a)) = tσ (.val (α a)) from TStore.extend_ne _ _ _ _ hne']
              obtain ⟨td, htσ, hd⟩ := h_store a d hσ'
              exact ⟨td, htσ, fc_denotableCorr_of_alpha_extends_fresh hd
                (fun a' ha' => if_neg (fun heq => by subst heq; exact absurd h_fresh_x ha'))
                h_tσ₁_mono (h_store_scoped _ _ hσ')⟩
          -- StoreReflects after first extension
          have h_refl₁ : StoreReflects α₁ tσ₁ (σ_c.extend a_v' d_arg) := by
            intro ta h_ne
            simp only [tσ₁, TStore.extend] at h_ne
            split at h_ne
            · rename_i heq; exact ⟨a_v', by simp [Store.extend], by simp [α₁, TAddr.val.inj heq]⟩
            · rename_i hne_ta
              obtain ⟨a, ha, hα⟩ := h_refl ta h_ne
              have ha_ne : a ≠ a_v' := by intro heq; subst heq; exact absurd h_fresh_x ha
              refine ⟨a, ?_, ?_⟩
              · simp [Store.extend]; split
                · rename_i heq; exact absurd heq ha_ne
                · exact ha
              · simp only [α₁]; rw [if_neg ha_ne]; exact hα
          -- AlphaExtends for first extension
          have h_alpha_ext₁ : AlphaExtends α α₁ σ_c :=
            fun a ha => show α₁ a = α a from if_neg (fun heq => by subst heq; exact absurd h_fresh_x ha)
          -- EnvScoped after first extension
          have h_scope₁ : EnvScoped (ρ_c.extend x_op a_v') (σ_c.extend a_v' d_arg) := by
            intro v a hxa; simp only [Env.extend] at hxa; split at hxa
            · injection hxa with hxa; subst hxa; simp [Store.extend]
            · have := h_scope _ _ hxa
              intro h_eq; rw [show σ_c.extend a_v' d_arg a = σ_c a from by simp [Store.extend, show a ≠ a_v' from fun heq => by subst heq; exact absurd h_fresh_x (h_scope _ _ hxa)]] at h_eq
              exact this h_eq
          -- Second allocation: ⟨"resume", t⟩ for kontClosure
          let d_kont_c : Denotable := .kontClosure hdl ρ_c κ_c
          let td_kont : TDenotable := .kontClosure hdl ρ_handler a_κ_prev
          -- DenotableCorr for the kontClosure (build at α/tσ level, then lift)
          have h_den_kont_orig : DenotableCorr α tσ d_kont_c td_kont :=
            DenotableCorr.kontClosure h_env h_envR h_kont_corr
          have h_den_kont : DenotableCorr α₁ tσ₁ d_kont_c td_kont :=
            fc_denotableCorr_of_alpha_extends_fresh h_den_kont_orig
              (fun a ha => if_neg (fun heq => by subst heq; exact absurd h_fresh_x ha))
              h_tσ₁_mono ⟨h_scope, h_val_scoped.2⟩
          let α₂ : VAddr → TVAddr := fun a => if a = a_vk then ta_resume else α₁ a
          let tσ₂ := tσ₁.extend (.val ta_resume) (.denotable td_kont)
          -- Fresh resume in tσ₁
          have h_ne_taddr : (TAddr.val ta_resume : TAddr) ≠ TAddr.val ta_x := by
            intro h; exact h_ne_ta (TAddr.val.inj h).symm
          have h_tfresh_resume₁ : tσ₁ (.val ta_resume) = none := by
            show (tσ.extend (.val ta_x) (.denotable td_arg)) (.val ta_resume) = none
            rw [TStore.extend_ne _ _ _ _ h_ne_taddr]
            exact h_tfresh_resume
          -- Injectivity for second extension
          have h_inj₂ : ∀ a', (σ_c.extend a_v' d_arg) a' ≠ none → α₁ a' ≠ ta_resume := by
            intro a' ha' heq
            simp only [Store.extend] at ha'
            split at ha'
            · rename_i heq_a; subst heq_a; simp [α₁] at heq
              have : x_op = "resume" := by
                have := congr_arg TVAddr.name heq; simp [ta_x, ta_resume] at this; exact this
              exact absurd this (wellNamedSubHandler_x_ne_resume h_wf_hdl.wn _ h_op_mem)
            · rw [Option.ne_none_iff_exists'] at ha'; obtain ⟨d, hd⟩ := ha'
              obtain ⟨_, htσ', _⟩ := h_store a' d hd
              have : α₁ a' = α a' := if_neg (fun heq_av => by subst heq_av; exact absurd h_fresh_x (by rw [hd]; exact nofun))
              rw [this] at heq
              rw [show α a' = ta_resume from heq] at htσ'
              rw [h_tfresh_resume] at htσ'; exact absurd htσ' nofun
          have h_tσ₂_mono : ∀ addr, tσ₁ addr ≠ none → tσ₂ addr = tσ₁ addr :=
            fun addr haddr => TStore.extend_ne _ _ _ _ (by intro heq; subst heq; exact absurd h_tfresh_resume₁ haddr)
          -- EnvCorr after second extension
          have h_env₂ : EnvCorr α₂ ((ρ_c.extend x_op a_v').extend "resume" a_vk) ((ρ_handler.extend x_op ta_x).extend "resume" ta_resume) := by
            intro v a hxa; simp only [Env.extend] at hxa; split at hxa
            · rename_i heq; subst heq; injection hxa with hxa; subst hxa; simp [α₂, TEnv.lookup_extend_same]
            · rename_i hne
              rw [TEnv.lookup_extend_ne _ _ _ _ hne]
              have ha_ne : a ≠ a_vk := by
                intro heq; subst heq
                have h_sc := h_scope₁ _ _ hxa
                rw [show (σ_c.extend a_v' d_arg) a = σ_c a from by
                  unfold Store.extend; rw [if_neg (Ne.symm h_ne_xk)]] at h_sc
                exact absurd h_fresh_k h_sc
              rw [show α₂ a = α₁ a from if_neg ha_ne]
              exact h_env₁ _ _ hxa
          -- Helper: a_vk not in domain of σ_c.extend a_v' d_arg
          have h_vk_fresh_ext : (σ_c.extend a_v' d_arg) a_vk = none := by
            unfold Store.extend; rw [if_neg (Ne.symm h_ne_xk)]; exact h_fresh_k
          -- Helper for alpha₂ ↔ α₁ on (σ_c.extend a_v' d_arg)-live addresses
          have h_α₂_eq_α₁ : ∀ a, (σ_c.extend a_v' d_arg) a ≠ none → α₂ a = α₁ a :=
            fun a ha => if_neg (fun heq => by subst heq; exact absurd h_vk_fresh_ext ha)
          -- StoreCorr after second extension
          have h_store₂ : StoreCorr α₂ tσ₂ ((σ_c.extend a_v' d_arg).extend a_vk d_kont_c) := by
            intro a d hσ'
            by_cases ha_eq : a = a_vk
            · rw [ha_eq] at hσ' ⊢
              have : d = d_kont_c := by unfold Store.extend at hσ'; simp at hσ'; exact hσ'.symm
              subst this
              rw [show α₂ a_vk = ta_resume from if_pos rfl]
              exact ⟨td_kont, TStore.extend_same _ _ _,
                fc_denotableCorr_of_alpha_extends_fresh h_den_kont h_α₂_eq_α₁ h_tσ₂_mono
                  (denotableScoped_mono ⟨h_scope, h_val_scoped.2⟩ (fun a ha => by
                    simp only [Store.extend]; split <;> [exact nofun; exact ha]))⟩
            · have hσ'_inner : (σ_c.extend a_v' d_arg) a = some d := by
                unfold Store.extend at hσ'; rw [if_neg ha_eq] at hσ'; exact hσ'
              rw [show α₂ a = α₁ a from if_neg ha_eq]
              have hne' : TAddr.val (α₁ a) ≠ TAddr.val ta_resume := by
                intro heq; exact h_inj₂ a (by rw [hσ'_inner]; exact nofun) (TAddr.val.inj heq)
              rw [show tσ₂ (.val (α₁ a)) = tσ₁ (.val (α₁ a)) from TStore.extend_ne _ _ _ _ hne']
              obtain ⟨td, htσ, hd⟩ := h_store₁ a d hσ'_inner
              have h_d_scoped : DenotableScoped d (σ_c.extend a_v' d_arg) := by
                have : StoreScoped (σ_c.extend a_v' d_arg) := storeScoped_extend h_store_scoped
                  (denotableScoped_mono (h_store_scoped _ _ h_lookup) (fun a ha => by
                    simp only [Store.extend]; split <;> [exact nofun; exact ha]))
                exact this _ _ hσ'_inner
              exact ⟨td, htσ, fc_denotableCorr_of_alpha_extends_fresh hd h_α₂_eq_α₁ h_tσ₂_mono
                h_d_scoped⟩
          -- StoreReflects after second extension
          have h_refl₂ : StoreReflects α₂ tσ₂ ((σ_c.extend a_v' d_arg).extend a_vk d_kont_c) := by
            intro ta h_ne
            simp only [tσ₂, TStore.extend] at h_ne
            split at h_ne
            · rename_i heq; exact ⟨a_vk, by simp [Store.extend], by simp [α₂, TAddr.val.inj heq]⟩
            · rename_i hne_ta
              obtain ⟨a, ha, hα⟩ := h_refl₁ ta h_ne
              have ha_ne : a ≠ a_vk := by
                intro heq; subst heq
                have : (σ_c.extend a_v' d_arg) a = σ_c a := by
                  unfold Store.extend; rw [if_neg (Ne.symm h_ne_xk)]
                rw [this] at ha; exact absurd h_fresh_k ha
              refine ⟨a, ?_, ?_⟩
              · simp [Store.extend]; split
                · rename_i heq; exact absurd heq ha_ne
                · exact ha
              · simp only [α₂]; rw [if_neg ha_ne]; exact hα
          -- EnvScoped after second extension
          have h_scope₂ : EnvScoped ((ρ_c.extend x_op a_v').extend "resume" a_vk) ((σ_c.extend a_v' d_arg).extend a_vk d_kont_c) := by
            intro v a hxa; simp only [Env.extend] at hxa; split at hxa
            · injection hxa with hxa; subst hxa; simp [Store.extend]
            · have h_sc := h_scope₁ _ _ hxa
              have ha_ne_vk : a ≠ a_vk := by
                intro heq; subst heq
                rw [show (σ_c.extend a_v' d_arg) a = σ_c a from by
                  unfold Store.extend; rw [if_neg (Ne.symm h_ne_xk)]] at h_sc
                exact absurd h_fresh_k h_sc
              intro h_eq
              rw [show (σ_c.extend a_v' d_arg).extend a_vk d_kont_c a = (σ_c.extend a_v' d_arg) a from by
                unfold Store.extend; rw [if_neg ha_ne_vk]] at h_eq
              exact h_sc h_eq
          -- FreshInvariant after first val extend
          have h_wf_d_arg : WellFormedStorable (.denotable td_arg) :=
            wellFormedStorable_of_store_lookup hinv.wf_store htσ_arg
          have hinv₁ := hinv.extend_val ⟨x_op, t⟩ _ h_wf_d_arg
            (fun hdl' ρ' oa heq => by cases heq; exact hinv.pairwiseChain_of_lookup htσ_arg)
          -- FreshInvariant after second val extend
          have h_wf_d_kont : WellFormedStorable (.denotable td_kont) := h_wf_hdl
          have hinv₂ := hinv₁.extend_val ⟨"resume", t⟩ _ h_wf_d_kont
            (fun hdl' ρ' oa heq => by
              have h_eq := TStorable.denotable.inj heq
              have h_oa : oa = a_κ_prev := by simp [td_kont] at h_eq; exact h_eq.2.2.symm
              subst h_oa
              obtain ⟨u, uv, hc⟩ := h_wfv.suspChain op_name tas_v oa rfl
              exact ⟨u, uv, hc.extend_val _ _⟩)
          -- Subset lemmas
          have h_op_labels_sub : e_op.allLabels ⊆ hdl.allLabels := fc_handler_op_allLabels_sub h_op_mem
          have h_op_vars_sub : e_op.topAllocVars ⊆ hdl.topAllocVars := handler_op_topAllocVars_subset h_op_mem
          have h_x_in : x_op ∈ hdl.topAllocVars := fc_handler_op_x_mem_topAllocVars h_op_mem
          have h_resume_in : "resume" ∈ hdl.topAllocVars := fc_handler_resume_mem_topAllocVars hdl
          have h_x_notin_op : x_op ∉ e_op.topAllocVars :=
            wellNamedSubHandler_x_notin_op_body h_wf_hdl.wn _ h_op_mem
          have h_resume_notin_op : "resume" ∉ e_op.topAllocVars :=
            wellNamedSubHandler_resume_notin_op_body h_wf_hdl.wn _ h_op_mem
          -- Freshness preconditions for body IH (after two val extends)
          have h_body_vf : ∀ v ∈ e_op.topAllocVars, tσ₂ (.val ⟨v, t⟩) = none := by
            intro v hv
            show (tσ.extend (.val ta_x) (.denotable td_arg)).extend (.val ta_resume) (.denotable td_kont) (.val ⟨v, t⟩) = none
            rw [val_extend_preserves_val_ne (ne_of_mem_of_not_mem hv h_resume_notin_op)]
            rw [val_extend_preserves_val_ne (ne_of_mem_of_not_mem hv h_x_notin_op)]
            exact h_var_fresh v (h_op_vars_sub hv)
          have h_body_kf : ∀ l ∈ e_op.allLabels, ∀ k : TKAddr,
              k.frame.time = t → k.frame.label = l → tσ₂ (.kont k) = none := by
            intro l hl k hk hlk
            show (tσ.extend (.val ta_x) (.denotable td_arg)).extend (.val ta_resume) (.denotable td_kont) (.kont k) = none
            rw [val_extend_preserves_kont, val_extend_preserves_kont]
            exact h_kont_fresh l (h_op_labels_sub hl) k hk hlk
          have h_body_cdf : ∀ l ∈ e_op.allLabels, CallDescFresh tσ₂ t l :=
            fun l hl => (h_cdf l (h_op_labels_sub hl)).extend_val.extend_val
          have h_op_handlerLabels_sub : e_op.handlerLabels ⊆ hdl.handlerLabels :=
            fc_handler_op_handlerLabels_sub h_op_mem
          have h_body_hdf : ∀ l ∈ e_op.handlerLabels, HandlerDescFresh tσ₂ t l :=
            fun l hl => (h_hdf l (h_op_handlerLabels_sub hl)).extend_val.extend_val
          -- P_exp IH on e_op
          obtain ⟨ih_exp, _, _, _, _⟩ := ih n_body (by omega)
          -- StoreScoped for double-extended store
          have h_store_scoped₁ : StoreScoped (σ_c.extend a_v' d_arg) := by
            apply storeScoped_extend h_store_scoped
            exact denotableScoped_mono (h_store_scoped _ _ h_lookup) (fun a ha => by
              simp only [Store.extend]; split <;> [exact nofun; exact ha])
          have h_store_scoped₂ : StoreScoped ((σ_c.extend a_v' d_arg).extend a_vk d_kont_c) := by
            apply storeScoped_extend h_store_scoped₁
            -- DenotableScoped d_kont_c ((σ_c.extend a_v' d_arg).extend a_vk d_kont_c)
            -- d_kont_c = .kontClosure hdl ρ_c κ_c
            -- Need EnvScoped ρ_c σ_c ∧ KontScoped κ_c σ_c, monotoned to double-extended store
            have h_mono2 : ∀ a, σ_c a ≠ none → ((σ_c.extend a_v' d_arg).extend a_vk d_kont_c) a ≠ none := by
              intro a ha; simp only [Store.extend]; split <;> [exact nofun; split <;> [exact nofun; exact ha]]
            constructor
            · exact fun x a hxa => h_mono2 _ (h_scope x a hxa)
            · exact fun f hf => by
                have hfs := h_val_scoped.2 f hf
                cases f with
                | letFrame clo => exact fun x a hxa => h_mono2 _ (hfs x a hxa)
                | handlerFrame _ ρ' => exact fun x a hxa => h_mono2 _ (hfs x a hxa)
          obtain ⟨α₃, tv₃, tσ₃, h_tn_body, h_ts_body, hval₃, hstore₃, hrefl₃, hext₃,
                  h_wfv₃, hfi₃, h_wb_body, h_cb_body, h_val_scoped', h_store_scoped'⟩ :=
            ih_exp e_op ((ρ_c.extend x_op a_v').extend "resume" a_vk)
              ((σ_c.extend a_v' d_arg).extend a_vk d_kont_c) v_c' σ_c'
              h_body_c h_wf_e α₂ ((ρ_handler.extend x_op ta_x).extend "resume" ta_resume) tσ₂ t
              h_env₂ (fc_envReflects_extend_alpha
                (fc_envReflects_extend_alpha h_envR h_fresh_x h_scope) h_vk_fresh_ext h_scope₁)
                h_store₂ h_refl₂ h_scope₂ h_store_scoped₂ hinv₂
              h_body_vf h_body_kf h_body_cdf h_body_hdf
          -- WriteBound for the first val extend step
          have h_wb_ext₁ : WriteBound tσ tσ₁ t {x_op} ∅ ∅ ∅ := by
            intro a ha
            simp only [tσ₁] at ha
            constructor
            · intro hat; by_cases heq : a = .val ⟨x_op, t⟩
              · subst heq; left; exact ⟨x_op, rfl, Finset.mem_singleton_self _⟩
              · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
            · intro hne; exfalso; by_cases heq : a = .val ⟨x_op, t⟩
              · subst heq; exact hne rfl
              · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
          -- WriteBound for the second val extend step
          have h_wb_ext₂ : WriteBound tσ₁ tσ₂ t {"resume"} ∅ ∅ ∅ := by
            intro a ha
            simp only [tσ₂] at ha
            constructor
            · intro hat; by_cases heq : a = .val ⟨"resume", t⟩
              · subst heq; left; exact ⟨"resume", rfl, Finset.mem_singleton_self _⟩
              · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
            · intro hne; exfalso; by_cases heq : a = .val ⟨"resume", t⟩
              · subst heq; exact hne rfl
              · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
          have h_wb_combined := (h_wb_ext₁.trans h_wb_ext₂).trans h_wb_body
          -- AlphaExtends composition
          have h_alpha_ext₂ : AlphaExtends α₁ α₂ (σ_c.extend a_v' d_arg) :=
            fun a ha => show α₂ a = α₁ a from if_neg (fun heq => by
              rw [heq] at ha; rw [show (σ_c.extend a_v' d_arg) a_vk = σ_c a_vk from by
                unfold Store.extend; rw [if_neg (Ne.symm h_ne_xk)]] at ha
              exact absurd h_fresh_k ha)
          have h_alpha_composed : AlphaExtends α α₂ σ_c :=
            h_alpha_ext₁.trans h_alpha_ext₂ (fun a ha => by
              intro h_eq; rw [show σ_c.extend a_v' d_arg a = σ_c a from by
                simp [Store.extend, show a ≠ a_v' from fun heq => by subst heq; exact absurd h_fresh_x ha]] at h_eq
              exact ha h_eq)
          -- Compose outputs
          have h_tσ_lookup : tσ (.val (α (a_arg_c))) = some (.denotable td_arg) := htσ_arg
          exact ⟨α₃, tv₃, tσ₃,
                 .handle_op h_find rfl rfl h_tasv_eq h_tσ_lookup rfl rfl h_tn_body,
                 .handle_op h_find rfl rfl h_tfresh_x h_tfresh_resume h_ne_ta
                   h_tasv_eq h_tσ_lookup rfl rfl h_ts_body,
                 hval₃, hstore₃, hrefl₃,
                 h_alpha_composed.trans hext₃ (fun a ha => by
                   intro h_eq
                   have ha_ne_v' : a ≠ a_v' := fun heq => by subst heq; exact absurd h_fresh_x ha
                   have ha_ne_vk : a ≠ a_vk := fun heq => by subst heq; exact absurd h_fresh_k ha
                   rw [show (σ_c.extend a_v' d_arg).extend a_vk d_kont_c a = σ_c a from by
                     simp [Store.extend, ha_ne_vk, ha_ne_v']] at h_eq
                   exact ha h_eq),
                 h_wfv₃, hfi₃,
                 h_wb_combined.mono
                   (by intro v hv; simp only [Finset.mem_union, Finset.mem_singleton] at hv
                       rcases hv with (hv | hv) | hv
                       · exact hv ▸ h_x_in
                       · exact hv ▸ h_resume_in
                       · exact h_op_vars_sub hv)
                   (by intro l hl; simp only [Finset.mem_union] at hl
                       rcases hl with (hl | hl) | hl
                       · simp at hl
                       · simp at hl
                       · exact h_op_labels_sub hl)
                   (by intro l hl; simp only [Finset.mem_union] at hl
                       rcases hl with (hl | hl) | hl
                       · simp at hl
                       · simp at hl
                       · exact Finset.mem_union_right _ (h_op_labels_sub hl))
                   (by intro l hl; simp only [Finset.mem_union] at hl
                       rcases hl with (hl | hl) | hl
                       · simp at hl
                       · simp at hl
                       · exact h_op_labels_sub hl),
                 fun op args oa hv =>
                   let ⟨used, usedV, hchain, hbound, hvar_bound, htk_suf, h_bridge⟩ := h_cb_body op args oa hv
                   ⟨used, usedV, hchain, fun a' hoa htk =>
                     (hbound a' hoa htk).trans (h_op_labels_sub.trans Finset.subset_union_right),
                     fun a' hoa htk => (hvar_bound a' hoa htk).trans h_op_vars_sub,
                     htk_suf,
                     fun a' hoa h_ne_tk =>
                       let ⟨l_br, h_mem, h_suf⟩ := h_bridge a' hoa h_ne_tk
                       ⟨l_br, Finset.mem_union_right {l_enc} (h_op_labels_sub h_mem), h_suf⟩⟩,
                 h_val_scoped',
                 h_store_scoped'⟩
      | handle_capture_op h_no_op h_v'_eq =>
        subst h_v'_eq
        rename_i op_name as_v_c κ_c
        cases h_val with
        | suspended h_len h_map h_kont_corr =>
          rename_i tas_v a_κ_prev
          let a_κ_new : TKAddr := ⟨⟨.handlerFrame hdl ρ_handler, t, l_enc⟩, op_name⟩
          have h_fresh : tσ (.kont a_κ_new) = none :=
            h_kont_enc_fresh a_κ_new rfl rfl
          let tσ' := tσ.extend (.kont a_κ_new) (.kontLink a_κ_prev)
          have h_tσ_mono : ∀ addr, tσ addr ≠ none → tσ' addr = tσ addr :=
            fun addr h => TStore.extend_ne _ _ _ _ (fun heq => by subst heq; exact absurd h_fresh h)
          -- Correspondence preserved (kont extend doesn't affect val addresses)
          have h_kont_corr' : KontCorr α tσ' (Frame.handlerFrame hdl ρ_c :: κ_c) (some a_κ_new) :=
            .cons (TStore.extend_same _ _ _) (FrameCorr.handlerFrame h_env h_envR) (h_kont_corr.mono h_tσ_mono)
          have h_val' : ValueCorr α tσ' (.suspended op_name as_v_c (Frame.handlerFrame hdl ρ_c :: κ_c))
              (.suspended op_name tas_v (some a_κ_new)) :=
            .suspended h_len h_map h_kont_corr'
          have h_store' : StoreCorr α tσ' σ_c := by
            intro a d hσ
            obtain ⟨td, htσ, hd⟩ := h_store a d hσ
            have hne : TAddr.val (α a) ≠ TAddr.kont a_κ_new := by intro h; cases h
            refine ⟨td, ?_, hd.mono h_tσ_mono⟩
            show tσ' (.val (α a)) = some (.denotable td)
            simp only [tσ', TStore.extend_ne _ _ _ _ hne]
            exact htσ
          have h_refl' : StoreReflects α tσ' σ_c := by
            intro ta h_ne
            have hne : (TAddr.val ta) ≠ TAddr.kont a_κ_new := by intro h; cases h
            simp only [tσ', TStore.extend_ne _ _ _ _ hne] at h_ne
            exact h_refl ta h_ne
          -- WriteBound
          have h_wb : WriteBound tσ tσ' t ∅ ∅ {l_enc} ∅ := by
            intro a ha; constructor
            · intro hat; by_cases heq : a = .kont a_κ_new
              · subst heq; right; right; exact ⟨a_κ_new, rfl, rfl, Finset.mem_singleton_self _⟩
              · simp only [tσ', TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
            · intro hne; exfalso; by_cases heq : a = .kont a_κ_new
              · subst heq; exact hne rfl
              · simp only [tσ', TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
          -- WellFormedValue6
          have h_wfv6 : WellFormedValue6 tσ' (.suspended op_name tas_v (some a_κ_new)) := by
            refine ⟨trivial, fun _ _ _ h => ?_, fun _ _ _ h => ?_⟩
            · cases h
            · cases h
              obtain ⟨innerUsed, innerVars, h_inner_chain⟩ := h_wfv.suspChain op_name tas_v a_κ_prev rfl
              exact ⟨_, _, .handler_frame (a_κ := a_κ_new) (TStore.extend_same _ _ _) rfl h_wf_hdl
                h_lenc_notin (h_inner_chain.extend_kont a_κ_new _ h_fresh)⟩
          have h_cb : FCChainBound tσ' (.suspended op_name tas_v (some a_κ_new)) t ({l_enc} ∪ hdl.allLabels) ({l_enc} ∪ hdl.allLabels) hdl.topAllocVars := by
            intro op args oa hv; cases hv
            obtain ⟨innerUsed2, innerVars2, h_ic2⟩ := h_wfv.suspChain op_name tas_v a_κ_prev rfl
            exact ⟨_, _, .handler_frame (a_κ := a_κ_new) (TStore.extend_same _ _ _) rfl h_wf_hdl
              h_lenc_notin (h_ic2.extend_kont a_κ_new _ h_fresh),
              fun _ _ _ => Finset.Subset.refl _,
              fun _ _ _ => Finset.Subset.refl _,
              fun _ hoa => by cases hoa; exact List.suffix_refl _,
              fun a' hoa h_ne_tk => by cases hoa; exact absurd rfl h_ne_tk⟩
          exact ⟨α, .suspended op_name tas_v (some a_κ_new), tσ',
                 .handle_capture_op h_no_op rfl rfl rfl,
                 .handle_capture_op h_no_op rfl rfl h_fresh rfl,
                 h_val', h_store', h_refl', AlphaExtends.refl,
                 h_wfv6,
                 hinv.extend_kont a_κ_new _ (fun k hk_t hk_l _ => h_kont_enc_fresh k hk_t hk_l),
                 h_wb.mono (by simp) (by simp)
                   (by intro l hl; exact Finset.mem_union_left _ hl)
                   (by simp),
                 h_cb,
                 -- ValueScoped (.suspended op_name as_v_c (Frame.handlerFrame hdl ρ_c :: κ_c)) σ_c
                 ⟨h_val_scoped.1, fun f hf => by
                   rcases List.mem_cons.mp hf with rfl | hf
                   · exact h_scope
                   · exact h_val_scoped.2 f hf⟩,
                 h_store_scoped⟩
    -- P_apply
    · intro κ_c d_c σ_c v_c σ_c' oa_κ td tmk chainLabels chainVars
        h_eval α tσ h_kont h_den h_store h_refl h_store_scoped h_den_scoped h_kont_scoped
        h_wf_d h_d_chain hinv h_tmk_fresh h_chain
      cases h_eval with
      | apply_continue =>
        cases h_kont
        have h_wfv6 : WellFormedValue6 tσ (.den td) := by
          refine ⟨WellFormedValue.of_wellFormedStorable h_wf_d, fun hdl ρ oa h => ?_, fun _ _ _ h => ?_⟩
          · cases h; exact h_d_chain hdl ρ oa rfl
          · cases h
        exact ⟨α, .den td, tσ,
               .apply_continue, .apply_continue,
               ValueCorr.den h_den, h_store, h_refl, AlphaExtends.refl,
               h_wfv6, hinv, fun a h => absurd rfl h,
               fun a_κ₀ h => absurd h (by simp),
               fun a_κ₀ h => absurd h (by simp),
               fun a_κ₀ h => absurd h (by simp),
               fun a_κ₀ h => absurd h (by simp),
               (fun op args oa hv => by cases hv),
               h_den_scoped,
               h_store_scoped⟩
      | apply_restore h_apply h_cont =>
        -- Decompose KontCorr: Frame.letFrame clo :: κ ↔ some a_κ
        cases h_kont with
        | cons h_kont_lookup h_kont_frame h_kont_rest =>
          -- h_kont_lookup : tσ (.kont a_κ) = some (.kontLink a_next)
          -- h_kont_frame : FrameCorr α (Frame.letFrame clo✝) a_κ.frame.content
          -- h_kont_rest : KontCorr α tσ κ✝ a_next
          rename_i n1_c κ_inner v_mid σ_mid n2_c clo_c a_κ a_next
          cases h_chain with
          | same_tk h_lookup' h_content' h_wfp h_y_notin_body _ceLabels_stk h_stk_sub_ce h_disj_ce h_lnb_ce_stk h_lnb h_inner_label_in_ce h_tk_eq h_disj_vars h_inner =>
            rw [h_lookup'] at h_kont_lookup; cases h_kont_lookup
            rw [h_content'] at h_kont_frame
            cases h_kont_frame with
            | letFrame h_clo_corr =>
              -- same_tk apply_restore: inner chain at SAME tk
              -- Step 1: IH P_apply on inner kont
              rename_i sameTkLabels sameTkVars clo_t
              obtain ⟨_, _, _, _, ih_apply⟩ := ih n1_c (by omega)
              have h_kont_scoped_inner : KontScoped κ_inner σ_c :=
                fun f hf => h_kont_scoped f (.tail _ hf)
              obtain ⟨α₁, tv₁, tσ₁, h_tn_apply, h_ts_apply, hval₁, hstore₁, hrefl₁, hext₁,
                      h_wfv1, hinv1, h_desc1, h_dfp1, h_hdfp1, h_sd1, h_stw1, h_cb1,
                      h_val_scoped₁, h_store_scoped₁⟩ :=
                ih_apply κ_inner d_c σ_c v_mid σ_mid a_next td tmk sameTkLabels sameTkVars
                  h_apply α tσ h_kont_rest h_den h_store h_refl h_store_scoped h_den_scoped
                  h_kont_scoped_inner h_wf_d h_d_chain hinv h_tmk_fresh h_inner
              -- Step 2: IH P_continue on letFrame
              obtain ⟨_, _, ih_cont, _, _⟩ := ih n2_c (by omega)
              -- Need to prepare ~20 freshness preconditions for ih_cont
              -- Key: apply doesn't write at addresses outside its chain bounds (h_stw1, h_sd1)
              -- The frame's body labels/vars are disjoint from the chain (h_disj_ce, h_disj_vars)
              have h_clo_corr₁ : ClosureCorr α₁ clo_c clo_t :=
                h_clo_corr.of_alpha_scoped (hext₁ · ·) (h_kont_scoped _ (.head _))
              let t_restored : Time := ⟨a_κ.frame.time.tk, tmk⟩
              -- Build h_cb_n1r: ChainBound at a_κ time level from h_cb1
              have h_cb_n1r : FCChainBound tσ₁ tv₁ t_restored sameTkLabels sameTkLabels sameTkVars := by
                cases h_fr : a_next with
                | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; intro op args oa hv; cases hv
                | some ap =>
                  rw [h_fr] at h_cb1
                  have h_tk := h_tk_eq ap h_fr
                  have h_ap_in_stk : ap.frame.label ∈ sameTkLabels := by
                    rw [h_fr] at h_inner; exact h_inner.frame_label_mem
                  intro op args oa hv
                  obtain ⟨used, usedVars, hpc, hsub_l, hsub_v, hsuf, hbr⟩ := h_cb1 op args oa hv
                  simp only at hsub_l hsub_v hsuf hbr
                  have h_ap_stk_eq : {ap.frame.label} ∪ sameTkLabels = sameTkLabels :=
                    Finset.union_eq_right.mpr (Finset.singleton_subset_iff.mpr h_ap_in_stk)
                  exact ⟨used, usedVars, hpc,
                    fun a' hoa htk => h_ap_stk_eq ▸ hsub_l a' hoa (h_tk ▸ htk),
                    fun a' hoa htk => hsub_v a' hoa (h_tk ▸ htk),
                    fun a' hoa => by simp [t_restored]; rw [h_tk]; exact hsuf a' hoa,
                    fun a' hoa hne => by
                      obtain ⟨lb, hlb, hsuf'⟩ := hbr a' hoa (fun h => hne (by simp [t_restored]; rw [h_tk]; exact h))
                      exact ⟨lb, h_ap_stk_eq ▸ hlb, by simp [t_restored]; rw [h_tk]; exact hsuf'⟩⟩
              obtain ⟨α₂, tv₂, tσ₂, h_tn_cont, h_ts_cont, hval₂, hstore₂, hrefl₂, hext₂,
                      h_wfv2, hinv2, ⟨dls, hdls_sub, hdls_excl, h_wb2⟩, h_cb2,
                      h_val_scoped₂, h_store_scoped₂⟩ :=
                ih_cont (Frame.letFrame clo_c) v_mid σ_mid v_c σ_c'
                  a_κ.frame.label (.letFrame clo_t) t_restored
                  (clo_t.params.toFinset ∪ clo_t.body.topAllocVars ∪ sameTkVars)
                  ({a_κ.frame.label} ∪ clo_t.body.allLabels ∪ sameTkLabels)
                  h_cont α₁ tv₁ tσ₁
                  (.letFrame h_clo_corr₁) hval₁ hstore₁ hrefl₁
                  (fun clo heq => by cases heq; exact envScoped_mono (h_kont_scoped (.letFrame clo_c) (.head _)) (fun a ha => by
                    intro h_eq; cases h_σ : σ_c a with
                    | none => exact ha h_σ
                    | some d => have := eval_apply_store_mono (apply_kontN_to h_apply) a d h_σ; rw [h_eq] at this; exact absurd this (by simp)))
                  h_store_scoped₁ h_val_scoped₁ h_wfv1 hinv1
                  (fun c h => by cases h; exact h_wfp)
                  (fun y e ρ h => by
                    cases h
                    by_contra h_ne; push Not at h_ne
                    have h_σ_none := h_tmk_fresh (.val ⟨y, t_restored⟩) (List.suffix_refl _)
                    have h_changed : tσ₁ (.val ⟨y, t_restored⟩) ≠ tσ (.val ⟨y, t_restored⟩) := by
                      rw [h_σ_none]; exact h_ne
                    cases h_fr : a_next with
                    | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; exact h_changed rfl
                    | some ap =>
                      have h_tk := h_tk_eq ap h_fr
                      rcases h_stw1 ap h_fr (.val ⟨y, t_restored⟩) h_changed (by simp [TAddr.time]; exact h_tk) rfl with
                        ⟨x, hx_eq, hx_mem⟩ | ⟨k, hk_eq, _⟩
                      · cases hx_eq
                        exact Finset.disjoint_left.mp (h_disj_vars y rfl)
                          (Finset.mem_union_left _ (Finset.mem_singleton_self _)) hx_mem
                      · cases hk_eq)
                  (fun k hk hlk _hlet => by
                    by_contra h_ne; push Not at h_ne
                    have h_σ_none := h_tmk_fresh (.kont k) (by simp [TAddr.time]; rw [hk])
                    have h_changed : tσ₁ (.kont k) ≠ tσ (.kont k) := by rw [h_σ_none]; exact h_ne
                    cases h_fr : a_next with
                    | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; exact h_changed rfl
                    | some ap =>
                      have h_tk := h_tk_eq ap h_fr
                      rcases h_stw1 ap h_fr (.kont k) h_changed (by simp [TAddr.time]; rw [hk]; exact h_tk) (by simp [TAddr.time]; rw [hk]) with
                        ⟨_, hx_eq, _⟩ | ⟨k', hk_eq, hk_mem⟩
                      · cases hx_eq
                      · cases hk_eq
                        -- k.frame.label = a_κ.frame.label (from hlk)
                        -- a_κ.frame.label ∉ _ceLabels_stk (from h_lnb_ce_stk)
                        -- {ap.frame.label} ∪ sameTkLabels ⊆ _ceLabels_stk
                        rw [hlk] at hk_mem
                        rcases Finset.mem_union.mp hk_mem with h_ap | h_stk
                        · exact h_lnb_ce_stk (Finset.mem_singleton.mp h_ap ▸ h_inner_label_in_ce ap h_fr)
                        · exact h_lnb_ce_stk (h_stk_sub_ce h_stk))
                  (fun y e ρ h => by cases h; exact h_y_notin_body y rfl)
                  (fun y e ρ h => by
                    cases h; intro x hx
                    by_contra h_ne; push Not at h_ne
                    have h_σ_none := h_tmk_fresh (.val ⟨x, t_restored⟩) (List.suffix_refl _)
                    have h_changed : tσ₁ (.val ⟨x, t_restored⟩) ≠ tσ (.val ⟨x, t_restored⟩) := by
                      rw [h_σ_none]; exact h_ne
                    cases h_fr : a_next with
                    | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; exact h_changed rfl
                    | some ap =>
                      have h_tk := h_tk_eq ap h_fr
                      rcases h_stw1 ap h_fr _ h_changed (by simp [TAddr.time]; exact h_tk) rfl with
                        ⟨x', hx_eq, hx_mem⟩ | ⟨k, hk_eq, _⟩
                      · cases hx_eq
                        exact Finset.disjoint_left.mp (h_disj_vars y rfl)
                          (Finset.mem_union_right _ hx) hx_mem
                      · cases hk_eq)
                  (fun y e ρ h => by
                    cases h; intro l hl k hk hlk
                    by_contra h_ne; push Not at h_ne
                    have h_σ_none := h_tmk_fresh (.kont k) (by simp [TAddr.time]; rw [hk])
                    have h_changed : tσ₁ (.kont k) ≠ tσ (.kont k) := by rw [h_σ_none]; exact h_ne
                    cases h_fr : a_next with
                    | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; exact h_changed rfl
                    | some ap =>
                      have h_tk := h_tk_eq ap h_fr
                      rcases h_stw1 ap h_fr _ h_changed (by simp [TAddr.time]; rw [hk]; exact h_tk) (by simp [TAddr.time]; rw [hk]) with
                        ⟨_, hx_eq, _⟩ | ⟨k', hk_eq, hk_mem⟩
                      · cases hx_eq
                      · cases hk_eq; rw [hlk] at hk_mem
                        rcases Finset.mem_union.mp hk_mem with h_ap | h_stk
                        · exact Finset.disjoint_right.mp h_disj_ce hl
                            (Finset.mem_singleton.mp h_ap ▸ h_inner_label_in_ce ap h_fr)
                        · exact Finset.disjoint_right.mp h_disj_ce hl (h_stk_sub_ce h_stk))
                  (fun y e ρ h => by -- body_cdf
                    cases h; intro l hl
                    cases h_fr : a_next with
                    | none => rw [h_fr] at h_tn_apply; cases h_tn_apply
                              exact fun a ha => h_tmk_fresh a ha.tmk_suffix
                    | some ap =>
                      obtain ⟨DL, hDL_sub, hDL_pres⟩ := h_dfp1 ap h_fr
                      have h_tk := h_tk_eq ap h_fr
                      have h_not_in_DL : l ∉ DL :=
                        fun h_in => Finset.disjoint_right.mp h_disj_ce hl (h_stk_sub_ce (hDL_sub h_in))
                      have h_eq : t_restored = ⟨ap.frame.time.tk, tmk⟩ := by simp only [t_restored]; congr 1
                      rw [h_eq]; exact hDL_pres l h_not_in_DL (fun a ha => h_tmk_fresh a ha.tmk_suffix))
                  (fun y e ρ h => by -- body_hdf
                    cases h; intro l hl
                    cases h_fr : a_next with
                    | none => rw [h_fr] at h_tn_apply; cases h_tn_apply
                              exact fun a tk' ha => h_tmk_fresh a ((List.suffix_cons _ _).trans ha.tmk_suffix)
                    | some ap =>
                      obtain ⟨DL, hDL_sub, hDL_pres⟩ := h_hdfp1 ap h_fr
                      have h_tk := h_tk_eq ap h_fr
                      have h_not_in_DL : l ∉ DL := fun h_in => by
                        rcases Finset.mem_union.mp (hDL_sub h_in) with h_ap | h_stk
                        · exact Finset.disjoint_right.mp h_disj_ce
                            (Exp.handlerLabels_subset_allLabels _ hl)
                            (Finset.mem_singleton.mp h_ap ▸ h_inner_label_in_ce ap h_fr)
                        · exact Finset.disjoint_right.mp h_disj_ce
                            (Exp.handlerLabels_subset_allLabels _ hl) (h_stk_sub_ce h_stk)
                      have h_eq : t_restored = ⟨ap.frame.time.tk, tmk⟩ := by simp only [t_restored]; congr 1
                      rw [h_eq]; exact hDL_pres l h_not_in_DL (fun a tk' ha => h_tmk_fresh a ((List.suffix_cons _ _).trans ha.tmk_suffix)))
                  (fun c h => by cases h; exact h_lnb)
                  (fun clo h => by
                    cases h; intro op args oa hv used usedVars hpc a' hoa htk
                    obtain ⟨used', _, hpc', hsub_l, _, _, _⟩ := h_cb_n1r op args oa hv
                    have ⟨h_eq, _⟩ := PairwiseChain.used_unique hpc hpc'; subst h_eq
                    exact h_disj_ce.symm.mono_right ((hsub_l a' hoa htk).trans h_stk_sub_ce))
                  (fun clo h => by
                    cases h; intro op args oa hv used usedVars hpc a' hoa htk y hy
                    obtain ⟨_, usedVars', hpc', _, hsub_v, _, _⟩ := h_cb_n1r op args oa hv
                    have ⟨_, h_eq⟩ := PairwiseChain.used_unique hpc hpc'; subst h_eq
                    exact (h_disj_vars y hy).mono_right (hsub_v a' hoa htk))
                  (fun op args oa hv a' hoa => by
                    obtain ⟨_, _, _, _, _, hsuf, _⟩ := h_cb_n1r op args oa hv
                    exact hsuf a' hoa)
                  (fun clo h => by
                    cases h; intro op args oa hv a' hoa hne
                    obtain ⟨_, _, _, _, _, _, hbr⟩ := h_cb_n1r op args oa hv
                    obtain ⟨lb, hlb, hsuf⟩ := hbr a' hoa hne
                    exact ⟨lb, Finset.mem_union_right _ hlb,
                      fun h_in => Finset.disjoint_right.mp h_disj_ce h_in (h_stk_sub_ce hlb), hsuf⟩)
                  (fun clo h => by
                    cases h; intro op args oa hv
                    -- Witness: sameTkLabels (not _ceLabels_stk)
                    have h_lnb_stk : a_κ.frame.label ∉ sameTkLabels :=
                      fun h => h_lnb_ce_stk (h_stk_sub_ce h)
                    refine ⟨sameTkLabels, ?_, h_lnb_stk, ?_, ?_, Finset.subset_union_right⟩
                    · exact h_disj_ce.mono_left h_stk_sub_ce
                    · intro used usedVars hpc a' hoa htk
                      obtain ⟨used', _, hpc', hsub_l, _, _, _⟩ := h_cb_n1r op args oa hv
                      have ⟨h_eq, _⟩ := PairwiseChain.used_unique hpc hpc'; subst h_eq
                      exact hsub_l a' hoa htk
                    · intro a' hoa htk
                      obtain ⟨used', _, hpc', hsub_l', _, _, _⟩ := h_cb_n1r op args oa hv
                      subst hoa
                      exact hsub_l' a' rfl htk hpc'.frame_label_mem)
                  (fun y e ρ h => by cases h; simp)
                  (fun y e ρ h => by cases h; simp; exact Finset.subset_union_left.trans (Finset.subset_insert _ _))
                  (fun c h => by cases h; exact Finset.singleton_subset_iff.mpr (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))))
                  (fun c h => by cases h; exact Finset.subset_union_right.trans Finset.subset_union_left)
                  (fun c h => by cases h; exact Finset.subset_union_left)
                  (fun c h => by
                    cases h; intro op args oa hv used usedVars hpc a' hoa htk
                    obtain ⟨_, usedV₀, hpc₀, _, h_var_sub, _, _⟩ := h_cb_n1r op args oa hv
                    have ⟨_, h_eq⟩ := PairwiseChain.used_unique hpc hpc₀; subst h_eq
                    exact (h_var_sub a' hoa htk).trans Finset.subset_union_right)
              -- Step 3: Compose outputs
              have h_store_mono₁ : ∀ a, σ_c a ≠ none → σ_mid a ≠ none := by
                intro a h_ne h_eq
                cases h_σ : σ_c a with
                | none => exact h_ne h_σ
                | some d =>
                  have := eval_apply_store_mono (apply_kontN_to h_apply) a d h_σ
                  rw [h_eq] at this; exact absurd this (by simp)
              -- Compose output fields
              have h_tmk_suf : ∀ a, tσ₂ a ≠ tσ a → tmk <:+ a.time.tmk := fun a ha => by
                by_cases h_eq : tσ₂ a = tσ₁ a
                · exact h_desc1 a (fun h => ha (h_eq ▸ h))
                · exact (List.suffix_refl tmk).trans (h_wb2.descendant h_eq).tmk_suffix
              have h_cdf_compose : ∀ a_κ₀, some a_κ = some a_κ₀ →
                  ∃ DL ⊆ ({a_κ.frame.label} ∪ clo_t.body.allLabels ∪ sameTkLabels),
                    ∀ l, l ∉ DL → CallDescFresh tσ ⟨a_κ₀.frame.time.tk, tmk⟩ l →
                      CallDescFresh tσ₂ ⟨a_κ₀.frame.time.tk, tmk⟩ l := by
                intro a_κ₀ h_eq; cases h_eq
                -- dls from P_continue: DL ⊆ {a_κ.frame.label} ∪ body ∪ sameTkLabels, l ∉ dls → CDF tσ₁ → CDF tσ₂
                -- Need to also compose with P_apply's CDF preservation
                cases h_fr : a_next with
                | none =>
                  -- apply_continue: tσ₁ = tσ
                  rw [h_fr] at h_tn_apply; cases h_tn_apply
                  exact ⟨dls, hdls_sub, fun l hl h_cdf => h_wb2.callDescFresh hl h_cdf⟩
                | some ap =>
                  obtain ⟨DL₁, hDL₁_sub, hDL₁_pres⟩ := h_dfp1 ap h_fr
                  -- t_restored = ⟨a_κ.frame.time.tk, tmk⟩ = ⟨ap.frame.time.tk, tmk⟩ (by h_tk_eq)
                  -- h_dfp1 gives CDF preservation at ⟨ap.frame.time.tk, tmk⟩
                  -- h_wb2.callDescFresh gives CDF preservation at t_restored
                  -- These match because t_restored.tk = a_κ.frame.time.tk = ap.frame.time.tk
                  refine ⟨DL₁ ∪ dls, Finset.union_subset (hDL₁_sub.trans Finset.subset_union_right) hdls_sub,
                    fun l hl h_cdf => ?_⟩
                  have hl1 : l ∉ DL₁ := fun h => hl (Finset.mem_union_left _ h)
                  have hl2 : l ∉ dls := fun h => hl (Finset.mem_union_right _ h)
                  -- Need: CallDescFresh tσ₂ ⟨a_κ.frame.time.tk, tmk⟩ l
                  -- From: h_cdf : CallDescFresh tσ ⟨a_κ.frame.time.tk, tmk⟩ l
                  -- Step 1: CDF tσ → CDF tσ₁ via h_dfp1 (at ap.frame.time.tk = a_κ.frame.time.tk)
                  have h_tk := h_tk_eq ap h_fr
                  -- h_dfp1 preserves CDF at ⟨ap.tk, tmk⟩, h_wb2 at t_restored = ⟨a_κ.tk, tmk⟩
                  -- Since h_tk : a_κ.tk = ap.tk, these are the same time
                  -- Convert between t_restored and ⟨ap.tk, tmk⟩ explicitly
                  have h_t_eq : t_restored = ⟨ap.frame.time.tk, tmk⟩ :=
                    congr_arg₂ Time.mk h_tk rfl
                  have h_cdf_1r : CallDescFresh tσ₁ t_restored l := by
                    rw [h_t_eq]; exact hDL₁_pres l hl1 (by rw [← h_t_eq]; exact h_cdf)
                  exact h_wb2.callDescFresh hl2 h_cdf_1r
              have h_hdf_compose : ∀ a_κ₀, some a_κ = some a_κ₀ →
                  ∃ DL ⊆ ({a_κ₀.frame.label} ∪ ({a_κ.frame.label} ∪ clo_t.body.allLabels ∪ sameTkLabels)),
                    ∀ l, l ∉ DL → HandlerDescFresh tσ ⟨a_κ₀.frame.time.tk, tmk⟩ l →
                      HandlerDescFresh tσ₂ ⟨a_κ₀.frame.time.tk, tmk⟩ l := by
                intro a_κ₀ h_eq; cases h_eq
                cases h_fr : a_next with
                | none =>
                  rw [h_fr] at h_tn_apply; cases h_tn_apply
                  exact ⟨dls, hdls_sub.trans Finset.subset_union_right,
                    fun l hl h_hdf => h_wb2.handlerDescFresh hl h_hdf⟩
                | some ap =>
                  obtain ⟨DL₁, hDL₁_sub, hDL₁_pres⟩ := h_hdfp1 ap h_fr
                  have h_t_eq : t_restored = ⟨ap.frame.time.tk, tmk⟩ := congr_arg₂ Time.mk (h_tk_eq ap h_fr) rfl
                  have h_ap_in_stk : ap.frame.label ∈ sameTkLabels := by
                    rw [h_fr] at h_inner; exact h_inner.frame_label_mem
                  refine ⟨DL₁ ∪ dls, ?_, fun l hl h_hdf => ?_⟩
                  · -- DL₁ ⊆ {ap.frame.label} ∪ sameTkLabels, ap.frame.label ∈ sameTkLabels
                    -- so DL₁ ⊆ sameTkLabels ⊆ {a_κ₀.frame.label} ∪ chainLabels
                    intro l hl'
                    rcases Finset.mem_union.mp hl' with h_l | h_l
                    · have h_mem := hDL₁_sub h_l
                      rcases Finset.mem_union.mp h_mem with h | h
                      · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_singleton.mp h ▸ h_ap_in_stk))
                      · exact Finset.mem_union_right _ (Finset.mem_union_right _ h)
                    · exact Finset.mem_union_right _ (hdls_sub h_l)
                  · have hl1 : l ∉ DL₁ := fun h => hl (Finset.mem_union_left _ h)
                    have hl2 : l ∉ dls := fun h => hl (Finset.mem_union_right _ h)
                    have h_hdf_1r : HandlerDescFresh tσ₁ t_restored l := by
                      rw [h_t_eq]; exact hDL₁_pres l hl1 (by rw [← h_t_eq]; exact h_hdf)
                    exact h_wb2.handlerDescFresh hl2 h_hdf_1r
              exact ⟨α₂, tv₂, tσ₂,
                .apply_restore h_lookup' h_content' h_tn_apply rfl h_tn_cont,
                .apply_restore h_lookup' h_content' h_ts_apply rfl h_ts_cont,
                hval₂, hstore₂, hrefl₂,
                hext₁.trans hext₂ h_store_mono₁,
                h_wfv2, hinv2,
                h_tmk_suf,
                h_cdf_compose,
                h_hdf_compose,
                (fun a_κ₀ h_eq a ha => by
                  cases h_eq
                  by_cases h1 : tσ₁ a = tσ a
                  · -- Changed in P_continue: Descendant t_restored a.time → Descendant ⟨a_κ.frame.time.tk, tmk⟩ a.time
                    exact h_wb2.descendant (by rw [h1]; exact ha)
                  · -- Changed in P_apply: use h_sd1 from IH
                    cases h_fr : a_next with
                    | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; exact absurd rfl h1
                    | some ap =>
                      have h_tk := h_tk_eq ap h_fr
                      have h_from_apply := h_sd1 ap h_fr a h1
                      -- h_from_apply : Descendant ⟨ap.frame.time.tk, tmk⟩ a.time
                      -- goal : Descendant ⟨a_κ.frame.time.tk, tmk⟩ a.time
                      rwa [show (⟨a_κ.frame.time.tk, tmk⟩ : Time) = ⟨ap.frame.time.tk, tmk⟩ from by congr 1]),
                (fun a_κ₀ h_eq a ha h_atk h_atmk => by
                  cases h_eq
                  by_cases h1 : tσ₁ a = tσ a
                  · -- Write from P_continue
                    have h_ne : tσ₂ a ≠ tσ₁ a := by rw [h1]; exact ha
                    have ⟨h_at, _⟩ := h_wb2 a h_ne
                    by_cases h_eq_t : a.time = t_restored
                    · rcases h_at h_eq_t with ⟨x, hx_eq, hx_mem⟩ | ⟨k, hk_eq, _, hk_mem⟩ | ⟨k, hk_eq, _, hk_mem⟩
                      · left; exact ⟨x, by rw [hx_eq]; simp, hx_mem⟩
                      · right; exact ⟨k, hk_eq, Finset.mem_union_right _ hk_mem⟩
                      · right; exact ⟨k, hk_eq, Finset.mem_union_right _ hk_mem⟩
                    · exfalso; exact h_eq_t (by
                        have : a.time = ⟨a.time.tk, a.time.tmk⟩ := by cases a.time; rfl
                        rw [this, h_atk, h_atmk])
                  · -- Write from P_apply
                    cases h_fr : a_next with
                    | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; exact absurd rfl h1
                    | some ap =>
                      have h_tk := h_tk_eq ap h_fr
                      rcases h_stw1 ap h_fr a h1 (h_tk ▸ h_atk) h_atmk with ⟨x, hx_eq, hx_mem⟩ | ⟨k, hk_eq, hk_mem⟩
                      · left; exact ⟨x, hx_eq, Finset.mem_union_right _ hx_mem⟩
                      · have h_ap_in : ap.frame.label ∈ sameTkLabels := by
                          rw [h_fr] at h_inner; exact h_inner.frame_label_mem
                        right; exact ⟨k, hk_eq, by
                          rcases Finset.mem_union.mp hk_mem with h | h
                          · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_singleton.mp h ▸ h_ap_in))
                          · exact Finset.mem_union_right _ (Finset.mem_union_right _ h)⟩),
                (fun op args oa hv => by
                  obtain ⟨used, usedV, hchain, hbound, hvar_bound, htk_suf, h_bridge⟩ := h_cb2 op args oa hv
                  exact ⟨used, usedV, hchain,
                    fun a' hoa htk => (hbound a' hoa htk).trans Finset.subset_union_right,
                    hvar_bound,
                    htk_suf,
                    fun a' hoa h_ne => by
                      obtain ⟨l_br, h_mem, h_suf⟩ := h_bridge a' hoa h_ne
                      exact ⟨l_br, h_mem, h_suf⟩⟩),
                h_val_scoped₂, h_store_scoped₂⟩
          | diff_tk h_lookup' h_content' h_wfp h_y_notin_body h_lnb l_bridge h_l_bridge_notin h_tk_suf _h_ne h_inner =>
            rw [h_lookup'] at h_kont_lookup; cases h_kont_lookup
            rw [h_content'] at h_kont_frame
            cases h_kont_frame with
            | letFrame h_clo_corr =>
              -- diff_tk apply_restore: inner chain at DIFFERENT tk
              rename_i innerLabels innerVars clo_t
              obtain ⟨_, _, _, _, ih_apply⟩ := ih n1_c (by omega)
              have h_kont_scoped_inner : KontScoped κ_inner σ_c :=
                fun f hf => h_kont_scoped f (.tail _ hf)
              obtain ⟨α₁, tv₁, tσ₁, h_tn_apply, h_ts_apply, hval₁, hstore₁, hrefl₁, hext₁,
                      h_wfv1, hinv1, h_desc1, h_dfp1, h_hdfp1, h_sd1, h_stw1, h_cb1,
                      h_val_scoped₁, h_store_scoped₁⟩ :=
                ih_apply κ_inner d_c σ_c v_mid σ_mid a_next td tmk innerLabels innerVars
                  h_apply α tσ h_kont_rest h_den h_store h_refl h_store_scoped h_den_scoped
                  h_kont_scoped_inner h_wf_d h_d_chain hinv h_tmk_fresh h_inner
              -- Step 2: IH P_continue on letFrame
              obtain ⟨_, _, ih_cont, _, _⟩ := ih n2_c (by omega)
              -- diff_tk: P_apply writes at deeper tmk, so addresses at t_restored are preserved
              let t_restored : Time := ⟨a_κ.frame.time.tk, tmk⟩
              -- P_apply preserves at tmk-level because writes go deeper
              -- In diff_tk: P_apply writes are at a deeper tk (via bridge).
              -- Addresses at t_restored = ⟨a_κ.frame.time.tk, tmk⟩ are preserved.
              have h_pres_restored : ∀ a : TAddr, a.time = t_restored → tσ₁ a = tσ a := by
                intro a ha; by_contra h_ne
                cases h_fr : a_next with
                | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; exact h_ne rfl
                | some ap =>
                  have h_suf_tk := h_tk_suf ap h_fr
                  have h_sd := h_sd1 ap h_fr a h_ne
                  have h_tk_a := h_sd.tk_suffix_of_same_tmk (by rw [ha])
                  -- h_tk_a : ap.frame.time.tk <:+ a.time.tk
                  -- h_suf_tk : (l_bridge :: a_κ.frame.time.tk) <:+ ap.frame.time.tk
                  -- ha : a.time = t_restored, so a.time.tk = a_κ.frame.time.tk
                  have : (l_bridge :: a_κ.frame.time.tk) <:+ a_κ.frame.time.tk :=
                    h_suf_tk.trans h_tk_a |>.trans (by rw [ha])
                  exact absurd this.length_le (by simp)
              -- With h_pres_restored, all freshness at t_restored follows from tσ freshness
              have h_clo_corr₁ : ClosureCorr α₁ clo_c clo_t :=
                h_clo_corr.of_alpha_scoped (hext₁ · ·) (h_kont_scoped _ (.head _))
              obtain ⟨_, _, ih_cont, _, _⟩ := ih n2_c (by omega)
              obtain ⟨α₂, tv₂, tσ₂, h_tn_cont, h_ts_cont, hval₂, hstore₂, hrefl₂, hext₂,
                      h_wfv2, hinv2, ⟨dls, hdls_sub, hdls_excl, h_wb2⟩, h_cb2,
                      h_val_scoped₂, h_store_scoped₂⟩ :=
                ih_cont (Frame.letFrame clo_c) v_mid σ_mid v_c σ_c'
                  a_κ.frame.label (.letFrame clo_t) t_restored
                  (clo_t.params.toFinset ∪ clo_t.body.topAllocVars)
                  ({a_κ.frame.label} ∪ {l_bridge} ∪ clo_t.body.allLabels)
                  h_cont α₁ tv₁ tσ₁
                  (.letFrame h_clo_corr₁) hval₁ hstore₁ hrefl₁
                  (fun clo heq => by cases heq; exact envScoped_mono (h_kont_scoped (.letFrame clo_c) (.head _)) (fun a ha => by
                    intro h_eq; cases h_σ : σ_c a with
                    | none => exact ha h_σ
                    | some d => have := eval_apply_store_mono (apply_kontN_to h_apply) a d h_σ; rw [h_eq] at this; exact absurd this (by simp)))
                  h_store_scoped₁ h_val_scoped₁ h_wfv1 hinv1
                  (fun c h => by cases h; exact h_wfp)
                  (fun y e ρ h => by cases h; rw [h_pres_restored _ rfl]; exact h_tmk_fresh _ (List.suffix_refl _))
                  (fun k hk hlk _ => by rw [h_pres_restored _ (by simp [TAddr.time]; exact hk)]; exact h_tmk_fresh _ (by simp [TAddr.time]; rw [hk]))
                  (fun y e ρ h => by cases h; exact h_y_notin_body y rfl)
                  (fun y e ρ h => by cases h; intro x hx; rw [h_pres_restored _ rfl]; exact h_tmk_fresh _ (List.suffix_refl _))
                  (fun y e ρ h => by cases h; intro l hl k hk hlk; rw [h_pres_restored _ (by simp [TAddr.time]; exact hk)]; exact h_tmk_fresh _ (by simp [TAddr.time]; rw [hk]))
                  (fun y e ρ h => by -- body_cdf
                    cases h; intro l hl a ha
                    by_cases h_eq : tσ₁ a = tσ a
                    · rw [h_eq]; exact h_tmk_fresh a ha.tmk_suffix
                    · exfalso
                      cases h_fr : a_next with
                      | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; exact h_eq rfl
                      | some ap =>
                        have h_sd := h_sd1 ap h_fr a h_eq
                        have h_longer := h_tk_suf ap h_fr
                        by_cases h_same_tmk : a.time.tmk = tmk
                        · -- Same tmk: suffix lengths force l = l_bridge
                          have h_tk1 := ha.tk_suffix_of_same_tmk h_same_tmk.symm
                          have h_tk2 := h_sd.tk_suffix_of_same_tmk h_same_tmk.symm
                          have h_eq_suf := suffix_eq_of_length_eq
                            (l :: a_κ.frame.time.tk) (l_bridge :: a_κ.frame.time.tk)
                            a.time.tk h_tk1 (h_longer.trans h_tk2) (by simp)
                          exact h_l_bridge_notin ((List.cons.inj h_eq_suf).1 ▸ hl)
                        · -- Deeper tmk: call_first_tmk_entry gives same contradiction
                          have h_sd_call : Descendant ⟨l_bridge :: a_κ.frame.time.tk, tmk⟩ a.time :=
                            (Descendant.of_tk_suffix h_longer).trans h_sd
                          have ⟨l_e, tk_e, h_entry⟩ := tmk_strict_suffix_entry
                            (h_desc1 a h_eq) h_same_tmk
                          have h_cdf_tk := ha.call_first_tmk_entry h_entry
                          have h_sd_tk := h_sd_call.call_first_tmk_entry h_entry
                          have h_eq_suf := suffix_eq_of_length_eq
                            (l :: a_κ.frame.time.tk) (l_bridge :: a_κ.frame.time.tk)
                            tk_e h_cdf_tk h_sd_tk (by simp)
                          exact h_l_bridge_notin ((List.cons.inj h_eq_suf).1 ▸ hl))
                  (fun y e ρ h => by -- body_hdf
                    cases h; intro l hl a tk' ha
                    by_cases h_eq : tσ₁ a = tσ a
                    · rw [h_eq]; exact h_tmk_fresh a ((List.suffix_cons _ _).trans ha.tmk_suffix)
                    · exfalso
                      cases h_fr : a_next with
                      | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; exact h_eq rfl
                      | some ap =>
                        have h_sd := h_sd1 ap h_fr a h_eq
                        have h_longer := h_tk_suf ap h_fr
                        have h_sd_call : Descendant ⟨l_bridge :: a_κ.frame.time.tk, tmk⟩ a.time :=
                          (Descendant.of_tk_suffix h_longer).trans h_sd
                        have h_entry := h_sd_call.call_first_tmk_entry ha.tmk_suffix
                        exact absurd h_entry.length_le (by simp [t_restored]))
                  (fun c h => by cases h; exact h_lnb)
                  (fun clo h => by
                    cases h; intro op args oa hv used usedVars hpc a' hoa htk
                    -- Need: Disjoint clo_t.body.allLabels used
                    -- Strategy: show htk leads to contradiction (a'.tk can't equal a_κ.tk)
                    exfalso
                    obtain ⟨_, _, hpc', _, _, hsuf', _⟩ := h_cb1 op args oa hv
                    have ⟨h_eq, _⟩ := PairwiseChain.used_unique hpc hpc'
                    subst h_eq
                    cases h_fr : a_next with
                    | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; cases hv
                    | some ap =>
                      rw [h_fr] at hsuf'
                      simp only at hsuf'
                      have h_longer := (h_tk_suf ap h_fr).trans (hsuf' a' hoa)
                      simp only [t_restored] at htk
                      rw [htk] at h_longer
                      exact absurd h_longer.length_le (by simp))
                  (fun clo h => by
                    cases h; intro op args oa hv used usedVars hpc a' hoa htk y hy
                    exfalso
                    obtain ⟨_, _, hpc', _, _, hsuf', _⟩ := h_cb1 op args oa hv
                    have ⟨_, h_eq⟩ := PairwiseChain.used_unique hpc hpc'; subst h_eq
                    cases h_fr : a_next with
                    | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; cases hv
                    | some ap =>
                      rw [h_fr] at hsuf'; simp only at hsuf'
                      have h_longer := (h_tk_suf ap h_fr).trans (hsuf' a' hoa)
                      simp only [t_restored] at htk
                      rw [htk] at h_longer
                      exact absurd h_longer.length_le (by simp))
                  (fun op args oa hv a' hoa => by
                    obtain ⟨_, _, _, _, _, hsuf, _⟩ := h_cb1 op args oa hv
                    -- hsuf gives suffix at (match a_next with ...).tk level
                    -- Need suffix at t_restored.tk = a_κ.frame.time.tk level
                    cases h_fr : a_next with
                    | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; cases hv
                    | some ap =>
                      rw [h_fr] at hsuf; simp only at hsuf
                      have h_suf_ap := hsuf a' hoa
                      -- h_suf_ap : ap.frame.time.tk <:+ a'.frame.time.tk
                      -- h_tk_suf ap h_fr : (l_bridge :: a_κ.frame.time.tk) <:+ ap.frame.time.tk
                      -- so a_κ.frame.time.tk <:+ ap.frame.time.tk <:+ a'.frame.time.tk
                      exact ((List.suffix_cons l_bridge _).trans (h_tk_suf ap h_fr)).trans h_suf_ap)
                  (fun clo h => by -- chain_bridge
                    cases h; intro op args oa hv a' hoa hne
                    cases h_fr : a_next with
                    | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; cases hv
                    | some ap =>
                      rw [h_fr] at h_cb1
                      obtain ⟨_, _, _, _, _, h_suf, _⟩ := h_cb1 op args oa hv
                      simp only at h_suf
                      exact ⟨l_bridge,
                        Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _)),
                        h_l_bridge_notin,
                        (h_tk_suf ap h_fr).trans (h_suf a' hoa)⟩)
                  (fun clo h => by -- ceLabels_exist
                    cases h; intro op args oa hv
                    exact ⟨∅, Finset.disjoint_empty_left _, (by simp),
                      fun used usedVars hpc a' hoa htk => by
                        cases h_fr : a_next with
                        | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; cases hv
                        | some ap =>
                          rw [h_fr] at h_cb1
                          obtain ⟨_, _, _, _, _, h_suf, _⟩ := h_cb1 op args oa hv
                          simp only at h_suf
                          have h_ap_suf := h_suf a' hoa
                          have h_longer := h_tk_suf ap h_fr
                          simp [t_restored] at htk; rw [htk] at h_ap_suf
                          exact absurd h_ap_suf.length_le (by have := h_longer.length_le; simp at this ⊢; omega),
                      fun a' hoa htk => by
                        cases h_fr : a_next with
                        | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; cases hv
                        | some ap =>
                          rw [h_fr] at h_cb1
                          obtain ⟨_, _, _, _, _, h_suf, _⟩ := h_cb1 op args oa hv
                          simp only at h_suf
                          have h_ap_suf := h_suf a' hoa
                          have h_longer := h_tk_suf ap h_fr
                          simp [t_restored] at htk; rw [htk] at h_ap_suf
                          exact absurd h_ap_suf.length_le (by have := h_longer.length_le; simp at this ⊢; omega),
                      Finset.empty_subset _⟩)
                  (fun y e ρ h => by cases h; simp)
                  (fun y e ρ h => by cases h; exact Finset.subset_union_right)
                  (fun c h => by cases h; exact Finset.singleton_subset_iff.mpr (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))))
                  (fun c h => by cases h; exact Finset.subset_union_right)
                  (fun c h => by cases h; exact Finset.Subset.refl _)
                  (fun clo h op args oa hsusp used usedVars hpc a' hoa htk => by
                    cases h
                    cases h_fr : a_next with
                    | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; cases hsusp
                    | some ap =>
                      rw [h_fr] at h_cb1
                      obtain ⟨_, _, _, _, _, h_suf, _⟩ := h_cb1 op args oa hsusp
                      simp only at h_suf
                      have h_ap_suf := h_suf a' hoa
                      have h_longer := h_tk_suf ap h_fr
                      simp [t_restored] at htk; rw [htk] at h_ap_suf
                      exact absurd h_ap_suf.length_le (by have := h_longer.length_le; simp at this ⊢; omega))
              -- Compose diff_tk outputs (same pattern as same_tk)
              have h_store_mono₁ : ∀ a, σ_c a ≠ none → σ_mid a ≠ none := by
                intro a h_ne h_eq
                cases h_σ : σ_c a with
                | none => exact h_ne h_σ
                | some d =>
                  have := eval_apply_store_mono (apply_kontN_to h_apply) a d h_σ
                  rw [h_eq] at this; exact absurd this (by simp)
              exact ⟨α₂, tv₂, tσ₂,
                .apply_restore h_lookup' h_content' h_tn_apply rfl h_tn_cont,
                .apply_restore h_lookup' h_content' h_ts_apply rfl h_ts_cont,
                hval₂, hstore₂, hrefl₂,
                hext₁.trans hext₂ h_store_mono₁,
                h_wfv2, hinv2,
                -- tmk_suf: same as same_tk
                (fun a ha => by
                  by_cases h_eq : tσ₂ a = tσ₁ a
                  · exact h_desc1 a (fun h => ha (h_eq ▸ h))
                  · exact (List.suffix_refl tmk).trans (h_wb2.descendant h_eq).tmk_suffix),
                -- CDF compose
                (fun a_κ₀ h_eq => by
                  cases h_eq
                  refine ⟨{l_bridge} ∪ dls,
                    Finset.union_subset
                      (Finset.singleton_subset_iff.mpr (Finset.mem_union_left _
                        (Finset.mem_union_right _ (Finset.mem_singleton_self _))))
                      hdls_sub,
                    fun l hl h_cdf => ?_⟩
                  have h_l_ne : l ≠ l_bridge :=
                    fun h => hl (Finset.mem_union_left _ (h ▸ Finset.mem_singleton_self _))
                  have h_l_not_dls : l ∉ dls :=
                    fun h => hl (Finset.mem_union_right _ h)
                  have h_cdf_1r : CallDescFresh tσ₁ t_restored l := by
                    intro a ha
                    by_cases h_eq : tσ₁ a = tσ a
                    · rw [h_eq]; exact h_cdf a ha
                    · exfalso
                      cases h_fr : a_next with
                      | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; exact h_eq rfl
                      | some ap =>
                        have h_sd := h_sd1 ap h_fr a h_eq
                        have h_longer := h_tk_suf ap h_fr
                        by_cases h_same_tmk : a.time.tmk = tmk
                        · have h_tk1 := ha.tk_suffix_of_same_tmk h_same_tmk.symm
                          have h_tk2 := h_sd.tk_suffix_of_same_tmk h_same_tmk.symm
                          exact h_l_ne (List.cons.inj (suffix_eq_of_length_eq
                            (l :: a_κ.frame.time.tk) (l_bridge :: a_κ.frame.time.tk)
                            a.time.tk h_tk1 (h_longer.trans h_tk2) (by simp))).1
                        · have h_sd_call := (Descendant.of_tk_suffix h_longer).trans h_sd
                          have ⟨_, _, h_entry⟩ := tmk_strict_suffix_entry (h_desc1 a h_eq) h_same_tmk
                          exact h_l_ne (List.cons.inj (suffix_eq_of_length_eq
                            (l :: a_κ.frame.time.tk) (l_bridge :: a_κ.frame.time.tk)
                            _ (ha.call_first_tmk_entry h_entry)
                            (h_sd_call.call_first_tmk_entry h_entry) (by simp))).1
                  exact h_wb2.callDescFresh h_l_not_dls h_cdf_1r),
                -- HDF compose
                (fun a_κ₀ h_eq => by
                  cases h_eq
                  exact ⟨dls, hdls_sub.trans Finset.subset_union_right,
                    fun l hl h_hdf => by
                    have h_hdf_1r : HandlerDescFresh tσ₁ t_restored l := by
                      intro a tk' ha
                      by_cases h_eq : tσ₁ a = tσ a
                      · rw [h_eq]; exact h_hdf a tk' ha
                      · exfalso
                        cases h_fr : a_next with
                        | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; exact h_eq rfl
                        | some ap =>
                          have h_sd := h_sd1 ap h_fr a h_eq
                          have h_longer := h_tk_suf ap h_fr
                          have h_sd_call := (Descendant.of_tk_suffix h_longer).trans h_sd
                          exact absurd (h_sd_call.call_first_tmk_entry ha.tmk_suffix).length_le
                            (by simp [t_restored])
                    exact h_wb2.handlerDescFresh hl h_hdf_1r⟩),
                -- Scoped descendant compose
                (fun a_κ₀ h_eq a ha => by
                  cases h_eq
                  by_cases h1 : tσ₁ a = tσ a
                  · exact h_wb2.descendant (by rw [h1]; exact ha)
                  · cases h_fr : a_next with
                    | none => rw [h_fr] at h_tn_apply; cases h_tn_apply; exact absurd rfl h1
                    | some ap =>
                      exact (Descendant.of_tk_suffix
                        ((List.suffix_cons l_bridge _).trans (h_tk_suf ap h_fr))).trans
                        (h_sd1 ap h_fr a h1)),
                -- Same-tk writes compose
                (fun a_κ₀ h_eq a ha h_atk h_atmk => by
                  cases h_eq
                  have h_time_eq : a.time = t_restored := by
                    have : a.time = ⟨a.time.tk, a.time.tmk⟩ := by cases a.time; rfl
                    rw [this, h_atk, h_atmk]
                  have h_ne_1r : tσ₂ a ≠ tσ₁ a := by
                    rw [h_pres_restored a h_time_eq]; exact ha
                  have ⟨h_at, _⟩ := h_wb2 a h_ne_1r
                  by_cases h_eq_t : a.time = t_restored
                  · rcases h_at h_eq_t with ⟨x, hx_eq, hx_mem⟩ | ⟨k, hk_eq, _, hk_mem⟩ | ⟨k, hk_eq, _, hk_mem⟩
                    · left; exact ⟨x, by rw [hx_eq]; simp, hx_mem⟩
                    · right; exact ⟨k, hk_eq, Finset.mem_union_right _ hk_mem⟩
                    · right; exact ⟨k, hk_eq, Finset.mem_union_right _ hk_mem⟩
                  · exfalso; exact h_eq_t (by
                      have : a.time = ⟨a.time.tk, a.time.tmk⟩ := by cases a.time; rfl
                      rw [this, h_atk, h_atmk])),
                -- FCChainBound: from h_cb2 with subset embedding
                (fun op args oa hv => by
                  simp only
                  obtain ⟨used, usedV, hchain, hbound, hvar_bound, htk_suf, h_bridge⟩ := h_cb2 op args oa hv
                  exact ⟨used, usedV, hchain,
                    fun a' hoa htk => (hbound a' hoa htk).trans (by
                      intro l hl; simp at hl ⊢; tauto),
                    hvar_bound, htk_suf,
                    fun a' hoa h_ne => by
                      obtain ⟨lb, hlb, hsuf⟩ := h_bridge a' hoa h_ne
                      refine ⟨lb, ?_, hsuf⟩
                      simp at hlb ⊢; tauto⟩),
                h_val_scoped₂, h_store_scoped₂⟩
          | handler_frame h_lookup' h_content' _ _ _ =>
            rw [h_lookup'] at h_kont_lookup; cases h_kont_lookup
            rw [h_content'] at h_kont_frame; cases h_kont_frame -- letFrame ≠ handlerFrame
      | apply_restore_handle h_apply h_handle =>
        -- Decompose KontCorr: Frame.handlerFrame h ρ :: κ ↔ some a_κ
        cases h_kont with
        | cons h_kont_lookup h_kont_frame h_kont_rest =>
          cases h_chain with
          | handler_frame h_lookup' h_content' h_wf_hdl h_lnb_hdl_hf h_inner =>
            rw [h_lookup'] at h_kont_lookup; cases h_kont_lookup
            rw [h_content'] at h_kont_frame
            cases h_kont_frame with
            | handlerFrame h_env_hdl h_envR_hdl =>
              -- apply_restore_handle: handler frame, apply at deeper tmk', then handle at tmk
              rename_i n1_c κ_inner v_mid σ_mid n2_c hdl_c ρ_h_c a_κ a_next _iL _iV tρ_hdl
              let l_frame := a_κ.frame.label
              let t_frame := a_κ.frame.time
              let tmk' := (l_frame, t_frame.tk) :: tmk
              let t_restored : Time := ⟨t_frame.tk, tmk⟩
              have h_tmk'_fresh : ∀ a, tmk' <:+ a.time.tmk → tσ a = none :=
                fun a h => h_tmk_fresh a ((List.suffix_cons _ _).trans h)
              -- Step 1: IH P_apply at deeper tmk'
              obtain ⟨_, _, _, _, ih_apply⟩ := ih n1_c (by omega)
              obtain ⟨α₁, tv₁, tσ₁, h_tn_apply, h_ts_apply, hval₁, hstore₁, hrefl₁, hext₁,
                      h_wfv1, hinv1, h_desc_apply, h_dfp_apply, _, h_scope_apply, _, _, h_val_scoped_mid, h_store_scoped_apply⟩ :=
                ih_apply _ d_c σ_c _ _ _ _ tmk' _ _
                  h_apply α tσ h_kont_rest h_den h_store h_refl h_store_scoped
                  h_den_scoped (fun f hf => h_kont_scoped f (List.mem_cons_of_mem _ hf))
                  h_wf_d h_d_chain hinv h_tmk'_fresh h_inner
              -- Apply preserves tmk-level addresses
              have h_pres_tmk : ∀ a, a.time.tmk = tmk → tσ₁ a = tσ a := by
                intro a ha; by_contra h_ne
                have := h_desc_apply a h_ne; rw [ha] at this
                exact absurd this.length_le (by simp [tmk'])
              -- Store monotonicity: σ_c → σ_mid (apply preserves existing bindings)
              have h_store_mono_apply : ∀ a, σ_c a ≠ none → σ_mid a ≠ none := by
                intro a h_ne h_eq
                cases h_σ : σ_c a with
                | none => exact h_ne h_σ
                | some d =>
                  have := eval_apply_store_mono (apply_kontN_to h_apply) a d h_σ
                  rw [h_eq] at this; exact absurd this (by simp)
              -- EnvScoped for handler env at σ_c (handler was pushed when env was scoped)
              have h_scope_c : EnvScoped ρ_h_c σ_c :=
                -- handlerFrame is first frame in κ_c, h_kont_scoped gives FrameScoped for all frames
                h_kont_scoped (.handlerFrame hdl_c ρ_h_c) List.mem_cons_self
              -- EnvCorr updated for α₁
              have h_env₁ : EnvCorr α₁ ρ_h_c tρ_hdl :=
                h_env_hdl.of_alpha_extends hext₁ h_scope_c
              -- EnvScoped at intermediate store
              have h_scope_mid : EnvScoped ρ_h_c σ_mid :=
                fun x a hxa => h_store_mono_apply _ (h_scope_c x a hxa)
              -- Freshness preconditions for P_handle
              have h_var_fresh_σ₁ : ∀ x ∈ hdl_c.topAllocVars, tσ₁ (.val ⟨x, t_restored⟩) = none := by
                intro x _; rw [h_pres_tmk _ rfl]; exact h_tmk_fresh _ (List.suffix_refl _)
              have h_kont_fresh_σ₁ : ∀ l ∈ hdl_c.allLabels, ∀ k : TKAddr,
                  k.frame.time = t_restored → k.frame.label = l → tσ₁ (.kont k) = none := by
                intro l _ k hk _
                rw [h_pres_tmk _ (by simp [TAddr.time]; rw [hk])]
                exact h_tmk_fresh _ (by simp [TAddr.time]; rw [hk])
              have h_kont_enc_fresh_σ₁ : ∀ k : TKAddr,
                  k.frame.time = t_restored → k.frame.label = l_frame → tσ₁ (.kont k) = none := by
                intro k hk _
                rw [h_pres_tmk _ (by simp [TAddr.time]; rw [hk])]
                exact h_tmk_fresh _ (by simp [TAddr.time]; rw [hk])
              have h_cdf_σ₁ : ∀ l ∈ hdl_c.allLabels, CallDescFresh tσ₁ t_restored l := by
                intro l _ a ha
                by_cases h_eq : tσ₁ a = tσ a
                · rw [h_eq]; exact h_tmk_fresh a ha.tmk_suffix
                · exact absurd (h_desc_apply a h_eq) (fun h => ha.no_shorter_tmk_entry h)
              have h_hdf_σ₁ : ∀ l ∈ hdl_c.handlerLabels, HandlerDescFresh tσ₁ t_restored l := by
                intro l hl a tk' ha
                have h_l_ne : l ≠ l_frame := fun h_eq => h_lnb_hdl_hf (show l_frame ∈ _ from h_eq ▸ hl)
                by_cases h_eq : tσ₁ a = tσ a
                · rw [h_eq]; exact h_tmk_fresh a ((List.suffix_cons _ _).trans ha.tmk_suffix)
                · have h_tmk'_suf := h_desc_apply a h_eq
                  have h_l_suf := ha.tmk_suffix
                  have h_len : ((l, t_frame.tk) :: tmk).length = tmk'.length := by simp [tmk']
                  have h_eq_entry := suffix_eq_of_length_eq _ _ _ h_l_suf h_tmk'_suf h_len
                  exact absurd (Prod.ext_iff.mp (List.cons.inj h_eq_entry).1).1 h_l_ne
              -- Step 2: IH P_handle
              obtain ⟨_, _, _, ih_handle, _⟩ := ih n2_c (by omega)
              obtain ⟨α₂, tv₂, tσ₂, h_tn_handle, h_ts_handle, hval₂, hstore₂, hrefl₂, hext₂,
                      h_wfv2, hinv2, h_wb_handle, h_cb_handle, h_val_scoped', h_store_scoped'⟩ :=
                ih_handle hdl_c ρ_h_c v_mid σ_mid v_c σ_c' l_frame _ t_restored
                  h_handle h_wf_hdl
                  α₁ tv₁ tσ₁ h_env₁ (h_envR_hdl.of_alpha_extends hext₁ h_scope_c) hval₁ hstore₁ hrefl₁ h_scope_mid h_store_scoped_apply h_val_scoped_mid h_wfv1 hinv1
                  h_var_fresh_σ₁ h_kont_fresh_σ₁ h_kont_enc_fresh_σ₁ h_cdf_σ₁ h_hdf_σ₁ h_lnb_hdl_hf
              -- Compose outputs
              exact ⟨α₂, tv₂, tσ₂,
                     .apply_restore_handle h_lookup' h_content' rfl h_tn_apply rfl h_tn_handle,
                     .apply_restore_handle h_lookup' h_content' rfl h_ts_apply rfl h_ts_handle,
                     hval₂, hstore₂, hrefl₂,
                     hext₁.trans hext₂ h_store_mono_apply,
                     h_wfv2, hinv2,
                     -- Write scope
                     fun a ha => by
                       by_cases h1 : tσ₁ a = tσ a
                       · exact h_wb_handle.descendant (by rw [h1]; exact ha) |>.tmk_suffix
                       · exact (List.suffix_cons _ _).trans (h_desc_apply a h1),
                     -- CDF preservation
                     fun a_κ₀ h_eq => by
                       cases h_eq
                       exact ⟨hdl_c.allLabels, Finset.subset_union_right, fun l hl h_cdf => by
                         have h_cdf_1 : CallDescFresh tσ₁ t_restored l := by
                           intro a ha
                           by_cases h_eq : tσ₁ a = tσ a
                           · rw [h_eq]; exact h_cdf a ha
                           · exact absurd (h_desc_apply a h_eq) (fun h => ha.no_shorter_tmk_entry h)
                         exact h_wb_handle.callDescFresh hl h_cdf_1⟩,
                     -- HDF preservation
                     fun a_κ₀ h_eq => by
                       cases h_eq
                       refine ⟨{l_frame} ∪ hdl_c.allLabels, ?_, fun l hl h_hdf => ?_⟩
                       · intro l hl
                         rcases Finset.mem_union.mp hl with h | h
                         · exact Finset.mem_union_left _ (Finset.mem_singleton.mp h ▸ Finset.mem_singleton_self _)
                         · exact Finset.mem_union_right _ (Finset.mem_union_right _ h)
                       have h_l_ne : l ≠ l_frame := fun h => hl (Finset.mem_union_left _ (h ▸ Finset.mem_singleton_self _))
                       have h_l_not_hdl : l ∉ hdl_c.allLabels := fun h => hl (Finset.mem_union_right _ h)
                       have h_hdf_1 : HandlerDescFresh tσ₁ t_restored l := by
                         intro a tk' ha
                         by_cases h_eq : tσ₁ a = tσ a
                         · rw [h_eq]; exact h_hdf a tk' ha
                         · exfalso
                           have h_tmk'_suf := h_desc_apply a h_eq
                           have h_l_suf := ha.tmk_suffix
                           have h_len : ((l, t_frame.tk) :: tmk).length = tmk'.length := by simp [tmk']
                           have h_eq_entry := suffix_eq_of_length_eq _ _ _ h_l_suf h_tmk'_suf h_len
                           exact h_l_ne (Prod.ext_iff.mp (List.cons.inj h_eq_entry).1).1
                       exact h_wb_handle.handlerDescFresh (fun h => h_l_not_hdl h) h_hdf_1,
                     -- Scoped descendant
                     fun a_κ₀ h_eq a ha => by
                       cases h_eq
                       by_cases h1 : tσ₁ a = tσ a
                       · exact h_wb_handle.descendant (by rw [h1]; exact ha)
                       · have h_tmk'_suf := h_desc_apply a h1
                         obtain ⟨tk₀, hd⟩ := Descendant.of_tmk_suffix h_tmk'_suf a.time.tk
                         exact (Descendant.appKont l_frame tk₀ Descendant.refl).trans hd,
                     -- Same-tk writes bounded
                     fun a_κ₀ h_eq a ha h_atk h_atmk => by
                       cases h_eq
                       by_cases h1 : tσ₁ a = tσ a
                       · have h_ne_1 : tσ₂ a ≠ tσ₁ a := by rw [h1]; exact ha
                         have ⟨h_at, _⟩ := h_wb_handle a h_ne_1
                         have h_eq_t : a.time = t_restored := by
                           have h_eta : a.time = ⟨a.time.tk, a.time.tmk⟩ := by cases a.time; rfl
                           rw [h_eta, h_atk, h_atmk]
                         rcases h_at h_eq_t with ⟨x, hx_eq, hx_mem⟩ | ⟨k, hk_eq, _, hk_mem⟩ | ⟨k, hk_eq, _, hk_mem⟩
                         · left; exact ⟨x, by rw [hx_eq]; simp, hx_mem⟩
                         · right; exact ⟨k, hk_eq, by simp; right; exact hk_mem⟩
                         · right; exact ⟨k, hk_eq, by simp at hk_mem ⊢; exact hk_mem⟩
                       · exfalso
                         have := h_desc_apply a h1; rw [h_atmk] at this
                         exact absurd this.length_le (by simp [tmk']),
                     -- ChainBound for result
                     (by
                       intro op args oa h_susp
                       obtain ⟨used, usedVars, h_pc, h_sub_l, h_sub_v, h_suf, h_br⟩ := h_cb_handle op args oa h_susp
                       refine ⟨used, usedVars, h_pc, ?_, h_sub_v, h_suf, ?_⟩
                       · intro a' hoa htk
                         have := h_sub_l a' hoa htk
                         show used ⊆ (match some a_κ with | some a => {a.frame.label} | none => ∅) ∪ ({a_κ.frame.label} ∪ hdl_c.allLabels)
                         simp only [Finset.union_left_idem]
                         exact this
                       · intro a' hoa hne
                         obtain ⟨lb, hlb, hsuf⟩ := h_br a' hoa hne
                         refine ⟨lb, ?_, hsuf⟩
                         rcases Finset.mem_union.mp hlb with h | h
                         · exact Finset.mem_union_left _ h
                         · exact Finset.mem_union_right _ (Finset.mem_union_right _ h)),
                     h_val_scoped',
                     h_store_scoped'⟩
          | same_tk h_lookup' h_content' _ _ _ _ _ _ _ _ _ _ _ =>
            rw [h_lookup'] at h_kont_lookup; cases h_kont_lookup
            rw [h_content'] at h_kont_frame; cases h_kont_frame -- handlerFrame ≠ letFrame
          | diff_tk h_lookup' h_content' _ _ _ _ _ _ _ _ =>
            rw [h_lookup'] at h_kont_lookup; cases h_kont_lookup
            rw [h_content'] at h_kont_frame; cases h_kont_frame -- handlerFrame ≠ letFrame

/-! ## Top-level corollary: Timestamp Completeness (Theorem 2)

  (e, [], []) ⇓e (v, σ)  ⟹  (e, [], [], t₀) ⇓et_f (v_t, σ_t)

  If a well-formed expression evaluates under the concrete semantics
  from empty initial state, it also evaluates under the fresh-guarded
  timestamped semantics at any initial timestamp. -/

theorem concrete_to_fresh_from_empty
    (isHandlerLabel : Label → Prop)
    (h_hl_consistent : ∀ (h : Handler), ∀ l ∈ h.handlerLabels, isHandlerLabel l)
    (h_hl_sound : ∀ l, isHandlerLabel l →
      ∀ (e : Exp), WellLabeledProgram e → l ∈ e.allLabels → l ∈ e.handlerLabels)
    {e : Exp} {v : Value} {σ' : Store}
    (h_eval : EvalExp e Env.empty Store.empty v σ')
    (h_wf : WellFormedProgram e) :
    ∀ (t : Time),
    ∃ tv tσ', TFreshEvalExp e TEnv.empty TStore.empty t tv tσ' := by
  intro t
  obtain ⟨n, hn⟩ := eval_exp_to_N h_eval
  obtain ⟨_, tv, tσ', _, h_ts, _, _, _, _, _, _, _, _, _, _⟩ :=
    (fresh_concrete isHandlerLabel h_hl_consistent h_hl_sound n).1
      e Env.empty Store.empty v σ' hn h_wf
      (fun _ => default) TEnv.empty TStore.empty t
      EnvCorr.empty EnvReflects.empty StoreCorr.empty StoreReflects.empty
      EnvScoped.empty StoreScoped.empty
      FreshInvariant.empty
      (fun _ _ => rfl)
      (fun _ _ _ _ _ => rfl)
      (fun l _ => empty_callDescFresh t l)
      (fun l _ => empty_handlerDescFresh t l)
  exact ⟨tv, tσ', teval_expN_to h_ts⟩

end DMCFA
