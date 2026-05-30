/-
  Freshness: Structural Timestamp Disjointness Simulation Proof

  Shows naive timestamped evaluation implies strict evaluation (with freshness checks).
  Mutual induction on 5 predicates: P_exp, P_cexp, P_continue, P_handle, P_apply.

  Key structural insights:
  - PairwiseChain includes frame labels → DL ⊆ chainLabels ∪ {frame.label} works for all cases
  - diff_tk carries explicit bridge label (may differ from frame.label)
  - tk_suffix_comparable unifies same/diff tmk suffix arguments
  - P_handle has dual context (Case A: per-label DescFresh, Case B: full timestamp fresh)
  - All predicates output chain bounds (labels, vars, tk suffix, bridge)
-/

import DMCFA.FreshnessLemmas

set_option maxHeartbeats 800000

namespace DMCFA

/-! ## WellNamed/WellLabeled Decomposition Helpers -/

theorem ne_of_mem_of_not_mem {α : Type*} [DecidableEq α] {x y : α} {S : Finset α}
    (hx : x ∈ S) (hy : y ∉ S) : x ≠ y :=
  fun h => hy (h ▸ hx)

theorem wellNamedProgram_letE_y_notin_body {y : Var} {ce : CExp} {e : Exp} {l : Label}
    (h : WellNamedProgram (.letE y ce e l)) : y ∉ e.topAllocVars := by
  cases h; assumption

/-! ## findOp/findBranch membership helpers -/

private lemma findSome_mem {l : List (OpName × Var × Exp)} {op : OpName} {x : Var} {e : Exp}
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

lemma findOp_mem {hdl : Handler} {op : OpName} {x : Var} {e : Exp}
    (hfind : Handler.findOp hdl op = some (x, e)) :
    (op, x, e) ∈ hdl.opClauses := by
  simp only [Handler.findOp] at hfind
  exact findSome_mem hfind

private lemma findBranch_mem {bs : List Branch} {c : ConLabel} {xs : List Var} {e : Exp}
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
private lemma branch_handlerLabels_subset_branchListHandlerLabels {b : Branch} {bs : List Branch}
    (h_mem : b ∈ bs) : b.handlerLabels ⊆ branchListHandlerLabels bs := by
  induction bs with
  | nil => simp at h_mem
  | cons hd tl ih =>
    simp only [branchListHandlerLabels]
    cases List.mem_cons.mp h_mem with
    | inl h => subst h; exact Finset.subset_union_left
    | inr h => exact Finset.Subset.trans (ih h) Finset.subset_union_right

lemma match_body_handlerLabels_subset {bs : List Branch} {c : ConLabel} {xs : List Var} {e : Exp}
    (h : findBranch bs c = some (xs, e)) : e.handlerLabels ⊆ (CExp.matchE ae bs).handlerLabels := by
  obtain ⟨b, hb_mem, hb_eq⟩ := findBranch_mem h; subst hb_eq
  simp only [CExp.handlerLabels]
  exact Finset.Subset.trans (by simp [Branch.handlerLabels])
    (branch_handlerLabels_subset_branchListHandlerLabels hb_mem)

lemma match_body_allLabels_subset {bs : List Branch} {c : ConLabel} {xs : List Var} {e : Exp}
    (h : findBranch bs c = some (xs, e)) : e.allLabels ⊆ (CExp.matchE ae bs).allLabels := by
  obtain ⟨b, hb_mem, hb_eq⟩ := findBranch_mem h; subst hb_eq
  simp [CExp.allLabels]
  exact Finset.Subset.trans (by simp [Branch.allLabels])
    (branch_allLabels_subset_branchListLabels hb_mem)

private lemma branch_topAllocVars_subset_list {b : Branch} {bs : List Branch}
    (h_mem : b ∈ bs) : b.topAllocVars ⊆ branchListAllocVars bs := by
  induction bs with
  | nil => simp at h_mem
  | cons hd tl ih =>
    simp only [branchListAllocVars]
    cases List.mem_cons.mp h_mem with
    | inl h => subst h; exact Finset.subset_union_left
    | inr h => exact Finset.Subset.trans (ih h) Finset.subset_union_right

lemma match_body_topAllocVars_subset {bs : List Branch} {c : ConLabel} {xs : List Var} {e : Exp}
    (h : findBranch bs c = some (xs, e)) : e.topAllocVars ⊆ (CExp.matchE ae bs).topAllocVars := by
  obtain ⟨b, hb_mem, hb_eq⟩ := findBranch_mem h; subst hb_eq
  simp only [CExp.topAllocVars]
  exact Finset.Subset.trans (branch_body_topAllocVars_subset c xs e)
    (branch_topAllocVars_subset_list hb_mem)

lemma match_xbind_mem_topAllocVars {bs : List Branch} {c : ConLabel} {x : Var} {e : Exp}
    (h : findBranch bs c = some ([x], e)) : x ∈ (CExp.matchE ae bs).topAllocVars := by
  obtain ⟨b, hb_mem, hb_eq⟩ := findBranch_mem h; subst hb_eq
  simp only [CExp.topAllocVars]
  exact branch_topAllocVars_subset_list hb_mem
    (show x ∈ (Branch.branch c [x] e).topAllocVars by simp [Branch.topAllocVars])

lemma handler_xret_mem_topAllocVars (hdl : Handler) :
    hdl.returnClause.1 ∈ hdl.topAllocVars := by
  cases hdl with | mk ret ops =>
    obtain ⟨x, e⟩ := ret; simp [Handler.topAllocVars]

lemma handler_resume_mem_topAllocVars (hdl : Handler) :
    "resume" ∈ hdl.topAllocVars := by
  cases hdl with | mk ret ops =>
    obtain ⟨x, e⟩ := ret; simp [Handler.topAllocVars]

private lemma x_mem_opClauseListAllocVars {ops : List (OpName × Var × Exp)}
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

lemma handler_op_x_mem_topAllocVars {hdl : Handler} {op : OpName} {x : Var} {e : Exp}
    (h_mem : (op, x, e) ∈ hdl.opClauses) : x ∈ hdl.topAllocVars := by
  cases hdl with | mk ret ops =>
    obtain ⟨x_ret, e_ret⟩ := ret; simp only [Handler.topAllocVars]
    exact Finset.mem_union_right _ (x_mem_opClauseListAllocVars h_mem)

lemma handler_op_allLabels_sub {hdl : Handler} {op : OpName} {x : Var} {e : Exp}
    (h_mem : (op, x, e) ∈ hdl.opClauses) : e.allLabels ⊆ hdl.allLabels :=
  handler_op_allLabels_subset h_mem

private lemma e_handlerLabels_subset_opClauseListHandlerLabels
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

lemma handler_op_handlerLabels_sub {hdl : Handler} {op : OpName} {x : Var} {e : Exp}
    (h_mem : (op, x, e) ∈ hdl.opClauses) : e.handlerLabels ⊆ hdl.handlerLabels := by
  cases hdl with | mk ret ops =>
    obtain ⟨x_ret, e_ret⟩ := ret
    simp only [Handler.handlerLabels]
    exact Finset.Subset.trans (e_handlerLabels_subset_opClauseListHandlerLabels h_mem)
      Finset.subset_union_right

private theorem foldl_val_preserves_fi {σ : TStore} {t_w : Time}
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

/-! ## Helper lemmas -/

private theorem mem_snd_of_mem_zip {α β : Type*} {a : α} {b : β}
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
def ChainBound (σ : TStore) (v : TValue) (t : Time)
    (boundLabels bridgeLabels : Finset Label) (boundVars : Finset Var := ∅) : Prop :=
  ∀ op args oa, v = .suspended op args oa →
    ∃ used usedVars, PairwiseChain σ oa used usedVars ∧
      (∀ a', oa = some a' → a'.frame.time.tk = t.tk → used ⊆ boundLabels) ∧
      (∀ a', oa = some a' → a'.frame.time.tk = t.tk → usedVars ⊆ boundVars) ∧
      (∀ a', oa = some a' → t.tk <:+ a'.frame.time.tk) ∧
      (∀ a', oa = some a' → a'.frame.time.tk ≠ t.tk →
        ∃ l_bridge ∈ bridgeLabels, (l_bridge :: t.tk) <:+ a'.frame.time.tk)

/-! ## Address Freshness (Theorem 3)

  (e, ρ, σ, t) ⇓et (v, σ')  ⟹  (e, ρ, σ, t) ⇓et_f (v, σ')

  Every timestamped derivation satisfies the freshness guards:
  distinct allocations receive distinct addresses. Proved by mutual
  induction on derivation height, threading wf_kont and write bounds. -/

theorem simulation (isHandlerLabel : Label → Prop)
    (h_handlerLabels_consistent : ∀ (h : Handler), ∀ l ∈ h.handlerLabels, isHandlerLabel l)
    (h_label_kind_sound : ∀ l, isHandlerLabel l →
      ∀ (e : Exp), WellLabeledProgram e → l ∈ e.allLabels → l ∈ e.handlerLabels)
    (n : Nat) :
    -- P_exp
    (∀ (e : Exp) (ρ : TEnv) (σ : TStore) (t : Time) (v : TValue) (σ' : TStore),
       TEvalExpN n e ρ σ t v σ' →
       WellFormedProgram e →
       FreshInvariant σ →
       (∀ x ∈ e.topAllocVars, σ (.val ⟨x, t⟩) = none) →
       (∀ l ∈ e.allLabels, ∀ k : TKAddr, k.frame.time = t → k.frame.label = l → σ (.kont k) = none) →
       -- CallDescFresh at all labels (call direction freshness)
       (∀ l ∈ e.allLabels, CallDescFresh σ t l) →
       -- HandlerDescFresh only at handler-CExp labels (handler direction freshness)
       (∀ l ∈ e.handlerLabels, HandlerDescFresh σ t l) →
       TFreshEvalExpN n e ρ σ t v σ' ∧
       WellFormedValue6 σ' v ∧
       FreshInvariant σ' ∧
       WriteBound σ σ' t e.topAllocVars e.allLabels e.allLabels e.allLabels ∧
       ChainBound σ' v t e.allLabels e.allLabels e.topAllocVars) ∧
    -- P_cexp
    (∀ (ce : CExp) (ρ : TEnv) (σ : TStore) (t : Time) (l_enc : Label)
       (v : TValue) (σ' : TStore),
       TEvalCExpN n ce ρ σ t l_enc v σ' →
       WellLabeledSubCExp ce →
       WellNamedSubCExp ce →
       FreshInvariant σ →
       (∀ x ∈ ce.topAllocVars, σ (.val ⟨x, t⟩) = none) →
       (∀ k : TKAddr, k.frame.time = t → k.frame.label = l_enc → σ (.kont k) = none) →
       (∀ l ∈ ce.allLabels, ∀ k : TKAddr, k.frame.time = t → k.frame.label = l → σ (.kont k) = none) →
       l_enc ∉ ce.allLabels →
       -- CallDescFresh at CExp labels + enclosing label
       (∀ l ∈ ce.allLabels, CallDescFresh σ t l) →
       CallDescFresh σ t l_enc →
       -- HandlerDescFresh at enclosing label ONLY if CExp is handler
       (ce.isHandlerCExp → HandlerDescFresh σ t l_enc) →
       -- HandlerDescFresh at handler sub-labels within CExp (match branch handlers, etc.)
       (∀ l ∈ ce.handlerLabels, HandlerDescFresh σ t l) →
       -- Label kind: if l_enc is a handler label, then the CExp must be a handler
       (isHandlerLabel l_enc → ce.isHandlerCExp = true) →
       TFreshEvalCExpN n ce ρ σ t l_enc v σ' ∧
       WellFormedValue6 σ' v ∧
       FreshInvariant σ' ∧
       WriteBound σ σ' t ce.topAllocVars ce.allLabels ({l_enc} ∪ ce.allLabels) ({l_enc} ∪ ce.allLabels) ∧
       ChainBound σ' v t ce.allLabels (({l_enc} : Finset Label) ∪ ce.allLabels) ce.topAllocVars) ∧
    -- P_continue
    (∀ (l_enc : Label) (fc : TFrameContent) (t_f : Time) (v : TValue)
       (σ : TStore) (v' : TValue) (σ' : TStore)
       (frameVars : Finset Var) (frameLabels : Finset Label),
       TContinueFrameN n l_enc fc t_f v σ v' σ' →
       WellFormedValue6 σ v →
       FreshInvariant σ →
       (∀ (clo : TClosure), fc = .letFrame clo → WellFormedProgram clo.body) →
       (∀ y (e : Exp) ρ, fc = .letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩ → σ (.val ⟨y, t_f⟩) = none) →
       (∀ k : TKAddr, k.frame.time = t_f → k.frame.label = l_enc →
         k.frame.content.isLetFrame = true → σ (.kont k) = none) →
       (∀ y (e : Exp) ρ, fc = .letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩ → y ∉ e.topAllocVars) →
       (∀ y (e : Exp) ρ, fc = .letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩ →
         ∀ x ∈ e.topAllocVars, σ (.val ⟨x, t_f⟩) = none) →
       (∀ y (e : Exp) ρ, fc = .letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩ →
         ∀ l ∈ e.allLabels, ∀ k : TKAddr, k.frame.time = t_f → k.frame.label = l → σ (.kont k) = none) →
       (∀ y (e : Exp) ρ, fc = .letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩ →
         ∀ l ∈ e.allLabels, CallDescFresh σ t_f l) →
       (∀ y (e : Exp) ρ, fc = .letFrame ⟨[y], e, ρ, List.nodup_singleton _⟩ →
         ∀ l ∈ e.handlerLabels, HandlerDescFresh σ t_f l) →
       (∀ clo, fc = .letFrame clo → l_enc ∉ clo.body.allLabels) →
       -- Chain label disjoint (at same tk)
       (∀ clo, fc = .letFrame clo →
         ∀ op args oa, v = .suspended op args oa →
           ∀ used usedVars, PairwiseChain σ oa used usedVars →
             ∀ a', oa = some a' → a'.frame.time.tk = t_f.tk →
               Disjoint clo.body.allLabels used) →
       -- Chain var disjoint (at same tk)
       (∀ clo, fc = .letFrame clo →
         ∀ op args oa, v = .suspended op args oa →
           ∀ used usedVars, PairwiseChain σ oa used usedVars →
             ∀ a', oa = some a' → a'.frame.time.tk = t_f.tk →
               ∀ y, clo.params = [y] →
                 Disjoint ({y} ∪ clo.body.topAllocVars) usedVars) →
       -- Chain tk suffix
       (∀ op args oa, v = .suspended op args oa →
         ∀ a', oa = some a' → t_f.tk <:+ a'.frame.time.tk) →
       -- Bridge label (at different tk)
       (∀ (clo : TClosure), fc = .letFrame clo →
         ∀ op args oa, v = .suspended op args oa →
           ∀ a', oa = some a' → a'.frame.time.tk ≠ t_f.tk →
             ∃ l_bridge ∈ frameLabels, l_bridge ∉ clo.body.allLabels ∧
               (l_bridge :: t_f.tk) <:+ a'.frame.time.tk) →
       -- CExp-side labels for PairwiseChain construction at continue_op
       (∀ clo, fc = .letFrame clo →
         ∀ op args oa, v = .suspended op args oa →
           ∃ ceLabels : Finset Label,
             Disjoint ceLabels clo.body.allLabels ∧
             l_enc ∉ ceLabels ∧
             (∀ used usedVars, PairwiseChain σ oa used usedVars →
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
         ∀ op args oa, v = .suspended op args oa →
           ∀ used usedVars, PairwiseChain σ oa used usedVars →
             ∀ a', oa = some a' → a'.frame.time.tk = t_f.tk →
               usedVars ⊆ frameVars) →
       TFreshContinueFrameN n l_enc fc t_f v σ v' σ' ∧
       WellFormedValue6 σ' v' ∧
       FreshInvariant σ' ∧
       (∃ frameDescLabels, frameDescLabels ⊆ frameLabels ∧ l_enc ∉ frameDescLabels ∧
         WriteBound σ σ' t_f frameVars frameLabels frameLabels frameDescLabels) ∧
       -- P_continue NOW outputs chain bound
       ChainBound σ' v' t_f frameLabels ({l_enc} ∪ frameLabels) frameVars) ∧
    -- P_handle (with dual context precondition)
    (∀ (l_enc : Label) (hdl : Handler) (ρ_handler : TEnv) (v : TValue)
       (σ : TStore) (t : Time) (v' : TValue) (σ' : TStore),
       THandleValueN n l_enc hdl ρ_handler v σ t v' σ' →
       WellFormedSubHandler hdl →
       WellFormedValue6 σ v →
       FreshInvariant σ →
       (∀ x ∈ hdl.topAllocVars, σ (.val ⟨x, t⟩) = none) →
       (∀ l ∈ hdl.allLabels, ∀ k : TKAddr, k.frame.time = t → k.frame.label = l → σ (.kont k) = none) →
       (∀ k : TKAddr, k.frame.time = t → k.frame.label = l_enc → σ (.kont k) = none) →
       -- CallDescFresh at handler labels + HandlerDescFresh at handler's handler labels
       (∀ l ∈ hdl.allLabels, CallDescFresh σ t l) →
       (∀ l ∈ hdl.handlerLabels, HandlerDescFresh σ t l) →
       l_enc ∉ hdl.handlerLabels →
       TFreshHandleValueN n l_enc hdl ρ_handler v σ t v' σ' ∧
       WellFormedValue6 σ' v' ∧
       FreshInvariant σ' ∧
       WriteBound σ σ' t hdl.topAllocVars hdl.allLabels ({l_enc} ∪ hdl.allLabels) hdl.allLabels ∧
       ChainBound σ' v' t ({l_enc} ∪ hdl.allLabels) ({l_enc} ∪ hdl.allLabels) hdl.topAllocVars) ∧
    -- P_apply
    (∀ (oa_κ : Option TKAddr) (d : TDenotable) (σ : TStore) (tmk : MKTime)
       (v : TValue) (σ' : TStore) (chainLabels : Finset Label) (chainVars : Finset Var),
       TApplyKontN n oa_κ d σ tmk v σ' →
       WellFormedStorable (.denotable d) →
       (∀ hdl ρ oa, d = .kontClosure hdl ρ oa → ∃ used usedVars, PairwiseChain σ oa used usedVars) →
       FreshInvariant σ →
       (∀ a, tmk <:+ a.time.tmk → σ a = none) →
       PairwiseChain σ oa_κ chainLabels chainVars →
       TFreshApplyKontN n oa_κ d σ tmk v σ' ∧
       WellFormedValue6 σ' v ∧
       FreshInvariant σ' ∧
       (∀ a, σ' a ≠ σ a → tmk <:+ a.time.tmk) ∧
       -- CallDescFresh preservation
       (∀ a_κ₀, oa_κ = some a_κ₀ →
         ∃ DL : Finset Label, DL ⊆ chainLabels ∧
           ∀ l, l ∉ DL →
             CallDescFresh σ ⟨a_κ₀.frame.time.tk, tmk⟩ l →
             CallDescFresh σ' ⟨a_κ₀.frame.time.tk, tmk⟩ l) ∧
       -- HandlerDescFresh preservation (DL may include frame label for handler_frame tmk' case)
       (∀ a_κ₀, oa_κ = some a_κ₀ →
         ∃ DL : Finset Label, DL ⊆ ({a_κ₀.frame.label} ∪ chainLabels) ∧
           ∀ l, l ∉ DL →
             HandlerDescFresh σ ⟨a_κ₀.frame.time.tk, tmk⟩ l →
             HandlerDescFresh σ' ⟨a_κ₀.frame.time.tk, tmk⟩ l) ∧
       -- Scoped Descendant
       (∀ a_κ₀, oa_κ = some a_κ₀ →
         ∀ a, σ' a ≠ σ a →
           Descendant ⟨a_κ₀.frame.time.tk, tmk⟩ a.time) ∧
       -- Same-tk writes bounded by chain vars/labels + frame label
       (∀ a_κ₀, oa_κ = some a_κ₀ →
         ∀ a, σ' a ≠ σ a → a.time.tk = a_κ₀.frame.time.tk → a.time.tmk = tmk →
           (∃ x, a = .val ⟨x, a.time⟩ ∧ x ∈ chainVars) ∨
           (∃ k, a = .kont k ∧ k.frame.label ∈ ({a_κ₀.frame.label} ∪ chainLabels))) ∧
       -- ChainBound for result value
       ChainBound σ' v ⟨(match oa_κ with | some a => a.frame.time.tk | none => []), tmk⟩
         ((match oa_κ with | some a => {a.frame.label} | none => {}) ∪ chainLabels)
         ((match oa_κ with | some a => {a.frame.label} | none => {}) ∪ chainLabels) chainVars) := by
  constructor
  -- P_exp
  · intro e ρ σ t v σ' h_naive h_wf hinv h_var_fresh h_kont_fresh h_cdf h_hdf
    cases h_naive with
    | eval_let h_ce h_cont =>
      rename_i n1 ce l_let vce σ₁ n2 y e_body
      have h_wf_body := wellFormedProgram_letE_body h_wf
      have h_wf_ce := wellFormedProgram_letE_ce h_wf
      have h_l_in := letE_label_mem_allLabels y ce e_body l_let
      have h_l_notin_ce := wellLabeled_label_notin_ce (wellLabeledProgram_letE_wl h_wf.wl)
      have ⟨h_strict_ce, h_wf_vce, hinv₁, h_wb_ce, _h_cb_ce⟩ :=
        (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).2.1 ce ρ σ t l_let vce σ₁
          h_ce h_wf_ce.wl h_wf_ce.wn hinv
          (fun x hx => h_var_fresh x (by simp; exact Or.inr (Or.inl hx)))
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
            -- h_in_hls : l_let ∈ (if ce.isHandlerCExp = true then {l_let} else ∅) ∪ ce.handlerLabels ∨ ...
            -- ce.isHandlerCExp ≠ true from h_neg
            have h_not_true : ¬ (ce.isHandlerCExp = true) := h_neg
            rcases h_in_hls with h1 | h2
            · simp [h_not_true] at h1
              exact h_l_notin_ce (CExp.handlerLabels_subset_allLabels ce h1)
            · exact (wellLabeled_label_notin_body (wellLabeledProgram_letE_wl h_wf.wl))
                (Exp.handlerLabels_subset_allLabels e_body h2))
      have h_wl := wellLabeledProgram_letE_wl h_wf.wl
      have h_ce_body_disj := wellLabeled_letE_disjoint h_wl
      have h_l_notin_body := wellLabeled_label_notin_body h_wl
      have h_y_fresh_σ₁ : σ₁ (.val ⟨y, t⟩) = none :=
        h_wb_ce.val_fresh (wellNamedProgram_letE_y_notin_ce h_wf.wn)
          (h_var_fresh y (by simp))
      have h_lkont_fresh_σ₁ : ∀ op, σ₁ (.kont ⟨⟨.letFrame ⟨[y], e_body, ρ, List.nodup_singleton _⟩, t, l_let⟩, op⟩) = none :=
        fun op => h_wb_ce.let_kont_fresh rfl rfl h_l_notin_ce
          (h_kont_fresh l_let h_l_in ⟨⟨.letFrame ⟨[y], e_body, ρ, List.nodup_singleton _⟩, t, l_let⟩, op⟩ rfl rfl)
      have h_body_vf_σ₁ : ∀ x ∈ e_body.topAllocVars, σ₁ (.val ⟨x, t⟩) = none :=
        fun x hx => h_wb_ce.val_fresh
          (Finset.disjoint_right.mp (wellNamedProgram_letE_disjoint h_wf.wn) hx)
          (h_var_fresh x (by simp; exact Or.inr (Or.inr hx)))
      have h_body_kf_σ₁ : ∀ l ∈ e_body.allLabels, ∀ k : TKAddr,
          k.frame.time = t → k.frame.label = l → σ₁ (.kont k) = none :=
        fun l hl k hk hlk => h_wb_ce.kont_fresh hk
          (by rw [hlk]; exact Finset.disjoint_right.mp h_ce_body_disj hl)
          (by rw [hlk]; simp only [Finset.mem_union, Finset.mem_singleton, not_or]
              exact ⟨fun h => h_l_notin_body (h ▸ hl), Finset.disjoint_right.mp h_ce_body_disj hl⟩)
          (h_kont_fresh l (letE_body_allLabels_subset y ce e_body l_let hl) k hk hlk)
      have h_body_cdf_σ₁ : ∀ l ∈ e_body.allLabels, CallDescFresh σ₁ t l :=
        fun l hl => h_wb_ce.callDescFresh
          (by simp only [Finset.mem_union, Finset.mem_singleton, not_or]
              exact ⟨fun h => h_l_notin_body (h ▸ hl), Finset.disjoint_right.mp h_ce_body_disj hl⟩)
          (h_cdf l (letE_body_allLabels_subset y ce e_body l_let hl))
      have h_body_hdf_σ₁ : ∀ l ∈ e_body.handlerLabels, HandlerDescFresh σ₁ t l :=
        fun l hl => h_wb_ce.handlerDescFresh
          (by have h_in_body := Exp.handlerLabels_subset_allLabels e_body hl
              simp only [Finset.mem_union, Finset.mem_singleton, not_or]
              exact ⟨fun h => h_l_notin_body (h ▸ h_in_body),
                     Finset.disjoint_right.mp h_ce_body_disj h_in_body⟩)
          (h_hdf l (by simp only [Exp.handlerLabels, Finset.mem_union]; exact Or.inr hl))
      -- P_continue — NOW outputs ChainBound
      have ⟨h_strict_cont, h_wf_v, hinv', ⟨_contDL, _contDL_sub, _contDL_excl, h_wb_cont⟩, h_cb_cont⟩ :=
        (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).2.2.1 l_let (.letFrame ⟨[y], e_body, ρ, List.nodup_singleton _⟩) t vce σ₁ v σ'
          ({y} ∪ ce.topAllocVars ∪ e_body.topAllocVars) ({l_let} ∪ ce.allLabels ∪ e_body.allLabels)
          h_cont h_wf_vce hinv₁
          (fun clo heq => by cases heq; exact h_wf_body)
          (fun _ _ _ heq => by cases heq; exact h_y_fresh_σ₁)
          (fun k hk hl hlet => h_wb_ce.let_kont_fresh hk hlet
            (by rw [hl]; exact h_l_notin_ce)
            (h_kont_fresh l_let h_l_in k hk hl))
          (fun _ _ _ heq => by cases heq; exact wellNamedProgram_letE_y_notin_body h_wf.wn)
          (fun _ _ _ heq => by cases heq; exact h_body_vf_σ₁)
          (fun _ _ _ heq => by cases heq; exact h_body_kf_σ₁)
          (fun _ _ _ heq => by cases heq; exact h_body_cdf_σ₁)
          (fun _ _ _ heq => by cases heq; exact h_body_hdf_σ₁)
          (fun clo heq => by cases heq; exact h_l_notin_body)
          -- Chain label disjoint: Disjoint ({l_let} ∪ body.allLabels) used
          (fun clo_arg heq => by
            cases heq
            intro op args oa hsusp used usedV hchain a' hoa htk
            obtain ⟨used₀, usedV₀, hchain₀, hbound₀, _, _, _⟩ := _h_cb_ce op args oa hsusp
            have ⟨h_eq_l, _⟩ := hchain.used_unique hchain₀; subst h_eq_l
            have h_sub := hbound₀ a' hoa htk -- used ⊆ ce.allLabels
            -- {l_let} disjoint: l_let ∉ ce.allLabels (h_l_notin_ce) → l_let ∉ used
            -- body.allLabels disjoint: Disjoint ce.allLabels body.allLabels → Disjoint body.allLabels used
            exact Finset.disjoint_left.mpr fun l hl =>
              fun h_in_used => Finset.disjoint_left.mp h_ce_body_disj.symm hl (h_sub h_in_used))
          -- Chain var disjoint
          (fun clo_arg heq => by
            cases heq
            intro op args oa hsusp used usedV hchain a' hoa htk y_param hp
            -- usedV ⊆ ce.topAllocVars (from ChainBound var bound)
            -- WellNamed: {y} ∪ body.topAllocVars disjoint from ce.topAllocVars
            cases hp
            obtain ⟨used₀, usedV₀, hchain₀, _, hvar_bound₀, _, _⟩ := _h_cb_ce op args oa hsusp
            have ⟨_, h_vars_eq⟩ := hchain.used_unique hchain₀; subst h_vars_eq
            have h_usedV_sub := hvar_bound₀ a' hoa htk
            have h_wn := h_wf.wn
            have h_y_notin_ce := wellNamedProgram_letE_y_notin_ce h_wn
            have h_ce_body_var_disj : Disjoint ce.topAllocVars e_body.topAllocVars := by
              cases h_wn; assumption
            exact Finset.disjoint_of_subset_right h_usedV_sub
              (Finset.disjoint_union_left.mpr ⟨Finset.disjoint_singleton_left.mpr h_y_notin_ce,
                h_ce_body_var_disj.symm⟩))
          -- Chain tk suffix
          (fun op args oa hsusp a' hoa => by
            obtain ⟨_, _, _, _, _, htk_suf, _⟩ := _h_cb_ce op args oa hsusp
            exact htk_suf a' hoa)
          -- Bridge label
          (fun clo_arg heq_fc op args oa hsusp a' hoa h_ne_tk => by
            cases heq_fc
            obtain ⟨_, _, _, _, _, _, h_bridge⟩ := _h_cb_ce op args oa hsusp
            obtain ⟨l_br, h_l_br_mem, h_l_br_suf⟩ := h_bridge a' hoa h_ne_tk
            have h_l_br_notin : l_br ∉ e_body.allLabels := by
              intro hmem
              cases Finset.mem_union.mp h_l_br_mem with
              | inl h => exact h_l_notin_body (Finset.mem_singleton.mp h ▸ hmem)
              | inr h => exact Finset.disjoint_left.mp h_ce_body_disj h hmem
            exact ⟨l_br, Finset.mem_union_left _ h_l_br_mem, h_l_br_notin, h_l_br_suf⟩)
          -- CExp-side labels (ceLabels = ce.allLabels from ChainBound of P_cexp)
          (fun clo_arg heq_fc op args oa hsusp => by
            cases heq_fc
            exact ⟨ce.allLabels,
              h_ce_body_disj,
              h_l_notin_ce,
              fun used usedVars hchain a' hoa htk => by
                obtain ⟨used₀, usedV₀, hchain₀, hbound₀, _, _, _⟩ := _h_cb_ce op args oa hsusp
                have ⟨h_eq_l, _⟩ := hchain.used_unique hchain₀; subst h_eq_l
                exact hbound₀ a' hoa htk,
              fun a' hoa htk => by
                obtain ⟨used₀, usedV₀, hchain₀, hbound₀, _, _, _⟩ := _h_cb_ce op args oa hsusp
                subst hoa
                exact hbound₀ a' rfl htk (hchain₀.frame_label_mem),
              Finset.subset_union_right.trans Finset.subset_union_left⟩)
          (fun _ _ _ heq => by cases heq; exact Finset.union_subset (Finset.subset_union_left.trans Finset.subset_union_left) Finset.subset_union_right)
          (fun _ _ _ heq => by cases heq; exact Finset.subset_union_right)
          (fun _ heq => by cases heq; exact (Finset.subset_union_left).trans Finset.subset_union_left)
          (fun _ heq => by cases heq; exact Finset.subset_union_right)
          (fun _ heq => by cases heq; exact Finset.union_subset (Finset.subset_union_left.trans Finset.subset_union_left) Finset.subset_union_right)
          (fun _ heq op args oa hsusp used usedVars hpc a' hoa htk => by
            cases heq
            obtain ⟨_, usedV₀, hpc₀, _, hvar_bound₀, _, _⟩ := _h_cb_ce op args oa hsusp
            have ⟨_, h_eq⟩ := hpc.used_unique hpc₀; subst h_eq
            exact (hvar_bound₀ a' hoa htk).trans ((Finset.subset_insert _ _).trans Finset.subset_union_left))
      -- Compose outputs
      exact ⟨.eval_let h_strict_ce h_strict_cont, h_wf_v, hinv',
             (h_wb_ce.trans (h_wb_cont.mono (Finset.Subset.refl _) (Finset.Subset.refl _) (Finset.Subset.refl _) _contDL_sub)).mono
               (by simp)
               (by simp)
               (by simp) (by simp),
             -- Chain bound from P_continue, lifted to e.allLabels
             fun op args oa hv => by
               obtain ⟨used, usedV, hchain, hbound, hvar_bound, htk_suf, h_bridge⟩ := h_cb_cont op args oa hv
               refine ⟨used, usedV, hchain,
                 fun a' hoa htk => (hbound a' hoa htk).trans (by simp),
                 fun a' hoa htk => (hvar_bound a' hoa htk).trans (by simp),
                 htk_suf,
                 fun a' hoa h_ne_tk => by
                   obtain ⟨l_br, h_mem, h_suf⟩ := h_bridge a' hoa h_ne_tk
                   refine ⟨l_br, ?_, h_suf⟩
                   -- h_mem : l_br ∈ {l_let} ∪ ({l_let} ∪ ce.allLabels ∪ e_body.allLabels)
                   -- Goal: l_br ∈ (Exp.letE ...).allLabels = {l_let} ∪ ce.allLabels ∪ e_body.allLabels
                   simp only [Exp.allLabels]
                   rcases Finset.mem_union.mp h_mem with h | h
                   · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
                   · exact h⟩⟩
    | eval_tail h_ce =>
      rename_i ce l_tail
      have h_wl_ce : WellLabeledSubCExp ce := by cases h_wf.1 with | tail _ _ h1 _ => exact h1
      have h_wn_ce : WellNamedSubCExp ce := by cases h_wf.2 with | tail _ _ h1 => exact h1
      have h_l_notin_ce : l_tail ∉ ce.allLabels := by cases h_wf.1 with | tail _ _ _ h2 => exact h2
      have h_in_tail : ∀ l, l ∈ (Exp.tail ce l_tail).allLabels ↔ l = l_tail ∨ l ∈ ce.allLabels := by simp
      have ⟨h_strict, h_wf_v, hinv', h_wb, _h_cb⟩ :=
        (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).2.1 ce ρ σ t l_tail v σ'
          h_ce h_wl_ce h_wn_ce hinv
          (fun x hx => h_var_fresh x (by simp; exact hx))
          (fun k hk hlk => h_kont_fresh l_tail ((h_in_tail _).mpr (Or.inl rfl)) k hk hlk)
          (fun l hl k hk hlk => h_kont_fresh l ((h_in_tail _).mpr (Or.inr hl)) k hk hlk)
          h_l_notin_ce
          (fun l hl => h_cdf l ((h_in_tail _).mpr (Or.inr hl)))
          (h_cdf l_tail ((h_in_tail _).mpr (Or.inl rfl)))
          (fun h_is_handler => h_hdf l_tail (by simp [Exp.handlerLabels, h_is_handler]))
          (fun l hl => h_hdf l (by simp only [Exp.handlerLabels, Finset.mem_union]; exact Or.inr hl))
          (fun h_hl => by
            by_contra h_neg
            have h_in_hls := h_label_kind_sound l_tail h_hl _ h_wf.wl
              ((h_in_tail _).mpr (Or.inl rfl))
            simp only [Exp.handlerLabels, Finset.mem_union] at h_in_hls
            have h_not_true : ¬ (ce.isHandlerCExp = true) := h_neg
            rcases h_in_hls with h1 | h2 <;>
              [simp [h_not_true] at h1;
               exact h_l_notin_ce (CExp.handlerLabels_subset_allLabels ce h2)])
      exact ⟨.eval_tail h_strict, h_wf_v, hinv',
             h_wb.mono (by simp) (by simp) (by simp) (by simp),
             fun op args oa hv => by
               obtain ⟨used, usedV, hchain, hbound, hvar_bound, htk_suf, h_bridge⟩ := _h_cb op args oa hv
               exact ⟨used, usedV, hchain, fun a' hoa htk =>
                 (hbound a' hoa htk).trans (by simp),
                 fun a' hoa htk => (hvar_bound a' hoa htk).trans (by simp),
                 htk_suf,
                 fun a' hoa h_ne_tk => by
                   obtain ⟨l_br, h_mem, h_suf⟩ := h_bridge a' hoa h_ne_tk
                   exact ⟨l_br, by simp; exact Or.elim (Finset.mem_union.mp h_mem) (fun h => Or.inl (Finset.mem_singleton.mp h)) (fun h => Or.inr h), h_suf⟩⟩⟩
  constructor
  -- P_cexp
  · intro ce ρ σ t l_enc v σ' h_naive h_wl h_wn hinv
          h_var_fresh h_kont_enc_fresh h_kont_fresh h_l_notin_ce
          h_cdf h_cdf_enc h_hdf_enc h_hdf_sub h_label_kind
    cases h_naive with
    | eval_atomic h1 =>
      exact ⟨.eval_atomic h1,
             ⟨WellFormedValue.of_wellFormedStorable
               (wellFormedStorable_of_evalTAtomic hinv.wf_store
                 (fun xs body hlam => ⟨wellFormedSubCExp_atomic_ae ⟨h_wl, h_wn⟩ xs body hlam,
                                       wellFormedSubCExp_atomic_ae_disjoint ⟨h_wl, h_wn⟩ xs body hlam,
                                       wellNamedSubCExp_atomic_ae_nodup h_wn xs body hlam⟩) h1),
              fun hdl ρ' oa h => by cases h; exact pairwiseChain_of_evalTAtomic hinv.chain_wf h1,
              fun _ _ _ h => by cases h⟩,
             hinv,
             WriteBound.refl,
             fun op args oa hv => by cases hv⟩
    | eval_fun h_av _h_nd h_vf_eq h_σ' =>
      subst h_av; subst h_vf_eq; subst h_σ'
      rename_i f xs e1
      have h_fresh_f : σ (.val ⟨f, t⟩) = none :=
        h_var_fresh f (by simp)
      have h_wf_ce : WellFormedSubCExp (.funDef f xs e1) := ⟨h_wl, h_wn⟩
      have h_wfv6 : WellFormedValue6
          (σ.extend (.val ⟨f, t⟩) (.denotable (.closure ⟨xs, e1, ρ.extend f ⟨f, t⟩, _h_nd⟩)))
          (.den (.closure ⟨xs, e1, ρ.extend f ⟨f, t⟩, _h_nd⟩)) := by
        refine ⟨⟨wellFormedSubCExp_funDef_body h_wf_ce, wellFormedSubCExp_funDef_disjoint h_wf_ce, _h_nd⟩, fun _ _ _ h => ?_, fun _ _ _ h => ?_⟩
        · cases h
        · cases h
      exact ⟨.eval_fun rfl h_fresh_f _h_nd rfl rfl, h_wfv6,
             hinv.extend_val ⟨f, t⟩ _
               ⟨wellFormedSubCExp_funDef_body h_wf_ce, wellFormedSubCExp_funDef_disjoint h_wf_ce, _h_nd⟩
               (fun _ _ _ h => by cases h),
             fun a ha => by
               by_cases heq : a = .val ⟨f, t⟩
               · constructor
                 · intro _; subst heq; left; exact ⟨f, rfl, by simp⟩
                 · intro hne; subst heq; exact (hne rfl).elim
               · constructor
                 · intro _; rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
                 · intro _; rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha,
             fun op args oa hv => by cases hv⟩
    | eval_opApp h_lookup =>
      rename_i x_op a_v_op op_n
      have h_wfv6 : WellFormedValue6 σ (.suspended op_n [a_v_op] none) := by
        refine ⟨trivial, fun _ _ _ h => ?_, fun _ _ _ h => ?_⟩
        · cases h
        · cases h; exact ⟨∅, ∅, .none⟩
      exact ⟨.eval_opApp h_lookup, h_wfv6, hinv,
             WriteBound.refl,
             fun op args oa hv => by cases hv; refine ⟨∅, ∅, .none, fun a' h => ?_, fun a' h => ?_, fun a' h => ?_, fun a' h => ?_⟩ <;> cases h⟩
    | eval_match h_eval h_d h_find h_xs h_body =>
      subst h_d; subst h_xs
      rename_i ae c bs e_m n
      have h_body_labels_sub : e_m.allLabels ⊆ (CExp.matchE ae bs).allLabels :=
        match_body_allLabels_subset h_find
      have h_body_vars_sub : e_m.topAllocVars ⊆ (CExp.matchE ae bs).topAllocVars :=
        match_body_topAllocVars_subset h_find
      have h_wf_body : WellFormedProgram e_m := by
        obtain ⟨b, hb_mem, hb_eq⟩ := findBranch_mem h_find; subst hb_eq
        constructor
        · cases wellLabeledSubCExp_matchE_branches h_wl _ hb_mem with | branch h => exact h
        · cases wellNamedSubCExp_matchE_branches h_wn _ hb_mem with | branch h _ => exact h
      have h_body_handlerLabels_sub : e_m.handlerLabels ⊆ (CExp.matchE ae bs).handlerLabels :=
        match_body_handlerLabels_subset h_find
      have ⟨h_strict, h_wf_v, hinv', h_wb, _h_cb⟩ :=
        (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).1 e_m _ σ t _ σ'
          h_body h_wf_body hinv
          (fun x hx => h_var_fresh x (h_body_vars_sub hx))
          (fun l hl k hk hlk => h_kont_fresh l (h_body_labels_sub hl) k hk hlk)
          (fun l hl => h_cdf l (h_body_labels_sub hl))
          (fun l hl => h_hdf_sub l (h_body_handlerLabels_sub hl))
      exact ⟨.eval_match h_eval rfl h_find rfl h_strict, h_wf_v, hinv',
             h_wb.mono h_body_vars_sub h_body_labels_sub
               (h_body_labels_sub.trans Finset.subset_union_right)
               (h_body_labels_sub.trans Finset.subset_union_right),
             fun op args oa hv => by
               obtain ⟨used, usedV, hchain, hbound, hvar_bound, htk_suf, h_bridge⟩ := _h_cb op args oa hv
               exact ⟨used, usedV, hchain, fun a' hoa htk =>
                 (hbound a' hoa htk).trans h_body_labels_sub,
                 fun a' hoa htk => (hvar_bound a' hoa htk).trans h_body_vars_sub,
                 htk_suf,
                 fun a' hoa h_ne_tk =>
                   let ⟨l_br, h_mem, h_suf⟩ := h_bridge a' hoa h_ne_tk
                   ⟨l_br, Finset.mem_union_right _ (h_body_labels_sub h_mem), h_suf⟩⟩⟩
    | eval_match_succ h_ae h_branch h_inner h_xs h_afresh h_σ_new h_ρ_new h_body =>
      subst h_xs; subst h_afresh; subst h_σ_new; subst h_ρ_new
      rename_i ae a_inner bs e_m d_inner x_bind n
      have h_body_labels_sub : e_m.allLabels ⊆ (CExp.matchE ae bs).allLabels :=
        match_body_allLabels_subset h_branch
      have h_body_vars_sub : e_m.topAllocVars ⊆ (CExp.matchE ae bs).topAllocVars :=
        match_body_topAllocVars_subset h_branch
      have h_xbind_in : x_bind ∈ (CExp.matchE ae bs).topAllocVars :=
        match_xbind_mem_topAllocVars h_branch
      have h_fresh_x : σ (.val ⟨x_bind, t⟩) = none := h_var_fresh x_bind h_xbind_in
      have h_wf_body : WellFormedProgram e_m := by
        obtain ⟨b, hb_mem, hb_eq⟩ := findBranch_mem h_branch; subst hb_eq
        constructor
        · cases wellLabeledSubCExp_matchE_branches h_wl _ hb_mem with | branch h => exact h
        · cases wellNamedSubCExp_matchE_branches h_wn _ hb_mem with | branch h _ => exact h
      have h_wf_d : WellFormedStorable (.denotable d_inner) :=
        wellFormedStorable_of_store_lookup hinv.wf_store h_inner
      have hinv_ext := hinv.extend_val ⟨x_bind, t⟩ _ h_wf_d
        (fun _ _ _ heq => by cases heq; exact hinv.pairwiseChain_of_lookup h_inner)
      have h_body_var_fresh : ∀ x ∈ e_m.topAllocVars,
          (σ.extend (.val ⟨x_bind, t⟩) (.denotable d_inner)) (.val ⟨x, t⟩) = none := by
        intro x hx
        have h_branch_mem := findBranch_mem h_branch
        have h_xbind_notin : x_bind ∉ e_m.topAllocVars := by
          obtain ⟨b, hb_mem, hb_eq⟩ := h_branch_mem; subst hb_eq
          have h_wnb := (wellNamedSubCExp_matchE_branches h_wn) _ hb_mem
          cases h_wnb with | branch _ h_vars => exact h_vars x_bind List.mem_cons_self
        rw [val_extend_preserves_val_ne (ne_of_mem_of_not_mem hx h_xbind_notin)]
        exact h_var_fresh x (h_body_vars_sub hx)
      have h_body_kont_fresh : ∀ l ∈ e_m.allLabels, ∀ k : TKAddr,
          k.frame.time = t → k.frame.label = l →
          (σ.extend (.val ⟨x_bind, t⟩) (.denotable d_inner)) (.kont k) = none := by
        intro l hl k hk hlk; rw [val_extend_preserves_kont]
        exact h_kont_fresh l (h_body_labels_sub hl) k hk hlk
      have h_cdf_ext : ∀ l ∈ e_m.allLabels,
          CallDescFresh (σ.extend (.val ⟨x_bind, t⟩) (.denotable d_inner)) t l :=
        fun l hl => (h_cdf l (h_body_labels_sub hl)).extend_val
      have h_body_handlerLabels_sub : e_m.handlerLabels ⊆ (CExp.matchE ae bs).handlerLabels :=
        match_body_handlerLabels_subset h_branch
      have h_hdf_ext : ∀ l ∈ e_m.handlerLabels,
          HandlerDescFresh (σ.extend (.val ⟨x_bind, t⟩) (.denotable d_inner)) t l :=
        fun l hl => (h_hdf_sub l (h_body_handlerLabels_sub hl)).extend_val
      have ⟨h_strict, h_wf_v, hinv', h_wb_body, _h_cb_body⟩ :=
        (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).1 e_m _ _ t _ σ'
          h_body h_wf_body hinv_ext h_body_var_fresh h_body_kont_fresh
          h_cdf_ext h_hdf_ext
      have h_wb_ext : WriteBound σ (σ.extend (.val ⟨x_bind, t⟩) (.denotable d_inner)) t {x_bind} ∅ ∅ ∅ := by
        intro a ha; constructor
        · intro hat; by_cases heq : a = .val ⟨x_bind, t⟩
          · subst heq; left; exact ⟨x_bind, rfl, Finset.mem_singleton_self _⟩
          · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
        · intro hne; exfalso; by_cases heq : a = .val ⟨x_bind, t⟩
          · subst heq; exact hne rfl
          · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
      exact ⟨.eval_match_succ h_ae h_branch h_inner rfl rfl h_fresh_x rfl rfl h_strict,
             h_wf_v, hinv',
             (h_wb_ext.trans h_wb_body).mono
               (by intro x hx; simp only [Finset.mem_union, Finset.mem_singleton] at hx ⊢
                   rcases hx with rfl | hx; exact h_xbind_in; exact h_body_vars_sub hx)
               (by intro l hl; simp only [Finset.mem_union] at hl
                   rcases hl with hl | hl; simp at hl; exact h_body_labels_sub hl)
               (by intro l hl; simp only [Finset.mem_union] at hl
                   rcases hl with hl | hl; simp at hl; exact Finset.mem_union_right _ (h_body_labels_sub hl))
               (by intro l hl; simp only [Finset.mem_union] at hl
                   rcases hl with hl | hl; simp at hl; exact Finset.mem_union_right _ (h_body_labels_sub hl)),
             fun op args oa hv => by
               obtain ⟨used, usedV, hchain, hbound, hvar_bound, htk_suf, h_bridge⟩ := _h_cb_body op args oa hv
               exact ⟨used, usedV, hchain, fun a' hoa htk =>
                 (hbound a' hoa htk).trans h_body_labels_sub,
                 fun a' hoa htk => (hvar_bound a' hoa htk).trans h_body_vars_sub,
                 htk_suf,
                 fun a' hoa h_ne_tk =>
                   let ⟨l_br, h_mem, h_suf⟩ := h_bridge a' hoa h_ne_tk
                   ⟨l_br, Finset.mem_union_right _ (h_body_labels_sub h_mem), h_suf⟩⟩⟩
    | eval_funApp_clos h_f h_args h_clo h_tnew h_σnew h_ρnew h_body =>
      subst h_tnew; subst h_σnew; subst h_ρnew
      rename_i f xs e_body ρ_lam _h_nd aes ds n
      let t_new : Time := ⟨l_enc :: t.tk, t.tmk⟩
      have h_fresh_at_tnew : ∀ (a : TAddr), a.time = t_new → σ a = none :=
        fun a ha => h_cdf_enc a (ha ▸ .refl)
      have h_fresh_args : ∀ i, (h : i < xs.length) → σ (.val ⟨xs[i], t_new⟩) = none :=
        fun i _hi => h_fresh_at_tnew (.val ⟨xs[i], t_new⟩) rfl
      have h_body_kont_fresh : ∀ l ∈ e_body.allLabels, ∀ k : TKAddr,
          k.frame.time = t_new → k.frame.label = l →
          (xs.zip ds).foldl (fun s (x, d) =>
            s.extend (.val ⟨x, t_new⟩) (.denotable d)) σ (.kont k) = none := by
        intro l hl k hk hlk; rw [foldl_val_preserves_kont]
        exact h_fresh_at_tnew (.kont k) (by simp [TAddr.time]; exact hk)
      have h_cdf_at_tnew : ∀ l, CallDescFresh σ t_new l :=
        fun l a ha => h_cdf_enc a ((Descendant.call l .refl).trans ha)
      have h_hdf_at_tnew : ∀ l, HandlerDescFresh σ t_new l :=
        fun l a tk ha => h_cdf_enc a ((Descendant.appKont l tk .refl).trans ha)
      have h_cdf_new : ∀ l ∈ e_body.allLabels, CallDescFresh
          ((xs.zip ds).foldl (fun s (x, d) =>
            s.extend (.val ⟨x, t_new⟩) (.denotable d)) σ) t_new l :=
        fun l _hl => (h_cdf_at_tnew l).foldl_val
      have h_hdf_new : ∀ l ∈ e_body.handlerLabels, HandlerDescFresh
          ((xs.zip ds).foldl (fun s (x, d) =>
            s.extend (.val ⟨x, t_new⟩) (.denotable d)) σ) t_new l :=
        fun l _hl => (h_hdf_at_tnew l).foldl_val
      have h_wf_clo := wellFormedStorable_of_evalTAtomic hinv.wf_store
          (fun xs' body' hlam => by
            cases h_wl with | funApp h_wl_f _ =>
            cases h_wn with | funApp h_wn_f h_disj h_nodup _ =>
            exact ⟨⟨h_wl_f _ _ hlam, h_wn_f _ _ hlam⟩, h_disj _ _ hlam, h_nodup _ _ hlam⟩) h_f
      have h_wf_body : WellFormedProgram e_body := h_wf_clo.1
      have h_disj_xs_body : Disjoint xs.toFinset e_body.topAllocVars := h_wf_clo.2.1
      have h_body_var_fresh : ∀ x ∈ e_body.topAllocVars,
          (xs.zip ds).foldl (fun s (x, d) =>
            s.extend (.val ⟨x, t_new⟩) (.denotable d)) σ (.val ⟨x, t_new⟩) = none := by
        intro x hx
        have hx_notin_fs : x ∉ xs.toFinset := Finset.disjoint_right.mp h_disj_xs_body hx
        have h_len : xs.length ≤ ds.length := by
          have := List.Forall₂.length_eq h_clo; omega
        have hx_notin_map : x ∉ (xs.zip ds).map Prod.fst := by
          rw [List.map_fst_zip h_len]; exact fun h => hx_notin_fs (List.mem_toFinset.mpr h)
        rw [foldl_val_preserves_val_notin hx_notin_map]
        exact h_fresh_at_tnew _ rfl
      have h_ds_wf : ∀ d ∈ ds, WellFormedStorable (.denotable d) := by
        suffices ∀ (aes' : List AExp) (ds' : List TDenotable),
            List.Forall₂ (fun ae d => evalTAtomic ae ρ σ = some d) aes' ds' →
            (∀ ae ∈ aes', ∀ xs' body', ae = .lam xs' body' →
              WellFormedProgram body' ∧ Disjoint xs'.toFinset body'.topAllocVars ∧ xs'.Nodup) →
            ∀ d ∈ ds', WellFormedStorable (.denotable d) from
          this aes ds h_clo (fun ae h_ae xs' body' hlam =>
            ⟨⟨by cases h_wl with | funApp _ h => exact h ae h_ae _ _ hlam,
              by cases h_wn with | funApp _ _ _ h _ _ => exact h ae h_ae _ _ hlam⟩,
             by cases h_wn with | funApp _ _ _ _ h _ => exact h ae h_ae _ _ hlam,
             by cases h_wn with | funApp _ _ _ _ _ h => exact h ae h_ae _ _ hlam⟩)
        intro aes' ds' h_forall h_wf_aes d hd
        induction h_forall with
        | nil => simp at hd
        | @cons ae₀ d₀ _ _ h_eval _ ih =>
          cases List.mem_cons.mp hd with
          | inl heq =>
            subst heq
            exact wellFormedStorable_of_evalTAtomic hinv.wf_store
              (h_wf_aes ae₀ (List.Mem.head _)) h_eval
          | inr h => exact ih (fun ae h_ae => h_wf_aes ae (List.Mem.tail _ h_ae)) h
      have hinv_new : FreshInvariant
          ((xs.zip ds).foldl (fun s (x, d) =>
            s.extend (.val ⟨x, t_new⟩) (.denotable d)) σ) :=
        foldl_val_preserves_fi hinv (fun ⟨_, d⟩ hp => h_ds_wf d (mem_snd_of_mem_zip hp))
          (fun ⟨_, d⟩ hp hdl ρ oa heq => by
            have h_d_in_ds := mem_snd_of_mem_zip hp
            subst heq
            suffices ∀ (aes' : List AExp) (ds' : List TDenotable),
                List.Forall₂ (fun ae d => evalTAtomic ae _ σ = some d) aes' ds' →
                (.kontClosure hdl ρ oa) ∈ ds' → ∃ used usedVars, PairwiseChain σ oa used usedVars from
              this aes ds h_clo h_d_in_ds
            intro aes' ds' h_f₂ h_mem
            induction h_f₂ with
            | nil => simp at h_mem
            | @cons ae₀ d₀ _ _ h_eval _ ih =>
              cases List.mem_cons.mp h_mem with
              | inl heq => subst heq; exact pairwiseChain_of_evalTAtomic hinv.chain_wf h_eval
              | inr h => exact ih h)
      have ⟨h_strict_body, h_wf_v, hinv', h_wb_body, _h_cb_body⟩ :=
        (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).1 e_body _ _ t_new v σ'
          h_body h_wf_body hinv_new h_body_var_fresh h_body_kont_fresh
          h_cdf_new h_hdf_new
      exact ⟨.eval_funApp_clos h_f h_args h_clo rfl
               (fun i hi => h_fresh_args i hi) rfl rfl h_strict_body,
             h_wf_v, hinv',
             fun a ha => by
               have h_desc_tnew : Descendant t_new (a : TAddr).time := by
                 by_contra hnd
                 have h_fp := foldl_val_preserves_non_desc (σ := σ) (t_w := t_new) (pairs := xs.zip ds) hnd
                 exact hnd (h_wb_body.descendant (show σ' a ≠ _ from by rw [h_fp]; exact ha))
               exact ⟨fun hat => by subst hat; exact absurd h_desc_tnew not_descendant_of_call_ext,
                      fun _ => ⟨l_enc, Finset.mem_union_left _ (Finset.mem_singleton_self _),
                        Or.inl h_desc_tnew⟩⟩,
             fun op args oa hv => by
               obtain ⟨used, usedV, hchain, hbound, _hvar, _htk, _h_bridge⟩ := _h_cb_body op args oa hv
               exact ⟨used, usedV, hchain,
                 fun a' hoa htk => by
                   have hlen := (_htk a' hoa).length_le
                   simp only [t_new] at hlen; rw [htk, List.length_cons] at hlen; omega,
                 fun a' hoa htk => by
                   have hlen := (_htk a' hoa).length_le
                   simp only [t_new] at hlen; rw [htk, List.length_cons] at hlen; omega,
                 fun a' hoa => List.IsSuffix.trans ⟨[l_enc], rfl⟩ (_htk a' hoa),
                 fun a' hoa h_ne_tk => by
                   exact ⟨l_enc, Finset.mem_union_left _ (Finset.mem_singleton_self _), _htk a' hoa⟩⟩⟩
    | eval_funApp_kont h_f h_ae h_tmk h_apply h_teq h_handle =>
      subst h_tmk; subst h_teq
      rename_i f hdl ρ_h a_κ ae_arg d_arg n1 v' σ₁ n2
      let t_handle : Time := ⟨l_enc :: t.tk, t.tmk⟩
      let tmk_apply : MKTime := (l_enc, l_enc :: t.tk) :: t.tmk
      have h_tmk_fresh_apply : ∀ a, tmk_apply <:+ a.time.tmk → σ a = none := by
        intro a ha
        obtain ⟨tk₀, hd⟩ := Descendant.of_tmk_suffix ha a.time.tk
        exact h_cdf_enc a ((Descendant.appKont l_enc tk₀ .refl).trans hd)
      obtain ⟨chainUsed, chainVars, h_chain_f⟩ := pairwiseChain_of_evalTAtomic hinv.chain_wf h_f
      have h_wf_d_arg := wellFormedStorable_of_evalTAtomic hinv.wf_store
        (fun xs body hlam => by
          cases h_wl with | funApp _ h_aes =>
            cases h_wn with | funApp _ _ _ h_wn_aes h_disj_aes h_nodup_aes =>
              exact ⟨⟨h_aes _ (List.Mem.head _) _ _ hlam,
                      h_wn_aes _ (List.Mem.head _) _ _ hlam⟩,
                     h_disj_aes _ (List.Mem.head _) _ _ hlam,
                     h_nodup_aes _ (List.Mem.head _) _ _ hlam⟩) h_ae
      have h_d_chain_arg : ∀ hdl' ρ' oa, d_arg = .kontClosure hdl' ρ' oa →
          ∃ u uv, PairwiseChain σ oa u uv := by
        intro hdl' ρ' oa heq; cases heq; exact pairwiseChain_of_evalTAtomic hinv.chain_wf h_ae
      have ⟨h_strict_apply, h_wf_v', hinv₁, h_desc_apply, _h_dfp_apply, _h_desc_scope_apply⟩ :=
        (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).2.2.2.2 a_κ d_arg σ tmk_apply v' σ₁ chainUsed chainVars
          h_apply h_wf_d_arg h_d_chain_arg hinv h_tmk_fresh_apply h_chain_f
      -- Freshness preservation through inner P_Apply
      have h_pres_apply : ∀ a, a.time.tmk = t.tmk → σ₁ a = σ a := by
        intro a hat; by_contra h_ne; push_neg at h_ne
        have h_desc := h_desc_apply a h_ne
        rw [hat] at h_desc
        obtain ⟨px, hpx⟩ := h_desc
        have hlen := congr_arg List.length hpx
        simp only [tmk_apply, List.length_append, List.length_cons] at hlen; omega
      have h_fresh_th : ∀ a, a.time = t_handle → σ a = none :=
        fun a ha => h_cdf_enc a (ha ▸ .refl)
      have h_var_fresh_σ₁ : ∀ x ∈ hdl.topAllocVars, σ₁ (.val ⟨x, t_handle⟩) = none := by
        intro x _; rw [h_pres_apply _ rfl]; exact h_fresh_th _ rfl
      have h_kont_fresh_σ₁ : ∀ l ∈ hdl.allLabels, ∀ k : TKAddr,
          k.frame.time = t_handle → k.frame.label = l → σ₁ (.kont k) = none := by
        intro l _ k hk _
        rw [h_pres_apply _ (by simp [TAddr.time]; rw [hk])]
        exact h_fresh_th _ (by simp [TAddr.time]; exact hk)
      have h_kont_enc_fresh_σ₁ : ∀ k : TKAddr,
          k.frame.time = t_handle → k.frame.label = l_enc → σ₁ (.kont k) = none := by
        intro k hk _
        rw [h_pres_apply _ (by simp [TAddr.time]; rw [hk])]
        exact h_fresh_th _ (by simp [TAddr.time]; exact hk)
      -- CallDescFresh at t_handle preserved through inner P_Apply:
      -- Key argument: descendants of ⟨l :: l_enc :: t.tk, t.tmk⟩ can't have
      -- tmk_apply = (l_enc, l_enc :: t.tk) :: t.tmk as suffix, because the first handler entry
      -- from that starting point has tk with l :: l_enc :: t.tk as suffix (strictly longer than
      -- l_enc :: t.tk), making the suffix match impossible.
      have h_cdf_handle_σ₁ : ∀ l ∈ hdl.allLabels, CallDescFresh σ₁ t_handle l := by
        intro l _ a ha
        by_contra h_ne; push_neg at h_ne
        have h_orig := h_cdf_enc a ((Descendant.call l (Descendant.refl (t := t_handle))).trans ha)
        have h_changed : σ₁ a ≠ σ a := by rw [h_orig]; exact h_ne
        have h_tmk_suf := h_desc_apply a h_changed
        exact ha.no_shorter_tmk_entry h_tmk_suf
      -- HandlerDescFresh at t_handle: entries at (l, l_enc :: t.tk) :: t.tmk
      -- vs inner writes at tmk_apply = (l_enc, l_enc :: t.tk) :: t.tmk
      -- Descendants of ⟨tk, (l, l_enc :: t.tk) :: t.tmk⟩ have (l, l_enc :: t.tk) :: t.tmk as tmk suffix.
      -- The first handler entry has tk with l_enc :: t.tk as suffix (from call chain).
      -- For tmk_apply to also be suffix: (l_enc, l_enc :: t.tk) must match the entry just before t.tmk,
      -- but that entry has second component with l_enc :: t.tk as suffix (which differs from l_enc :: t.tk
      -- only if there was a call prepend... actually it IS l_enc :: t.tk or longer).
      -- Same structural argument as CallDescFresh case.
      have h_not_handler_l_enc : ¬ isHandlerLabel l_enc := fun h =>
        by have := h_label_kind h; simp [CExp.isHandlerCExp] at this
      have h_hdf_handle_σ₁ : ∀ l ∈ hdl.handlerLabels, HandlerDescFresh σ₁ t_handle l := by
        intro l hl a tk ha
        have h_l_ne : l ≠ l_enc := fun h_eq =>
          h_not_handler_l_enc (h_eq ▸ h_handlerLabels_consistent hdl l hl)
        -- l ≠ l_enc: suffix equality on tmk entries gives contradiction
        by_contra h_ne; push_neg at h_ne
        have h_desc_of_t : Descendant t_handle a.time :=
          (Descendant.appKont l tk Descendant.refl).trans ha
        have h_orig := h_cdf_enc a h_desc_of_t
        have h_changed : σ₁ a ≠ σ a := by rw [h_orig]; exact h_ne
        have h_tmk_suf := h_desc_apply a h_changed
        -- (l, l_enc :: t.tk) :: t.tmk and (l_enc, l_enc :: t.tk) :: t.tmk both suffix of a.time.tmk
        -- Same length → equal → l = l_enc, contradicting h_l_ne
        have heq := suffix_eq_of_length_eq
          ((l, l_enc :: t.tk) :: t.tmk)
          ((l_enc, l_enc :: t.tk) :: t.tmk)
          a.time.tmk ha.tmk_suffix h_tmk_suf (by simp)
        exact h_l_ne (Prod.ext_iff.mp (List.cons.inj heq).1).1
      have h_wf_hdl : WellFormedSubHandler hdl := by
        have := wellFormedStorable_of_evalTAtomic hinv.wf_store
          (fun xs body hlam => by subst hlam; simp [evalTAtomic] at h_f) h_f
        exact this
      have ⟨h_strict_handle, h_wf_v, hinv', h_wb_handle, _h_cb_handle⟩ :=
        (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).2.2.2.1 l_enc hdl ρ_h v' σ₁ t_handle v σ'
          h_handle h_wf_hdl h_wf_v' hinv₁
          h_var_fresh_σ₁ h_kont_fresh_σ₁ h_kont_enc_fresh_σ₁ h_cdf_handle_σ₁ h_hdf_handle_σ₁
          (fun h_in => h_not_handler_l_enc (h_handlerLabels_consistent hdl l_enc h_in))
      -- Compose outputs (WriteBound across apply + handle steps)
      exact ⟨.eval_funApp_kont h_f h_ae rfl h_strict_apply rfl h_strict_handle,
             h_wf_v, hinv',
             -- WriteBound: all writes go through t_handle, hence DescendantVia t l_enc
             (fun a ha => by
               have h_desc_t_handle : Descendant t_handle a.time := by
                 by_cases h1 : σ₁ a = σ a
                 · exact h_wb_handle.descendant (by rw [h1]; exact ha)
                 · have h_suf := h_desc_apply a h1
                   obtain ⟨tk₀, hd⟩ := Descendant.of_tmk_suffix h_suf a.time.tk
                   exact (Descendant.appKont l_enc tk₀ Descendant.refl).trans hd
               exact ⟨fun hat => absurd (hat ▸ h_desc_t_handle) not_descendant_of_call_ext,
                      fun _ => ⟨l_enc, by simp, Or.inl h_desc_t_handle⟩⟩),
             fun op args oa hv => by
               obtain ⟨used, usedV, hchain, hbound, hvar_bound, htk_suf, h_bridge⟩ := _h_cb_handle op args oa hv
               -- t_handle.tk = l_enc :: t.tk, so same-tk at t is vacuous
               have h_tk_suf_t : ∀ a', oa = some a' → t.tk <:+ a'.frame.time.tk :=
                 fun a' hoa => (List.suffix_cons l_enc t.tk).trans (htk_suf a' hoa)
               exact ⟨used, usedV, hchain,
                 fun a' hoa htk => by
                   have := (htk ▸ htk_suf a' hoa).length_le; simp [t_handle] at this; omega,
                 fun a' hoa htk => by
                   have := (htk ▸ htk_suf a' hoa).length_le; simp [t_handle] at this; omega,
                 h_tk_suf_t,
                 fun a' hoa h_ne_tk =>
                   ⟨l_enc, by simp, htk_suf a' hoa⟩⟩⟩
    | eval_handler h_tb h_body_eval h_handle =>
      subst h_tb
      rename_i n1 e_body_h v_mid σ_mid n2 l_h hdl
      have h_wf_ce' : WellFormedSubCExp (.handler hdl e_body_h l_h) := ⟨h_wl, h_wn⟩
      have h_wf_body := wellFormedSubCExp_handler_body h_wf_ce'
      have h_wf_handler := wellFormedSubCExp_handler_sub h_wf_ce'
      let t_body : Time := ⟨[], (l_h, t.tk) :: t.tmk⟩
      have h_l_h_in_ce : l_h ∈ (CExp.handler hdl e_body_h l_h).allLabels := by
        simp
      have h_l_h_in_ce_hl : l_h ∈ (CExp.handler hdl e_body_h l_h).handlerLabels := by
        simp [CExp.handlerLabels]
      have h_l_h_notin_hdl : l_h ∉ hdl.allLabels := by
        cases h_wl with | handler _ _ h1 _ => exact h1
      have h_l_h_notin_body : l_h ∉ e_body_h.allLabels := by
        cases h_wl with | handler _ _ _ h2 => exact h2
      have h_df_enc : DescFresh σ t l_h :=
        DescFresh.of_cdf_hdf (h_cdf l_h h_l_h_in_ce) (h_hdf_sub l_h h_l_h_in_ce_hl)
      have h_body_fresh : ∀ (a : TAddr), a.time = t_body → σ a = none :=
        fun a ha => h_df_enc a (Or.inr ⟨[], by rw [ha]; exact .refl⟩)
      have h_body_var_fresh : ∀ x ∈ e_body_h.topAllocVars, σ (.val ⟨x, t_body⟩) = none :=
        fun x _ => h_body_fresh (.val ⟨x, t_body⟩) rfl
      have h_body_kont_fresh : ∀ l ∈ e_body_h.allLabels, ∀ k : TKAddr,
          k.frame.time = t_body → k.frame.label = l → σ (.kont k) = none :=
        fun _ _ k hk _ => h_body_fresh (.kont k) (by simp [TAddr.time]; exact hk)
      have h_body_cdf : ∀ l ∈ e_body_h.allLabels, CallDescFresh σ t_body l :=
        fun l _ a ha => h_df_enc a (Or.inr ⟨[], (Descendant.call l .refl).trans ha⟩)
      have h_body_hdf : ∀ l ∈ e_body_h.handlerLabels, HandlerDescFresh σ t_body l :=
        -- t_body = ⟨[], (l_h, t.tk) :: t.tmk⟩ is a handler-descendant of t at l_h.
        -- HandlerDescFresh at t_body at label l means freshness at ⟨tk, (l, []) :: (l_h, t.tk) :: t.tmk⟩.
        -- This is a descendant of t_body via appKont, hence descendant of t via handler at l_h.
        -- h_df_enc (DescFresh at l_h) gives freshness at all such descendants.
        fun l _ a tk ha => h_df_enc a (Or.inr ⟨[], (Descendant.appKont l tk .refl).trans ha⟩)
      have ⟨h_strict_body, h_wf_v_body, hinv₁, h_wb_body, _h_cb_body⟩ :=
        (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).1 e_body_h _ σ t_body _ _
          h_body_eval h_wf_body hinv h_body_var_fresh h_body_kont_fresh
          h_body_cdf h_body_hdf
      have h_hdl_labels_sub : hdl.allLabels ⊆ (CExp.handler hdl e_body_h l_h).allLabels :=
        handler_allLabels_subset_cexp hdl _ l_h
      have h_hdl_vars_sub : hdl.topAllocVars ⊆ (CExp.handler hdl e_body_h l_h).topAllocVars := by
        simp [CExp.topAllocVars]
      have h_pres_at_t : ∀ a, a.time = t → σ_mid a = σ a := by
        intro a hat
        by_contra h_ne; push_neg at h_ne
        have h_desc := h_wb_body.descendant h_ne
        rw [hat] at h_desc
        exact not_descendant_of_handler_ext h_desc
      have h_var_fresh_mid : ∀ x ∈ hdl.topAllocVars, σ_mid (.val ⟨x, t⟩) = none :=
        fun x hx => by rw [h_pres_at_t _ rfl]; exact h_var_fresh x (by simp [CExp.topAllocVars]; exact hx)
      have h_kont_fresh_mid : ∀ l ∈ hdl.allLabels, ∀ k : TKAddr,
          k.frame.time = t → k.frame.label = l → σ_mid (.kont k) = none :=
        fun l hl k hk hlk => by rw [h_pres_at_t _ (by simp [TAddr.time]; exact hk)]
                                exact h_kont_fresh l (h_hdl_labels_sub hl) k hk hlk
      have h_kont_enc_fresh_mid : ∀ k : TKAddr,
          k.frame.time = t → k.frame.label = l_enc → σ_mid (.kont k) = none :=
        fun k hk hlk => by rw [h_pres_at_t _ (by simp [TAddr.time]; exact hk)]
                           exact h_kont_enc_fresh k hk hlk
      have h_hdl_handlerLabels_sub : hdl.handlerLabels ⊆ (CExp.handler hdl e_body_h l_h).handlerLabels :=
        fun l hl => by simp only [CExp.handlerLabels]; exact Finset.mem_union_left _ (Finset.mem_union_right _ hl)
      have h_cdf_orig : ∀ l ∈ hdl.allLabels, CallDescFresh σ t l :=
        fun l hl => h_cdf l (h_hdl_labels_sub hl)
      have h_hdf_orig : ∀ l ∈ hdl.handlerLabels, HandlerDescFresh σ t l :=
        fun l hl => h_hdf_sub l (h_hdl_handlerLabels_sub hl)
      have h_cdf_mid : ∀ l ∈ hdl.allLabels, CallDescFresh σ_mid t l := by
        intro l hl a ha
        by_contra h_ne; push_neg at h_ne
        have h_orig := h_cdf_orig l hl a ha
        have h_changed : σ_mid a ≠ σ a := by rw [h_orig]; exact h_ne
        have h_desc := h_wb_body.descendant h_changed
        exact Descendant.call_handler_disjoint ha h_desc.tmk_suffix
      have h_hdf_mid : ∀ l ∈ hdl.handlerLabels, HandlerDescFresh σ_mid t l := by
        intro l hl a tk ha
        by_contra h_ne; push_neg at h_ne
        have h_orig := h_hdf_orig l hl a tk ha
        have h_changed : σ_mid a ≠ σ a := by rw [h_orig]; exact h_ne
        have h_desc := h_wb_body.descendant h_changed
        have hne : l ≠ l_h := fun heq => h_l_h_notin_hdl (heq ▸ Handler.handlerLabels_subset_allLabels hdl hl)
        exact Descendant.handler_disjoint ha h_desc hne
      have h_kont_l_h_fresh : ∀ k : TKAddr, k.frame.time = t → k.frame.label = l_h → σ_mid (.kont k) = none :=
        fun k hk hlk => by
          rw [h_pres_at_t _ (by simp [TAddr.time]; exact hk)]
          exact h_kont_fresh l_h h_l_h_in_ce k hk hlk
      have ⟨h_strict_handle, h_wf_v, hinv', h_wb_handle, _h_cb_handle⟩ :=
        (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).2.2.2.1 l_h hdl _ v_mid σ_mid t v σ'
          h_handle h_wf_handler h_wf_v_body hinv₁
          h_var_fresh_mid h_kont_fresh_mid h_kont_l_h_fresh h_cdf_mid h_hdf_mid
          (fun h => h_l_h_notin_hdl (Handler.handlerLabels_subset_allLabels hdl h))
      have h_wb_body_at_t : WriteBound σ σ_mid t ∅ ∅ ∅ {l_h} := by
        intro a ha
        have h_desc := h_wb_body.descendant ha
        constructor
        · intro hat; subst hat; exact absurd h_desc not_descendant_of_handler_ext
        · intro hne; exact ⟨l_h, Finset.mem_singleton_self _, Or.inr ⟨[], h_desc⟩⟩
      refine ⟨.eval_handler rfl h_strict_body h_strict_handle,
             h_wf_v, hinv',
             WriteBound.mono (h_wb_body_at_t.trans h_wb_handle)
               (by simp [CExp.topAllocVars, Finset.empty_union])
               (by -- hdl.allLabels ⊆ {l_h} ∪ hdl.allLabels ∪ e_body_h.allLabels
                   simp only [Finset.empty_union]
                   exact h_hdl_labels_sub)
               (by -- {l_h} ∪ hdl.allLabels ⊆ {l_enc} ∪ ce.allLabels
                   simp only [Finset.empty_union]
                   intro l hl
                   rcases Finset.mem_insert.mp hl with rfl | hl'
                   · exact Finset.mem_insert_of_mem h_l_h_in_ce
                   · exact Finset.mem_insert_of_mem (h_hdl_labels_sub hl'))
               (by -- {l_h} ∪ hdl.allLabels ⊆ {l_enc} ∪ ce.allLabels
                   intro l hl
                   rcases Finset.mem_insert.mp hl with rfl | hl'
                   · exact Finset.mem_insert_of_mem h_l_h_in_ce
                   · exact Finset.mem_insert_of_mem (h_hdl_labels_sub hl')),
             by -- ChainBound widening
               have h_lh_hdl_sub_ce : insert l_h hdl.allLabels ⊆ (CExp.handler hdl e_body_h l_h).allLabels :=
                 fun l hl => by
                   rcases Finset.mem_insert.mp hl with rfl | hl'
                   · exact h_l_h_in_ce
                   · exact h_hdl_labels_sub hl'
               have h_lh_hdl_sub_enc_ce : insert l_h hdl.allLabels ⊆ insert l_enc (CExp.handler hdl e_body_h l_h).allLabels :=
                 h_lh_hdl_sub_ce.trans (Finset.subset_insert _ _)
               have h_cb := _h_cb_handle
               intro op args oa hv
               obtain ⟨used, usedVars, hpc, hsub, hvsub, htk, hbr⟩ := h_cb op args oa hv
               refine ⟨used, usedVars, hpc,
                 fun a' hoa htk' => (hsub a' hoa htk').trans h_lh_hdl_sub_ce,
                 fun a' hoa htk' => (hvsub a' hoa htk').trans (by simp [CExp.topAllocVars]),
                 htk,
                 fun a' hoa hne => ?_⟩
               · obtain ⟨l, hl, hsuf⟩ := hbr a' hoa hne
                 exact ⟨l, h_lh_hdl_sub_enc_ce hl, hsuf⟩⟩
  constructor
  -- P_continue
  · intro l_enc fc t_f v σ v' σ' frameVars frameLabels h_naive h_wf_v hinv
          h_wf_body h_y_fresh h_kont_fresh h_y_notin_body h_body_var_fresh
          h_body_kont_fresh h_body_cdf h_body_hdf h_l_enc_notin_body
          h_chain_disjoint h_chain_var_disjoint h_chain_tk_suf h_chain_tk_suf_strong
          h_ceLabels_exist
          h_frame_vars_sub h_frame_labels_sub h_frame_enc_sub
          h_frame_body_labels_sub h_frame_body_vars_sub h_inner_vars_sub
    cases h_naive with
    | continue_let h_eq h_body_eval =>
      rename_i y_var n_body e_body ρ_body d_val
      subst h_eq
      have h_fresh_y : σ (.val ⟨y_var, t_f⟩) = none := h_y_fresh y_var e_body ρ_body rfl
      have h_wf_b := h_wf_body ⟨[y_var], e_body, ρ_body, List.nodup_singleton _⟩ rfl
      have hinv_ext := hinv.extend_val ⟨y_var, t_f⟩ _ (h_wf_v.wfv.to_wellFormedStorable)
        (fun hdl ρ oa heq => by cases heq; exact h_wf_v.2 hdl ρ oa rfl)
      have h_body_vf : ∀ x ∈ e_body.topAllocVars,
          (σ.extend (.val ⟨y_var, t_f⟩) (.denotable d_val)) (.val ⟨x, t_f⟩) = none := by
        intro x hx
        have h_x_ne_y : x ≠ y_var :=
          ne_of_mem_of_not_mem hx (h_y_notin_body y_var e_body ρ_body rfl)
        simp [val_extend_preserves_val_ne h_x_ne_y]
        exact h_body_var_fresh y_var e_body ρ_body rfl x hx
      have h_body_kf : ∀ l ∈ e_body.allLabels, ∀ k : TKAddr,
          k.frame.time = t_f → k.frame.label = l →
          (σ.extend (.val ⟨y_var, t_f⟩) (.denotable d_val)) (.kont k) = none := by
        intro l hl k hk hlk; rw [val_extend_preserves_kont]
        exact h_body_kont_fresh y_var e_body ρ_body rfl l hl k hk hlk
      have h_body_cdf_ext : ∀ l ∈ e_body.allLabels,
          CallDescFresh (σ.extend (.val ⟨y_var, t_f⟩) (.denotable d_val)) t_f l :=
        fun l hl => (h_body_cdf y_var e_body ρ_body rfl l hl).extend_val
      have h_body_hdf_ext : ∀ l ∈ e_body.handlerLabels,
          HandlerDescFresh (σ.extend (.val ⟨y_var, t_f⟩) (.denotable d_val)) t_f l :=
        fun l hl => (h_body_hdf y_var e_body ρ_body rfl l hl).extend_val
      have ⟨h_strict, h_wf_v', hinv', h_wb, _h_cb⟩ :=
        (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).1 e_body _ _ t_f _ _
          h_body_eval h_wf_b hinv_ext h_body_vf h_body_kf h_body_cdf_ext h_body_hdf_ext
      have h_wb_ext : WriteBound σ (σ.extend (.val ⟨y_var, t_f⟩) (.denotable d_val)) t_f {y_var} ∅ ∅ ∅ := by
        intro a ha; constructor
        · intro hat; by_cases heq : a = .val ⟨y_var, t_f⟩
          · subst heq; left; exact ⟨y_var, rfl, Finset.mem_singleton_self _⟩
          · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
        · intro hne; exfalso; by_cases heq : a = .val ⟨y_var, t_f⟩
          · subst heq; exact hne rfl
          · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
      have h_wb_combined := h_wb_ext.trans h_wb
      exact ⟨.continue_let rfl h_fresh_y h_strict, h_wf_v', hinv',
             ⟨e_body.allLabels,
              h_frame_labels_sub y_var e_body ρ_body rfl,
              h_l_enc_notin_body ⟨[y_var], e_body, ρ_body, List.nodup_singleton _⟩ rfl,
              h_wb_combined.mono
                (by intro x hx; simp only [Finset.mem_union, Finset.mem_singleton] at hx
                    exact h_frame_vars_sub y_var e_body ρ_body rfl (hx.elim
                      (fun h => Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
                      (fun h => Finset.mem_union_right _ h)))
                (by intro l hl; simp only [Finset.mem_union] at hl
                    rcases hl with hl | hl
                    · simp at hl
                    · exact h_frame_labels_sub y_var e_body ρ_body rfl hl)
                (by intro l hl; simp only [Finset.mem_union] at hl
                    rcases hl with hl | hl
                    · simp at hl
                    · exact h_frame_labels_sub y_var e_body ρ_body rfl hl)
                (by intro l hl; simp only [Finset.mem_union] at hl
                    rcases hl with hl | hl
                    · simp at hl
                    · exact hl)⟩,
             fun op args oa hv => by
               obtain ⟨used, usedV, hchain, hbound, hvar_bound, htk_suf, h_bridge⟩ := _h_cb op args oa hv
               exact ⟨used, usedV, hchain, fun a' hoa htk =>
                 (hbound a' hoa htk).trans (h_frame_labels_sub y_var e_body ρ_body rfl),
                 fun a' hoa htk => (hvar_bound a' hoa htk).trans
                   (Finset.subset_union_right.trans (h_frame_vars_sub y_var e_body ρ_body rfl)),
                 htk_suf,
                 fun a' hoa h_ne_tk =>
                   let ⟨l_br, h_mem, h_suf⟩ := h_bridge a' hoa h_ne_tk
                   ⟨l_br, Finset.mem_union_right {l_enc} ((h_frame_labels_sub y_var e_body ρ_body rfl) h_mem), h_suf⟩⟩⟩
    | continue_op h_ψ h_aκ h_σ' =>
      subst h_σ'; subst h_aκ; subst h_ψ
      rename_i op_name clo as_v a_κ_prev
      set a_κ : TKAddr := ⟨⟨.letFrame clo, t_f, l_enc⟩, op_name⟩
      have h_fresh : σ (.kont a_κ) = none := h_kont_fresh a_κ rfl rfl rfl
      have h_susp_chain := h_wf_v.suspChain op_name as_v a_κ_prev rfl
      have h_wfp := h_wf_body clo rfl
      have h_l_enc_nb := h_l_enc_notin_body clo rfl
      have h_y_notin_clo : ∀ y, clo.params = [y] → y ∉ clo.body.topAllocVars := fun y hy =>
        h_y_notin_body y clo.body clo.env (by cases clo; simp_all)
      have hinv' : FreshInvariant (σ.extend (.kont a_κ) (.kontLink a_κ_prev)) :=
        hinv.extend_kont a_κ a_κ_prev (fun k hk hl hlet => h_kont_fresh k hk hl hlet)
      have h_strict : TFreshContinueFrameN 0 l_enc (.letFrame clo) t_f
          (.suspended op_name as_v a_κ_prev) σ
          (.suspended op_name as_v (some a_κ)) (σ.extend (.kont a_κ) (.kontLink a_κ_prev)) :=
        .continue_op rfl rfl h_fresh rfl
      -- WellFormedValue6
      have h_wf_v' : WellFormedValue6 (σ.extend (.kont a_κ) (.kontLink a_κ_prev))
          (.suspended op_name as_v (some a_κ)) := by
        refine ⟨trivial, fun _ _ _ h => ?_, fun _ _ _ h => ?_⟩
        · cases h
        · cases h
          obtain ⟨innerUsed, innerVars, h_inner_chain⟩ := h_susp_chain
          have h_inner_ext := h_inner_chain.extend_kont a_κ (.kontLink a_κ_prev) h_fresh
          cases ha_prev : a_κ_prev with
          | none =>
            exact ⟨_, _, .same_tk (TStore.extend_same _ _ _) rfl h_wfp h_y_notin_clo
              ∅ (by simp) (by simp) (by simp) h_l_enc_nb
              (fun a' h => by cases h)
              (fun a' h => by cases h) (fun _ _ => by simp)
              (PairwiseChain.none)⟩
          | some a_prev =>
            have h_v_eq : TValue.suspended op_name as_v a_κ_prev = .suspended op_name as_v (some a_prev) := by
              rw [ha_prev]
            rw [ha_prev] at h_inner_chain
            -- Obtain ceLabels from the new precondition
            obtain ⟨ceLabels, h_disj_ce, h_lenc_notin_ce, h_same_tk_sub, h_inner_label_mem, h_ce_sub_fl⟩ :=
              h_ceLabels_exist clo rfl op_name as_v (some a_prev) h_v_eq
            by_cases htk_eq : a_prev.frame.time.tk = t_f.tk
            · -- same_tk: innerUsed ⊆ ceLabels from h_same_tk_sub
              have h_used_sub := h_same_tk_sub innerUsed innerVars h_inner_chain a_prev rfl htk_eq
              exact ⟨_, _, .same_tk (TStore.extend_same _ _ _) rfl h_wfp h_y_notin_clo
                ceLabels h_used_sub h_disj_ce h_lenc_notin_ce h_l_enc_nb
                (fun a' heq => by cases heq; exact h_inner_label_mem a_prev rfl htk_eq)
                (fun a' heq => by cases heq; exact htk_eq.symm)
                (fun y hy => h_chain_var_disjoint clo rfl op_name as_v (some a_prev) h_v_eq
                  innerUsed innerVars h_inner_chain a_prev rfl htk_eq y hy)
                (h_inner_chain.extend_kont a_κ (.kontLink (some a_prev)) h_fresh)⟩
            · -- diff_tk: bridge label from chain strong suffix
              obtain ⟨l_bridge, h_lb_in_fl, h_lb_notin, h_lb_suf⟩ :=
                h_chain_tk_suf_strong clo rfl op_name as_v (some a_prev) h_v_eq a_prev rfl htk_eq
              exact ⟨_, _, .diff_tk (TStore.extend_same _ _ _) rfl h_wfp h_y_notin_clo h_l_enc_nb
                l_bridge h_lb_notin
                (fun a' heq => by cases heq; exact h_lb_suf)
                (Option.some_ne_none _)
                (h_inner_chain.extend_kont a_κ (.kontLink (some a_prev)) h_fresh)⟩
      -- WriteBound
      have h_wb : WriteBound σ (σ.extend (.kont a_κ) (.kontLink a_κ_prev)) t_f ∅ {l_enc} ∅ ∅ := by
        intro a ha; constructor
        · intro hat
          by_cases heq : a = .kont a_κ
          · subst heq; right; left; exact ⟨a_κ, rfl, rfl, Finset.mem_singleton_self _⟩
          · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
        · intro hne; exfalso
          by_cases heq : a = .kont a_κ
          · subst heq; simp [a_κ] at hne
          · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
      -- Package
      exact ⟨h_strict, h_wf_v', hinv',
             ⟨∅, by simp, by simp, h_wb.mono (by simp) (h_frame_enc_sub clo rfl) (by simp) (by simp)⟩,
             fun op args oa hv => by
               cases hv
               obtain ⟨innerUsed, innerVars, h_inner_chain⟩ := h_susp_chain
               have h_inner_ext := h_inner_chain.extend_kont a_κ (.kontLink a_κ_prev) h_fresh
               obtain ⟨ceLabels, h_disj_ce, h_lenc_notin_ce, h_same_tk_sub, h_inner_label_mem, h_ce_sub_fl⟩ :=
                 h_ceLabels_exist clo rfl op_name as_v a_κ_prev rfl
               cases ha_prev : a_κ_prev with
               | none =>
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
                 rw [ha_prev] at h_inner_chain h_inner_ext
                 have h_v_eq : TValue.suspended op_name as_v a_κ_prev = .suspended op_name as_v (some a_prev) := by
                   rw [ha_prev]
                 by_cases htk_eq : a_prev.frame.time.tk = t_f.tk
                 · -- same_tk
                   have h_used_sub := h_same_tk_sub innerUsed innerVars (ha_prev ▸ h_inner_chain) a_prev ha_prev htk_eq
                   exact ⟨_, _, .same_tk (TStore.extend_same _ _ _) rfl h_wfp h_y_notin_clo
                     ceLabels h_used_sub h_disj_ce h_lenc_notin_ce h_l_enc_nb
                     (fun a' heq => by cases heq; exact h_inner_label_mem a_prev ha_prev htk_eq)
                     (fun a' heq => by cases heq; exact htk_eq.symm)
                     (fun y hy => h_chain_var_disjoint clo rfl op_name as_v (some a_prev) h_v_eq
                       innerUsed innerVars h_inner_chain a_prev rfl htk_eq y hy)
                     h_inner_ext,
                     fun _ h => by cases h; intro _; exact Finset.union_subset (Finset.insert_subset_iff.mpr ⟨h_frame_enc_sub clo rfl (Finset.mem_singleton_self _), h_frame_body_labels_sub clo rfl⟩) (h_used_sub.trans h_ce_sub_fl),
                     fun _ h => by cases h; intro _; exact Finset.union_subset (h_frame_body_vars_sub clo rfl) (h_inner_vars_sub clo rfl op_name as_v (some a_prev) h_v_eq innerUsed innerVars h_inner_chain a_prev rfl htk_eq),
                     fun _ h => by cases h; exact List.suffix_refl _,
                     fun a' h h_ne => by cases h; exact absurd rfl h_ne⟩
                 · -- diff_tk
                   obtain ⟨l_bridge, h_lb_in_fl, h_lb_notin, h_lb_suf⟩ :=
                     h_chain_tk_suf_strong clo rfl op_name as_v (some a_prev) h_v_eq a_prev rfl htk_eq
                   exact ⟨_, _, .diff_tk (TStore.extend_same _ _ _) rfl h_wfp h_y_notin_clo h_l_enc_nb
                     l_bridge h_lb_notin (fun a' heq => by cases heq; exact h_lb_suf)
                     (Option.some_ne_none _) h_inner_ext,
                     fun _ h => by cases h; intro _; exact Finset.union_subset (Finset.union_subset (h_frame_enc_sub clo rfl) (Finset.singleton_subset_iff.mpr h_lb_in_fl)) (h_frame_body_labels_sub clo rfl),
                     fun _ h => by cases h; intro _; exact h_frame_body_vars_sub clo rfl,
                     fun _ h => by cases h; exact List.suffix_refl _,
                     fun a' h h_ne => by cases h; exact absurd rfl h_ne⟩⟩
  constructor
  -- P_handle (DescFresh version — used by eval_handler)
  · intro l_enc hdl ρ_handler v σ t v' σ'
          h_naive h_wf h_wf_v hinv h_var_fresh h_kont_fresh h_kont_enc_fresh
          h_cdf h_hdf h_lenc_notin_hdl_hls
    cases h_naive with
    | handle_return h_ret h_eq h_body_eval =>
      subst h_eq
      rename_i x_ret e_ret n_body d_val
      have h_x_ret := congr_arg Prod.fst h_ret
      have h_e_ret := congr_arg Prod.snd h_ret
      simp at h_x_ret h_e_ret
      have h_xret_in : x_ret ∈ hdl.topAllocVars := by
        rw [h_x_ret]; exact handler_xret_mem_topAllocVars hdl
      have h_fresh_x : σ (.val ⟨x_ret, t⟩) = none := h_var_fresh x_ret h_xret_in
      have h_wf_e_ret : WellFormedProgram e_ret := by rw [h_e_ret]; exact wellFormedSubHandler_ret h_wf
      have hinv_ext := hinv.extend_val ⟨x_ret, t⟩ _ (h_wf_v.wfv.to_wellFormedStorable)
        (fun hdl ρ oa heq => by cases heq; exact h_wf_v.2 hdl ρ oa rfl)
      have h_ret_labels_sub : e_ret.allLabels ⊆ hdl.allLabels := by
        rw [h_e_ret]; exact handler_ret_allLabels_subset hdl
      have h_ret_vars_sub : e_ret.topAllocVars ⊆ hdl.topAllocVars := by
        rw [h_e_ret]; exact handler_ret_topAllocVars_subset hdl
      have h_body_var_fresh : ∀ x ∈ e_ret.topAllocVars,
          (σ.extend (.val ⟨x_ret, t⟩) (.denotable d_val)) (.val ⟨x, t⟩) = none := by
        intro x hx
        rw [val_extend_preserves_val_ne
          (ne_of_mem_of_not_mem hx (by rw [h_e_ret, h_x_ret]; exact wellNamedSubHandler_xret_notin_ret h_wf.wn))]
        exact h_var_fresh x (h_ret_vars_sub hx)
      have h_body_kont_fresh : ∀ l ∈ e_ret.allLabels, ∀ k : TKAddr,
          k.frame.time = t → k.frame.label = l →
          (σ.extend (.val ⟨x_ret, t⟩) (.denotable d_val)) (.kont k) = none := by
        intro l hl k hk hlk; rw [val_extend_preserves_kont]
        exact h_kont_fresh l (h_ret_labels_sub hl) k hk hlk
      have h_cdf_ext : ∀ l ∈ e_ret.allLabels,
          CallDescFresh (σ.extend (.val ⟨x_ret, t⟩) (.denotable d_val)) t l := by
        intro l hl
        exact (h_cdf l (h_ret_labels_sub hl)).extend_val
      have h_ret_handlerLabels_sub : e_ret.handlerLabels ⊆ hdl.handlerLabels := by
        rw [h_e_ret]
        cases hdl with | mk ret ops =>
          obtain ⟨_, _⟩ := ret
          unfold Handler.handlerLabels
          exact Finset.subset_union_left
      have h_hdf_ext : ∀ l ∈ e_ret.handlerLabels,
          HandlerDescFresh (σ.extend (.val ⟨x_ret, t⟩) (.denotable d_val)) t l := by
        intro l hl
        exact (h_hdf l (h_ret_handlerLabels_sub hl)).extend_val
      have ⟨h_strict, h_wf_v', hinv', h_wb_ret, _h_cb_ret⟩ :=
        (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).1 e_ret _ _ t _ _
          h_body_eval h_wf_e_ret hinv_ext h_body_var_fresh h_body_kont_fresh
          h_cdf_ext h_hdf_ext
      have h_wb_ext : WriteBound σ (σ.extend (.val ⟨x_ret, t⟩) (.denotable d_val)) t {x_ret} ∅ ∅ ∅ := by
        intro a ha; constructor
        · intro hat; by_cases heq : a = .val ⟨x_ret, t⟩
          · subst heq; left; exact ⟨x_ret, rfl, Finset.mem_singleton_self _⟩
          · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
        · intro hne; exfalso; by_cases heq : a = .val ⟨x_ret, t⟩
          · subst heq; exact hne rfl
          · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
      exact ⟨.handle_return h_ret rfl h_fresh_x h_strict, h_wf_v', hinv',
             (h_wb_ext.trans h_wb_ret).mono
               (by intro x hx; simp only [Finset.mem_union, Finset.mem_singleton] at hx
                   exact hx.elim (fun h => h ▸ h_xret_in) (fun h => h_ret_vars_sub h))
               (by intro l hl; simp only [Finset.mem_union] at hl
                   exact hl.elim (fun h => absurd h (by simp)) (fun h => h_ret_labels_sub h))
               (by intro l hl; simp only [Finset.mem_union] at hl
                   exact hl.elim (fun h => absurd h (by simp)) (fun h => Finset.mem_union_right _ (h_ret_labels_sub h)))
               (by intro l hl; simp only [Finset.mem_union] at hl
                   exact hl.elim (fun h => absurd h (by simp)) (fun h => h_ret_labels_sub h)),
             fun op args oa hv => by
               obtain ⟨used, usedV, hchain, hbound, hvar_bound, htk_suf, h_bridge⟩ := _h_cb_ret op args oa hv
               exact ⟨used, usedV, hchain, fun a' hoa htk =>
                 (hbound a' hoa htk).trans (h_ret_labels_sub.trans Finset.subset_union_right),
                 fun a' hoa htk => (hvar_bound a' hoa htk).trans h_ret_vars_sub,
                 htk_suf,
                 fun a' hoa h_ne_tk =>
                   let ⟨l_br, h_l_br_mem, h_l_br_suf⟩ := h_bridge a' hoa h_ne_tk
                   ⟨l_br, Finset.mem_union_right {l_enc} (h_ret_labels_sub h_l_br_mem), h_l_br_suf⟩⟩⟩
    | handle_op h_find h_ax h_ar h_as h_lookup h_dk h_sop h_body_eval =>
      subst h_ax; subst h_ar; subst h_as; subst h_dk; subst h_sop
      rename_i op_name x e_op a_arg a_κ_prev n_body d_arg
      have h_op_mem := findOp_mem h_find
      have h_x_in : x ∈ hdl.topAllocVars := handler_op_x_mem_topAllocVars h_op_mem
      have h_resume_in : "resume" ∈ hdl.topAllocVars := handler_resume_mem_topAllocVars hdl
      have h_fresh_x : σ (.val ⟨x, t⟩) = none := h_var_fresh x h_x_in
      have h_fresh_resume : σ (.val ⟨"resume", t⟩) = none := h_var_fresh "resume" h_resume_in
      have h_ne : (.val ⟨x, t⟩ : TAddr) ≠ .val ⟨"resume", t⟩ := by
        simp; exact wellNamedSubHandler_x_ne_resume h_wf.wn _ h_op_mem
      have h_wf_body : WellFormedProgram e_op := wellFormedSubHandler_ops h_wf _ h_op_mem
      have h_wf_d_arg : WellFormedStorable (.denotable d_arg) :=
        wellFormedStorable_of_store_lookup hinv.wf_store h_lookup
      let d_kont : TDenotable := .kontClosure hdl ρ_handler a_κ_prev
      have h_wf_d_kont : WellFormedStorable (.denotable d_kont) := h_wf
      have hinv₁ := hinv.extend_val ⟨x, t⟩ _ h_wf_d_arg
        (fun _ _ _ heq => by cases heq; exact hinv.pairwiseChain_of_lookup h_lookup)
      have h_fresh_resume₁ : (σ.extend (.val ⟨x, t⟩) (.denotable d_arg)) (.val ⟨"resume", t⟩) = none := by
        rw [TStore.extend_ne _ _ _ _ (Ne.symm h_ne)]; exact h_fresh_resume
      have hinv₂ := hinv₁.extend_val ⟨"resume", t⟩ _ h_wf_d_kont
        (fun _ _ oa heq => by
          have : oa = a_κ_prev := by simp [d_kont] at heq; exact heq.2.2.symm
          subst this
          obtain ⟨u, uv, hc⟩ := h_wf_v.suspChain op_name [a_arg] oa rfl
          exact ⟨u, uv, hc.extend_val _ _⟩)
      have h_op_labels_sub : e_op.allLabels ⊆ hdl.allLabels := handler_op_allLabels_sub h_op_mem
      have h_op_vars_sub : e_op.topAllocVars ⊆ hdl.topAllocVars := by
        exact handler_op_topAllocVars_subset h_op_mem
      have h_body_var_fresh : ∀ x' ∈ e_op.topAllocVars,
          (σ.extend (.val ⟨x, t⟩) (.denotable d_arg)).extend (.val ⟨"resume", t⟩) (.denotable d_kont) (.val ⟨x', t⟩) = none := by
        intro x' hx'
        rw [val_extend_preserves_val_ne (by
          exact ne_of_mem_of_not_mem hx' (wellNamedSubHandler_resume_notin_op_body h_wf.wn _ h_op_mem))]
        rw [val_extend_preserves_val_ne (by
          exact ne_of_mem_of_not_mem hx' (wellNamedSubHandler_x_notin_op_body h_wf.wn _ h_op_mem))]
        exact h_var_fresh x' (h_op_vars_sub hx')
      have h_body_kont_fresh : ∀ l ∈ e_op.allLabels, ∀ k : TKAddr,
          k.frame.time = t → k.frame.label = l →
          (σ.extend (.val ⟨x, t⟩) (.denotable d_arg)).extend (.val ⟨"resume", t⟩) (.denotable d_kont) (.kont k) = none := by
        intro l hl k hk hlk; rw [val_extend_preserves_kont, val_extend_preserves_kont]
        exact h_kont_fresh l (h_op_labels_sub hl) k hk hlk
      have h_cdf_ext : ∀ l ∈ e_op.allLabels,
          CallDescFresh ((σ.extend (.val ⟨x, t⟩) (.denotable d_arg)).extend (.val ⟨"resume", t⟩) (.denotable d_kont)) t l := by
        intro l hl
        exact (h_cdf l (h_op_labels_sub hl)).extend_val.extend_val
      have h_op_handlerLabels_sub : e_op.handlerLabels ⊆ hdl.handlerLabels :=
        handler_op_handlerLabels_sub h_op_mem
      have h_hdf_ext : ∀ l ∈ e_op.handlerLabels,
          HandlerDescFresh ((σ.extend (.val ⟨x, t⟩) (.denotable d_arg)).extend (.val ⟨"resume", t⟩) (.denotable d_kont)) t l := by
        intro l hl
        exact (h_hdf l (h_op_handlerLabels_sub hl)).extend_val.extend_val
      have ⟨h_strict, h_wf_v', hinv', h_wb_op, _h_cb_op⟩ :=
        (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).1 e_op _ _ t _ _
          h_body_eval h_wf_body hinv₂ h_body_var_fresh h_body_kont_fresh h_cdf_ext h_hdf_ext
      have h_wb_ext₁ : WriteBound σ (σ.extend (.val ⟨x, t⟩) (.denotable d_arg)) t {x} ∅ ∅ ∅ := by
        intro a ha; constructor
        · intro hat; by_cases heq : a = .val ⟨x, t⟩
          · subst heq; left; exact ⟨x, rfl, Finset.mem_singleton_self _⟩
          · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
        · intro hne; exfalso; by_cases heq : a = .val ⟨x, t⟩
          · subst heq; exact hne rfl
          · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
      have h_wb_ext₂ : WriteBound (σ.extend (.val ⟨x, t⟩) (.denotable d_arg))
          ((σ.extend (.val ⟨x, t⟩) (.denotable d_arg)).extend
            (.val ⟨"resume", t⟩) (.denotable d_kont)) t {"resume"} ∅ ∅ ∅ := by
        intro a ha; constructor
        · intro hat; by_cases heq : a = .val ⟨"resume", t⟩
          · subst heq; left; exact ⟨"resume", rfl, Finset.mem_singleton_self _⟩
          · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
        · intro hne; exfalso; by_cases heq : a = .val ⟨"resume", t⟩
          · subst heq; exact hne rfl
          · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
      exact ⟨.handle_op h_find rfl rfl h_fresh_x h_fresh_resume
               (by simp; exact wellNamedSubHandler_x_ne_resume h_wf.wn _ h_op_mem)
               rfl h_lookup rfl rfl h_strict,
             h_wf_v', hinv',
             ((h_wb_ext₁.trans h_wb_ext₂).trans h_wb_op).mono
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
             fun op args oa hv => by
               obtain ⟨used, usedV, hchain, hbound, hvar_bound, htk_suf, h_bridge⟩ := _h_cb_op op args oa hv
               exact ⟨used, usedV, hchain, fun a' hoa htk =>
                 (hbound a' hoa htk).trans (h_op_labels_sub.trans Finset.subset_union_right),
                 fun a' hoa htk => (hvar_bound a' hoa htk).trans h_op_vars_sub,
                 htk_suf,
                 fun a' hoa h_ne_tk =>
                   let ⟨l_br, h_l_br_mem, h_l_br_suf⟩ := h_bridge a' hoa h_ne_tk
                   ⟨l_br, Finset.mem_union_right {l_enc} (h_op_labels_sub h_l_br_mem), h_l_br_suf⟩⟩⟩
    | handle_capture_op h_no_op h_ψ h_aκ h_σ' =>
      subst h_ψ; subst h_aκ; subst h_σ'
      rename_i op_name as_v a_κ_prev
      let a_κ_new : TKAddr := ⟨⟨.handlerFrame hdl ρ_handler, t, l_enc⟩, op_name⟩
      have h_fresh : σ (.kont a_κ_new) = none :=
        h_kont_enc_fresh a_κ_new rfl rfl
      have h_wb_cap : WriteBound σ (σ.extend (.kont a_κ_new) (.kontLink a_κ_prev)) t ∅ ∅ {l_enc} ∅ := by
        intro a ha; constructor
        · intro hat; by_cases heq : a = .kont a_κ_new
          · subst heq; right; right; exact ⟨a_κ_new, rfl, rfl, Finset.mem_singleton_self _⟩
          · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
        · intro hne; exfalso; by_cases heq : a = .kont a_κ_new
          · subst heq; exact hne rfl
          · rw [TStore.extend_ne _ _ _ _ heq] at ha; exact absurd rfl ha
      have h_wfv6 : WellFormedValue6
          (σ.extend (.kont a_κ_new) (.kontLink a_κ_prev))
          (.suspended op_name as_v (some a_κ_new)) := by
        refine ⟨trivial, fun _ _ _ h => ?_, fun op' as' oa h => ?_⟩
        · cases h
        · cases h
          obtain ⟨innerUsed, innerVars, h_inner_chain⟩ := h_wf_v.suspChain op_name as_v a_κ_prev rfl
          exact ⟨_, _, .handler_frame (a_κ := a_κ_new) (TStore.extend_same _ _ _) rfl h_wf
            h_lenc_notin_hdl_hls (h_inner_chain.extend_kont a_κ_new _ h_fresh)⟩
      exact ⟨.handle_capture_op h_no_op rfl rfl h_fresh rfl, h_wfv6,
             hinv.extend_kont a_κ_new _ (fun k hk_t hk_l _ => h_kont_enc_fresh k hk_t hk_l),
             h_wb_cap.mono (by simp) (by simp)
               (by intro l hl; exact Finset.mem_union_left _ hl)
               (by simp),
             fun op args oa hv => by
               cases hv
               obtain ⟨innerUsed2, innerVars2, h_ic2⟩ := h_wf_v.suspChain op_name as_v a_κ_prev rfl
               exact ⟨_, _, .handler_frame (a_κ := a_κ_new) (TStore.extend_same _ _ _) rfl h_wf
                 h_lenc_notin_hdl_hls (h_ic2.extend_kont a_κ_new _ h_fresh),
                 fun _ _ _ => Finset.Subset.refl _,
                 fun _ _ _ => Finset.Subset.refl _,
                 fun _ hoa => by cases hoa; exact List.suffix_refl _,
                 fun a' hoa h_ne_tk => by cases hoa; exact absurd rfl h_ne_tk⟩⟩
  -- P_apply
  · intro oa_κ d σ tmk v σ' chainLabels chainVars
          h_naive h_wf_d h_d_chain hinv h_tmk_fresh h_chain
    cases h_naive with
    | apply_continue =>
      have h_wfv6 : WellFormedValue6 σ (.den d) := by
        refine ⟨WellFormedValue.of_wellFormedStorable h_wf_d, fun hdl ρ oa h => ?_, fun _ _ _ h => ?_⟩
        · cases h; exact h_d_chain hdl ρ oa rfl
        · cases h
      refine ⟨.apply_continue, h_wfv6, hinv, fun _ h => absurd rfl h,
             fun _ h => ?_, fun _ h => ?_, fun _ h => ?_, fun _ h => ?_, ?_⟩
      · cases h_chain; cases h
      · cases h_chain; cases h
      · cases h_chain; cases h
      · cases h_chain; cases h
      · -- ChainBound for den d (not suspended → vacuous)
        intro op args oa hv; cases hv
    | apply_restore h_lookup h_content h_apply h_eq h_cont =>
      subst h_eq
      -- Name the inaccessible variables from apply_restore pattern
      -- Order (reverse): a_κ, clo, n2, σ₁, v', a_next, n1
      rename_i ak fr n2r σ1r vmr anr n1r
      cases h_chain with
      | same_tk h_lookup' h_content' h_wfp h_y_notin_body _ceLabels_stk h_stk_sub_ce h_disj_ce h_lnb_ce_stk h_lnb h_inner_label_in_ce h_tk_eq h_disj_vars h_inner =>
        rw [h_lookup'] at h_lookup; cases h_lookup
        rw [h_content'] at h_content; cases h_content
        rename_i stk_clo stk_anext
        -- Derive old-style disjointness from ceLabels
        -- stk_clo = sameTkLabels, stk_anext = sameTkVars, anr = clo (after cases h_content)
        have h_disj : Disjoint anr.body.allLabels stk_clo :=
          (h_disj_ce.symm).mono_right h_stk_sub_ce
        have h_lnb_stk : n1r.frame.label ∉ stk_clo := fun h => h_lnb_ce_stk (h_stk_sub_ce h)
        -- same_tk apply_restore: inner chain at SAME tk, label/var disjointness
        -- Step 1: recursive P_apply
        obtain ⟨h_sa, h_wfv1, hinv1, h_ws1, h_dfp1, h_hdfp1, h_sd1, h_stw1, h_cb_apply⟩ :=
          (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).2.2.2.2
            _ d σ tmk _ _ _ _ h_apply h_wf_d h_d_chain hinv h_tmk_fresh h_inner
        -- For same_tk: inner chain at same tk. Use label/var disjointness.
        -- h_dfp1 gives CDF preservation with DL ⊆ sameTkLabels (= chainLabels for inner)
        -- h_hdfp1 gives HDF preservation with DL ⊆ sameTkLabels
        -- h_disj: body labels disjoint from sameTkLabels → body labels ∉ DL
        -- Convert h_cb_apply to use n1r.frame.time.tk
        have h_cb_n1r : ChainBound σ1r n2r ⟨n1r.frame.time.tk, tmk⟩ stk_clo stk_clo stk_anext := by
          rcases h_fr : fr with _ | ap
          · -- fr = none: apply_continue, so n2r = .den d (never suspended → vacuous)
            rw [h_fr] at h_sa
            cases h_sa
            -- n2r = .den d, ChainBound is vacuous
            intro op args oa hv; cases hv
          · -- fr = some ap
            rw [h_fr] at h_inner h_cb_apply h_tk_eq
            -- {ap.frame.label} ∪ stk_clo ⊆ ceLabels always holds
            have h_ap_stk_sub_ce : {ap.frame.label} ∪ stk_clo ⊆ _ceLabels_stk :=
              Finset.union_subset (Finset.singleton_subset_iff.mpr (h_inner_label_in_ce ap h_fr)) h_stk_sub_ce
            have h_ap_in_stk : ap.frame.label ∈ stk_clo := h_inner.frame_label_mem
            have h_ap_stk_eq : {ap.frame.label} ∪ stk_clo = stk_clo :=
              Finset.union_eq_right.mpr (Finset.singleton_subset_iff.mpr h_ap_in_stk)
            have h_tk := h_tk_eq ap rfl
            intro op args oa hv
            obtain ⟨used, usedVars, h_pc, h_sub_l, h_sub_v, h_suf, h_br⟩ := h_cb_apply op args oa hv
            simp only at h_sub_l h_sub_v h_suf h_br
            exact ⟨used, usedVars, h_pc,
              fun a' hoa htk => h_ap_stk_eq ▸ h_sub_l a' hoa (h_tk ▸ htk),
              fun a' hoa htk => h_sub_v a' hoa (h_tk ▸ htk),
              fun a' hoa => by simp; rw [h_tk]; exact h_suf a' hoa,
              fun a' hoa hne => by
                simp only at hne
                have := h_br a' hoa (fun h => hne (h_tk ▸ h))
                obtain ⟨lb, hlb, hsuf⟩ := this
                exact ⟨lb, h_ap_stk_eq ▸ hlb, by simp; rw [h_tk]; exact hsuf⟩⟩
        -- Step 2: P_continue — now with accessible chain label/var names
        obtain ⟨h_sc, h_wfv2, hinv2, ⟨dls, hdls_sub, hdls_excl, h_wb2⟩, h_cb2⟩ :=
          (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).2.2.1
            _ (.letFrame _) _ _ _ v σ'
            (anr.params.toFinset ∪ anr.body.topAllocVars ∪ stk_anext)
            ({n1r.frame.label} ∪ anr.body.allLabels ∪ stk_clo)
            h_cont h_wfv1 hinv1
            (fun c h => by cases h; exact h_wfp) -- WF body
            (by -- y fresh: apply doesn't write at y (disjoint from chainVars)
                intro y e ρ h; cases h
                by_contra h_ne; push_neg at h_ne
                have h_σ_none := h_tmk_fresh (.val ⟨y, ⟨n1r.frame.time.tk, tmk⟩⟩) (List.suffix_refl _)
                have h_ne2 : σ1r (.val ⟨y, ⟨n1r.frame.time.tk, tmk⟩⟩) ≠ σ (.val ⟨y, ⟨n1r.frame.time.tk, tmk⟩⟩) := by
                  rw [h_σ_none]; exact h_ne
                cases h_fr2 : fr with
                | none =>
                  cases h_sa with
                  | apply_continue => exact h_ne2 rfl
                  | apply_restore _ _ _ _ _ => simp at h_fr2
                  | apply_restore_handle _ _ _ _ _ _ => simp at h_fr2
                | some ap =>
                  have h_tk := h_tk_eq ap h_fr2
                  rcases h_stw1 ap h_fr2 _ h_ne2 (by simp [TAddr.time]; exact h_tk) rfl with
                    ⟨x, hx_eq, hx_mem⟩ | ⟨k, hk_eq, _⟩
                  · cases hx_eq; exact Finset.disjoint_left.mp
                      (h_disj_vars y rfl) (Finset.mem_union_left _ (Finset.mem_singleton_self _)) hx_mem
                  · cases hk_eq)
            (by -- kont fresh: n1r.frame.label ∉ sameTkLabels (from h_lnb_stk)
                intro k hk hlk hlet
                by_contra h_ne; push_neg at h_ne
                have h_σ_none := h_tmk_fresh (.kont k) (by simp [TAddr.time]; rw [hk])
                have h_ne2 : σ1r (.kont k) ≠ σ (.kont k) := by rw [h_σ_none]; exact h_ne
                cases h_fr2 : fr with
                | none =>
                  cases h_sa with
                  | apply_continue => exact h_ne2 rfl
                  | apply_restore _ _ _ _ _ => simp at h_fr2
                  | apply_restore_handle _ _ _ _ _ _ => simp at h_fr2
                | some ap =>
                  have h_tk := h_tk_eq ap h_fr2
                  rcases h_stw1 ap h_fr2 _ h_ne2 (by simp [TAddr.time]; rw [hk]; exact h_tk) (by simp [TAddr.time]; rw [hk]) with
                    ⟨x, hx_eq, _⟩ | ⟨k', hk_eq, hk_mem⟩
                  · cases hx_eq -- val ≠ kont
                  · -- k'.frame.label ∈ {ap.frame.label} ∪ sameTkLabels, but k' = k (from hk_eq), so
                    -- k.frame.label ∈ {ap.frame.label} ∪ sameTkLabels. Need to rule out ap.frame.label case too.
                    cases hk_eq
                    simp at hk_mem
                    rcases hk_mem with hk_eq_ap | hk_mem
                    · -- k.frame.label = ap.frame.label, hlk: k.frame.label = n1r.frame.label
                      -- so n1r.frame.label = ap.frame.label, contradiction with h_lnb_ce_stk
                      have h_ap_in_ce := h_inner_label_in_ce ap h_fr2
                      exact absurd (hlk ▸ hk_eq_ap ▸ h_ap_in_ce) h_lnb_ce_stk
                    · exact h_lnb_stk (hlk ▸ hk_mem))
            (fun y e ρ h => by cases h; exact h_y_notin_body y rfl) -- y notin body
            (by -- body var fresh: same pattern
                intro y e ρ h; cases h; intro x hx
                by_contra h_ne; push_neg at h_ne
                have h_σ_none := h_tmk_fresh (.val ⟨x, ⟨n1r.frame.time.tk, tmk⟩⟩) (List.suffix_refl _)
                have h_ne2 : σ1r (.val ⟨x, ⟨n1r.frame.time.tk, tmk⟩⟩) ≠ σ (.val ⟨x, ⟨n1r.frame.time.tk, tmk⟩⟩) := by
                  rw [h_σ_none]; exact h_ne
                cases h_fr2 : fr with
                | none =>
                  cases h_sa with
                  | apply_continue => exact h_ne2 rfl
                  | apply_restore _ _ _ _ _ => simp at h_fr2
                  | apply_restore_handle _ _ _ _ _ _ => simp at h_fr2
                | some ap =>
                  have h_tk := h_tk_eq ap h_fr2
                  rcases h_stw1 ap h_fr2 _ h_ne2 (by simp [TAddr.time]; exact h_tk) rfl with
                    ⟨x', hx_eq, hx_mem⟩ | ⟨k, hk_eq, _⟩
                  · cases hx_eq; exact Finset.disjoint_left.mp
                      (h_disj_vars y rfl) (Finset.mem_union_right _ hx) hx_mem
                  · cases hk_eq)
            (by -- body kont fresh: l ∈ body.allLabels, disjoint from sameTkLabels
                intro y e ρ h; cases h; intro l hl k hk hlk
                by_contra h_ne; push_neg at h_ne
                have h_σ_none := h_tmk_fresh (.kont k) (by simp [TAddr.time]; rw [hk])
                have h_ne2 : σ1r (.kont k) ≠ σ (.kont k) := by rw [h_σ_none]; exact h_ne
                cases h_fr2 : fr with
                | none =>
                  cases h_sa with
                  | apply_continue => exact h_ne2 rfl
                  | apply_restore _ _ _ _ _ => simp at h_fr2
                  | apply_restore_handle _ _ _ _ _ _ => simp at h_fr2
                | some ap =>
                  have h_tk := h_tk_eq ap h_fr2
                  rcases h_stw1 ap h_fr2 _ h_ne2 (by simp [TAddr.time]; rw [hk]; exact h_tk) (by simp [TAddr.time]; rw [hk]) with
                    ⟨x, hx_eq, _⟩ | ⟨k', hk_eq, hk_mem⟩
                  · cases hx_eq
                  · cases hk_eq
                    simp [] at hk_mem
                    rcases hk_mem with hk_eq_ap | hk_mem
                    · -- k.frame.label = ap.frame.label but k.frame.label = l ∈ body.allLabels
                      have h_ap_in_ce := h_inner_label_in_ce ap h_fr2
                      have h_ap_notin_body := Finset.disjoint_left.mp h_disj_ce h_ap_in_ce
                      rw [← hk_eq_ap, hlk] at h_ap_notin_body
                      exact absurd hl h_ap_notin_body
                    · exact Finset.disjoint_right.mp h_disj hk_mem (by rw [hlk]; exact hl))
            (by -- body CDF: use h_dfp1 (DL ⊆ sameTkLabels) + h_disj
                intro y e ρ h; cases h; intro l hl
                cases h_fr2 : fr with
                | none =>
                  -- fr = none → apply_continue → σ1r = σ
                  cases h_sa with
                  | apply_continue => exact fun a ha => h_tmk_fresh a ha.tmk_suffix
                  | apply_restore _ _ _ _ _ => simp at h_fr2
                  | apply_restore_handle _ _ _ _ _ _ => simp at h_fr2
                | some ap =>
                  obtain ⟨DL, hDL_sub, hDL_pres⟩ := h_dfp1 ap h_fr2
                  have h_tk := h_tk_eq ap h_fr2
                  have h_not_in_DL : l ∉ DL := by
                    intro h_in; exact Finset.disjoint_left.mp h_disj hl (hDL_sub h_in)
                  have h_cdf_orig : CallDescFresh σ ⟨ap.frame.time.tk, tmk⟩ l :=
                    fun a ha => h_tmk_fresh a ha.tmk_suffix
                  rw [h_tk]; exact hDL_pres l h_not_in_DL h_cdf_orig)
            (by -- body HDF: use h_hdfp1 (DL ⊆ sameTkLabels) + h_disj
                intro y e ρ h; cases h; intro l hl
                cases h_fr2 : fr with
                | none =>
                  -- fr = none → apply_continue → σ1r = σ
                  cases h_sa with
                  | apply_continue =>
                    exact fun a tk' ha => h_tmk_fresh a ((List.suffix_cons _ _).trans ha.tmk_suffix)
                  | apply_restore _ _ _ _ _ => simp at h_fr2
                  | apply_restore_handle _ _ _ _ _ _ => simp at h_fr2
                | some ap =>
                  obtain ⟨DL, hDL_sub, hDL_pres⟩ := h_hdfp1 ap h_fr2
                  have h_tk := h_tk_eq ap h_fr2
                  have h_not_in_DL : l ∉ DL := by
                    intro h_in
                    have h_mem := hDL_sub h_in
                    simp at h_mem
                    rcases h_mem with rfl | h_mem
                    · -- l = ap.frame.label, but l ∈ body.handlerLabels ⊆ body.allLabels, ap.frame.label ∈ ceLabels, disjoint
                      exact Finset.disjoint_left.mp h_disj_ce (h_inner_label_in_ce ap h_fr2) (Exp.handlerLabels_subset_allLabels _ hl)
                    · exact Finset.disjoint_right.mp h_disj h_mem (Exp.handlerLabels_subset_allLabels _ hl)
                  have h_hdf_orig : HandlerDescFresh σ ⟨ap.frame.time.tk, tmk⟩ l :=
                    fun a tk' ha => h_tmk_fresh a ((List.suffix_cons _ _).trans ha.tmk_suffix)
                  rw [h_tk]; exact hDL_pres l h_not_in_DL h_hdf_orig)
            (fun c h => by cases h; exact h_lnb) -- l_enc notin body
            (by -- chain disjoint: use h_cb_n1r + h_disj_ce
                intro clo h_clo; cases h_clo; intro op args oa h_susp used usedVars h_pc a' h_oa h_atk
                obtain ⟨used', _, h_pc', h_sub, _, _, _⟩ := h_cb_n1r op args oa h_susp
                have ⟨h_eq, _⟩ := PairwiseChain.used_unique h_pc h_pc'
                subst h_eq
                exact h_disj.mono_right (h_sub a' h_oa h_atk))
            (by -- chain var disjoint: use h_cb_n1r + h_disj_vars
                intro clo h_clo; cases h_clo; intro op args oa h_susp used usedVars h_pc a' h_oa h_atk y h_y
                obtain ⟨_, usedVars', h_pc', _, h_sub, _, _⟩ := h_cb_n1r op args oa h_susp
                have ⟨_, h_eq⟩ := PairwiseChain.used_unique h_pc h_pc'
                subst h_eq
                exact Disjoint.mono_right (h_sub a' h_oa h_atk) (h_disj_vars y h_y))
            (by -- chain tk suffix: use h_cb_n1r
                intro op args oa h_susp a' h_oa
                obtain ⟨_, _, _, _, _, h_suf, _⟩ := h_cb_n1r op args oa h_susp
                exact h_suf a' h_oa)
            (by -- chain bridge: use h_cb_n1r + h_disj_ce
                intro clo h_clo; cases h_clo; intro op args oa h_susp a' h_oa h_ne
                obtain ⟨_, _, _, _, _, _, h_br⟩ := h_cb_n1r op args oa h_susp
                obtain ⟨l_bridge, hl_mem, hl_suf⟩ := h_br a' h_oa h_ne
                exact ⟨l_bridge, Finset.mem_union_right _ hl_mem, -- bridge in stk_clo ⊆ frameLabels
                  fun hl => Finset.disjoint_right.mp h_disj_ce hl (h_stk_sub_ce hl_mem), hl_suf⟩)
            -- CExp-side labels: use _ceLabels_stk from PairwiseChain.same_tk
            (by intro clo h_clo; cases h_clo; intro op args oa h_susp
                exact ⟨stk_clo,
                  h_disj_ce.mono_left h_stk_sub_ce,
                  h_lnb_stk,
                  fun used usedVars h_pc a' h_oa h_atk => by
                    obtain ⟨used', _, h_pc', h_sub, _, _, _⟩ := h_cb_n1r op args oa h_susp
                    have ⟨h_eq, _⟩ := PairwiseChain.used_unique h_pc h_pc'
                    subst h_eq
                    exact h_sub a' h_oa h_atk,
                  fun a' h_oa h_atk => by
                    obtain ⟨used', _, h_pc', h_sub, _, _, _⟩ := h_cb_n1r op args oa h_susp
                    subst h_oa
                    exact h_sub a' rfl h_atk (h_pc'.frame_label_mem),
                  Finset.subset_union_right⟩) -- stk_clo ⊆ frameLabels
            (fun y e ρ h => by cases h; intro x hx; simp_all [List.toFinset, Finset.mem_union]; tauto)
            (fun y e ρ h => by cases h; intro l hl; simp_all [Finset.mem_union])
            (fun c h => by cases h; intro l hl; simp_all [Finset.mem_union, Finset.mem_singleton])
            (fun c h => by cases h; exact (Finset.subset_insert _ _).trans Finset.subset_union_left)
            (fun c h => by cases h; exact Finset.subset_union_left)
            (fun c h op args oa hsusp used usedVars hpc a' hoa htk => by
              cases h
              obtain ⟨_, usedV₀, hpc₀, _, h_var_sub, _, _⟩ := h_cb_n1r op args oa hsusp
              have ⟨_, h_eq⟩ := hpc.used_unique hpc₀; subst h_eq
              exact (h_var_sub a' hoa htk).trans Finset.subset_union_right)
        exact ⟨.apply_restore h_lookup' h_content' h_sa rfl h_sc, h_wfv2, hinv2,
               -- Output 4: write scope
               fun a ha => by
                 by_cases h1 : σ1r a = σ a
                 · exact h_wb2.descendant (by rw [h1]; exact ha) |>.tmk_suffix
                 · exact h_ws1 a h1,
               -- Output 5: CDF preservation
               fun a_κ₀ h_eq => by
                 cases h_eq
                 -- Compose: DL = DL₁ ∪ dls where DL₁ from inner apply, dls from P_continue
                 rcases fr with _ | ap
                 · -- fr = none → apply_continue → σ1r = σ
                   cases h_sa
                   exact ⟨dls, (by intro l hl; have := hdls_sub hl; simp [Finset.mem_union] at this ⊢; rcases this with rfl | h; exact absurd hl hdls_excl; exact Or.inr h), fun l hl h_cdf => h_wb2.callDescFresh hl h_cdf⟩
                 · -- fr = some ap → compose h_dfp1 + WriteBound.callDescFresh
                   obtain ⟨DL₁, hDL₁_sub, hDL₁_pres⟩ := h_dfp1 ap rfl
                   have h_tk := h_tk_eq ap rfl
                   refine ⟨DL₁ ∪ dls, ?_, fun l hl h_cdf => ?_⟩
                   · exact Finset.union_subset (hDL₁_sub.trans Finset.subset_union_right) ((by intro l hl; have := hdls_sub hl; simp [Finset.mem_union] at this ⊢; rcases this with rfl | h; exact absurd hl hdls_excl; exact Or.inr h))
                   · have hl1 : l ∉ DL₁ := fun h => hl (Finset.mem_union_left _ h)
                     have hl2 : l ∉ dls := fun h => hl (Finset.mem_union_right _ h)
                     have h_cdf_1r := hDL₁_pres l hl1 (h_tk ▸ h_cdf)
                     exact h_wb2.callDescFresh hl2 (h_tk ▸ h_cdf_1r),
               -- Output 5.5: HDF preservation
               fun a_κ₀ h_eq => by
                 cases h_eq
                 rcases fr with _ | ap
                 · cases h_sa
                   exact ⟨dls, (by intro l hl; have h_mem := hdls_sub hl; simp [Finset.mem_union] at h_mem ⊢; rcases h_mem with rfl | h_mem; exact absurd hl hdls_excl; exact Or.inr h_mem), fun l hl h_hdf => h_wb2.handlerDescFresh hl h_hdf⟩
                 · obtain ⟨DL₁, hDL₁_sub, hDL₁_pres⟩ := h_hdfp1 ap rfl
                   have h_tk := h_tk_eq ap rfl
                   refine ⟨DL₁ ∪ dls, ?_, fun l hl h_hdf => ?_⟩
                   · -- DL₁ ⊆ {ap.frame.label} ∪ stk_clo ⊆ stk_clo (ap.label ∈ stk_clo from frame_label_mem)
                     have h_ap_in : ap.frame.label ∈ stk_clo :=
                       (h_inner.frame_label_mem (a_κ := ap))
                     intro l hl
                     rcases Finset.mem_union.mp hl with h_l | h_l
                     · -- l ∈ DL₁ ⊆ {ap.frame.label} ∪ stk_clo
                       have h_mem := hDL₁_sub h_l
                       rcases Finset.mem_union.mp h_mem with h | h
                       · -- l = ap.frame.label ∈ stk_clo
                         exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_singleton.mp h ▸ h_ap_in))
                       · exact Finset.mem_union_right _ (Finset.mem_union_right _ h)
                     · -- l ∈ dls
                       have h_mem := hdls_sub h_l
                       simp [Finset.mem_union] at h_mem ⊢
                       rcases h_mem with rfl | h; exact absurd h_l hdls_excl; exact Or.inr h
                   · have hl1 : l ∉ DL₁ := fun h => hl (Finset.mem_union_left _ h)
                     have hl2 : l ∉ dls := fun h => hl (Finset.mem_union_right _ h)
                     have h_hdf_1r := hDL₁_pres l hl1 (h_tk ▸ h_hdf)
                     exact h_wb2.handlerDescFresh hl2 (h_tk ▸ h_hdf_1r),
               -- Output 6: scoped descendant
               fun a_κ₀ h_eq a ha => by
                 cases h_eq
                 by_cases h1 : σ1r a = σ a
                 · exact h_wb2.descendant (by rw [h1]; exact ha)
                 · -- For same_tk: ap.tk = n1r.tk. Use h_sd1 directly.
                   cases h_fr2 : fr with
                   | none =>
                     cases h_sa with
                     | apply_continue => exact absurd rfl h1
                     | apply_restore _ _ _ _ _ => simp at h_fr2
                     | apply_restore_handle _ _ _ _ _ _ => simp at h_fr2
                   | some ap =>
                     have h_tk := h_tk_eq ap h_fr2
                     exact h_tk ▸ (h_sd1 ap h_fr2 a h1),
               -- Output 7: same-tk writes bounded
               fun a_κ₀ h_eq a ha h_atk h_atmk => by
                 cases h_eq
                 by_cases h1 : σ1r a = σ a
                 · -- Write from P_continue (h_wb2)
                   have h_ne : σ' a ≠ σ1r a := by rw [h1]; exact ha
                   have ⟨h_at, h_desc⟩ := h_wb2 a h_ne
                   by_cases h_eq_t : a.time = ⟨n1r.frame.time.tk, tmk⟩
                   · rcases h_at h_eq_t with ⟨x, hx_eq, hx_mem⟩ | ⟨k, hk_eq, _, hk_mem⟩ | ⟨k, hk_eq, _, hk_mem⟩
                     · left; exact ⟨x, by rw [hx_eq]; simp, hx_mem⟩
                     · right; exact ⟨k, hk_eq, by
                         simp [Finset.mem_union] at hk_mem ⊢
                         rcases hk_mem with h | h; exact Or.inl h; exact Or.inr h⟩
                     · right; exact ⟨k, hk_eq, by
                         simp [Finset.mem_union] at hk_mem ⊢
                         rcases hk_mem with h | h; exact Or.inl h; exact Or.inr h⟩
                   · exfalso; apply h_eq_t
                     have h_eta : a.time = ⟨a.time.tk, a.time.tmk⟩ := by cases a.time; rfl
                     rw [h_eta, h_atk, h_atmk]
                 · -- Write from inner apply (h_stw1)
                   cases h_fr3 : fr with
                   | none => cases h_sa with
                     | apply_continue => exact absurd rfl h1
                     | apply_restore _ _ _ _ _ => simp at h_fr3
                     | apply_restore_handle _ _ _ _ _ _ => simp at h_fr3
                   | some ap =>
                     have h_tk := h_tk_eq ap h_fr3
                     rcases h_stw1 ap h_fr3 a h1 (h_tk ▸ h_atk) h_atmk with ⟨x, hx_eq, hx_mem⟩ | ⟨k, hk_eq, hk_mem⟩
                     · left; exact ⟨x, hx_eq, Finset.mem_of_subset Finset.subset_union_right hx_mem⟩
                     · -- k.frame.label ∈ {ap.frame.label} ∪ stk_clo ⊆ stk_clo (ap.label ∈ stk_clo)
                       have h_ap_in : ap.frame.label ∈ stk_clo := by
                         rw [h_fr3] at h_inner; exact h_inner.frame_label_mem
                       right; exact ⟨k, hk_eq, by
                         rcases Finset.mem_union.mp hk_mem with h | h
                         · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_singleton.mp h ▸ h_ap_in))
                         · exact Finset.mem_union_right _ (Finset.mem_union_right _ h)⟩,
               -- Output 8: ChainBound for result
               by
                 simp only
                 rw [show {n1r.frame.label} ∪ ({n1r.frame.label} ∪ anr.body.allLabels ∪ stk_clo) = {n1r.frame.label} ∪ anr.body.allLabels ∪ stk_clo from by simp]
                 rw [show {n1r.frame.label} ∪ ({n1r.frame.label} ∪ anr.body.allLabels ∪ stk_clo) = {n1r.frame.label} ∪ anr.body.allLabels ∪ stk_clo from by simp] at h_cb2
                 rw [show anr.params.toFinset ∪ anr.body.topAllocVars ∪ stk_anext = anr.params.toFinset ∪ (anr.body.topAllocVars ∪ stk_anext) from (Finset.union_assoc _ _ _)] at h_cb2
                 rw [show anr.params.toFinset ∪ anr.body.topAllocVars ∪ stk_anext = anr.params.toFinset ∪ (anr.body.topAllocVars ∪ stk_anext) from (Finset.union_assoc _ _ _)]
                 exact h_cb2⟩
      | diff_tk h_lookup' h_content' h_wfp h_y_notin_body h_lnb l_bridge h_l_bridge_notin h_tk_suf _h_ne h_inner =>
        rw [h_lookup'] at h_lookup; cases h_lookup
        rw [h_content'] at h_content; cases h_content
        -- n1r = a_κ (kont addr), anr = clo (closure), σ1r = σ₁ (mid store)
        -- Step 1: recursive P_apply
        obtain ⟨h_sa, h_wfv1, hinv1, h_ws1, h_dfp1, h_hdfp1, h_sd1, h_stw1, h_cb_apply⟩ :=
          (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).2.2.2.2
            _ d σ tmk _ _ _ _ h_apply h_wf_d h_d_chain hinv h_tmk_fresh h_inner
        -- Key: apply preserves addresses at n1r.frame.time (shorter tk than inner chain)
        have h_pres : ∀ a, a.time.tk = n1r.frame.time.tk → a.time.tmk = tmk → σ1r a = σ a := by
          intro a h_atk h_atmk; by_contra h_ne
          cases h_inner with
          | none => cases h_sa; exact h_ne rfl
          | _ =>
            have h_desc := h_sd1 _ rfl a h_ne
            -- h_desc: Descendant ⟨a_κ✝.frame.time.tk, tmk⟩ a.time
            -- a.time.tmk = tmk (h_atmk), so same tmk → tk suffix
            have h_tk_suf_a := h_desc.tk_suffix_of_same_tmk h_atmk.symm
            -- a_κ✝.frame.time.tk <:+ a.time.tk = n1r.frame.time.tk (h_atk)
            rw [h_atk] at h_tk_suf_a
            -- h_tk_suf gives l_bridge :: n1r.frame.time.tk <:+ a_κ✝.frame.time.tk
            have h_longer := h_tk_suf _ rfl
            -- a_κ✝.frame.time.tk <:+ n1r.frame.time.tk AND l_bridge :: n1r.frame.time.tk <:+ a_κ✝.frame.time.tk
            -- Length: |a_κ✝.tk| ≤ |n1r.tk| AND |n1r.tk| + 1 ≤ |a_κ✝.tk|
            exact absurd h_tk_suf_a.length_le (by have := h_longer.length_le; simp at this ⊢; omega)
        -- Step 2: P_continue — use h_pres for all σ₁-freshness args
        -- h_pres shows: at t_restored = ⟨n1r.frame.time.tk, tmk⟩, σ₁ = σ
        obtain ⟨h_sc, h_wfv2, hinv2, ⟨dls, hdls_sub, hdls_excl, h_wb2⟩, h_cb2⟩ :=
          (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).2.2.1
            _ (.letFrame _) _ _ _ v σ'
            (anr.params.toFinset ∪ anr.body.topAllocVars) ({n1r.frame.label} ∪ {l_bridge} ∪ anr.body.allLabels)
            h_cont h_wfv1 hinv1
            (fun c h => by cases h; exact h_wfp) -- WF body
            (fun y e ρ h => by cases h; rw [h_pres _ rfl rfl]; exact h_tmk_fresh _ (List.suffix_refl _))
            (fun k hk hlk hlet => by
              rw [h_pres _ (by simp [TAddr.time]; rw [hk]) (by simp [TAddr.time]; rw [hk])]
              exact h_tmk_fresh _ (by simp [TAddr.time]; rw [hk]))
            (fun y e ρ h => by cases h; exact h_y_notin_body y rfl)
            (fun y e ρ h => by cases h; intro x hx; rw [h_pres _ rfl rfl]; exact h_tmk_fresh _ (List.suffix_refl _))
            (by intro y e ρ h; cases h; intro l hl k hk hlk
                rw [h_pres _ (by simp [TAddr.time]; rw [hk]) (by simp [TAddr.time]; rw [hk])]
                exact h_tmk_fresh _ (by simp [TAddr.time]; rw [hk]))
            (by -- body CDF: Descendant from ⟨l :: n1r.tk, tmk⟩. Apply writes at
                -- descendants of ⟨ap.tk, tmk⟩ where l_bridge :: n1r.tk <:+ ap.tk.
                -- no_shorter_tmk_entry gives contradiction: l :: n1r.tk and ap.tk
                -- as same-length suffixes forces l = l_bridge ∉ body.allLabels.
                intro y e ρ h; cases h; intro l hl a ha
                by_cases h_eq : σ1r a = σ a
                · rw [h_eq]; exact h_tmk_fresh a ha.tmk_suffix
                · exfalso; cases h_fr2 : fr with
                  | none =>
                    cases h_sa with
                    | apply_continue => exact h_eq rfl
                    | apply_restore _ _ _ _ _ => simp at h_fr2
                    | apply_restore_handle _ _ _ _ _ _ => simp at h_fr2
                  | some ap =>
                    have h_sd := h_sd1 ap h_fr2 a h_eq
                    have h_longer := h_tk_suf ap h_fr2
                    -- ha: Descendant ⟨l :: n1r.tk, tmk⟩ a.time
                    -- h_sd: Descendant ⟨ap.tk, tmk⟩ a.time
                    -- h_longer: l_bridge :: n1r.tk <:+ ap.tk
                    -- Both descendants at same starting tmk.
                    -- Case on a.time.tmk = tmk:
                    by_cases h_same_tmk : a.time.tmk = tmk
                    · -- Same tmk: tk suffixes. l :: n1r.tk <:+ a.tk, ap.tk <:+ a.tk.
                      -- Same length → l :: n1r.tk = l_bridge :: n1r.tk → l = l_bridge
                      have h_tk1 := ha.tk_suffix_of_same_tmk h_same_tmk.symm
                      have h_tk2 := h_sd.tk_suffix_of_same_tmk h_same_tmk.symm
                      -- h_tk1: l :: n1r.tk <:+ a.tk. h_tk2: ap.tk <:+ a.tk.
                      -- l_bridge :: n1r.tk <:+ ap.tk <:+ a.tk.
                      -- l :: n1r.tk and l_bridge :: n1r.tk same length, both <:+ a.tk
                      have h_eq_suf := suffix_eq_of_length_eq (l :: n1r.frame.time.tk)
                        (l_bridge :: n1r.frame.time.tk) a.time.tk
                        h_tk1 (h_longer.trans h_tk2) (by simp)
                      exact h_l_bridge_notin ((List.cons.inj h_eq_suf).1 ▸ hl)
                    · -- Deeper tmk: same call_first_tmk_entry argument as HDF
                      have h_sd_call : Descendant ⟨l_bridge :: n1r.frame.time.tk, tmk⟩ a.time :=
                        (Descendant.of_tk_suffix h_longer).trans h_sd
                      -- ha starts from ⟨l :: n1r.tk, tmk⟩. At deeper tmk, need an entry.
                      -- But ha is CDF (starts from l :: n1r.tk), not HDF. For deeper tmk:
                      -- no_shorter_tmk_entry on ha with the entry from h_sd_call.
                      -- h_sd_call: Descendant ⟨l_bridge :: n1r.tk, tmk⟩ a.time
                      -- Since a.time.tmk ≠ tmk: the descent went through handler entry.
                      -- call_first_tmk_entry on h_sd_call with... need a (_, _) :: tmk suffix.
                      -- From h_ws1: tmk <:+ a.time.tmk. Since ≠ tmk: a.time.tmk is deeper.
                      -- So ∃ entry (l', tk') :: tmk <:+ a.time.tmk.
                      -- call_first_tmk_entry on h_sd_call: l_bridge :: n1r.tk <:+ tk'
                      -- no_shorter_tmk_entry on ha needs (_, n1r.tk) :: tmk <:+ a.time.tmk.
                      -- From the entry: (l', tk') :: tmk. tk' has l_bridge :: n1r.tk as suffix.
                      -- |tk'| ≥ |n1r.tk| + 1 > |n1r.tk|. So tk' ≠ n1r.tk. So (l', tk') ≠ (_, n1r.tk).
                      -- no_shorter_tmk_entry needs EXACTLY (_, n1r.tk). But the entry has longer tk'.
                      -- Actually no_shorter_tmk_entry takes ANY entry with second comp = n1r.tk.
                      -- The actual entry has tk' with |tk'| > |n1r.tk|. So it's NOT the entry
                      -- no_shorter_tmk_entry expects. The entry is fine for the descendant.
                      -- The contradiction: ha at deeper tmk means ha.call_first_tmk_entry gives
                      -- l :: n1r.tk <:+ tk' (the entry's second component from ha's perspective).
                      -- h_sd_call.call_first_tmk_entry gives l_bridge :: n1r.tk <:+ tk'.
                      -- Both same length, both suffixes → l = l_bridge. Contradiction.
                      have h_ws := h_ws1 a h_eq -- tmk <:+ a.time.tmk
                      -- Need a tmk entry. Since h_same_tmk is False: a.time.tmk ≠ tmk.
                      -- Get an entry from the tmk suffix.
                      -- Use no_shorter_tmk_entry: ha from ⟨l :: n1r.tk, tmk⟩,
                      -- and the scoped desc creates a tmk entry that no_shorter_tmk_entry catches.
                      -- Simpler: use the same approach as HDF (call_first_tmk_entry on h_sd_call)
                      -- But need an entry (l_e, tk_e) :: tmk <:+ a.time.tmk.
                      -- ha.tmk_suffix gives tmk <:+ a.time.tmk (same as h_ws).
                      -- ha from ⟨l :: n1r.tk, tmk⟩ at deeper tmk: no_shorter_tmk_entry says
                      -- can't have (_, n1r.tk) :: tmk as suffix. But the scoped desc entry
                      -- has (_, entry_tk) :: tmk where |entry_tk| > |n1r.tk|. So it's compatible.
                      -- The approach: ha.tmk_suffix and h_sd.tmk_suffix both give tmk <:+ a.time.tmk.
                      -- For the deeper case, a.time.tmk has entries above tmk. Both ha and h_sd_call
                      -- contribute to these entries. Use call_handler_disjoint:
                      -- Actually, simplest: note that ha gives no_shorter_tmk_entry,
                      -- and h_sd_call.tmk_suffix gives tmk <:+ a.time.tmk. Since a.time.tmk ≠ tmk,
                      -- h_sd_call must have gone through handler entries.
                      -- At the FIRST handler entry from h_sd_call:
                      -- entry has l_bridge :: n1r.tk <:+ entry_tk. And from ha, same entry
                      -- has l :: n1r.tk <:+ entry_tk. Same length → l = l_bridge. Contradiction.
                      -- But we need the entry to use call_first_tmk_entry.
                      -- We need (entry_l, entry_tk) :: tmk <:+ a.time.tmk.
                      -- This is exactly what happens when h_sd_call (from ⟨l_bridge :: n1r.tk, tmk⟩)
                      -- enters a handler: appKont creates (_, l_bridge :: ...) :: tmk entry.
                      -- Use Descendant.tmk_entry_exists or similar...
                      -- Extract first tmk entry above tmk
                      have ⟨l_e, tk_e, h_entry⟩ := tmk_strict_suffix_entry
                        (h_ws1 a h_eq) h_same_tmk
                      have h_cdf_tk := ha.call_first_tmk_entry h_entry
                      have h_sd_tk := h_sd_call.call_first_tmk_entry h_entry
                      have h_eq_suf := suffix_eq_of_length_eq
                        (l :: n1r.frame.time.tk) (l_bridge :: n1r.frame.time.tk)
                        tk_e h_cdf_tk h_sd_tk (by simp)
                      exact h_l_bridge_notin ((List.cons.inj h_eq_suf).1 ▸ hl))
            (by -- body HDF: Descendant from ⟨tk', (l, n1r.tk) :: tmk⟩. Same argument.
                intro y e ρ h; cases h; intro l hl a tk' ha
                by_cases h_eq : σ1r a = σ a
                · rw [h_eq]; exact h_tmk_fresh a ((List.suffix_cons _ _).trans ha.tmk_suffix)
                · exfalso; cases h_fr2 : fr with
                  | none =>
                    cases h_sa with
                    | apply_continue => exact h_eq rfl
                    | apply_restore _ _ _ _ _ => simp at h_fr2
                    | apply_restore_handle _ _ _ _ _ _ => simp at h_fr2
                  | some ap =>
                    have h_sd := h_sd1 ap h_fr2 a h_eq
                    have h_longer := h_tk_suf ap h_fr2
                    -- ha.tmk_suffix: (l, n1r.tk) :: tmk <:+ a.time.tmk
                    -- h_sd: Descendant ⟨ap.tk, tmk⟩ a.time
                    -- a.time.tmk deeper than tmk → h_sd went through handler entry
                    -- call_first_tmk_entry on h_sd gives entry_tk with ap.tk <:+ entry_tk
                    -- suffix_eq on entries → entry_tk = n1r.tk → ap.tk <:+ n1r.tk
                    -- but l_bridge :: n1r.tk <:+ ap.tk → length contradiction
                    -- Build call descendant: Descendant ⟨l_bridge :: n1r.tk, tmk⟩ a.time
                    have h_sd_call : Descendant ⟨l_bridge :: n1r.frame.time.tk, tmk⟩ a.time :=
                      (Descendant.of_tk_suffix h_longer).trans h_sd
                    -- call_first_tmk_entry on h_sd_call with ha.tmk_suffix
                    have h_entry := h_sd_call.call_first_tmk_entry ha.tmk_suffix
                    -- h_entry: l_bridge :: n1r.tk <:+ n1r.tk (from the matching tmk entry)
                    -- Length contradiction: |n1r.tk| + 1 ≤ |n1r.tk|
                    exact absurd h_entry.length_le (by simp))
            (fun c h => by cases h; exact h_lnb)
            (by -- chain disjoint: a'.tk = n1r.tk contradicts l_bridge :: n1r.tk <:+ ap.tk <:+ a'.tk
                intro clo h_clo; cases h_clo; intro op args oa h_susp used usedVars h_pc a' h_oa h_atk
                rcases fr with _ | ap
                · cases h_sa; cases h_susp
                · obtain ⟨_, _, _, _, _, h_suf, _⟩ := h_cb_apply op args oa h_susp
                  have h_ap_suf := h_suf a' h_oa -- ap.tk <:+ a'.tk
                  have h_longer := h_tk_suf ap rfl -- l_bridge :: n1r.tk <:+ ap.tk
                  simp at h_atk; rw [h_atk] at h_ap_suf
                  exact absurd h_ap_suf.length_le (by have := h_longer.length_le; simp at this ⊢; omega))
            (by -- chain var disjoint: same length contradiction
                intro clo h_clo; cases h_clo; intro op args oa h_susp used usedVars h_pc a' h_oa h_atk y h_y
                rcases fr with _ | ap
                · cases h_sa; cases h_susp
                · obtain ⟨_, _, _, _, _, h_suf, _⟩ := h_cb_apply op args oa h_susp
                  have h_ap_suf := h_suf a' h_oa
                  have h_longer := h_tk_suf ap rfl
                  simp at h_atk; rw [h_atk] at h_ap_suf
                  exact absurd h_ap_suf.length_le (by have := h_longer.length_le; simp at this ⊢; omega))
            (by -- chain tk suffix: n1r.tk <:+ l_bridge :: n1r.tk <:+ ap.tk <:+ a'.tk
                intro op args oa h_susp a' h_oa
                rcases fr with _ | ap
                · cases h_sa; cases h_susp
                · obtain ⟨_, _, _, _, _, h_suf, _⟩ := h_cb_apply op args oa h_susp
                  exact (List.suffix_cons l_bridge _).trans ((h_tk_suf ap rfl).trans (h_suf a' h_oa)))
            (by -- chain bridge: use l_bridge
                intro clo h_clo; cases h_clo; intro op args oa h_susp a' h_oa h_ne
                rcases fr with _ | ap
                · cases h_sa; cases h_susp
                · obtain ⟨_, _, _, _, _, h_suf, _⟩ := h_cb_apply op args oa h_susp
                  exact ⟨l_bridge, Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _)), h_l_bridge_notin, (h_tk_suf ap rfl).trans (h_suf a' h_oa)⟩)
            -- CExp-side labels: construct from l_bridge (diff_tk → same-tk vacuous)
            (by intro clo h_clo; cases h_clo; intro op args oa h_susp
                -- Use ∅: same-tk is vacuous for diff_tk (length contradiction)
                exact ⟨∅, Finset.disjoint_empty_left _, (by simp),
                  fun used usedVars h_pc a' h_oa h_atk => by
                    -- diff_tk: a'.tk = n1r.tk contradicts l_bridge :: n1r.tk <:+ ap.tk <:+ a'.tk
                    rcases fr with _ | ap
                    · cases h_sa; cases h_susp
                    · obtain ⟨_, _, _, _, _, h_suf, _⟩ := h_cb_apply op args oa h_susp
                      have h_ap_suf := h_suf a' h_oa
                      have h_longer := h_tk_suf ap rfl
                      simp at h_atk; rw [h_atk] at h_ap_suf
                      exact absurd h_ap_suf.length_le (by have := h_longer.length_le; simp at this ⊢; omega),
                  fun a' h_oa h_atk => by
                    -- diff_tk: same contradiction as above
                    rcases fr with _ | ap
                    · cases h_sa; cases h_susp
                    · obtain ⟨_, _, _, _, _, h_suf, _⟩ := h_cb_apply op args oa h_susp
                      have h_ap_suf := h_suf a' h_oa
                      have h_longer := h_tk_suf ap rfl
                      simp at h_atk; rw [h_atk] at h_ap_suf
                      exact absurd h_ap_suf.length_le (by have := h_longer.length_le; simp at this ⊢; omega),
                  Finset.empty_subset _⟩)
            (fun y e ρ h => by cases h; exact Finset.Subset.refl _)
            (fun y e ρ h => by cases h; exact Finset.subset_union_right)
            (fun c h => by cases h; exact Finset.singleton_subset_iff.mpr (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))))
            (fun c h => by cases h; exact Finset.subset_union_right)
            (fun c h => by cases h; exact Finset.Subset.refl _)
            (fun c h op args oa hsusp used usedVars hpc a' hoa htk => by
              cases h
              rcases fr with _ | ap
              · cases h_sa; cases hsusp
              · obtain ⟨_, _, _, _, _, h_suf, _⟩ := h_cb_apply op args oa hsusp
                have h_ap_suf := h_suf a' hoa
                have h_longer := h_tk_suf ap rfl
                simp at htk; rw [htk] at h_ap_suf
                exact absurd h_ap_suf.length_le (by have := h_longer.length_le; simp at this ⊢; omega))
        exact ⟨.apply_restore h_lookup' h_content' h_sa rfl h_sc, h_wfv2, hinv2,
               -- Output 4: write scope
               fun a ha => by
                 by_cases h1 : σ1r a = σ a
                 · exact h_wb2.descendant (by rw [h1]; exact ha) |>.tmk_suffix
                 · exact h_ws1 a h1,
               -- Output 5: CDF preservation
               fun a_κ₀ h_eq => by
                 cases h_eq
                 -- DL = {l_bridge} ∪ dls (apply dirties at l_bridge, continue at dls)
                 refine ⟨{l_bridge} ∪ dls, Finset.union_subset (Finset.singleton_subset_iff.mpr (by simp [Finset.mem_insert]))
                   hdls_sub,
                   fun l hl h_cdf => ?_⟩
                 have h_l_ne : l ≠ l_bridge := fun h => hl (Finset.mem_union_left _ (h ▸ Finset.mem_singleton_self _))
                 have h_l_not_dls : l ∉ dls := fun h => hl (Finset.mem_union_right _ h)
                 have h_cdf_1r : CallDescFresh σ1r ⟨n1r.frame.time.tk, tmk⟩ l := by
                   intro a ha
                   by_cases h_eq : σ1r a = σ a
                   · rw [h_eq]; exact h_cdf a ha
                   · exfalso; cases h_fr2 : fr with
                     | none =>
                       cases h_sa with
                       | apply_continue => exact h_eq rfl
                       | apply_restore _ _ _ _ _ => simp at h_fr2
                       | apply_restore_handle _ _ _ _ _ _ => simp at h_fr2
                     | some ap =>
                       have h_sd := h_sd1 ap h_fr2 a h_eq
                       have h_longer := h_tk_suf ap h_fr2
                       by_cases h_same_tmk : a.time.tmk = tmk
                       · have h_tk1 := ha.tk_suffix_of_same_tmk h_same_tmk.symm
                         have h_tk2 := h_sd.tk_suffix_of_same_tmk h_same_tmk.symm
                         have h_eq_suf := suffix_eq_of_length_eq
                           (l :: n1r.frame.time.tk) (l_bridge :: n1r.frame.time.tk)
                           a.time.tk h_tk1 (h_longer.trans h_tk2) (by simp)
                         exact h_l_ne (List.cons.inj h_eq_suf).1
                       · have h_sd_call : Descendant ⟨l_bridge :: n1r.frame.time.tk, tmk⟩ a.time :=
                           (Descendant.of_tk_suffix h_longer).trans h_sd
                         have ⟨l_e, tk_e, h_entry⟩ := tmk_strict_suffix_entry
                           (h_ws1 a h_eq) h_same_tmk
                         have h_cdf_tk := ha.call_first_tmk_entry h_entry
                         have h_sd_tk := h_sd_call.call_first_tmk_entry h_entry
                         have h_eq_suf := suffix_eq_of_length_eq
                           (l :: n1r.frame.time.tk) (l_bridge :: n1r.frame.time.tk)
                           tk_e h_cdf_tk h_sd_tk (by simp)
                         exact h_l_ne (List.cons.inj h_eq_suf).1
                 exact h_wb2.callDescFresh h_l_not_dls h_cdf_1r,
               -- Output 5.5: HDF preservation
               fun a_κ₀ h_eq => by
                 cases h_eq
                 exact ⟨dls, hdls_sub.trans (Finset.subset_insert _ _), fun l hl h_hdf => by
                   -- Step 1: HDF σ → HDF σ1r (inner apply doesn't write at HDF descendants)
                   have h_hdf_1r : HandlerDescFresh σ1r ⟨n1r.frame.time.tk, tmk⟩ l := by
                     intro a tk' ha
                     by_cases h_eq : σ1r a = σ a
                     · rw [h_eq]; exact h_hdf a tk' ha
                     · exfalso; cases h_fr2 : fr with
                       | none =>
                         cases h_sa with
                         | apply_continue => exact h_eq rfl
                         | apply_restore _ _ _ _ _ => simp at h_fr2
                         | apply_restore_handle _ _ _ _ _ _ => simp at h_fr2
                       | some ap =>
                         have h_sd := h_sd1 ap h_fr2 a h_eq
                         have h_longer := h_tk_suf ap h_fr2
                         -- ha.tmk_suffix: (l, n1r.tk) :: tmk <:+ a.time.tmk
                         -- h_sd: Descendant ⟨ap.tk, tmk⟩ a.time where l_bridge :: n1r.tk <:+ ap.tk
                         -- Build call descendant
                         have h_sd_call : Descendant ⟨l_bridge :: n1r.frame.time.tk, tmk⟩ a.time :=
                           (Descendant.of_tk_suffix h_longer).trans h_sd
                         -- call_first_tmk_entry gives l_bridge :: n1r.tk <:+ n1r.tk (length contradiction)
                         have h_entry := h_sd_call.call_first_tmk_entry ha.tmk_suffix
                         exact absurd h_entry.length_le (by simp)
                   -- Step 2: HDF σ1r → HDF σ' (via WriteBound.handlerDescFresh)
                   exact h_wb2.handlerDescFresh hl h_hdf_1r⟩,
               -- Output 6: scoped descendant
               fun a_κ₀ h_eq a ha => by
                 cases h_eq
                 by_cases h1 : σ1r a = σ a
                 · exact h_wb2.descendant (by rw [h1]; exact ha)
                 · -- Apply changed a: use h_sd1 + tk suffix to show descendant
                   cases h_fr : fr with
                   | none =>
                     -- fr = none → apply_continue → σ1r = σ → contradiction with h1
                     cases h_sa with
                     | apply_continue => exact absurd rfl h1
                     | apply_restore _ _ _ _ _ => simp at h_fr
                     | apply_restore_handle _ _ _ _ _ _ => simp at h_fr
                   | some a_prev =>
                     have h_desc := h_sd1 a_prev h_fr a h1
                     have h_longer := h_tk_suf a_prev h_fr
                     -- n1r.tk <:+ l_bridge :: n1r.tk <:+ a_prev.tk
                     have h_tk_sub : n1r.frame.time.tk <:+ a_prev.frame.time.tk :=
                       (List.suffix_cons l_bridge _).trans h_longer
                     exact (Descendant.of_tk_suffix h_tk_sub).trans h_desc,
               -- Output 7: same-tk writes bounded
               fun a_κ₀ h_eq a ha h_atk h_atmk => by
                 cases h_eq
                 -- All writes at n1r.frame.time.tk/tmk come from P_continue (h_pres: apply preserves at this tk)
                 have h_ne_1r : σ' a ≠ σ1r a := by
                   rw [h_pres a h_atk h_atmk]; exact ha
                 have ⟨h_at, h_desc⟩ := h_wb2 a h_ne_1r
                 by_cases h_eq_t : a.time = ⟨n1r.frame.time.tk, tmk⟩
                 · rcases h_at h_eq_t with ⟨x, hx_eq, hx_mem⟩ | ⟨k, hk_eq, _, hk_mem⟩ | ⟨k, hk_eq, _, hk_mem⟩
                   · left; exact ⟨x, by rw [hx_eq]; simp, hx_mem⟩
                   · right; exact ⟨k, hk_eq, Finset.mem_union_right _ hk_mem⟩
                   · right; exact ⟨k, hk_eq, Finset.mem_union_right _ hk_mem⟩
                 · exfalso; apply h_eq_t
                   have h_eta : a.time = ⟨a.time.tk, a.time.tmk⟩ := by cases a.time; rfl
                   rw [h_eta, h_atk, h_atmk],
               -- Output 8: ChainBound for result
               by
                 intro op args oa h_susp
                 obtain ⟨used, usedVars, h_pc, h_sub_l, h_sub_v, h_suf, h_br⟩ := h_cb2 op args oa h_susp
                 exact ⟨used, usedVars, h_pc,
                   fun a' hoa htk => (h_sub_l a' hoa htk).trans (Finset.subset_insert _ _),
                   fun a' hoa htk => h_sub_v a' hoa htk,
                   h_suf,
                   fun a' hoa hne => by
                     obtain ⟨lb, hlb, hsuf⟩ := h_br a' hoa hne
                     have : insert n1r.frame.label ({n1r.frame.label} ∪ {l_bridge} ∪ anr.body.allLabels) = {n1r.frame.label} ∪ {l_bridge} ∪ anr.body.allLabels :=
                       Finset.insert_eq_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _)))
                     exact ⟨lb, this ▸ hlb, hsuf⟩⟩⟩
      | handler_frame h_lookup' h_content' h_wf_hdl _ h_inner =>
        rw [h_lookup'] at h_lookup; cases h_lookup
        rw [h_content'] at h_content; cases h_content -- letFrame ≠ handlerFrame
    | apply_restore_handle h_lookup h_content h_eq h_apply h_eq2 h_handle =>
      subst h_eq; subst h_eq2
      -- apply_restore_handle: handler frame, recursive apply at deeper tmk', then handle at tmk
      rename_i n1 a_next v' σ₁ n2 hdl ρ_hdl a_κ
      -- Extract handler frame info from PairwiseChain
      cases h_chain with
      | handler_frame h_lookup' h_content' h_wf_hdl h_lnb_hdl_hf h_inner =>
        rw [h_lookup'] at h_lookup; cases h_lookup
        rw [h_content'] at h_content; cases h_content
        let l_frame := a_κ.frame.label
        let t_frame := a_κ.frame.time
        let tmk' := (l_frame, t_frame.tk) :: tmk
        let t_restored : Time := ⟨t_frame.tk, tmk⟩
        -- tmk' freshness (from tmk freshness + one extra entry)
        have h_tmk'_fresh : ∀ a, tmk' <:+ a.time.tmk → σ a = none :=
          fun a h => h_tmk_fresh a ((List.suffix_cons _ _).trans h)
        -- Recursive P_apply at deeper tmk'
        have ⟨h_strict_apply, h_wf_v', hinv₁, h_desc_apply, h_dfp_apply, _, h_scope_apply, _, _⟩ :=
          (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).2.2.2.2
            a_next d σ tmk' v' σ₁ _ _
            h_apply h_wf_d h_d_chain hinv h_tmk'_fresh h_inner
        -- Apply step preserves tmk-level addresses
        have h_pres_tmk : ∀ a, a.time.tmk = tmk → σ₁ a = σ a := by
          intro a ha
          by_contra h_ne
          have := h_desc_apply a h_ne
          rw [ha] at this
          exact absurd this.length_le (by simp [tmk'])
        -- P_handle preconditions (all tmk-level, preserved by apply)
        have h_var_fresh_σ₁ : ∀ x ∈ hdl.topAllocVars, σ₁ (.val ⟨x, t_restored⟩) = none := by
          intro x _; rw [h_pres_tmk _ rfl]; exact h_tmk_fresh _ (List.suffix_refl _)
        have h_kont_fresh_σ₁ : ∀ l ∈ hdl.allLabels, ∀ k : TKAddr,
            k.frame.time = t_restored → k.frame.label = l → σ₁ (.kont k) = none := by
          intro l _ k hk _
          have h_tmk_eq : (.kont k : TAddr).time.tmk = tmk := by simp [TAddr.time]; rw [hk]
          rw [h_pres_tmk _ h_tmk_eq]
          exact h_tmk_fresh _ (h_tmk_eq ▸ List.suffix_refl _)
        have h_kont_enc_fresh_σ₁ : ∀ k : TKAddr,
            k.frame.time = t_restored → k.frame.label = l_frame → σ₁ (.kont k) = none := by
          intro k hk _
          have h_tmk_eq : (.kont k : TAddr).time.tmk = tmk := by simp [TAddr.time]; rw [hk]
          rw [h_pres_tmk _ h_tmk_eq]
          exact h_tmk_fresh _ (h_tmk_eq ▸ List.suffix_refl _)
        have h_cdf_σ₁ : ∀ l ∈ hdl.allLabels, CallDescFresh σ₁ t_restored l := by
          intro l _ a ha
          -- ha : Descendant ⟨l :: t_frame.tk, tmk⟩ a.time, so tmk <:+ a.time.tmk
          by_cases h_eq : σ₁ a = σ a
          · rw [h_eq]; exact h_tmk_fresh a ha.tmk_suffix
          · -- Apply changed a: tmk' <:+ a.time.tmk. But no_shorter_tmk_entry contradicts.
            exact absurd (h_desc_apply a h_eq) (fun h => ha.no_shorter_tmk_entry h)
        have h_hdf_σ₁ : ∀ l ∈ hdl.handlerLabels, HandlerDescFresh σ₁ t_restored l := by
          intro l hl a tk ha
          have h_l_in_all : l ∈ hdl.allLabels := Handler.handlerLabels_subset_allLabels hdl hl
          have h_l_ne : l ≠ l_frame := fun h_eq => h_lnb_hdl_hf (show l_frame ∈ _ from h_eq ▸ hl)
          by_cases h_eq : σ₁ a = σ a
          · rw [h_eq]; exact h_tmk_fresh a ((List.suffix_cons _ _).trans ha.tmk_suffix)
          · -- Apply changed a: tmk' <:+ a.time.tmk. Also (l, t_frame.tk) :: tmk <:+ a.time.tmk.
            -- Same length → equal → l = l_frame, contradicting h_l_ne
            have h_tmk'_suf := h_desc_apply a h_eq
            have h_l_suf := ha.tmk_suffix
            have h_len : ((l, t_frame.tk) :: tmk).length = tmk'.length := by simp [tmk']
            have h_eq_entry := suffix_eq_of_length_eq
              ((l, t_frame.tk) :: tmk) tmk' a.time.tmk h_l_suf h_tmk'_suf h_len
            exact absurd (Prod.ext_iff.mp (List.cons.inj h_eq_entry).1).1 h_l_ne
        -- Call P_handle
        have ⟨h_strict_handle, h_wf_v_out, hinv', h_wb_handle, _h_cb_handle⟩ :=
          (simulation isHandlerLabel h_handlerLabels_consistent h_label_kind_sound _).2.2.2.1
            l_frame hdl ρ_hdl v' σ₁ t_restored v σ'
            h_handle h_wf_hdl h_wf_v' hinv₁
            h_var_fresh_σ₁ h_kont_fresh_σ₁ h_kont_enc_fresh_σ₁ h_cdf_σ₁ h_hdf_σ₁ h_lnb_hdl_hf
        -- Compose outputs
        exact ⟨.apply_restore_handle h_lookup' h_content' rfl h_strict_apply rfl h_strict_handle,
               h_wf_v_out, hinv',
               -- Write scope: both steps write at tmk suffix
               fun a ha => by
                 by_cases h1 : σ₁ a = σ a
                 · -- Handle step changed a: descendant of t_restored (tmk level)
                   have h2 : σ' a ≠ σ₁ a := by rw [h1]; exact ha
                   have := h_wb_handle.descendant h2
                   -- t_restored.tmk = tmk, so descendants have tmk <:+ a.time.tmk
                   exact this.tmk_suffix
                 · -- Apply step changed a: tmk' <:+ a.time.tmk, hence tmk <:+ a.time.tmk
                   exact (List.suffix_cons _ _).trans (h_desc_apply a h1),
               -- CDF preservation
               fun a_κ₀ h_eq => by
                 cases h_eq
                 exact ⟨hdl.allLabels, Finset.subset_union_right, fun l hl h_cdf => by
                   -- Step 1: CDF σ → CDF σ₁ (apply at tmk' doesn't touch tmk-level CDF)
                   have h_cdf_1 : CallDescFresh σ₁ t_restored l := by
                     intro a ha
                     by_cases h_eq : σ₁ a = σ a
                     · rw [h_eq]; exact h_cdf a ha
                     · exact absurd (h_desc_apply a h_eq) (fun h => ha.no_shorter_tmk_entry h)
                   -- Step 2: CDF σ₁ → CDF σ' (via WriteBound.callDescFresh)
                   exact h_wb_handle.callDescFresh hl h_cdf_1⟩,
               -- HDF preservation: DL = {l_frame} ∪ hdl.allLabels
               fun a_κ₀ h_eq => by
                 cases h_eq
                 refine ⟨{l_frame} ∪ hdl.allLabels, ?_, fun l hl h_hdf => ?_⟩
                 · intro l hl
                   rcases Finset.mem_union.mp hl with h | h
                   · exact Finset.mem_union_left _ (Finset.mem_singleton.mp h ▸ Finset.mem_singleton_self _)
                   · exact Finset.mem_union_right _ (Finset.mem_union_right _ h)
                 have h_l_ne : l ≠ l_frame := fun h => hl (Finset.mem_union_left _ (h ▸ Finset.mem_singleton_self _))
                 have h_l_not_hdl : l ∉ hdl.allLabels := fun h => hl (Finset.mem_union_right _ h)
                 have h_hdf_1 : HandlerDescFresh σ₁ t_restored l := by
                   intro a tk ha
                   by_cases h_eq : σ₁ a = σ a
                   · rw [h_eq]; exact h_hdf a tk ha
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
                 by_cases h1 : σ₁ a = σ a
                 · exact h_wb_handle.descendant (by rw [h1]; exact ha)
                 · have h_tmk'_suf := h_desc_apply a h1
                   obtain ⟨tk₀, hd⟩ := Descendant.of_tmk_suffix h_tmk'_suf a.time.tk
                   exact (Descendant.appKont l_frame tk₀ Descendant.refl).trans hd,
               -- Same-tk writes bounded
               fun a_κ₀ h_eq a ha h_atk h_atmk => by
                 cases h_eq
                 -- Writes at a_κ.frame.time.tk/tmk: apply writes at tmk' (deeper), so must be from handle
                 by_cases h1 : σ₁ a = σ a
                 · -- Handle step: use h_wb_handle
                   have h_ne_1 : σ' a ≠ σ₁ a := by rw [h1]; exact ha
                   have ⟨h_at, _⟩ := h_wb_handle a h_ne_1
                   have h_eq_t : a.time = t_restored := by
                     have h_eta : a.time = ⟨a.time.tk, a.time.tmk⟩ := by cases a.time; rfl
                     rw [h_eta, h_atk, h_atmk]
                   rcases h_at h_eq_t with ⟨x, hx_eq, hx_mem⟩ | ⟨k, hk_eq, _, hk_mem⟩ | ⟨k, hk_eq, _, hk_mem⟩
                   · left; exact ⟨x, by rw [hx_eq]; simp, hx_mem⟩
                   · right; exact ⟨k, hk_eq, by simp; right; exact hk_mem⟩
                   · right; exact ⟨k, hk_eq, by
                       simp at hk_mem ⊢
                       exact hk_mem⟩
                 · -- Apply step: writes at tmk' <:+ a.time.tmk, but a.time.tmk = tmk ≠ tmk'
                   exfalso
                   have := h_desc_apply a h1
                   rw [h_atmk] at this
                   exact absurd this.length_le (by simp [tmk']),
               -- ChainBound for result
               by
                 intro op args oa h_susp
                 obtain ⟨used, usedVars, h_pc, h_sub_l, h_sub_v, h_suf, h_br⟩ := _h_cb_handle op args oa h_susp
                 refine ⟨used, usedVars, h_pc, ?_, h_sub_v, h_suf, ?_⟩
                 · intro a' hoa htk
                   have := h_sub_l a' hoa htk
                   show used ⊆ (match some a_κ with | some a => {a.frame.label} | none => ∅) ∪ ({a_κ.frame.label} ∪ hdl.allLabels)
                   simp only [Finset.union_left_idem]
                   exact this
                 · intro a' hoa hne
                   obtain ⟨lb, hlb, hsuf⟩ := h_br a' hoa hne
                   refine ⟨lb, ?_, hsuf⟩
                   rcases Finset.mem_union.mp hlb with h | h
                   · exact Finset.mem_union_left _ h
                   · exact Finset.mem_union_right _ (Finset.mem_union_right _ h)⟩
      | same_tk h_lookup' h_content' _ _ _ _ _ _ _ _ _ _ _ =>
        rw [h_lookup'] at h_lookup; cases h_lookup
        rw [h_content'] at h_content; cases h_content -- handlerFrame ≠ letFrame
      | diff_tk h_lookup' h_content' _ _ _ _ _ _ _ _ =>
        rw [h_lookup'] at h_lookup; cases h_lookup
        rw [h_content'] at h_content; cases h_content -- handlerFrame ≠ letFrame

end DMCFA
