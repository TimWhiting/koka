/-
  Soundness: TFresh → Concrete

  Given a fresh-guarded timestamped derivation and store correspondence,
  produce a concrete derivation with corresponding results.

  We prove soundness for TFresh (which includes freshness guards at each
  allocation). The freshness guards give us the injectivity needed to
  maintain StoreCorr/StoreReflects when extending stores.

  At allocation points, we use `exists_fresh` (axiom) to pick fresh concrete
  addresses. The correspondence uses α : VAddr → TVAddr (concrete → timestamped)
  with EnvCorr, EnvReflects, StoreCorr, StoreReflects forming a bidirectional
  correspondence.

  Soundness for the plain timestamped semantics follows by composing with
  the freshness theorem (T → TFresh for well-formed programs).
-/

import DMCFA.Correspondence
import DMCFA.FreshSemantics
import DMCFA.Semantics
import DMCFA.Lemmas

namespace DMCFA

/-! ## Reverse atomic expression correspondence -/

/-- Given a timestamped atomic eval and correspondence, produce a concrete one -/
theorem evalTAtomic_corr {α : VAddr → TVAddr} {ρ : Env} {tρ : TEnv}
    {σ : Store} {tσ : TStore}
    (h_env : EnvCorr α ρ tρ) (h_envR : EnvReflects α ρ tρ)
    (h_store : StoreCorr α tσ σ) (_h_refl : StoreReflects α tσ σ)
    (h_scope : EnvScoped ρ σ)
    {ae : AExp} {td : TDenotable} (h_eval : evalTAtomic ae tρ tσ = some td) :
    ∃ d, evalAtomic ae ρ σ = some d ∧ DenotableCorr α tσ d td := by
  cases ae with
  | var x =>
    simp only [evalTAtomic] at h_eval
    cases htρ : Finmap.lookup x tρ with
    | none => simp [htρ] at h_eval
    | some ta =>
      simp [htρ] at h_eval
      obtain ⟨a, hρ, hα⟩ := h_envR x ta htρ
      -- σ a ≠ none from EnvScoped
      have hσ_ne := h_scope x a hρ
      obtain ⟨d, hσ⟩ := Option.ne_none_iff_exists'.mp hσ_ne
      obtain ⟨td', htσ', hcorr⟩ := h_store a d hσ
      -- α a = ta, so tσ (.val ta) = tσ (.val (α a))
      rw [hα] at htσ'
      cases htσ_val : tσ (.val ta) with
      | none => simp [htσ_val] at h_eval
      | some s =>
        simp [htσ_val] at h_eval
        rw [htσ_val] at htσ'; injection htσ' with htσ'
        cases s with
        | denotable dd =>
          have h_eq := TStorable.denotable.inj htσ'
          subst h_eq; simp at h_eval; subst h_eval
          exact ⟨d, by simp [evalAtomic, hρ, hσ], hcorr⟩
        | kontLink => simp at h_eval
  | lam xs body =>
    simp only [evalTAtomic] at h_eval
    split_ifs at h_eval with h_nd
    · injection h_eval with h_eval; subst h_eval
      exact ⟨.closure ⟨xs, body, ρ, h_nd⟩, by simp [evalAtomic, h_nd],
             DenotableCorr.closure ⟨rfl, rfl, h_env, h_envR⟩⟩
  | con c =>
    simp only [evalTAtomic] at h_eval; injection h_eval with h_eval; subst h_eval
    exact ⟨.conLabel c, by simp [evalAtomic], DenotableCorr.conLabel⟩
  | succE x =>
    simp only [evalTAtomic] at h_eval
    cases htρ : Finmap.lookup x tρ with
    | none => simp [htρ] at h_eval
    | some ta =>
      simp [htρ] at h_eval
      obtain ⟨a, hρ, hα⟩ := h_envR x ta htρ
      -- σ a ≠ none from EnvScoped
      have hσ_ne := h_scope x a hρ
      obtain ⟨d_c, hσ_c⟩ := Option.ne_none_iff_exists'.mp hσ_ne
      -- evalTAtomic succE just needs tσ (.val ta) to be some (.denotable _)
      -- Result is .succVal ta regardless of the stored value
      cases htσ : tσ (.val ta) with
      | none => simp [htσ] at h_eval
      | some s =>
        cases s with
        | denotable _ =>
          simp [htσ] at h_eval; subst h_eval
          -- Concrete succE: look up x → a, then look up σ a → d_c, return .succVal a
          refine ⟨.succVal a, ?_, hα ▸ .succVal⟩
          simp [evalAtomic, hρ, hσ_c]
        | kontLink => simp [htσ] at h_eval

/-! ## Single-allocation correspondence extension

  Given freshness in the timestamped store (`tσ (.val ta) = none`) and
  `exists_fresh σ`, produce a fresh concrete address and extended correspondence. -/

theorem sound_extend_val
    {α : VAddr → TVAddr} {tσ : TStore} {σ : Store}
    {ta : TVAddr} {td : TDenotable} {d : Denotable}
    (h_store : StoreCorr α tσ σ) (h_refl : StoreReflects α tσ σ)
    (h_ss : StoreScoped σ)
    (h_tfresh : tσ (.val ta) = none)
    (h_dcorr : DenotableCorr α tσ d td)
    (h_dscoped : DenotableScoped d σ) :
    ∃ a_v : VAddr, σ a_v = none ∧
      let α' := fun a => if a = a_v then ta else α a
      let tσ' := tσ.extend (.val ta) (.denotable td)
      let σ' := σ.extend a_v d
      StoreCorr α' tσ' σ' ∧
      StoreReflects α' tσ' σ' ∧
      AlphaExtends α α' σ ∧
      (∀ a', σ a' ≠ none → α a' ≠ ta) := by
  obtain ⟨a_v, h_fresh⟩ := exists_fresh σ
  have h_inj : ∀ a', σ a' ≠ none → α a' ≠ ta := by
    intro a' ha' heq; rw [← heq] at h_tfresh
    obtain ⟨_, htσ', _⟩ := h_store a' _ (Option.ne_none_iff_exists'.mp ha').choose_spec
    rw [htσ'] at h_tfresh; exact absurd h_tfresh nofun
  have h_ext_α : ∀ a, σ a ≠ none → (fun a => if a = a_v then ta else α a) a = α a :=
    fun a ha => dif_neg (fun heq => by subst heq; exact absurd h_fresh ha)
  have h_ext_tσ : ∀ addr, tσ addr ≠ none → (tσ.extend (.val ta) (.denotable td)) addr = tσ addr :=
    fun addr haddr => TStore.extend_ne _ _ _ _ (by intro heq; subst heq; exact absurd h_tfresh haddr)
  refine ⟨a_v, h_fresh, ?_, ?_, h_ext_α, h_inj⟩
  · -- StoreCorr
    intro a d' hσ'
    simp only [Store.extend] at hσ'
    split at hσ'
    · rename_i heq; subst heq; injection hσ' with hσ'; subst hσ'
      simp only []
      exact ⟨td, TStore.extend_same _ _ _,
             h_dcorr.of_alpha_extends_fresh h_ext_α h_ext_tσ h_dscoped⟩
    · rename_i hne
      simp
      have hne' : TAddr.val (α a) ≠ TAddr.val ta :=
        fun heq => h_inj a (by rw [hσ']; exact nofun) (TAddr.val.inj heq)
      obtain ⟨td', htσ_old, hd⟩ := h_store a d' hσ'
      refine ⟨td', ?_, hd.of_alpha_extends_fresh h_ext_α h_ext_tσ (h_ss a d' hσ')⟩
      have : (if a = a_v then ta else α a) = α a := if_neg hne
      rw [show (TAddr.val (if a = a_v then ta else α a) : TAddr) = TAddr.val (α a) from by rw [this]]
      rw [TStore.extend_ne _ _ _ _ hne']
      exact htσ_old
  · -- StoreReflects
    intro ta' h_ne
    by_cases heq : ta' = ta
    · subst heq
      exact ⟨a_v, by simp [Store.extend], by simp⟩
    · have hne_addr : (TAddr.val ta' : TAddr) ≠ TAddr.val ta :=
        fun h => heq (TAddr.val.inj h)
      have h_old : tσ (.val ta') ≠ none := by
        intro h_none; exact h_ne (by rw [show (tσ.extend (.val ta) (.denotable td)) (.val ta') = tσ (.val ta') from
          TStore.extend_ne _ _ _ _ hne_addr]; exact h_none)
      obtain ⟨a, hσ, hα⟩ := h_refl ta' h_old
      refine ⟨a, ?_, ?_⟩
      · intro h_eq; cases h_σ : σ a with
        | none => exact absurd h_σ hσ
        | some _ => simp [Store.extend] at h_eq; split at h_eq <;> simp_all
      · rw [h_ext_α a hσ]; exact hα

/-- Variant where DenotableCorr is given at the extended α'/tσ' (for self-referencing closures) -/
theorem sound_extend_val_self
    {α : VAddr → TVAddr} {tσ : TStore} {σ : Store}
    {ta : TVAddr} {td : TDenotable} {d : Denotable}
    (h_store : StoreCorr α tσ σ) (h_refl : StoreReflects α tσ σ)
    (h_ss : StoreScoped σ)
    (h_tfresh : tσ (.val ta) = none)
    (a_v : VAddr) (h_fresh : σ a_v = none)
    (h_dcorr_ext : DenotableCorr (fun a => if a = a_v then ta else α a)
      (tσ.extend (.val ta) (.denotable td)) d td) :
    let α' := fun a => if a = a_v then ta else α a
    let tσ' := tσ.extend (.val ta) (.denotable td)
    let σ' := σ.extend a_v d
    StoreCorr α' tσ' σ' ∧ StoreReflects α' tσ' σ' := by
  have h_inj : ∀ a', σ a' ≠ none → α a' ≠ ta := by
    intro a' ha' heq
    obtain ⟨_, htσ', _⟩ := h_store a' _ (Option.ne_none_iff_exists'.mp ha').choose_spec
    rw [heq] at htσ'; rw [h_tfresh] at htσ'; exact absurd htσ' nofun
  have h_ext_α : ∀ a, σ a ≠ none → (fun a => if a = a_v then ta else α a) a = α a :=
    fun a ha => dif_neg (fun heq => by subst heq; exact absurd h_fresh ha)
  have h_ext_tσ : ∀ addr, tσ addr ≠ none → (tσ.extend (.val ta) (.denotable td)) addr = tσ addr :=
    fun addr haddr => TStore.extend_ne _ _ _ _ (by intro heq; subst heq; exact absurd h_tfresh haddr)
  constructor
  · -- StoreCorr
    intro a d' hσ'; simp only [Store.extend] at hσ'
    split at hσ'
    · rename_i heq; subst heq; injection hσ' with hσ'; subst hσ'
      simp only []
      exact ⟨td, TStore.extend_same _ _ _, h_dcorr_ext⟩
    · rename_i hne; simp only []
      have hne' : TAddr.val (α a) ≠ TAddr.val ta :=
        fun heq => h_inj a (by rw [hσ']; exact nofun) (TAddr.val.inj heq)
      obtain ⟨td', htσ_old, hd⟩ := h_store a d' hσ'
      refine ⟨td', ?_, hd.of_alpha_extends_fresh h_ext_α h_ext_tσ (h_ss a d' hσ')⟩
      have : (fun a => if a = a_v then ta else α a) a = α a := dif_neg hne
      simp only [this]; rw [TStore.extend_ne _ _ _ _ hne']; exact htσ_old
  · -- StoreReflects
    intro ta' h_ne
    by_cases heq : ta' = ta
    · subst heq; exact ⟨a_v, by simp [Store.extend], by simp⟩
    · have hne_addr : (TAddr.val ta' : TAddr) ≠ TAddr.val ta := fun h => heq (TAddr.val.inj h)
      have h_old : tσ (.val ta') ≠ none := by
        intro h_none; apply h_ne
        show (tσ.extend (.val ta) (.denotable td)) (.val ta') = none
        rw [TStore.extend_ne _ _ _ _ hne_addr]; exact h_none
      obtain ⟨a, hσ, hα⟩ := h_refl ta' h_old
      refine ⟨a, ?_, ?_⟩
      · exact fun heq_σ => by
          simp only [Store.extend] at heq_σ; split at heq_σ <;> simp_all
      · have : a ≠ a_v := fun h => by subst h; exact absurd h_fresh hσ
        show (if a = a_v then ta else α a) = ta'
        rw [if_neg this]; exact hα

/-- If evalAtomic returns succVal a, and the store is scoped, then σ a ≠ none -/
theorem evalAtomic_succVal_scoped {ae : AExp} {ρ : Env} {σ : Store} {a : VAddr}
    (h : evalAtomic ae ρ σ = some (.succVal a))
    (_h_scope : EnvScoped ρ σ) (h_ss : StoreScoped σ) : σ a ≠ none := by
  cases ae with
  | var x =>
    simp only [evalAtomic] at h
    cases hρ : ρ x with
    | none => simp [hρ] at h
    | some a' =>
      simp [hρ] at h
      cases hσ : σ a' with
      | none => simp [hσ] at h
      | some d =>
        simp [hσ] at h; subst h
        -- d = .succVal a, by StoreScoped: DenotableScoped (.succVal a) σ = (σ a ≠ none)
        exact h_ss a' _ hσ
  | succE x =>
    simp only [evalAtomic] at h
    cases hρ : ρ x with
    | none => simp [hρ] at h
    | some a' =>
      simp [hρ] at h
      cases hσ : σ a' with
      | none => simp [hσ] at h
      | some _ => simp [hσ] at h; subst h; rw [hσ]; exact nofun
  | _ => simp [evalAtomic] at h

/-- Combined env extend for soundness: given sound_extend_val's output,
    build EnvCorr + EnvReflects + EnvScoped for the extended env/store -/
theorem sound_env_extend
    {α : VAddr → TVAddr} {ρ : Env} {tρ : TEnv} {σ : Store}
    {x : Var} {ta : TVAddr} {a_v : VAddr} {d : Denotable}
    (h_env : EnvCorr α ρ tρ) (h_envR : EnvReflects α ρ tρ)
    (h_scope : EnvScoped ρ σ) (h_fresh : σ a_v = none)
    (h_ext_α : AlphaExtends α (fun a => if a = a_v then ta else α a) σ) :
    let α' := fun a => if a = a_v then ta else α a
    EnvCorr α' (ρ.extend x a_v) (tρ.extend x ta) ∧
    EnvReflects α' (ρ.extend x a_v) (tρ.extend x ta) ∧
    EnvScoped (ρ.extend x a_v) (σ.extend a_v d) := by
  refine ⟨?_, ?_, ?_⟩
  · -- EnvCorr
    intro y a hya; simp only [Env.extend] at hya
    split at hya
    · rename_i heq; subst heq; injection hya with hya; subst hya
      simp [TEnv.extend]
    · rename_i hne
      have ha_ne : a ≠ a_v := fun h => by subst h; exact absurd h_fresh (h_scope _ _ hya)
      show Finmap.lookup y (tρ.extend x ta) = some (if a = a_v then ta else α a)
      rw [if_neg ha_ne, TEnv.lookup_extend_ne _ _ _ _ hne]; exact h_env _ _ hya
  · -- EnvReflects
    intro y ta' htρ'
    show ∃ a, (ρ.extend x a_v) y = some a ∧ (if a = a_v then ta else α a) = ta'
    by_cases heq : y = x
    · subst heq; simp [TEnv.extend] at htρ'; subst htρ'
      exact ⟨a_v, by simp [Env.extend], by simp⟩
    · simp [TEnv.extend, Finmap.lookup_insert_of_ne _ heq] at htρ'
      obtain ⟨a, hρ, hα⟩ := h_envR y ta' htρ'
      exact ⟨a, by simp [Env.extend, heq]; exact hρ,
             by rw [if_neg (fun h => by subst h; exact absurd h_fresh (h_scope _ _ hρ))]; exact hα⟩
  · -- EnvScoped
    intro y a hya; simp only [Env.extend] at hya
    split at hya
    · injection hya with hya; subst hya; simp [Store.extend]
    · intro h_eq; simp only [Store.extend] at h_eq
      split at h_eq
      · simp at h_eq
      · exact h_scope _ _ hya h_eq

/-- Result of evalAtomic is scoped if env and store are scoped -/
theorem evalAtomic_scoped {ae : AExp} {ρ : Env} {σ : Store} {d : Denotable}
    (h : evalAtomic ae ρ σ = some d) (h_scope : EnvScoped ρ σ) (h_ss : StoreScoped σ) :
    DenotableScoped d σ := by
  cases ae with
  | var x =>
    simp only [evalAtomic] at h
    cases hρ : ρ x with
    | none => simp [hρ] at h
    | some a =>
      simp [hρ] at h
      cases hσ : σ a with
      | none => simp [hσ] at h
      | some d' => simp [hσ] at h; subst h; exact h_ss a d' hσ
  | lam xs body =>
    simp only [evalAtomic] at h; split_ifs at h with h_nd
    · injection h with h; subst h; exact h_scope

  | con c => simp only [evalAtomic] at h; injection h with h; subst h; exact trivial
  | succE x =>
    simp only [evalAtomic] at h
    cases hρ : ρ x with
    | none => simp [hρ] at h
    | some a =>
      simp [hρ] at h
      cases hσ : σ a with
      | none => simp [hσ] at h
      | some _ => simp [hσ] at h; subst h; show σ a ≠ none; rw [hσ]; exact nofun

/-! ## Store monotonicity (concrete) -/

private theorem store_extend_mono {σ : Store} {a_v : VAddr} {d : Denotable} :
    ∀ a, σ a ≠ none → (σ.extend a_v d) a ≠ none := by
  intro a ha; simp [Store.extend]; split <;> [exact nofun; exact ha]

/-! ## Foldl allocation helper for eval_funApp_clos -/

/-- Pick N fresh concrete addresses and build correspondence for foldl-extended stores.
    Given xs (parameter names), tds (timestamped values), ds_c (concrete values),
    picks fresh concrete addresses and proves the foldl-extended states correspond. -/
private theorem sound_foldl_extend
    {α : VAddr → TVAddr} {tσ : TStore} {σ : Store}
    {ρ_lam : Env} {tρ_lam : TEnv} {t_new : Time}
    (h_env : EnvCorr α ρ_lam tρ_lam)
    (h_envR : EnvReflects α ρ_lam tρ_lam)
    (h_store : StoreCorr α tσ σ)
    (h_refl : StoreReflects α tσ σ)
    (h_ss : StoreScoped σ)
    (h_scope : EnvScoped ρ_lam σ)
    (xs : List Var) (ds_c : List Denotable) (tds : List TDenotable)
    (h_corrs : List.Forall₂ (fun d td => DenotableCorr α tσ d td) ds_c tds)
    (h_tfresh : ∀ (x : Var), x ∈ xs → tσ (.val ⟨x, t_new⟩) = none)
    (h_ds_scoped : ∀ d ∈ ds_c, DenotableScoped d σ)
    (h_nodup : xs.Nodup)
    (h_len : ds_c.length = xs.length) :
    ∃ (as_v : List VAddr),
      as_v.length = xs.length ∧
      List.Forall₂ (fun a (_ : Denotable) => σ a = none) as_v ds_c ∧
      let σ_new := (as_v.zip ds_c).foldl (fun s (p : VAddr × Denotable) => s.extend p.1 p.2) σ
      let ρ_new := (xs.zip as_v).foldl (fun r (p : Var × VAddr) => r.extend p.1 p.2) ρ_lam
      let tσ_new := (xs.zip tds).foldl (fun s (p : Var × TDenotable) =>
        s.extend (.val ⟨p.1, t_new⟩) (.denotable p.2)) tσ
      let tρ_new := xs.foldl (fun r x => r.extend x ⟨x, t_new⟩) tρ_lam
      as_v.Nodup ∧
      (∀ a, σ a ≠ none → σ_new a ≠ none) ∧
      ∃ α' : VAddr → TVAddr,
        EnvCorr α' ρ_new tρ_new ∧
        EnvReflects α' ρ_new tρ_new ∧
        StoreCorr α' tσ_new σ_new ∧
        StoreReflects α' tσ_new σ_new ∧
        AlphaExtends α α' σ ∧
        StoreScoped σ_new ∧
        EnvScoped ρ_new σ_new := by
  -- Generalize and induct
  suffices ∀ (α₀ : VAddr → TVAddr) (tσ₀ : TStore) (σ₀ : Store) (ρ₀ : Env) (tρ₀ : TEnv)
      (xs' : List Var) (ds' : List Denotable) (tds' : List TDenotable),
      EnvCorr α₀ ρ₀ tρ₀ → EnvReflects α₀ ρ₀ tρ₀ →
      StoreCorr α₀ tσ₀ σ₀ → StoreReflects α₀ tσ₀ σ₀ →
      StoreScoped σ₀ → EnvScoped ρ₀ σ₀ →
      List.Forall₂ (fun d td => DenotableCorr α₀ tσ₀ d td) ds' tds' →
      (∀ x, x ∈ xs' → tσ₀ (.val ⟨x, t_new⟩) = none) →
      (∀ d ∈ ds', DenotableScoped d σ₀) →
      xs'.Nodup → ds'.length = xs'.length →
      (∀ a, σ a ≠ none → σ₀ a ≠ none) → AlphaExtends α α₀ σ →
      ∃ (as_v : List VAddr),
        as_v.length = xs'.length ∧
        List.Forall₂ (fun a (_ : Denotable) => σ a = none) as_v ds' ∧
        List.Forall₂ (fun a (_ : Denotable) => σ₀ a = none) as_v ds' ∧
        as_v.Nodup ∧
        let σ' := (as_v.zip ds').foldl (fun s (p : VAddr × Denotable) => s.extend p.1 p.2) σ₀
        let ρ' := (xs'.zip as_v).foldl (fun r (p : Var × VAddr) => r.extend p.1 p.2) ρ₀
        let tσ' := (xs'.zip tds').foldl (fun s (p : Var × TDenotable) =>
          s.extend (.val ⟨p.1, t_new⟩) (.denotable p.2)) tσ₀
        let tρ' := xs'.foldl (fun r x => r.extend x ⟨x, t_new⟩) tρ₀
        (∀ a, σ₀ a ≠ none → σ' a ≠ none) ∧
        ∃ α', EnvCorr α' ρ' tρ' ∧ EnvReflects α' ρ' tρ' ∧
          StoreCorr α' tσ' σ' ∧ StoreReflects α' tσ' σ' ∧
          AlphaExtends α α' σ ∧ StoreScoped σ' ∧ EnvScoped ρ' σ' by
    obtain ⟨as_v, h_len', h_fresh_σ, _, h_dist, h_mono', α', h_e, h_er, h_s, h_r, h_ext, h_ss', h_sc⟩ :=
      this α tσ σ ρ_lam tρ_lam xs ds_c tds h_env h_envR h_store h_refl h_ss h_scope
        h_corrs h_tfresh h_ds_scoped h_nodup h_len (fun _ h => h) AlphaExtends.refl
    exact ⟨as_v, h_len', h_fresh_σ, h_dist, h_mono', α', h_e, h_er, h_s, h_r, h_ext, h_ss', h_sc⟩
  intro α₀ tσ₀ σ₀ ρ₀ tρ₀ xs' ds' tds'
  induction xs' generalizing ds' tds' α₀ tσ₀ σ₀ ρ₀ tρ₀ with
  | nil =>
    intro h_e h_er h_s h_r h_ss' h_sc h_corrs' h_tf h_ds h_nd h_len' h_mono h_ext
    match ds', h_len', tds', h_corrs' with
    | [], _, [], _ =>
      exact ⟨[], rfl, .nil, .nil, List.nodup_nil,
        fun _ h => h, α₀, h_e, h_er, h_s, h_r, h_ext, h_ss', h_sc⟩
  | cons x xs_tl ih =>
    intro h_e₀ h_er₀ h_s₀ h_r₀ h_ss₀ h_sc₀ h_corrs₀ h_tf₀ h_ds₀ h_nd₀ h_len₀ h_mono₀ h_ext₀
    match ds', h_len₀, tds', h_corrs₀ with
    | d_hd :: ds_tl, h_len', td_hd :: tds_tl, .cons h_c_hd h_c_tl =>
      -- Single step: sound_extend_val
      obtain ⟨a_v, h_fresh_v, h_s₁, h_r₁, h_ext₁, h_inj₁⟩ :=
        sound_extend_val h_s₀ h_r₀ h_ss₀ (h_tf₀ x (.head _)) h_c_hd (h_ds₀ _ (.head _))
      -- Transfer tail DenotableCorr
      have h_α₁_eq : ∀ a, σ₀ a ≠ none →
          (fun a' => if a' = a_v then ⟨x, t_new⟩ else α₀ a') a = α₀ a :=
        fun a ha => if_neg (fun heq => by subst heq; exact absurd h_fresh_v ha)
      have h_tσ₁_eq : ∀ addr, tσ₀ addr ≠ none →
          (tσ₀.extend (.val ⟨x, t_new⟩) (.denotable td_hd)) addr = tσ₀ addr :=
        fun addr ha => TStore.extend_ne _ _ _ _ (by
          intro heq; rw [heq] at ha; exact absurd (h_tf₀ x (.head _)) ha)
      have h_c_tl' : List.Forall₂ (fun d td => DenotableCorr
          (fun a => if a = a_v then ⟨x, t_new⟩ else α₀ a)
          (tσ₀.extend (.val ⟨x, t_new⟩) (.denotable td_hd)) d td) ds_tl tds_tl := by
        suffices ∀ (ds₁ : List Denotable) (tds₁ : List TDenotable),
            List.Forall₂ (fun d td => DenotableCorr α₀ tσ₀ d td) ds₁ tds₁ →
            (∀ d ∈ ds₁, DenotableScoped d σ₀) →
            List.Forall₂ (fun d td => DenotableCorr (fun a => if a = a_v then ⟨x, t_new⟩ else α₀ a)
              (tσ₀.extend (.val ⟨x, t_new⟩) (.denotable td_hd)) d td) ds₁ tds₁ from
          this ds_tl tds_tl h_c_tl (fun d hd => h_ds₀ d (.tail _ hd))
        intro ds₁ tds₁ hf₂ hds; induction hf₂ with
        | nil => exact .nil
        | cons h_hd _ ih_f =>
          exact .cons (h_hd.of_alpha_extends_fresh h_α₁_eq h_tσ₁_eq (hds _ (.head _)))
            (ih_f (fun d hd => hds d (.tail _ hd)))
      -- Updated invariants at σ₁ = σ₀.extend a_v d_hd
      have h_mono_step : ∀ a, σ₀ a ≠ none → (σ₀.extend a_v d_hd) a ≠ none :=
        fun a ha => show (σ₀.extend a_v d_hd) a ≠ none by
          simp only [Store.extend]; split <;> [exact nofun; exact ha]
      have h_ss₁ := h_ss₀.extend_val (denotableScoped_mono (h_ds₀ _ (.head _)) h_mono_step)
      have h_sc₁_env : EnvScoped (ρ₀.extend x a_v) (σ₀.extend a_v d_hd) := by
        intro y b hyb; simp only [Env.extend] at hyb; split at hyb
        · injection hyb with hyb; subst hyb; simp [Store.extend]
        · exact h_mono_step b (h_sc₀ y b hyb)
      have h_e₁ : EnvCorr (fun a => if a = a_v then ⟨x, t_new⟩ else α₀ a)
          (ρ₀.extend x a_v) (tρ₀.extend x ⟨x, t_new⟩) := by
        convert (h_e₀.of_alpha_extends h_ext₁ h_sc₀).extend x a_v using 1
        simp [TEnv.extend]
      have h_er₁ : EnvReflects (fun a => if a = a_v then ⟨x, t_new⟩ else α₀ a)
          (ρ₀.extend x a_v) (tρ₀.extend x ⟨x, t_new⟩) := by
        convert (h_er₀.of_alpha_extends h_ext₁ h_sc₀).extend x a_v using 1
        simp [TEnv.extend]
      -- Freshness for tail xs in extended tσ
      have h_x_notin := (List.nodup_cons.mp h_nd₀).1
      have h_tf₁ : ∀ x', x' ∈ xs_tl →
          (tσ₀.extend (.val ⟨x, t_new⟩) (.denotable td_hd)) (.val ⟨x', t_new⟩) = none := by
        intro x' hx'
        rw [TStore.extend_ne _ _ _ _ (by
          intro heq; cases heq; exact h_x_notin hx')]
        exact h_tf₀ x' (.tail _ hx')
      -- Recurse on tail with EXTENDED env
      obtain ⟨as_tl, h_len_tl, h_fresh_tl, h_fresh_σ₁_tl, h_dist_tl, h_mono_tl,
              α', h_e', h_er', h_s', h_r', h_ext', h_ss', h_sc'⟩ :=
        ih (fun a => if a = a_v then ⟨x, t_new⟩ else α₀ a)
          (tσ₀.extend (.val ⟨x, t_new⟩) (.denotable td_hd))
          (σ₀.extend a_v d_hd)
          (ρ₀.extend x a_v) (tρ₀.extend x ⟨x, t_new⟩)
          ds_tl tds_tl
          h_e₁ h_er₁ h_s₁ h_r₁ h_ss₁ h_sc₁_env h_c_tl' h_tf₁
          (fun d hd => denotableScoped_mono (h_ds₀ d (.tail _ hd)) h_mono_step)
          (List.nodup_cons.mp h_nd₀).2 (by simp at h_len'; omega)
          (fun a ha => h_mono_step a (h_mono₀ a ha))
          (h_ext₀.trans h_ext₁ h_mono₀)
      -- Assemble: cons a_v onto as_tl
      simp only [List.zip_cons_cons, List.foldl_cons]
      refine ⟨a_v :: as_tl, by simp; omega,
        .cons (by by_contra h; push_neg at h; exact absurd h_fresh_v (h_mono₀ _ h)) h_fresh_tl,
        .cons h_fresh_v (by
          -- Transfer freshness: as_tl fresh in σ₀.extend a_v d_hd → fresh in σ₀
          -- Actually h_fresh_σ₁_tl gives freshness in σ₀.extend a_v d_hd
          -- We need freshness in σ₀, which is weaker (σ₀ ⊆ σ₀.extend)
          -- But wait, h_fresh_σ₁_tl says σ₀.extend a_v d_hd (as_tl[k]) = none
          -- which means as_tl[k] ≠ a_v AND σ₀ (as_tl[k]) = none
          suffices ∀ (as₁ : List VAddr) (ds₁ : List Denotable),
              List.Forall₂ (fun a _ => (σ₀.extend a_v d_hd) a = none) as₁ ds₁ →
              List.Forall₂ (fun a (_ : Denotable) => σ₀ a = none) as₁ ds₁ from
            this as_tl ds_tl h_fresh_σ₁_tl
          intro as₁ ds₁ hf; induction hf with
          | nil => exact .nil
          | cons h_hd _ ih_f =>
            exact .cons (by simp [Store.extend] at h_hd; split at h_hd <;> [exact absurd h_hd nofun; exact h_hd])
              ih_f),
        (by -- Distinctness: a_v ∉ as_tl (freshness in σ₀.extend a_v d_hd) + IH distinctness
          -- Key: h_fresh_σ₁_tl says as_tl[k] is fresh in σ₀.extend a_v d_hd
          -- But σ₀.extend a_v d_hd a_v = some d_hd, so as_tl[k] ≠ a_v
          -- From h_fresh_σ₁_tl: each as_tl element has (σ₀.extend a_v d_hd) a = none
          -- But (σ₀.extend a_v d_hd) a_v = some d_hd, so no as_tl element equals a_v
          have h_av_ne : ∀ a ∈ as_tl, a ≠ a_v := by
            suffices ∀ (as₁ : List VAddr) (ds₁ : List Denotable),
                List.Forall₂ (fun a _ => (σ₀.extend a_v d_hd) a = none) as₁ ds₁ →
                ∀ a ∈ as₁, a ≠ a_v from
              fun a ha => this as_tl ds_tl h_fresh_σ₁_tl a ha
            intro as₁ ds₁ hf a ha hne; subst hne
            induction hf with
            | nil => exact nomatch ha
            | cons h_hd _ ih =>
              cases ha with
              | head => simp [Store.extend] at h_hd
              | tail _ h => exact ih h
          exact List.nodup_cons.mpr ⟨fun hm => h_av_ne _ hm rfl, h_dist_tl⟩),
        fun a ha => h_mono_tl a (h_mono_step a ha),
        α', h_e', h_er', h_s', h_r', h_ext', h_ss', h_sc'⟩

/-! ## Generalized soundness: fresh-guarded timestamped ⟹ concrete

  For arbitrary intermediate configurations with corresponding stores:
  if (e, tρ, tσ, t) ⇓et_f (v_t, tσ') then ∃ α' v σ', (e, ρ, σ) ⇓e (v, σ')
  with v_t ~α' v and tσ' ~α' σ', where α' extends α.

  Proved by mutual strong induction on derivation height over all five
  judgment forms (eval_exp, eval_cexp, continue_frame, handle_value, apply_kont).
  At each allocation, freshness of the timestamped address lets us pick a
  fresh concrete address and extend α without collision. -/

theorem fresh_to_concrete (n : Nat) :
    -- P_exp
    (∀ (e : Exp) (tρ : TEnv) (tσ : TStore) (t : Time) (tv : TValue) (tσ' : TStore),
       TFreshEvalExpN n e tρ tσ t tv tσ' →
       ∀ (α : VAddr → TVAddr) (ρ : Env) (σ : Store),
         EnvCorr α ρ tρ → EnvReflects α ρ tρ →
         StoreCorr α tσ σ → StoreReflects α tσ σ →
         EnvScoped ρ σ → StoreScoped σ →
         ∃ α' v σ',
           EvalExpN n e ρ σ v σ' ∧
           ValueCorr α' tσ' v tv ∧
           StoreCorr α' tσ' σ' ∧
           StoreReflects α' tσ' σ' ∧
           AlphaExtends α α' σ ∧
           StoreScoped σ' ∧
           ValueScoped v σ') ∧
    -- P_cexp
    (∀ (ce : CExp) (tρ : TEnv) (tσ : TStore) (t : Time) (l_enc : Label)
       (tv : TValue) (tσ' : TStore),
       TFreshEvalCExpN n ce tρ tσ t l_enc tv tσ' →
       ∀ (α : VAddr → TVAddr) (ρ : Env) (σ : Store),
         EnvCorr α ρ tρ → EnvReflects α ρ tρ →
         StoreCorr α tσ σ → StoreReflects α tσ σ →
         EnvScoped ρ σ → StoreScoped σ →
         ∃ α' v σ',
           EvalCExpN n ce ρ σ v σ' ∧
           ValueCorr α' tσ' v tv ∧
           StoreCorr α' tσ' σ' ∧
           StoreReflects α' tσ' σ' ∧
           AlphaExtends α α' σ ∧
           StoreScoped σ' ∧
           ValueScoped v σ') ∧
    -- P_continue
    (∀ (l_enc : Label) (tfc : TFrameContent) (t : Time)
       (tv : TValue) (tσ : TStore) (tv' : TValue) (tσ' : TStore),
       TFreshContinueFrameN n l_enc tfc t tv tσ tv' tσ' →
       ∀ (α : VAddr → TVAddr) (σ : Store) (f : Frame) (v : Value),
         FrameCorr α f tfc → ValueCorr α tσ v tv → ValueScoped v σ →
         StoreCorr α tσ σ → StoreReflects α tσ σ →
         EnvScoped (match f with | .letFrame clo => clo.env | .handlerFrame _ ρ => ρ) σ →
         StoreScoped σ →
         ∃ α' v' σ',
           ContinueFrameN n f v σ v' σ' ∧
           ValueCorr α' tσ' v' tv' ∧
           StoreCorr α' tσ' σ' ∧
           StoreReflects α' tσ' σ' ∧
           AlphaExtends α α' σ ∧
           StoreScoped σ' ∧
           ValueScoped v' σ') ∧
    -- P_handle
    (∀ (l_enc : Label) (hdl : Handler) (tρ : TEnv) (tv : TValue) (tσ : TStore)
       (t : Time) (tv' : TValue) (tσ' : TStore),
       TFreshHandleValueN n l_enc hdl tρ tv tσ t tv' tσ' →
       ∀ (α : VAddr → TVAddr) (ρ : Env) (σ : Store) (v : Value),
         EnvCorr α ρ tρ → EnvReflects α ρ tρ →
         ValueCorr α tσ v tv → ValueScoped v σ →
         StoreCorr α tσ σ → StoreReflects α tσ σ →
         EnvScoped ρ σ → StoreScoped σ →
         ∃ α' v' σ',
           HandleValueN n hdl ρ v σ v' σ' ∧
           ValueCorr α' tσ' v' tv' ∧
           StoreCorr α' tσ' σ' ∧
           StoreReflects α' tσ' σ' ∧
           AlphaExtends α α' σ ∧
           StoreScoped σ' ∧
           ValueScoped v' σ') ∧
    -- P_apply
    (∀ (ta_κ : Option TKAddr) (td : TDenotable) (tσ : TStore) (tmk : MKTime)
       (tv : TValue) (tσ' : TStore),
       TFreshApplyKontN n ta_κ td tσ tmk tv tσ' →
       ∀ (α : VAddr → TVAddr) (σ : Store) (κ : Kont) (d : Denotable),
         KontCorr α tσ κ ta_κ → DenotableCorr α tσ d td → DenotableScoped d σ →
         StoreCorr α tσ σ → StoreReflects α tσ σ →
         StoreScoped σ → KontScoped κ σ →
         ∃ α' v σ',
           ApplyKontN n κ d σ v σ' ∧
           ValueCorr α' tσ' v tv ∧
           StoreCorr α' tσ' σ' ∧
           StoreReflects α' tσ' σ' ∧
           AlphaExtends α α' σ ∧
           StoreScoped σ' ∧
           ValueScoped v σ') := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    -----------------------------------------------------------------------
    -- P_exp
    -----------------------------------------------------------------------
    · intro e tρ tσ t tv tσ' h_eval α ρ σ
        h_env h_envR h_store h_refl h_scope h_ss
      cases h_eval with
      | eval_let h_ce h_cont =>
        rename_i n1 ce l_let tv₁ tσ₁ n2 y e_body
        -- IH for cexp
        obtain ⟨_, ih_ce, _, _, _⟩ := ih n1 (by omega)
        obtain ⟨α₁, v₁, σ₁, h_ce', hval₁, hstore₁, hrefl₁, hext₁, hss₁, hvs₁⟩ :=
          ih_ce ce tρ tσ t l_let tv₁ tσ₁ h_ce α ρ σ h_env h_envR h_store h_refl h_scope h_ss
        -- Transfer env for continue IH
        have h_env₁ := h_env.of_alpha_extends hext₁ h_scope
        have h_scope₁ : EnvScoped ρ σ₁ := fun x a hρ => by
          have h_ne := h_scope x a hρ
          obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp h_ne
          rw [Option.ne_none_iff_exists']
          exact ⟨d, eval_cexp_store_mono (eval_cexpN_to h_ce') a d hd⟩
        -- h_ss₁ already obtained from IH destructuring
        -- IH for continue
        obtain ⟨_, _, ih_co, _, _⟩ := ih n2 (by omega)
        obtain ⟨α₂, v₂, σ₂, h_cont', hval₂, hstore₂, hrefl₂, hext₂, hss₂, hvs₂⟩ :=
          ih_co l_let (.letFrame ⟨[y], e_body, tρ, List.nodup_singleton _⟩) t tv₁ tσ₁ tv tσ' h_cont
            α₁ σ₁ (.letFrame ⟨[y], e_body, ρ, List.nodup_singleton _⟩) v₁
            (.letFrame ⟨rfl, rfl, h_env₁, h_envR.of_alpha_extends hext₁ h_scope⟩) hval₁ hvs₁ hstore₁ hrefl₁ h_scope₁ hss₁
        exact ⟨α₂, v₂, σ₂, .eval_let h_ce' h_cont',
               hval₂, hstore₂, hrefl₂,
               hext₁.trans hext₂ (fun a ha => by
                 rw [Option.ne_none_iff_exists'] at ha ⊢
                 obtain ⟨d, hd⟩ := ha
                 exact ⟨d, eval_cexp_store_mono (eval_cexpN_to h_ce') a d hd⟩),
               hss₂, hvs₂⟩
      | eval_tail h_ce =>
        rename_i n_sub ce l_tail
        obtain ⟨_, ih_ce, _, _, _⟩ := ih n_sub (by omega)
        obtain ⟨α', v, σ', h_ce', hval, hstore', hrefl', hext, hss', hvs'⟩ :=
          ih_ce ce tρ tσ t l_tail _ tσ' h_ce α ρ σ h_env h_envR h_store h_refl h_scope h_ss
        exact ⟨α', v, σ', .eval_tail h_ce', hval, hstore', hrefl', hext, hss', hvs'⟩
    -----------------------------------------------------------------------
    -- P_cexp
    -----------------------------------------------------------------------
    · intro ce tρ tσ t l_enc tv tσ' h_eval α ρ σ
        h_env h_envR h_store h_refl h_scope h_ss
      cases h_eval with
      | eval_atomic h_ae =>
        obtain ⟨d, hd, hcorr⟩ := evalTAtomic_corr h_env h_envR h_store h_refl h_scope h_ae
        exact ⟨α, .den d, σ, .eval_atomic hd, .den hcorr, h_store, h_refl, AlphaExtends.refl, h_ss,
               evalAtomic_scoped hd h_scope h_ss⟩
      | eval_opApp htρ =>
        obtain ⟨a, hρ, hα⟩ := h_envR _ _ htρ
        exact ⟨α, .suspended _ [a] [], σ, .eval_opApp hρ,
               .suspended (by simp []) (fun i h1 h2 => by
                 have : i = 0 := by simp at h1; omega
                 subst this; simp [hα]) .nil,
               h_store, h_refl, AlphaExtends.refl, h_ss,
               ⟨fun a' ha' => by simp at ha'; subst ha'; exact h_scope _ _ hρ, fun _ h => by simp at h⟩⟩
      | eval_fun h_teq h_tfresh _h_nd h_tv h_tσ' =>
        subst h_teq; subst h_tv; subst h_tσ'
        rename_i f xs e1
        obtain ⟨a_v, h_fresh⟩ := exists_fresh σ
        let ta : TVAddr := ⟨f, t⟩
        let α' : VAddr → TVAddr := fun a => if a = a_v then ta else α a
        let d_c := Denotable.closure ⟨xs, e1, ρ.extend f a_v, _h_nd⟩
        -- EnvCorr for the extended env (self-referencing closure)
        have h_env' : EnvCorr α' (ρ.extend f a_v) (tρ.extend f ta) := by
          intro x a hxa; simp only [Env.extend] at hxa
          split at hxa
          · rename_i heq; subst heq; injection hxa with hxa; subst hxa
            simp [α', TEnv.extend]
          · rename_i hne
            have ha_ne : a ≠ a_v := fun heq => by subst heq; exact absurd h_fresh (h_scope _ _ hxa)
            show Finmap.lookup x (tρ.extend f ta) = some (α' a)
            rw [show α' a = α a from dif_neg ha_ne, TEnv.lookup_extend_ne _ _ _ _ hne]
            exact h_env _ _ hxa
        -- Build EnvReflects for extended env (same as h_env' but reflects)
        have h_envR' : EnvReflects α' (ρ.extend f a_v) (tρ.extend f ta) := by
          intro x ta' htρ'
          by_cases heq : x = f
          · subst heq; simp [TEnv.extend] at htρ'; subst htρ'
            exact ⟨a_v, by simp [Env.extend], by simp [α']⟩
          · rw [TEnv.lookup_extend_ne _ _ _ _ heq] at htρ'
            obtain ⟨a, hρ, hα⟩ := h_envR x ta' htρ'
            exact ⟨a, by simp [Env.extend, heq]; exact hρ,
                   by show α' a = ta'; rw [show α' a = α a from
                     if_neg (fun h => by subst h; exact absurd h_fresh (h_scope _ _ hρ))]; exact hα⟩
        have h_dcorr_ext : DenotableCorr α'
            (tσ.extend (.val ta) (.denotable (.closure ⟨xs, e1, tρ.extend f ta, _h_nd⟩)))
            d_c (.closure ⟨xs, e1, tρ.extend f ta, _h_nd⟩) :=
          .closure ⟨rfl, rfl, h_env', h_envR'⟩
        obtain ⟨h_store', h_refl'⟩ := sound_extend_val_self h_store h_refl h_ss h_tfresh a_v h_fresh h_dcorr_ext
        refine ⟨α', .den d_c, σ.extend a_v d_c, .eval_fun h_fresh _h_nd rfl rfl,
               .den (.closure ⟨rfl, rfl, h_env', h_envR'⟩), h_store', h_refl',
               fun a ha => dif_neg (fun heq => by subst heq; exact absurd h_fresh ha),
               h_ss.extend_val (fun x a hxa => by
                 simp only [Env.extend] at hxa
                 split at hxa
                 · injection hxa with hxa; subst hxa; simp [Store.extend]
                 · exact fun h => absurd (by simp [Store.extend] at h; split at h <;> simp_all) (h_scope _ _ hxa)),
               (fun x a hxa => by
                 simp only [Env.extend] at hxa
                 split at hxa
                 · injection hxa with hxa; subst hxa; simp [Store.extend]
                 · exact fun h => absurd (by simp [Store.extend] at h; split at h <;> simp_all) (h_scope _ _ hxa))⟩
      | eval_funApp_clos h_f h_len_xs h_targs h_tnew h_tfresh h_tσ_eq h_tρ_eq h_body_deriv =>
        subst h_tnew; subst h_tσ_eq; subst h_tρ_eq
        rename_i f_ae xs e_body tρ_lam aes tds n_body
        -- Step 1: Get concrete closure
        obtain ⟨d_f, hd_f, hcorr_f⟩ := evalTAtomic_corr h_env h_envR h_store h_refl h_scope h_f
        cases hcorr_f with
        | closure h_clo_corr =>
          obtain ⟨h_params, h_body_eq, h_env_lam, h_envR_lam⟩ := h_clo_corr
          simp only [] at h_params h_body_eq h_env_lam h_envR_lam
          subst h_params; subst h_body_eq
          rename_i ρ_lam
          -- Step 2: Get concrete denotables for each arg
          have h_args_c : ∃ ds_c, List.Forall₂ (fun ae d => evalAtomic ae ρ σ = some d) aes ds_c ∧
              List.Forall₂ (fun d td => DenotableCorr α tσ d td) ds_c tds := by
            suffices ∀ (aes' : List AExp) (tds' : List TDenotable),
                List.Forall₂ (fun ae d => evalTAtomic ae tρ tσ = some d) aes' tds' →
                ∃ ds_c, List.Forall₂ (fun ae d => evalAtomic ae ρ σ = some d) aes' ds_c ∧
                  List.Forall₂ (fun d td => DenotableCorr α tσ d td) ds_c tds' from
              this aes tds h_targs
            intro aes' tds' h_f2
            induction h_f2 with
            | nil => exact ⟨[], .nil, .nil⟩
            | @cons ae td _ _ h_eval _ ih_f2 =>
              obtain ⟨d_c, hd_c, hcorr⟩ := evalTAtomic_corr h_env h_envR h_store h_refl h_scope h_eval
              obtain ⟨ds', h_evals, h_corrs⟩ := ih_f2
              exact ⟨d_c :: ds', .cons hd_c h_evals, .cons hcorr h_corrs⟩
          obtain ⟨ds_c, h_evals_c, h_corrs⟩ := h_args_c
          -- Step 3: DenotableScoped for each arg
          have h_ds_scoped : ∀ d ∈ ds_c, DenotableScoped d σ := by
            intro d hd
            have : ∀ (aes' : List AExp) (ds' : List Denotable),
                List.Forall₂ (fun ae d => evalAtomic ae ρ σ = some d) aes' ds' →
                d ∈ ds' → DenotableScoped d σ := by
              intro aes' ds' h_f2 hd'
              induction h_f2 with
              | nil => exact nomatch hd'
              | cons h_eval _ ih =>
                cases hd' with
                | head => exact evalAtomic_scoped h_eval h_scope h_ss
                | tail _ h => exact ih h
            exact this aes ds_c h_evals_c hd
          -- Step 4: EnvScoped for lambda env (from evalAtomic_scoped on closure)
          have h_scope_lam : EnvScoped ρ_lam.env σ := evalAtomic_scoped hd_f h_scope h_ss
          -- Step 5: Pick N fresh concrete addresses + build foldl correspondence
          have h_len_ds : ds_c.length = ρ_lam.params.length := by
            have := (List.Forall₂.length_eq h_evals_c).symm; omega
          have h_tfresh_mem : ∀ (x : Var), x ∈ ρ_lam.params →
              tσ (.val ⟨x, ⟨l_enc :: t.tk, t.tmk⟩⟩) = none := by
            intro x hx
            obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
            exact h_tfresh i hi
          obtain ⟨as_v, h_len_as, h_fresh_as, h_distinct, h_σ_mono,
                  α', h_env', h_envR', h_store', h_refl', h_ext, h_ss', h_scope'⟩ :=
            sound_foldl_extend h_env_lam h_envR_lam h_store h_refl h_ss h_scope_lam
              ρ_lam.params ds_c tds h_corrs h_tfresh_mem h_ds_scoped
              ρ_lam.params_nodup h_len_ds
          -- Step 6: IH on body
          obtain ⟨ih_e, _, _, _, _⟩ := ih n_body (by omega)
          obtain ⟨α'', v_c, σ_c', h_body_c, hval_c, hstore_c, hrefl_c, hext_c, hss_c, hvs_c⟩ :=
            ih_e ρ_lam.body _ _ _ _ tσ' h_body_deriv α' _ _
              h_env' h_envR' h_store' h_refl' h_scope' h_ss'
          -- Step 7: Assemble
          exact ⟨α'', v_c, σ_c',
            .eval_funApp_clos hd_f (by omega) h_evals_c h_fresh_as
              h_distinct (by omega) rfl rfl h_body_c,
            hval_c, hstore_c, hrefl_c,
            h_ext.trans hext_c h_σ_mono,
            hss_c, hvs_c⟩
      | eval_funApp_kont h_f h_ae h_tmk_eq h_apply_ih h_thandle_eq h_handle_ih =>
        rename_i f_ae hdl_t tρ_h a_κ ae_arg d_t _tmk n1 v_mid tσ_mid _t_h n2
        subst h_tmk_eq; subst h_thandle_eq
        -- Reverse atomic for f (kontClosure) and ae (denotable)
        obtain ⟨d_f, hd_f, hcorr_f⟩ := evalTAtomic_corr h_env h_envR h_store h_refl h_scope h_f
        obtain ⟨d_a, hd_a, hcorr_a⟩ := evalTAtomic_corr h_env h_envR h_store h_refl h_scope h_ae
        -- Decompose kontClosure correspondence
        cases hcorr_f with
        | kontClosure h_env_h h_envR_h h_kont_corr =>
          rename_i ρ_h_c κ_c
          have h_f_scoped := evalAtomic_scoped hd_f h_scope h_ss
          -- h_f_scoped : EnvScoped ρ_h_c σ ∧ KontScoped κ_c σ
          -- IH apply
          obtain ⟨_, _, _, _, ih_apply⟩ := ih n1 (by omega)
          obtain ⟨α₁, v₁, σ₁, h_apply', hval₁, hstore₁, hrefl₁, hext₁, hss₁, hvs₁⟩ :=
            ih_apply a_κ d_t tσ _ v_mid tσ_mid h_apply_ih α σ κ_c d_a
              h_kont_corr hcorr_a (evalAtomic_scoped hd_a h_scope h_ss)
              h_store h_refl h_ss h_f_scoped.2
          -- Transfer env for handle IH
          have h_env₁ := h_env_h.of_alpha_scoped hext₁ h_f_scoped.1
          have h_envR₁ := h_envR_h.of_alpha_extends hext₁ h_f_scoped.1
          -- IH handle
          obtain ⟨_, _, _, ih_hv, _⟩ := ih n2 (by omega)
          obtain ⟨α₂, v₂, σ₂, h_handle', hval₂, hstore₂, hrefl₂, hext₂, hss₂, hvs₂⟩ :=
            ih_hv l_enc hdl_t tρ_h v_mid tσ_mid _ tv tσ' h_handle_ih α₁ ρ_h_c σ₁ v₁
              h_env₁ h_envR₁ hval₁ hvs₁ hstore₁ hrefl₁
              (fun x a hxa => by
                have := h_f_scoped.1 x a hxa
                rw [Option.ne_none_iff_exists'] at this ⊢
                obtain ⟨d', hd'⟩ := this
                exact ⟨d', eval_apply_store_mono (apply_kontN_to h_apply') a d' hd'⟩)
              hss₁
          exact ⟨α₂, v₂, σ₂, .eval_funApp_kont hd_f hd_a h_apply' h_handle',
                 hval₂, hstore₂, hrefl₂,
                 hext₁.trans hext₂ (fun a ha => by
                   rw [Option.ne_none_iff_exists'] at ha ⊢
                   obtain ⟨d', hd'⟩ := ha
                   exact ⟨d', eval_apply_store_mono (apply_kontN_to h_apply') a d' hd'⟩),
                 hss₂, hvs₂⟩
      | eval_match h_ae h_d h_br h_xs h_body =>
        subst h_d; subst h_xs
        rename_i n_sub
        obtain ⟨d, hd, hcorr⟩ := evalTAtomic_corr h_env h_envR h_store h_refl h_scope h_ae
        cases hcorr with
        | conLabel =>
          obtain ⟨ih_e, _, _, _, _⟩ := ih n_sub (by omega)
          obtain ⟨α', v, σ', h_body', hval, hstore', hrefl', hext, hss', hvs'⟩ :=
            ih_e _ tρ tσ t _ tσ' h_body α ρ σ h_env h_envR h_store h_refl h_scope h_ss
          exact ⟨α', v, σ', .eval_match hd rfl h_br rfl h_body', hval, hstore', hrefl', hext, hss', hvs'⟩
      | eval_match_succ h_ae h_br h_inner h_xs_eq h_afresh h_body_tfresh h_tσnew h_tρnew h_body =>
        -- eval_match_succ: reverse atomic → store lookup → allocate → IH
        -- Same pattern as handle_return but with succVal decomposition
        -- eval_match_succ: reverse atomic → store lookup → allocate → IH
        subst h_xs_eq; subst h_afresh; subst h_tσnew; subst h_tρnew
        -- After subst, inaccessibles: ae✝(AExp) a_inner✝(TVAddr) bs✝(Branches) ae_m(Exp=body) a_inner_t(TDenotable) bs_m(Var=x_bind) n_body(ℕ)
        rename_i ae_t a_inner_t bs_t e_body d_inner_t x_bind n_body
        obtain ⟨d_ae, hd_ae, hcorr_ae⟩ := evalTAtomic_corr h_env h_envR h_store h_refl h_scope h_ae
        cases hcorr_ae with
        | succVal =>
          rename_i a_c
          have h_σ_ac_ne := evalAtomic_succVal_scoped hd_ae h_scope h_ss
          obtain ⟨d_inner_c, hσ_inner⟩ := Option.ne_none_iff_exists'.mp h_σ_ac_ne
          obtain ⟨td_inner', htσ_inner', hcorr_inner⟩ := h_store a_c d_inner_c hσ_inner
          rw [h_inner] at htσ_inner'; injection htσ_inner' with htσ_inner'; cases htσ_inner'
          obtain ⟨a_fresh_c, h_fresh_c, h_store', h_refl', h_ext_α, _⟩ :=
            sound_extend_val h_store h_refl h_ss h_body_tfresh hcorr_inner (h_ss _ _ hσ_inner)
          obtain ⟨h_env', h_envR', h_scope'⟩ :=
            sound_env_extend h_env h_envR h_scope h_fresh_c h_ext_α
          obtain ⟨ih_e, _, _, _, _⟩ := ih n_body (by omega)
          obtain ⟨α'', v_c, σ_c', h_body_c, hval_c, hstore_c, hrefl_c, hext_c, hss_c, hvs_c⟩ :=
            ih_e e_body _ _ t _ tσ' h_body _ _ _
              h_env' h_envR' h_store' h_refl' h_scope'
              (h_ss.extend_val (denotableScoped_mono (h_ss _ _ hσ_inner)
                (fun a ha => by simp [Store.extend]; split <;> [exact nofun; exact ha])))
          exact ⟨α'', v_c, σ_c',
            .eval_match_succ hd_ae h_br hσ_inner h_fresh_c rfl rfl h_body_c,
            hval_c, hstore_c, hrefl_c,
            h_ext_α.trans hext_c (fun a ha => by
              simp [Store.extend]; split <;> [exact nofun; exact ha]),
            hss_c, hvs_c⟩
      | eval_handler h_tbody h_body h_handle =>
        rename_i n1 e_body tv₁ tσ₁ n2 l_h hdl
        subst h_tbody
        -- IH for body
        obtain ⟨ih_e, _, _, _, _⟩ := ih n1 (by omega)
        obtain ⟨α₁, v₁, σ₁, h_body', hval₁, hstore₁, hrefl₁, hext₁, hss₁, hvs₁⟩ :=
          ih_e e_body tρ tσ _ tv₁ tσ₁ h_body α ρ σ h_env h_envR h_store h_refl h_scope h_ss
        -- Transfer env correspondence for handle IH
        have h_env₁ := h_env.of_alpha_extends hext₁ h_scope
        have h_envR₁ := h_envR.of_alpha_extends hext₁ h_scope
        have h_scope₁ : EnvScoped ρ σ₁ := fun x a hρ => by
          have := h_scope x a hρ
          rw [Option.ne_none_iff_exists'] at this ⊢
          obtain ⟨d, hd⟩ := this
          exact ⟨d, eval_store_mono (eval_expN_to h_body') a d hd⟩
        -- hss₁ already obtained from IH
        -- IH for handle
        obtain ⟨_, _, _, ih_hv, _⟩ := ih n2 (by omega)
        obtain ⟨α₂, v₂, σ₂, h_handle', hval₂, hstore₂, hrefl₂, hext₂, hss₂, hvs₂⟩ :=
          ih_hv l_h hdl tρ tv₁ tσ₁ t tv tσ' h_handle α₁ ρ σ₁ v₁
            h_env₁ h_envR₁ hval₁ hvs₁ hstore₁ hrefl₁ h_scope₁ hss₁
        exact ⟨α₂, v₂, σ₂, .eval_handler h_body' h_handle',
               hval₂, hstore₂, hrefl₂,
               hext₁.trans hext₂ (fun a ha => by
                 rw [Option.ne_none_iff_exists'] at ha ⊢
                 obtain ⟨d, hd⟩ := ha
                 exact ⟨d, eval_store_mono (eval_expN_to h_body') a d hd⟩),
               hss₂, hvs₂⟩
    -----------------------------------------------------------------------
    -- P_continue
    -----------------------------------------------------------------------
    · intro l_enc tfc t tv tσ tv' tσ' h_eval α σ f v
        h_frame h_val h_vscoped h_store h_refl h_scope h_ss
      cases h_eval with
      | continue_let h_teq h_tfresh h_body =>
        rename_i y n_body e_b tρ_f d_t
        subst h_teq
        -- Decompose FrameCorr and ValueCorr
        obtain ⟨clo_c, rfl, h_clo⟩ : ∃ clo, f = .letFrame clo ∧ ClosureCorr α clo ⟨[y], e_b, tρ_f, List.nodup_singleton _⟩ := by
          cases h_frame with | letFrame h => exact ⟨_, rfl, h⟩
        obtain ⟨d_c, rfl, h_dcorr⟩ : ∃ d, v = .den d ∧ DenotableCorr α tσ d d_t := by
          cases h_val with | den h => exact ⟨_, rfl, h⟩
        -- h_clo gives params/body/env correspondence
        -- Allocate fresh address for y, use sound_extend_val, call IH
        -- Decompose FrameCorr and ValueCorr
        cases h_frame with | letFrame h_clo =>
        cases h_val with | den h_dcorr =>
        -- h_teq is the freshness hypothesis from TFreshContinueFrameN.continue_let
        -- Allocate fresh address using sound_extend_val
        obtain ⟨a_v, h_fresh, h_store', h_refl', h_ext_α, _⟩ :=
          sound_extend_val h_store h_refl h_ss h_tfresh (h_dcorr) h_vscoped
        -- Call IH for body
        obtain ⟨ih_e, _, _, _, _⟩ := ih n_body (by omega)
        obtain ⟨h_env', h_envR', h_scope'⟩ :=
          sound_env_extend h_clo.env_corr h_clo.env_reflects h_scope h_fresh h_ext_α
        obtain ⟨α'', v', σ'', h_body', hval', hstore'', hrefl'', hext', hss', hvs'⟩ :=
          ih_e _ _ _ t _ tσ' h_body _ _ _
            h_env' h_envR' h_store' h_refl' h_scope'
            (h_ss.extend_val (denotableScoped_mono h_vscoped
              (fun a ha => by simp [Store.extend]; split <;> [exact nofun; exact ha])))
        -- Show clo_c matches the expected shape
        have h_clo_eq : clo_c = ⟨[y], e_b, clo_c.env, List.nodup_singleton _⟩ := by
          cases clo_c; simp only [Closure.mk.injEq]; exact ⟨h_clo.params_eq, h_clo.body_eq, trivial⟩
        rw [h_clo_eq]
        exact ⟨α'', v', σ'', .continue_let h_fresh rfl h_body',
               hval', hstore'', hrefl'',
               h_ext_α.trans hext' (fun a ha => by
                 simp [Store.extend]; split <;> [exact nofun; exact ha]),
               hss', hvs'⟩
      | continue_op h_teq h_tσ h_kfresh h_kaddr =>
        subst h_kaddr; subst h_tσ; subst h_teq
        -- Decompose frame and value
        cases h_frame with | letFrame h_clo =>
        cases h_val with | suspended h_len h_addrs h_kont_corr =>
        -- Concrete: continue_op just prepends frame to kont, no store change
        -- Timestamped: extends tσ with kont addr
        -- StoreCorr/StoreReflects preserved (only kont addr added)
        exact ⟨α, .suspended _ _ (.letFrame _ :: _), σ, .continue_op,
               .suspended h_len h_addrs
                 (.cons (TStore.extend_same _ _ _) (.letFrame h_clo)
                   (h_kont_corr.extend_kont _ _ h_kfresh)),
               h_store.extend_kont h_ss _ _ h_kfresh,
               h_refl.extend_kont _ _,
               AlphaExtends.refl, h_ss,
               ⟨h_vscoped.1, fun f hf => by cases hf with
                | head => exact h_scope
                | tail _ h => exact h_vscoped.2 f h⟩⟩
    -----------------------------------------------------------------------
    -- P_handle
    -----------------------------------------------------------------------
    · intro l_enc hdl tρ tv tσ t tv' tσ' h_eval α ρ σ v
        h_env h_envR h_val h_vscoped h_store h_refl h_scope h_ss
      cases h_eval with
      | handle_return h_ret h_anew_eq h_tfresh h_body =>
        subst h_anew_eq
        rename_i x_ret e_ret n_body d_t
        cases h_val with | den h_dcorr =>
        rename_i d_c
        obtain ⟨a_v, h_fresh, h_store', h_refl', h_ext_α, _⟩ :=
          sound_extend_val h_store h_refl h_ss h_tfresh h_dcorr h_vscoped
        obtain ⟨ih_e, _, _, _, _⟩ := ih n_body (by omega)
        obtain ⟨h_env', h_envR', h_scope'⟩ :=
          sound_env_extend h_env h_envR h_scope h_fresh h_ext_α
        obtain ⟨α'', v', σ'', h_body', hval', hstore'', hrefl'', hext', hss', hvs'⟩ :=
          ih_e e_ret _ _ t _ tσ' h_body _ (ρ.extend x_ret a_v) (σ.extend a_v d_c)
            h_env' h_envR' h_store' h_refl' h_scope'
            (h_ss.extend_val (denotableScoped_mono h_vscoped
              (fun a ha => by simp [Store.extend]; split <;> [exact nofun; exact ha])))
        exact ⟨α'', v', σ'', .handle_return h_ret h_fresh rfl h_body',
               hval', hstore'', hrefl'',
               h_ext_α.trans hext' (fun a ha => by
                 simp [Store.extend]; split <;> [exact nofun; exact ha]),
               hss', hvs'⟩
      | handle_op h_op h_ax_eq h_ar_eq h_ax_fresh h_ar_fresh h_ne h_as_eq h_arg_lookup h_dk_eq h_sop_eq h_body_ih =>
        subst h_ax_eq; subst h_ar_eq; subst h_dk_eq; subst h_sop_eq; subst h_as_eq
        rename_i op_name x_op e_op a_arg_t a_κ_t n_body d_arg_t
        cases h_val with | suspended h_len h_addrs h_kont_corr =>
        rename_i as_v_c κ_c
        -- Step 1: Extract a_arg_c from as_v_c (length 1) and get denotable
        obtain ⟨a_arg_c, rfl⟩ := List.length_eq_one_iff.mp h_len
        have h_α_arg : α a_arg_c = a_arg_t := by
          have := h_addrs 0 (by simp) (by simp); simp at this; exact this.symm
        have h_σ_arg_ne := h_vscoped.1 a_arg_c (List.mem_singleton.mpr rfl)
        obtain ⟨d_arg_c, h_σ_arg⟩ := Option.ne_none_iff_exists'.mp h_σ_arg_ne
        obtain ⟨td_arg', h_tσ_arg', h_corr_arg⟩ := h_store a_arg_c d_arg_c h_σ_arg
        rw [h_α_arg] at h_tσ_arg'; rw [h_arg_lookup] at h_tσ_arg'
        injection h_tσ_arg' with h_tσ_arg'; cases h_tσ_arg'
        -- Step 2: First extend via sound_extend_val (arg copy)
        obtain ⟨a_v', h_fresh_v', h_store₁, h_refl₁, h_ext₁, h_inj₁⟩ :=
          sound_extend_val h_store h_refl h_ss h_ax_fresh h_corr_arg (h_ss _ _ h_σ_arg)
        -- Step 3: Transfer invariants to extended stores
        have h_env₁ := h_env.of_alpha_extends h_ext₁ h_scope
        have h_envR₁ := h_envR.of_alpha_extends h_ext₁ h_scope
        have h_ss₁ : StoreScoped (σ.extend a_v' d_arg_c) :=
          h_ss.extend_val (denotableScoped_mono (h_ss _ _ h_σ_arg)
            (fun a ha => by simp [Store.extend]; split <;> [exact nofun; exact ha]))
        -- Step 4: h_ar_fresh at extended tσ₁
        have h_ar_fresh₁ : (tσ.extend (.val ⟨x_op, t⟩) (.denotable d_arg_t)) (.val ⟨"resume", t⟩) = none := by
          rw [TStore.extend_ne _ _ _ _ (fun heq => h_ne (TAddr.val.inj heq).symm)]
          exact h_ar_fresh
        -- Step 5: KontCorr val-extend transfer
        have h_kont₁ : KontCorr (fun a => if a = a_v' then ⟨x_op, t⟩ else α a)
            (tσ.extend (.val ⟨x_op, t⟩) (.denotable d_arg_t)) κ_c a_κ_t :=
          h_kont_corr.of_alpha_tσ_scoped (σ_c := σ) h_ext₁
            (fun addr ha => by
              show (tσ.extend (.val ⟨x_op, t⟩) (.denotable d_arg_t)) addr = tσ addr
              exact TStore.extend_ne _ _ _ _ (fun heq => by rw [heq] at ha; exact absurd h_ax_fresh ha))
            h_vscoped.2
        -- Step 6: kontClosure DenotableCorr
        have h_dcorr_kont : DenotableCorr (fun a => if a = a_v' then ⟨x_op, t⟩ else α a)
            (tσ.extend (.val ⟨x_op, t⟩) (.denotable d_arg_t))
            (Denotable.kontClosure hdl ρ κ_c) (.kontClosure hdl tρ a_κ_t) :=
          .kontClosure h_env₁ h_envR₁ h_kont₁
        -- Step 7: EnvScoped mono
        have h_scope₁ : EnvScoped ρ (σ.extend a_v' d_arg_c) := fun x a hxa => by
          have := h_scope x a hxa; rw [Option.ne_none_iff_exists'] at this ⊢
          obtain ⟨d, hd⟩ := this; exact ⟨d, by simp only [Store.extend]; split <;> simp_all⟩
        -- Step 8: DenotableScoped for kontClosure in σ₁
        have h_dscoped_kont : DenotableScoped (Denotable.kontClosure hdl ρ κ_c) (σ.extend a_v' d_arg_c) :=
          ⟨h_scope₁, fun f hf => by
            have h_fs := h_vscoped.2 f hf
            have h_mono : ∀ a, σ a ≠ none → (σ.extend a_v' d_arg_c) a ≠ none :=
              fun a ha => by simp only [Store.extend]; split <;> [exact nofun; exact ha]
            cases f with
            | letFrame clo => exact envScoped_mono h_fs h_mono
            | handlerFrame _ ρ_h => exact envScoped_mono h_fs h_mono⟩
        -- Step 9: Second extend via sound_extend_val
        obtain ⟨a_vk, h_fresh_vk, h_store₂, h_refl₂, h_ext₂, _⟩ :=
          sound_extend_val h_store₁ h_refl₁ h_ss₁ h_ar_fresh₁ h_dcorr_kont h_dscoped_kont
        -- Step 10: Env extends using EnvCorr.extend / EnvReflects.extend
        -- α₂ maps a_v' → ⟨x_op, t⟩ and a_vk → ⟨"resume", t⟩
        -- We need EnvCorr/EnvReflects at α₂ for (ρ.extend x_op a_v').extend "resume" a_vk
        -- Use the existing h_env₁/h_envR₁ transferred through h_ext₂, then extend twice
        have h_env₂ := (h_env₁.of_alpha_extends h_ext₂
          (fun x a hxa => by
            have := h_scope₁ x a hxa; rw [Option.ne_none_iff_exists'] at this
            obtain ⟨d, hd⟩ := this; exact fun h => absurd hd (by rw [h]; exact nofun)))
        have h_envR₂ := (h_envR₁.of_alpha_extends h_ext₂
          (fun x a hxa => by
            have := h_scope₁ x a hxa; rw [Option.ne_none_iff_exists'] at this
            obtain ⟨d, hd⟩ := this; exact fun h => absurd hd (by rw [h]; exact nofun)))
        -- Now extend env twice
        -- First: x_op → a_v'. α₂ a_v' should be ⟨x_op, t⟩
        -- α₂ = fun a => if a = a_vk then ⟨"resume", t⟩ else if a = a_v' then ⟨x_op, t⟩ else α a
        -- So α₂ a_v' = if a_v' = a_vk then ... else ⟨x_op, t⟩
        -- If a_v' ≠ a_vk (which follows from distinctness): α₂ a_v' = ⟨x_op, t⟩ ✓
        have h_ne_c : a_v' ≠ a_vk := by
          intro heq; subst heq; simp [Store.extend] at h_fresh_vk
        -- The TEnv extend uses ⟨x_op, t⟩ which matches α₂ a_v'
        -- EnvCorr.extend needs α a_v' = ta, but α₂ a_v' = ⟨x_op, t⟩ only if a_v' ≠ a_vk
        -- EnvCorr/EnvReflects for extended env
        have h_env_xr : EnvCorr
            (fun a => if a = a_vk then ⟨"resume", t⟩ else if a = a_v' then ⟨x_op, t⟩ else α a)
            ((ρ.extend x_op a_v').extend "resume" a_vk)
            ((tρ.extend x_op ⟨x_op, t⟩).extend "resume" ⟨"resume", t⟩) := by
          convert (h_env₂.extend x_op a_v').extend "resume" a_vk using 1
          simp [TEnv.extend, if_neg h_ne_c]
        have h_envR_xr : EnvReflects
            (fun a => if a = a_vk then ⟨"resume", t⟩ else if a = a_v' then ⟨x_op, t⟩ else α a)
            ((ρ.extend x_op a_v').extend "resume" a_vk)
            ((tρ.extend x_op ⟨x_op, t⟩).extend "resume" ⟨"resume", t⟩) := by
          convert (h_envR₂.extend x_op a_v').extend "resume" a_vk using 1
          simp [TEnv.extend, if_neg h_ne_c]
        -- EnvScoped for extended env in σ₂
        have h_scope₂ : EnvScoped ((ρ.extend x_op a_v').extend "resume" a_vk)
            ((σ.extend a_v' d_arg_c).extend a_vk (Denotable.kontClosure hdl ρ κ_c)) := by
          intro x a hxa
          show ((σ.extend a_v' d_arg_c).extend a_vk _) a ≠ none
          simp only [Env.extend] at hxa; split at hxa
          · injection hxa with hxa; subst hxa; simp [Store.extend]
          · split at hxa
            · injection hxa with hxa; subst hxa
              simp only [Store.extend]; split
              · exact nofun
              · simp []
            · have := h_scope₁ x a hxa
              simp only [Store.extend]; split <;> [exact nofun; exact this]
        -- StoreScoped for σ₂
        have h_mono₂ : ∀ a, (σ.extend a_v' d_arg_c) a ≠ none →
            ((σ.extend a_v' d_arg_c).extend a_vk (Denotable.kontClosure hdl ρ κ_c)) a ≠ none := by
          intro a ha
          show (σ.extend a_v' d_arg_c).extend a_vk _ a ≠ none
          simp only [Store.extend]; split <;> [exact nofun; exact ha]
        have h_ss₂ : StoreScoped ((σ.extend a_v' d_arg_c).extend a_vk (Denotable.kontClosure hdl ρ κ_c)) :=
          h_ss₁.extend_val (denotableScoped_mono h_dscoped_kont h_mono₂)
        -- Step 11: IH
        obtain ⟨ih_e, _, _, _, _⟩ := ih n_body (by omega)
        obtain ⟨α'', v', σ'', h_body', hval', hstore'', hrefl'', hext', hss'', hvs'⟩ :=
          ih_e e_op _ _ t _ tσ' h_body_ih _ _ _
            h_env_xr h_envR_xr h_store₂ h_refl₂ h_scope₂ h_ss₂
        -- Step 12: Assemble
        exact ⟨α'', v', σ'',
          .handle_op h_op h_fresh_v' (by simp only [Store.extend] at h_fresh_vk; split at h_fresh_vk <;> [exact absurd h_fresh_vk nofun; exact h_fresh_vk]) h_ne_c h_σ_arg rfl h_body',
          hval', hstore'', hrefl'',
          h_ext₁.trans (h_ext₂.trans hext'
            (fun a ha => by
              show ((σ.extend a_v' d_arg_c).extend a_vk _) a ≠ none
              simp only [Store.extend]; split <;> [exact nofun; exact ha]))
            (fun a ha => by
              show (σ.extend a_v' d_arg_c) a ≠ none
              simp only [Store.extend]; split <;> [exact nofun; exact ha]),
          hss'', hvs'⟩
      | handle_capture_op h_hasop h_ψ h_aκ h_kfresh h_tσ' =>
        subst h_ψ; subst h_aκ; subst h_tσ'
        -- Decompose value: must be suspended
        cases h_val with | suspended h_len h_addrs h_kont_corr =>
        -- Concrete: handle_capture_op prepends handlerFrame to kont
        exact ⟨α, .suspended _ _ (.handlerFrame _ _ :: _), σ, .handle_capture_op h_hasop rfl,
               .suspended h_len h_addrs
                 (.cons (TStore.extend_same _ _ _) (.handlerFrame h_env h_envR)
                   (h_kont_corr.extend_kont _ _ h_kfresh)),
               h_store.extend_kont h_ss _ _ h_kfresh,
               h_refl.extend_kont _ _,
               AlphaExtends.refl, h_ss,
               ⟨h_vscoped.1, fun f hf => by cases hf with
                | head => exact h_scope
                | tail _ h => exact h_vscoped.2 f h⟩⟩
    -----------------------------------------------------------------------
    -- P_apply
    -----------------------------------------------------------------------
    · intro ta_κ td tσ tmk tv tσ' h_eval α σ κ d
        h_kont h_den h_dscoped h_store h_refl h_ss h_kscoped
      cases h_eval with
      | apply_continue =>
        cases h_kont
        exact ⟨α, .den d, σ, .apply_continue, .den h_den, h_store, h_refl, AlphaExtends.refl, h_ss, h_dscoped⟩
      | apply_restore h_lookup h_content h_apply h_tmk h_cont =>
        rename_i n1 a_next tv₁ tσ₁ t_rest n2 clo_t a_κ
        -- Decompose KontCorr: κ = frame :: rest with frame matching a_κ
        -- KontCorr.cons fields: a_next_kc (Option TKAddr), frame_c (Frame), κ_rest (Kont)
        cases h_kont with
        | cons h_kont_lookup h_frame_corr h_kont_rest =>
          -- From LSP: h_kont_rest : KontCorr α tσ κ_rest a_next_kc
          --           h_frame_corr : FrameCorr α frame_c a_κ.frame.content
          --           h_kont_lookup : tσ (.kont a_κ) = some (.kontLink a_next_kc)
          -- Goal: ApplyKontN (frame_c :: κ_rest) d σ ...
          -- Match kont lookups
          rw [h_kont_lookup] at h_lookup; injection h_lookup with h_lookup
          cases h_lookup -- a_next_kc = a_next
          rw [h_content] at h_frame_corr
          -- IH apply on the rest of the chain
          obtain ⟨_, _, _, _, ih_apply⟩ := ih n1 (by omega)
          obtain ⟨α₁, v₁, σ₁, h_apply', hval₁, hstore₁, hrefl₁, hext₁, hss₁, hvs₁⟩ :=
            ih_apply a_next td tσ tmk tv₁ tσ₁ h_apply α σ _ d
              h_kont_rest h_den h_dscoped h_store h_refl h_ss
              (fun f hf => h_kscoped f (.tail _ hf))
          -- frame✝ must be .letFrame by h_frame_corr; cases to get the concrete closure
          cases h_frame_corr with
          | letFrame h_clo =>
            have h_clo₁ := h_clo.of_alpha_scoped hext₁ (h_kscoped _ (.head _))
            obtain ⟨_, _, ih_co, _, _⟩ := ih n2 (by omega)
            obtain ⟨α₂, v₂, σ₂, h_cont', hval₂, hstore₂, hrefl₂, hext₂, hss₂, hvs₂⟩ :=
              ih_co _ (.letFrame clo_t) _ tv₁ tσ₁ tv tσ' h_cont
                α₁ σ₁ (.letFrame _) v₁ (.letFrame h_clo₁) hval₁ hvs₁ hstore₁ hrefl₁
                (fun x a hxa => by
                  have := h_kscoped _ (.head _) x a hxa
                  rw [Option.ne_none_iff_exists'] at this ⊢
                  obtain ⟨d', hd'⟩ := this
                  exact ⟨d', eval_apply_store_mono (apply_kontN_to h_apply') a d' hd'⟩) hss₁
            exact ⟨α₂, v₂, σ₂, .apply_restore h_apply' h_cont',
                   hval₂, hstore₂, hrefl₂,
                   hext₁.trans hext₂ (fun a ha => by
                     rw [Option.ne_none_iff_exists'] at ha ⊢
                     obtain ⟨d', hd'⟩ := ha
                     exact ⟨d', eval_apply_store_mono (apply_kontN_to h_apply') a d' hd'⟩),
                   hss₂, hvs₂⟩
      | apply_restore_handle h_lookup h_content h_tmk_eq h_apply_ih h_trest_eq h_handle_ih =>
        rename_i _tmk' n1 _a_next _v' _σ₁ _t_rest n2 _hdl _tρ_h _a_κ
        cases h_kont with
        | cons h_kont_lookup h_frame_corr h_kont_rest =>
          rw [h_kont_lookup] at h_lookup; injection h_lookup with h_lookup
          cases h_lookup
          rw [h_content] at h_frame_corr
          obtain ⟨_, _, _, _, ih_apply⟩ := ih n1 (by omega)
          obtain ⟨α₁, v₁, σ₁, h_apply', hval₁, hstore₁, hrefl₁, hext₁, hss₁, hvs₁⟩ :=
            ih_apply _ td tσ _ _ _ h_apply_ih α σ _ d
              h_kont_rest h_den h_dscoped h_store h_refl h_ss
              (fun f hf => h_kscoped f (.tail _ hf))
          cases h_frame_corr with
          | handlerFrame h_env_hdl h_envR_hdl =>
            have h_env₁ := h_env_hdl.of_alpha_scoped hext₁ (h_kscoped _ (.head _))
            have h_envR₁ := h_envR_hdl.of_alpha_extends hext₁ (h_kscoped _ (.head _))
            obtain ⟨_, _, _, ih_hv, _⟩ := ih n2 (by omega)
            obtain ⟨α₂, v₂, σ₂, h_handle', hval₂, hstore₂, hrefl₂, hext₂, hss₂, hvs₂⟩ :=
              ih_hv _ _ _ _ _ _ _ _ h_handle_ih α₁ _ σ₁ v₁
                h_env₁ h_envR₁ hval₁ hvs₁ hstore₁ hrefl₁
                (fun x a hxa => by
                  have := h_kscoped _ (.head _) x a hxa
                  rw [Option.ne_none_iff_exists'] at this ⊢
                  obtain ⟨d', hd'⟩ := this
                  exact ⟨d', eval_apply_store_mono (apply_kontN_to h_apply') a d' hd'⟩) hss₁
            exact ⟨α₂, v₂, σ₂, .apply_restore_handle h_apply' h_handle',
                   hval₂, hstore₂, hrefl₂,
                   hext₁.trans hext₂ (fun a ha => by
                     rw [Option.ne_none_iff_exists'] at ha ⊢
                     obtain ⟨d', hd'⟩ := ha
                     exact ⟨d', eval_apply_store_mono (apply_kontN_to h_apply') a d' hd'⟩),
                   hss₂, hvs₂⟩

/-! ## Top-level corollary: Timestamp Soundness (Theorem 1)

  (e, [], [], t₀) ⇓et_f (v_t, σ_t)  ⟹  (e, [], []) ⇓e (v, σ)

  If an expression evaluates under the fresh-guarded timestamped semantics
  from empty initial state, it also evaluates under the concrete semantics.
  Values and stores correspond under some witness mapping α. -/

theorem fresh_to_concrete_from_empty
    {e : Exp} {t : Time} {tv : TValue} {tσ' : TStore}
    (h_eval : TFreshEvalExp e TEnv.empty TStore.empty t tv tσ') :
    ∃ v σ', EvalExp e Env.empty Store.empty v σ' := by
  obtain ⟨n, hn⟩ := teval_exp_to_N h_eval
  obtain ⟨_, v, σ', h_eval_c, _, _, _, _, _, _⟩ :=
    (fresh_to_concrete n).1 e _ _ t _ tσ' hn
      (fun _ => default) Env.empty Store.empty
      EnvCorr.empty EnvReflects.empty StoreCorr.empty StoreReflects.empty
      EnvScoped.empty StoreScoped.empty
  exact ⟨v, σ', eval_expN_to h_eval_c⟩

end DMCFA
