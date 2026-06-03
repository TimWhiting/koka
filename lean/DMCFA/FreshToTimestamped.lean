/-
  TFresh → T: Every fresh-guarded timestamped derivation is also a (plain) timestamped one.

  This is trivial — the plain timestamped semantics has strictly weaker premises (no freshness checks).
  Combined with the Freshness proof (T → TFresh), this gives T ↔ TFresh.
-/

import DMCFA.FreshSemantics
import DMCFA.TimestampedSemantics

namespace DMCFA

/-! ## ⇓et_f ⟹ ⇓et (trivial: drop freshness premises)

  Every fresh-guarded derivation is a timestamped derivation,
  since the fresh-guarded rules are strictly stronger. -/

mutual

theorem strict_exp_to_naive {e : Exp} {ρ : TEnv} {σ : TStore} {t : Time}
    {v : TValue} {σ' : TStore}
    (h : TFreshEvalExp e ρ σ t v σ') : TEvalExp e ρ σ t v σ' :=
  match h with
  | .eval_let h1 h2 => .eval_let (strict_cexp_to_naive h1) (strict_cont_to_naive h2)
  | .eval_tail h1 => .eval_tail (strict_cexp_to_naive h1)

theorem strict_cexp_to_naive {ce : CExp} {ρ : TEnv} {σ : TStore} {t : Time}
    {l : Label} {v : TValue} {σ' : TStore}
    (h : TFreshEvalCExp ce ρ σ t l v σ') : TEvalCExp ce ρ σ t l v σ' :=
  match h with
  | .eval_atomic h1 => .eval_atomic h1
  | .eval_funApp_clos h1 h2 h3 h4 _hfresh h5 h6 h7 =>
    .eval_funApp_clos h1 h2 h3 h4 h5 h6 (strict_exp_to_naive h7)
  | .eval_opApp h1 => .eval_opApp h1
  | .eval_funApp_kont h1 h2 h3 h4 h5 h6 =>
    .eval_funApp_kont h1 h2 h3 (strict_apply_to_naive h4) h5 (strict_handle_to_naive h6)
  | .eval_fun h1 _hfresh h2 h3 h4 => .eval_fun h1 h2 h3 h4
  | .eval_match h1 h2 h3 h4 h5 => .eval_match h1 h2 h3 h4 (strict_exp_to_naive h5)
  | .eval_match_succ h1 h2 h3 h4 h5 _hfresh h6 h7 h8 =>
    .eval_match_succ h1 h2 h3 h4 h5 h6 h7 (strict_exp_to_naive h8)
  | .eval_handler h1 h2 h3 => .eval_handler h1 (strict_exp_to_naive h2) (strict_handle_to_naive h3)

theorem strict_cont_to_naive {l : Label} {fc : TFrameContent} {t : Time}
    {v : TValue} {σ : TStore} {v' : TValue} {σ' : TStore}
    (h : TFreshContinueFrame l fc t v σ v' σ') : TContinueFrame l fc t v σ v' σ' :=
  match h with
  | .continue_let h1 _hfresh h2 => .continue_let h1 (strict_exp_to_naive h2)
  | .continue_op h1 h2 _hfresh h3 => .continue_op h1 h2 h3

theorem strict_handle_to_naive {l : Label} {h : Handler} {ρ : TEnv}
    {v : TValue} {σ : TStore} {t : Time} {v' : TValue} {σ' : TStore}
    (hh : TFreshHandleValue l h ρ v σ t v' σ') : THandleValue l h ρ v σ t v' σ' :=
  match hh with
  | .handle_return h1 h2 _hfresh h3 => .handle_return h1 h2 (strict_exp_to_naive h3)
  | .handle_op h1 h2 h3 _hfresh1 _hfresh2 _hne h4 h5 h6 h7 h8 =>
    .handle_op h1 h2 h3 h4 h5 h6 h7 (strict_exp_to_naive h8)
  | .handle_capture_op h1 h2 h3 _hfresh h4 => .handle_capture_op h1 h2 h3 h4

theorem strict_apply_to_naive {oa : Option TKAddr} {d : TDenotable}
    {σ : TStore} {tmk : MKTime} {v : TValue} {σ' : TStore}
    (h : TFreshApplyKont oa d σ tmk v σ') : TApplyKont oa d σ tmk v σ' :=
  match h with
  | .apply_continue => .apply_continue
  | .apply_restore h1 h2 h3 h4 h5 =>
    .apply_restore h1 h2 (strict_apply_to_naive h3) h4 (strict_cont_to_naive h5)
  | .apply_restore_handle h1 h2 h3 h4 h5 h6 =>
    .apply_restore_handle h1 h2 h3 (strict_apply_to_naive h4) h5 (strict_handle_to_naive h6)

end

end DMCFA
