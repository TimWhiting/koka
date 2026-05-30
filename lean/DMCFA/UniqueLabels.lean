/-
  Well-labeled program assumption.

  A program is well-labeled if every let-binding site has a unique label.
  This is the formal counterpart of the "unique labels" assumption in the paper.
-/

import DMCFA.Syntax
import Mathlib.Data.Finset.Basic

namespace DMCFA

/-! ## Collecting all let-binding labels in a program -/

-- Explicit list recursion helpers (avoid inline lambdas for termination)
mutual

def Exp.allLabels : Exp → Finset Label
  | .letE _y ce e l => {l} ∪ CExp.allLabels ce ∪ Exp.allLabels e
  | .tail ce l_tail => {l_tail} ∪ CExp.allLabels ce
termination_by e => sizeOf e

def CExp.allLabels : CExp → Finset Label
  | .atomic _ => ∅
  | .funApp _ _ => ∅
  | .opApp _ _ => ∅
  | .matchE _ae bs => branchListLabels bs
  | .handler h e l_h => {l_h} ∪ Handler.allLabels h ∪ Exp.allLabels e
  | .funDef _f _xs e => Exp.allLabels e
termination_by ce => sizeOf ce

def Branch.allLabels : Branch → Finset Label
  | .branch _ _ e => Exp.allLabels e
termination_by b => sizeOf b

def Handler.allLabels : Handler → Finset Label
  | ⟨(_, e_ret), ops⟩ => Exp.allLabels e_ret ∪ opClauseListLabels ops
termination_by h => sizeOf h

def branchListLabels : List Branch → Finset Label
  | [] => ∅
  | b :: rest => Branch.allLabels b ∪ branchListLabels rest
termination_by bs => sizeOf bs

def opClauseListLabels : List (OpName × Var × Exp) → Finset Label
  | [] => ∅
  | (_, _, e) :: rest => Exp.allLabels e ∪ opClauseListLabels rest
termination_by ops => sizeOf ops

end

-- Simp lemmas for definitional equalities
@[simp] theorem Exp.allLabels_letE (y : Var) (ce : CExp) (e : Exp) (l : Label) :
    Exp.allLabels (.letE y ce e l) = {l} ∪ CExp.allLabels ce ∪ Exp.allLabels e := by
  simp [Exp.allLabels]
@[simp] theorem Exp.allLabels_tail (ce : CExp) (l_tail : Label) :
    Exp.allLabels (.tail ce l_tail) = {l_tail} ∪ CExp.allLabels ce := by
  simp [Exp.allLabels]
@[simp] theorem CExp.allLabels_atomic (ae : AExp) :
    CExp.allLabels (.atomic ae) = ∅ := by
  simp [CExp.allLabels]
@[simp] theorem CExp.allLabels_funApp (f : AExp) (aes : List AExp) :
    CExp.allLabels (.funApp f aes) = ∅ := by
  simp [CExp.allLabels]
@[simp] theorem CExp.allLabels_opApp (op : OpName) (x : Var) :
    CExp.allLabels (.opApp op x) = ∅ := by
  simp [CExp.allLabels]
@[simp] theorem CExp.allLabels_handler (h : Handler) (e : Exp) (l_h : Label) :
    CExp.allLabels (.handler h e l_h) = {l_h} ∪ Handler.allLabels h ∪ Exp.allLabels e := by
  simp [CExp.allLabels]
@[simp] theorem CExp.allLabels_funDef (f : Var) (xs : List Var) (e : Exp) :
    CExp.allLabels (.funDef f xs e) = Exp.allLabels e := by
  simp [CExp.allLabels]

/-! ## Well-labeled predicate -/

/-- A program is well-labeled if all let-binding labels are distinct.
    We define this inductively for clean hereditary reasoning. -/
inductive WellLabeled : Exp → Prop where
  | tail (ce : CExp) (l_tail : Label) :
      l_tail ∉ ce.allLabels →
      WellLabeled (.tail ce l_tail)
  | letE (y : Var) (ce : CExp) (e : Exp) (l : Label) :
      WellLabeled e →
      l ∉ e.allLabels →
      l ∉ ce.allLabels →
      Disjoint ce.allLabels e.allLabels →
      WellLabeled (.letE y ce e l)

/-! ## Hereditary lemmas for WellLabeled -/

lemma wellLabeled_letE_body {y : Var} {ce : CExp} {e : Exp} {l : Label}
    (h : WellLabeled (.letE y ce e l)) : WellLabeled e := by
  cases h; assumption

lemma wellLabeled_letE_disjoint {y : Var} {ce : CExp} {e : Exp} {l : Label}
    (h : WellLabeled (.letE y ce e l)) : Disjoint ce.allLabels e.allLabels := by
  cases h; assumption

lemma wellLabeled_label_notin_body {y : Var} {ce : CExp} {e : Exp} {l : Label}
    (h : WellLabeled (.letE y ce e l)) : l ∉ e.allLabels := by
  cases h; assumption

lemma wellLabeled_label_notin_ce {y : Var} {ce : CExp} {e : Exp} {l : Label}
    (h : WellLabeled (.letE y ce e l)) : l ∉ ce.allLabels := by
  cases h; assumption

/-- The label of a well-labeled letE is not in the combined labels of its subexpressions -/
lemma wellLabeled_label_unique {y : Var} {ce : CExp} {e : Exp} {l : Label}
    (h : WellLabeled (.letE y ce e l)) :
    l ∉ ce.allLabels ∧ l ∉ e.allLabels := by
  exact ⟨wellLabeled_label_notin_ce h, wellLabeled_label_notin_body h⟩

/-- The label l is not in the allLabels of its subexpressions -/
lemma letE_label_not_in_sub {y : Var} {ce : CExp} {e : Exp} {l : Label}
    (h : WellLabeled (.letE y ce e l)) :
    l ∉ CExp.allLabels ce ∧ l ∉ Exp.allLabels e :=
  ⟨wellLabeled_label_notin_ce h, wellLabeled_label_notin_body h⟩

/-! ## Deep well-labeledness across all sub-expressions -/

mutual

/-- Recursive well-labeledness: unique labels across the entire program
    (including function bodies, handler clause bodies, branch bodies) -/
inductive WellLabeledProgram : Exp → Prop where
  | tail (ce : CExp) (l_tail : Label) :
      WellLabeledSubCExp ce →
      l_tail ∉ ce.allLabels →
      WellLabeledProgram (.tail ce l_tail)
  | letE (y : Var) (ce : CExp) (e : Exp) (l : Label) :
      WellLabeled (.letE y ce e l) →
      WellLabeledProgram e →
      WellLabeledSubCExp ce →
      WellLabeledProgram (.letE y ce e l)

/-- Well-labeledness for sub-expressions within a CExp -/
inductive WellLabeledSubCExp : CExp → Prop where
  | atomic :
      (∀ xs body, ae = .lam xs body → WellLabeledProgram body) →
      WellLabeledSubCExp (.atomic ae)
  | funApp :
      (∀ xs body, f = .lam xs body → WellLabeledProgram body) →
      (∀ ae ∈ aes, ∀ xs body, ae = .lam xs body → WellLabeledProgram body) →
      WellLabeledSubCExp (.funApp f aes)
  | opApp : WellLabeledSubCExp (.opApp op x)
  | matchE :
      (∀ b ∈ bs, WellLabeledSubBranch b) →
      WellLabeledSubCExp (.matchE ae bs)
  | handler :
      WellLabeledProgram e_body →
      WellLabeledSubHandler h →
      l_h ∉ h.allLabels →
      l_h ∉ e_body.allLabels →
      WellLabeledSubCExp (.handler h e_body l_h)
  | funDef :
      WellLabeledProgram e_body →
      WellLabeledSubCExp (.funDef f xs e_body)

/-- Well-labeledness for branches -/
inductive WellLabeledSubBranch : Branch → Prop where
  | branch :
      WellLabeledProgram e →
      WellLabeledSubBranch (.branch c xs e)

/-- Well-labeledness for handler clauses -/
inductive WellLabeledSubHandler : Handler → Prop where
  | mk :
      WellLabeledProgram h.returnClause.2 →
      (∀ op_clause ∈ h.opClauses, WellLabeledProgram op_clause.2.2) →
      (∀ op_clause ∈ h.opClauses, op_clause.2.1 ≠ "resume") →
      WellLabeledSubHandler h

end

/-! ## Hereditary lemmas for WellLabeledProgram -/

lemma wellLabeledProgram_letE_body {y : Var} {ce : CExp} {e : Exp} {l : Label}
    (h : WellLabeledProgram (.letE y ce e l)) : WellLabeledProgram e := by
  cases h with | letE _ _ _ _ h1 h2 h3 => exact h2

lemma wellLabeledProgram_letE_wl {y : Var} {ce : CExp} {e : Exp} {l : Label}
    (h : WellLabeledProgram (.letE y ce e l)) : WellLabeled (.letE y ce e l) := by
  cases h with | letE _ _ _ _ h1 h2 h3 => exact h1

lemma wellLabeledProgram_letE_ce {y : Var} {ce : CExp} {e : Exp} {l : Label}
    (h : WellLabeledProgram (.letE y ce e l)) : WellLabeledSubCExp ce := by
  cases h with | letE _ _ _ _ h1 h2 h3 => exact h3

/-! ## Decomposition lemmas for WellLabeledSubCExp -/

lemma wellLabeledSubCExp_handler_body
    (h : WellLabeledSubCExp (.handler hdl e_body l_h)) : WellLabeledProgram e_body := by
  cases h with | handler h1 _ _ _ => exact h1

lemma wellLabeledSubCExp_handler_sub
    (h : WellLabeledSubCExp (.handler hdl e_body l_h)) : WellLabeledSubHandler hdl := by
  cases h with | handler _ h2 _ _ => exact h2

lemma wellLabeledSubCExp_funDef_body
    (h : WellLabeledSubCExp (.funDef f xs e_body)) : WellLabeledProgram e_body := by
  cases h with | funDef h1 => exact h1

lemma wellLabeledSubCExp_funApp_f
    (h : WellLabeledSubCExp (.funApp f aes)) :
    ∀ xs body, f = .lam xs body → WellLabeledProgram body := by
  cases h with | funApp h1 _ => exact h1

lemma wellLabeledSubCExp_funApp_aes
    (h : WellLabeledSubCExp (.funApp f aes)) :
    ∀ ae ∈ aes, ∀ xs body, ae = .lam xs body → WellLabeledProgram body := by
  cases h with | funApp _ h2 => exact h2

lemma wellLabeledSubCExp_atomic_ae
    (h : WellLabeledSubCExp (.atomic ae)) :
    ∀ xs body, ae = .lam xs body → WellLabeledProgram body := by
  cases h with | atomic h1 => exact h1

lemma wellLabeledSubCExp_matchE_branches
    (h : WellLabeledSubCExp (.matchE ae bs)) : ∀ b ∈ bs, WellLabeledSubBranch b := by
  cases h with | matchE h1 => exact h1

lemma wellLabeledSubHandler_ret
    (h : WellLabeledSubHandler hdl) : WellLabeledProgram hdl.returnClause.2 := by
  cases h with | mk h1 _ _ => exact h1

lemma wellLabeledSubHandler_ops
    (h : WellLabeledSubHandler hdl) :
    ∀ op_clause ∈ hdl.opClauses, WellLabeledProgram op_clause.2.2 := by
  cases h with | mk _ h2 _ => exact h2

lemma wellLabeledSubHandler_no_resume
    (h : WellLabeledSubHandler hdl) :
    ∀ op_clause ∈ hdl.opClauses, op_clause.2.1 ≠ "resume" := by
  cases h with | mk _ _ h3 => exact h3

/-! ## Collecting top-level allocation variable names -/

mutual

def Exp.topAllocVars : Exp → Finset Var
  | .letE y ce e _ => {y} ∪ ce.topAllocVars ∪ e.topAllocVars
  | .tail ce _l => ce.topAllocVars
termination_by e => sizeOf e

def CExp.topAllocVars : CExp → Finset Var
  | .atomic _ => ∅
  | .funApp _ _ => ∅
  | .opApp _ _ => ∅
  | .matchE _ae bs => branchListAllocVars bs
  | .handler h _ _ => h.topAllocVars  -- handler body runs at NEW time, not counted
  | .funDef f _ _ => {f}            -- funDef allocates f at current time
termination_by ce => sizeOf ce

def Branch.topAllocVars : Branch → Finset Var
  | .branch _ xs e => xs.toFinset ∪ e.topAllocVars
termination_by b => sizeOf b

def Handler.topAllocVars : Handler → Finset Var
  | ⟨(x_ret, e_ret), ops⟩ =>
      {x_ret, "resume"} ∪ e_ret.topAllocVars ∪ opClauseListAllocVars ops
termination_by h => sizeOf h

def branchListAllocVars : List Branch → Finset Var
  | [] => ∅
  | b :: rest => b.topAllocVars ∪ branchListAllocVars rest
termination_by bs => sizeOf bs

def opClauseListAllocVars : List (OpName × Var × Exp) → Finset Var
  | [] => ∅
  | (_, x, e) :: rest => {x, "resume"} ∪ e.topAllocVars ∪ opClauseListAllocVars rest
termination_by ops => sizeOf ops

end

-- Simp lemmas for topAllocVars
@[simp] theorem Exp.topAllocVars_letE (y : Var) (ce : CExp) (e : Exp) (l : Label) :
    Exp.topAllocVars (.letE y ce e l) = {y} ∪ ce.topAllocVars ∪ e.topAllocVars := by
  simp [Exp.topAllocVars]
@[simp] theorem Exp.topAllocVars_tail (ce : CExp) (l : Label) :
    Exp.topAllocVars (.tail ce l) = ce.topAllocVars := by
  simp [Exp.topAllocVars]
@[simp] theorem CExp.topAllocVars_atomic (ae : AExp) :
    CExp.topAllocVars (.atomic ae) = ∅ := by
  simp [CExp.topAllocVars]
@[simp] theorem CExp.topAllocVars_funApp (f : AExp) (aes : List AExp) :
    CExp.topAllocVars (.funApp f aes) = ∅ := by
  simp [CExp.topAllocVars]
@[simp] theorem CExp.topAllocVars_opApp (op : OpName) (x : Var) :
    CExp.topAllocVars (.opApp op x) = ∅ := by
  simp [CExp.topAllocVars]
@[simp] theorem CExp.topAllocVars_funDef (f : Var) (xs : List Var) (e : Exp) :
    CExp.topAllocVars (.funDef f xs e) = {f} := by
  simp [CExp.topAllocVars]

/-! ## Well-Named Program (Barendregt Convention) -/

mutual

inductive WellNamedProgram : Exp → Prop where
  | tail (ce : CExp) (l_tail : Label) :
      WellNamedSubCExp ce →
      WellNamedProgram (.tail ce l_tail)
  | letE (y : Var) (ce : CExp) (e : Exp) (l : Label) :
      WellNamedProgram e →
      WellNamedSubCExp ce →
      y ∉ ce.topAllocVars →
      y ∉ e.topAllocVars →
      Disjoint ce.topAllocVars e.topAllocVars →
      WellNamedProgram (.letE y ce e l)

inductive WellNamedSubCExp : CExp → Prop where
  | atomic :
      (∀ xs body, ae = .lam xs body → WellNamedProgram body) →
      (∀ xs body, ae = .lam xs body → Disjoint xs.toFinset body.topAllocVars) →
      (∀ xs body, ae = .lam xs body → xs.Nodup) →
      WellNamedSubCExp (.atomic ae)
  | funApp :
      (∀ xs body, f = .lam xs body → WellNamedProgram body) →
      (∀ xs body, f = .lam xs body → Disjoint xs.toFinset body.topAllocVars) →
      (∀ xs body, f = .lam xs body → xs.Nodup) →
      (∀ ae ∈ aes, ∀ xs body, ae = .lam xs body → WellNamedProgram body) →
      (∀ ae ∈ aes, ∀ xs body, ae = .lam xs body → Disjoint xs.toFinset body.topAllocVars) →
      (∀ ae ∈ aes, ∀ xs body, ae = .lam xs body → xs.Nodup) →
      WellNamedSubCExp (.funApp f aes)
  | opApp : WellNamedSubCExp (.opApp op x)
  | matchE :
      (∀ b ∈ bs, WellNamedSubBranch b) →
      WellNamedSubCExp (.matchE ae bs)
  | handler :
      WellNamedProgram e_body →
      WellNamedSubHandler h →
      WellNamedSubCExp (.handler h e_body l_h)
  | funDef :
      WellNamedProgram e_body →
      Disjoint xs.toFinset e_body.topAllocVars →
      xs.Nodup →
      WellNamedSubCExp (.funDef f xs e_body)

inductive WellNamedSubBranch : Branch → Prop where
  | branch :
      WellNamedProgram e →
      (∀ x ∈ xs, x ∉ e.topAllocVars) →
      WellNamedSubBranch (.branch c xs e)

inductive WellNamedSubHandler : Handler → Prop where
  | mk :
      WellNamedProgram h.returnClause.2 →
      (∀ op_clause ∈ h.opClauses, WellNamedProgram op_clause.2.2) →
      h.returnClause.1 ∉ h.returnClause.2.topAllocVars →
      "resume" ∉ h.returnClause.2.topAllocVars →
      h.returnClause.1 ≠ "resume" →
      (∀ op_clause ∈ h.opClauses, op_clause.2.1 ∉ op_clause.2.2.topAllocVars) →
      (∀ op_clause ∈ h.opClauses, "resume" ∉ op_clause.2.2.topAllocVars) →
      (∀ op_clause ∈ h.opClauses, op_clause.2.1 ≠ "resume") →
      Disjoint ({h.returnClause.1, "resume"} ∪ h.returnClause.2.topAllocVars)
               (opClauseListAllocVars h.opClauses) →
      WellNamedSubHandler h

end

/-! ## Decomposition lemmas for WellNamedProgram -/

lemma wellNamedProgram_letE_body {y : Var} {ce : CExp} {e : Exp} {l : Label}
    (h : WellNamedProgram (.letE y ce e l)) : WellNamedProgram e := by
  cases h with | letE _ _ _ _ h1 _ _ _ _ => exact h1

lemma wellNamedProgram_letE_ce {y : Var} {ce : CExp} {e : Exp} {l : Label}
    (h : WellNamedProgram (.letE y ce e l)) : WellNamedSubCExp ce := by
  cases h with | letE _ _ _ _ _ h2 _ _ _ => exact h2

lemma wellNamedProgram_letE_y_notin_ce {y : Var} {ce : CExp} {e : Exp} {l : Label}
    (h : WellNamedProgram (.letE y ce e l)) : y ∉ ce.topAllocVars := by
  cases h with | letE _ _ _ _ _ _ h3 _ _ => exact h3

lemma wellNamedProgram_letE_y_notin_e {y : Var} {ce : CExp} {e : Exp} {l : Label}
    (h : WellNamedProgram (.letE y ce e l)) : y ∉ e.topAllocVars := by
  cases h with | letE _ _ _ _ _ _ _ h4 _ => exact h4

lemma wellNamedProgram_letE_disjoint {y : Var} {ce : CExp} {e : Exp} {l : Label}
    (h : WellNamedProgram (.letE y ce e l)) : Disjoint ce.topAllocVars e.topAllocVars := by
  cases h with | letE _ _ _ _ _ _ _ _ h5 => exact h5

lemma wellNamedSubCExp_funApp_f
    (h : WellNamedSubCExp (.funApp f aes)) :
    ∀ xs body, f = .lam xs body → WellNamedProgram body := by
  cases h with | funApp h1 _ _ _ _ _ => exact h1

lemma wellNamedSubCExp_funApp_f_disjoint
    (h : WellNamedSubCExp (.funApp f aes)) :
    ∀ xs body, f = .lam xs body → Disjoint xs.toFinset body.topAllocVars := by
  cases h with | funApp _ h2 _ _ _ _ => exact h2

lemma wellNamedSubCExp_funApp_f_nodup
    (h : WellNamedSubCExp (.funApp f aes)) :
    ∀ xs body, f = .lam xs body → xs.Nodup := by
  cases h with | funApp _ _ h3 _ _ _ => exact h3

lemma wellNamedSubCExp_funApp_aes
    (h : WellNamedSubCExp (.funApp f aes)) :
    ∀ ae ∈ aes, ∀ xs body, ae = .lam xs body → WellNamedProgram body := by
  cases h with | funApp _ _ _ h4 _ _ => exact h4

lemma wellNamedSubCExp_funApp_aes_disjoint
    (h : WellNamedSubCExp (.funApp f aes)) :
    ∀ ae ∈ aes, ∀ xs body, ae = .lam xs body → Disjoint xs.toFinset body.topAllocVars := by
  cases h with | funApp _ _ _ _ h5 _ => exact h5

lemma wellNamedSubCExp_funApp_aes_nodup
    (h : WellNamedSubCExp (.funApp f aes)) :
    ∀ ae ∈ aes, ∀ xs body, ae = .lam xs body → xs.Nodup := by
  cases h with | funApp _ _ _ _ _ h6 => exact h6

lemma wellNamedSubCExp_atomic_ae
    (h : WellNamedSubCExp (.atomic ae)) :
    ∀ xs body, ae = .lam xs body → WellNamedProgram body := by
  cases h with | atomic h1 _ _ => exact h1

lemma wellNamedSubCExp_atomic_ae_disjoint
    (h : WellNamedSubCExp (.atomic ae)) :
    ∀ xs body, ae = .lam xs body → Disjoint xs.toFinset body.topAllocVars := by
  cases h with | atomic _ h2 _ => exact h2

lemma wellNamedSubCExp_atomic_ae_nodup
    (h : WellNamedSubCExp (.atomic ae)) :
    ∀ xs body, ae = .lam xs body → xs.Nodup := by
  cases h with | atomic _ _ h3 => exact h3

lemma wellNamedSubCExp_handler_body
    (h : WellNamedSubCExp (.handler hdl e_body l_h)) : WellNamedProgram e_body := by
  cases h with | handler h1 _ => exact h1

lemma wellNamedSubCExp_handler_sub
    (h : WellNamedSubCExp (.handler hdl e_body l_h)) : WellNamedSubHandler hdl := by
  cases h with | handler _ h2 => exact h2

lemma wellNamedSubCExp_funDef_body
    (h : WellNamedSubCExp (.funDef f xs e_body)) : WellNamedProgram e_body := by
  cases h with | funDef h1 _ _ => exact h1

lemma wellNamedSubCExp_funDef_disjoint
    (h : WellNamedSubCExp (.funDef f xs e_body)) : Disjoint xs.toFinset e_body.topAllocVars := by
  cases h with | funDef _ h2 _ => exact h2

lemma wellNamedSubCExp_funDef_nodup
    (h : WellNamedSubCExp (.funDef f xs e_body)) : xs.Nodup := by
  cases h with | funDef _ _ h3 => exact h3

lemma wellNamedSubCExp_matchE_branches
    (h : WellNamedSubCExp (.matchE ae bs)) : ∀ b ∈ bs, WellNamedSubBranch b := by
  cases h with | matchE h1 => exact h1

lemma wellNamedSubHandler_ret
    (h : WellNamedSubHandler hdl) : WellNamedProgram hdl.returnClause.2 := by
  cases h with | mk h1 _ _ _ _ _ _ _ _ => exact h1

lemma wellNamedSubHandler_ops
    (h : WellNamedSubHandler hdl) :
    ∀ op_clause ∈ hdl.opClauses, WellNamedProgram op_clause.2.2 := by
  cases h with | mk _ h2 _ _ _ _ _ _ _ => exact h2

lemma wellNamedSubHandler_xret_notin_ret
    (h : WellNamedSubHandler hdl) : hdl.returnClause.1 ∉ hdl.returnClause.2.topAllocVars := by
  cases h with | mk _ _ h3 _ _ _ _ _ _ => exact h3

lemma wellNamedSubHandler_resume_notin_ret
    (h : WellNamedSubHandler hdl) : "resume" ∉ hdl.returnClause.2.topAllocVars := by
  cases h with | mk _ _ _ h4 _ _ _ _ _ => exact h4

lemma wellNamedSubHandler_xret_ne_resume
    (h : WellNamedSubHandler hdl) : hdl.returnClause.1 ≠ "resume" := by
  cases h with | mk _ _ _ _ h5 _ _ _ _ => exact h5

lemma wellNamedSubHandler_x_notin_op_body
    (h : WellNamedSubHandler hdl) :
    ∀ op_clause ∈ hdl.opClauses, op_clause.2.1 ∉ op_clause.2.2.topAllocVars := by
  cases h with | mk _ _ _ _ _ h6 _ _ _ => exact h6

lemma wellNamedSubHandler_resume_notin_op_body
    (h : WellNamedSubHandler hdl) :
    ∀ op_clause ∈ hdl.opClauses, "resume" ∉ op_clause.2.2.topAllocVars := by
  cases h with | mk _ _ _ _ _ _ h7 _ _ => exact h7

lemma wellNamedSubHandler_x_ne_resume
    (h : WellNamedSubHandler hdl) :
    ∀ op_clause ∈ hdl.opClauses, op_clause.2.1 ≠ "resume" := by
  cases h with | mk _ _ _ _ _ _ _ h8 _ => exact h8

lemma wellNamedSubHandler_ret_disjoint_ops
    (h : WellNamedSubHandler hdl) :
    Disjoint ({hdl.returnClause.1, "resume"} ∪ hdl.returnClause.2.topAllocVars)
             (opClauseListAllocVars hdl.opClauses) := by
  cases h with | mk _ _ _ _ _ _ _ _ h9 => exact h9

/-! ## Subset lemmas for topAllocVars -/

/-- Return clause body's topAllocVars ⊆ handler's topAllocVars -/
lemma handler_ret_topAllocVars_subset (h : Handler) :
    h.returnClause.2.topAllocVars ⊆ h.topAllocVars := by
  cases h with
  | mk ret ops =>
    obtain ⟨x_ret, e_ret⟩ := ret
    simp only [Handler.topAllocVars]
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)

/-- Op clause body's topAllocVars ⊆ opClauseListAllocVars -/
lemma opClause_topAllocVars_subset_list {ops : List (OpName × Var × Exp)}
    {op : OpName} {x : Var} {e : Exp}
    (h_mem : (op, x, e) ∈ ops) :
    e.topAllocVars ⊆ opClauseListAllocVars ops := by
  induction ops with
  | nil => simp at h_mem
  | cons hd tl ih =>
    obtain ⟨op', x', e'⟩ := hd
    simp only [opClauseListAllocVars]
    cases List.mem_cons.mp h_mem with
    | inl heq =>
      have : e = e' := by
        have := congr_arg (fun p : OpName × Var × Exp => p.2.2) heq
        simpa using this
      subst this
      intro v hv
      exact Finset.mem_union_left _ (Finset.mem_union_right _ hv)
    | inr h => exact Finset.Subset.trans (ih h) Finset.subset_union_right

/-- Op clause body's topAllocVars ⊆ handler's topAllocVars -/
lemma handler_op_topAllocVars_subset {h : Handler} {op : OpName} {x : Var} {e : Exp}
    (h_mem : (op, x, e) ∈ h.opClauses) :
    e.topAllocVars ⊆ h.topAllocVars := by
  cases h with
  | mk ret ops =>
    obtain ⟨x_ret, e_ret⟩ := ret
    simp only [Handler.topAllocVars]
    exact Finset.Subset.trans (opClause_topAllocVars_subset_list h_mem) Finset.subset_union_right

/-- Branch body topAllocVars ⊆ branch topAllocVars -/
lemma branch_body_topAllocVars_subset (c : ConLabel) (xs : List Var) (e : Exp) :
    e.topAllocVars ⊆ (Branch.branch c xs e).topAllocVars := by
  intro x hx
  simp only [Branch.topAllocVars]
  exact Finset.mem_union_right _ hx

/-- Disjoint insert from disjoint + not mem -/
lemma disjoint_insert_of_disjoint_of_not_mem [DecidableEq α] {s₁ s₂ : Finset α} {x : α}
    (h_disj : Disjoint s₁ s₂) (hx : x ∉ s₂) :
    Disjoint (insert x s₁) s₂ := by
  rw [Finset.disjoint_insert_left]
  exact ⟨hx, h_disj⟩

/-! ## allLabels subset lemmas -/

/-- allLabels of CExp inside letE ⊆ allLabels of the letE -/
lemma letE_ce_allLabels_subset (y : Var) (ce : CExp) (e : Exp) (l : Label) :
    ce.allLabels ⊆ (Exp.letE y ce e l).allLabels := by
  intro x hx
  simp only [Exp.allLabels]
  exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)

/-- allLabels of body inside letE ⊆ allLabels of the letE -/
lemma letE_body_allLabels_subset (y : Var) (ce : CExp) (e : Exp) (l : Label) :
    e.allLabels ⊆ (Exp.letE y ce e l).allLabels := by
  intro x hx
  simp only [Exp.allLabels]
  exact Finset.mem_union_right _ hx

/-- The label of a letE is in its allLabels -/
lemma letE_label_mem_allLabels (y : Var) (ce : CExp) (e : Exp) (l : Label) :
    l ∈ (Exp.letE y ce e l).allLabels := by
  simp only [Exp.allLabels]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton_self _))

/-- Branch allLabels ⊆ branchListLabels for any branch in the list -/
lemma branch_allLabels_subset_branchListLabels {b : Branch} {bs : List Branch}
    (h_mem : b ∈ bs) : b.allLabels ⊆ branchListLabels bs := by
  induction bs with
  | nil => simp at h_mem
  | cons hd tl ih =>
    simp only [branchListLabels]
    cases List.mem_cons.mp h_mem with
    | inl h => subst h; exact Finset.subset_union_left
    | inr h => exact Finset.Subset.trans (ih h) Finset.subset_union_right

/-- Return clause body allLabels ⊆ handler allLabels -/
lemma handler_ret_allLabels_subset (h : Handler) :
    h.returnClause.2.allLabels ⊆ h.allLabels := by
  cases h with
  | mk ret ops =>
    obtain ⟨_, e_ret⟩ := ret
    simp [Handler.allLabels]

/-- Op clause body allLabels ⊆ opClauseListLabels -/
lemma opClause_allLabels_subset_opClauseListLabels
    {ops : List (OpName × Var × Exp)} {op : OpName} {x : Var} {e : Exp}
    (h_mem : (op, x, e) ∈ ops) : e.allLabels ⊆ opClauseListLabels ops := by
  induction ops with
  | nil => simp at h_mem
  | cons hd tl ih =>
    obtain ⟨op', x', e'⟩ := hd
    simp only [opClauseListLabels]
    cases List.mem_cons.mp h_mem with
    | inl h =>
      have : e = e' := by
        have := congr_arg (fun p : OpName × Var × Exp => p.2.2) h
        simpa using this
      subst this; exact Finset.subset_union_left
    | inr h => exact Finset.Subset.trans (ih h) Finset.subset_union_right

/-- Op clause body allLabels ⊆ handler allLabels -/
lemma handler_op_allLabels_subset {h : Handler} {op : OpName} {x : Var} {e : Exp}
    (h_mem : (op, x, e) ∈ h.opClauses) : e.allLabels ⊆ h.allLabels := by
  cases h with
  | mk ret ops =>
    obtain ⟨_, e_ret⟩ := ret
    unfold Handler.allLabels
    exact Finset.Subset.trans
      (opClause_allLabels_subset_opClauseListLabels h_mem) Finset.subset_union_right

/-- Handler allLabels ⊆ CExp.handler allLabels -/
lemma handler_allLabels_subset_cexp (h : Handler) (e : Exp) (l_h : Label) :
    h.allLabels ⊆ (CExp.handler h e l_h).allLabels := by
  simp only [CExp.allLabels]
  intro x hx
  exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)

/-! ## WellFormed Bundles (WellLabeled ∧ WellNamed) -/

/-- Combined well-formedness for programs -/
def WellFormedProgram (e : Exp) : Prop :=
  WellLabeledProgram e ∧ WellNamedProgram e

/-- Combined well-formedness for complex expressions -/
def WellFormedSubCExp (ce : CExp) : Prop :=
  WellLabeledSubCExp ce ∧ WellNamedSubCExp ce

/-- Combined well-formedness for branches -/
def WellFormedSubBranch (b : Branch) : Prop :=
  WellLabeledSubBranch b ∧ WellNamedSubBranch b

/-- Combined well-formedness for handlers -/
def WellFormedSubHandler (h : Handler) : Prop :=
  WellLabeledSubHandler h ∧ WellNamedSubHandler h

-- Projections
theorem WellFormedProgram.wl (h : WellFormedProgram e) : WellLabeledProgram e := h.1
theorem WellFormedProgram.wn (h : WellFormedProgram e) : WellNamedProgram e := h.2
theorem WellFormedSubCExp.wl (h : WellFormedSubCExp ce) : WellLabeledSubCExp ce := h.1
theorem WellFormedSubCExp.wn (h : WellFormedSubCExp ce) : WellNamedSubCExp ce := h.2
theorem WellFormedSubHandler.wl (h : WellFormedSubHandler hdl) : WellLabeledSubHandler hdl := h.1
theorem WellFormedSubHandler.wn (h : WellFormedSubHandler hdl) : WellNamedSubHandler hdl := h.2

-- Combined decomposition lemmas
theorem wellFormedSubCExp_handler_body (h : WellFormedSubCExp (.handler hdl e_body l_h)) :
    WellFormedProgram e_body :=
  ⟨wellLabeledSubCExp_handler_body h.wl, wellNamedSubCExp_handler_body h.wn⟩

theorem wellFormedSubCExp_handler_sub (h : WellFormedSubCExp (.handler hdl e_body l_h)) :
    WellFormedSubHandler hdl :=
  ⟨wellLabeledSubCExp_handler_sub h.wl, wellNamedSubCExp_handler_sub h.wn⟩

theorem wellFormedSubCExp_funDef_body (h : WellFormedSubCExp (.funDef f xs e_body)) :
    WellFormedProgram e_body :=
  ⟨wellLabeledSubCExp_funDef_body h.wl, wellNamedSubCExp_funDef_body h.wn⟩

theorem wellFormedSubCExp_funDef_disjoint (h : WellFormedSubCExp (.funDef f xs e_body)) :
    Disjoint xs.toFinset e_body.topAllocVars :=
  wellNamedSubCExp_funDef_disjoint h.wn

theorem wellFormedSubCExp_funApp_f (h : WellFormedSubCExp (.funApp f aes)) :
    (∀ xs body, f = .lam xs body → WellFormedProgram body) :=
  fun xs body hf => ⟨wellLabeledSubCExp_funApp_f h.wl xs body hf,
                     wellNamedSubCExp_funApp_f h.wn xs body hf⟩

theorem wellFormedSubCExp_funApp_f_disjoint (h : WellFormedSubCExp (.funApp f aes)) :
    (∀ xs body, f = .lam xs body → Disjoint xs.toFinset body.topAllocVars) :=
  wellNamedSubCExp_funApp_f_disjoint h.wn

theorem wellFormedSubCExp_funApp_aes (h : WellFormedSubCExp (.funApp f aes)) :
    (∀ ae ∈ aes, ∀ xs body, ae = .lam xs body → WellFormedProgram body) :=
  fun ae hae xs body hf => ⟨wellLabeledSubCExp_funApp_aes h.wl ae hae xs body hf,
                             wellNamedSubCExp_funApp_aes h.wn ae hae xs body hf⟩

theorem wellFormedSubCExp_funApp_aes_disjoint (h : WellFormedSubCExp (.funApp f aes)) :
    (∀ ae ∈ aes, ∀ xs body, ae = .lam xs body → Disjoint xs.toFinset body.topAllocVars) :=
  wellNamedSubCExp_funApp_aes_disjoint h.wn

theorem wellFormedSubHandler_ret (h : WellFormedSubHandler hdl) :
    WellFormedProgram hdl.returnClause.2 :=
  ⟨wellLabeledSubHandler_ret h.wl, wellNamedSubHandler_ret h.wn⟩

theorem wellFormedSubHandler_ops (h : WellFormedSubHandler hdl) :
    ∀ op_clause ∈ hdl.opClauses, WellFormedProgram op_clause.2.2 :=
  fun oc hoc => ⟨wellLabeledSubHandler_ops h.wl oc hoc, wellNamedSubHandler_ops h.wn oc hoc⟩

theorem wellFormedProgram_letE_body (h : WellFormedProgram (.letE y ce e l)) :
    WellFormedProgram e :=
  ⟨wellLabeledProgram_letE_body h.wl, wellNamedProgram_letE_body h.wn⟩

theorem wellFormedProgram_letE_ce (h : WellFormedProgram (.letE y ce e l)) :
    WellFormedSubCExp ce :=
  ⟨wellLabeledProgram_letE_ce h.wl, wellNamedProgram_letE_ce h.wn⟩

theorem wellFormedSubCExp_atomic_ae (h : WellFormedSubCExp (.atomic ae)) :
    (∀ xs body, ae = .lam xs body → WellFormedProgram body) :=
  fun xs body hf => ⟨wellLabeledSubCExp_atomic_ae h.wl xs body hf,
                     wellNamedSubCExp_atomic_ae h.wn xs body hf⟩

theorem wellFormedSubCExp_atomic_ae_disjoint (h : WellFormedSubCExp (.atomic ae)) :
    (∀ xs body, ae = .lam xs body → Disjoint xs.toFinset body.topAllocVars) :=
  wellNamedSubCExp_atomic_ae_disjoint h.wn

end DMCFA
