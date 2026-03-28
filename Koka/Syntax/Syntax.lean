/-
  Ported from Haskell Koka:
  File:   src/Syntax/Syntax.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Koka.Common.NamePrim
import Koka.Common.Name
import Koka.Common.Range
import Koka.Common.Failure
import Koka.Common.ResumeKind
import Koka.Common.Syntax
import Koka.Common.NameSet
import Koka.Syntax.Lexeme
import Koka.Common.NameSet

namespace Koka.Syntax.Syntax

open Koka.Common.NamePrim
open Koka.Common.Name
open Koka.Common.NameSet
open Koka.Common.Range
open Koka.Common.Failure
open Koka.Common.ResumeKind
open Koka.Common.Syntax
open Koka.Common
open Koka.Syntax.Lexeme

set_option autoImplicit false

/- --------------------------------------------------------------------------
  Literals and Basic Types
-------------------------------------------------------------------------- -/

inductive Lit where
  | LitInt (i : Int) (range : Range)
  | LitFloat (f : Float) (range : Range)
  | LitChar (c : Char) (range : Range)
  | LitString (s : String) (range : Range)
  deriving Repr, Inhabited

def Lit.range : Lit → Range
  | .LitInt _ r => r
  | .LitFloat _ r => r
  | .LitChar _ r => r
  | .LitString _ r => r

instance : Ranged Lit where
  getRange := Lit.range

inductive UserQuantifier where
  | QSome
  | QForall
  | QExists
  deriving Repr, Inhabited

instance : ToString UserQuantifier where
  toString
    | .QSome => "some"
    | .QForall => "forall"
    | .QExists => "exists"

structure TypeBinder (k : Type) where
  tbinderName      : Name
  tbinderKind      : k
  tbinderNameRange : Range
  tbinderRange     : Range
  deriving Repr, Inhabited

instance {k : Type} : Ranged (TypeBinder k) where
  getRange tb := tb.tbinderRange

inductive KUserType (k : Type) where
  | TpQuan (quant : UserQuantifier) (tname : TypeBinder k) (type : KUserType k) (range : Range)
  | TpFun (args : List (Name × KUserType k)) (effect : KUserType k) (type : KUserType k) (range : Range)
  | TpApp (tp : KUserType k) (args : List (KUserType k)) (range : Range)
  | TpVar (name : Name) (range : Range)
  | TpCon (name : Name) (range : Range)
  | TpParens (tp : KUserType k) (range : Range)
  | TpAnn (tp : KUserType k) (kind : k)
  deriving Repr, Inhabited

inductive UserKind where
  | KindCon (name : Name) (range : Range)
  | KindArrow (k1 k2 : UserKind)
  | KindParens (kind : UserKind) (range : Range)
  | KindNone
  deriving Repr, Inhabited

abbrev UserType := KUserType UserKind

mutual
  def KUserType.range {k : Type} (rk : k → Range) : KUserType k → Range
    | .TpQuan _ _ _ r => r
    | .TpFun _ _ _ r => r
    | .TpApp _ _ r => r
    | .TpVar _ r => r
    | .TpCon _ r => r
    | .TpParens tp _ => KUserType.range rk tp
    | .TpAnn tp knd => combineRange (KUserType.range rk tp) (rk knd)

  def UserKind.range : UserKind → Range
    | .KindCon _ r => r
    | .KindArrow k1 k2 => combineRange (UserKind.range k1) (UserKind.range k2)
    | .KindParens _ r => r
    | .KindNone => rangeNull
end

instance {k : Type} [Ranged k] : Ranged (KUserType k) where
  getRange := KUserType.range Ranged.getRange

instance : Ranged UserKind where
  getRange := UserKind.range

inductive ExternalCall where
  | ExternalInline (s : String)
  | ExternalCallNative (s : String)
  deriving Repr, Inhabited

structure ValueBinder (t e : Type) where
  binderName      : Name
  binderType      : t
  binderExpr      : e
  binderNameRange : Range
  binderRange     : Range
  deriving Repr, Inhabited

instance {t e : Type} : Ranged (ValueBinder t e) where
  getRange vb := vb.binderRange

inductive HandlerOverride where
  | HandlerNoOverride
  | HandlerOverride
  deriving Repr, BEq, Inhabited

inductive HandlerScope where
  | HandlerNoScope
  | HandlerScoped
  deriving Repr, BEq, Inhabited

/- --------------------------------------------------------------------------
  Mutual AST: Expression group
-------------------------------------------------------------------------- -/

mutual
  inductive Expr (t : Type) where
    | Lam (params : List (ValueBinder (Option t) (Option (Expr t)))) (body : Expr t) (topLevel : Bool) (range : Range)
    | Let (defns : DefGroup t) (body : Expr t) (range : Range)
    | Bind (defn : Def t) (body : Expr t) (range : Range)
    | App (f : Expr t) (args : List (Option (Name × Range) × Expr t)) (range : Range)
    | Var (name : Name) (isOp : Bool) (range : Range)
    | Lit (lit : Lit)
    | Ann (expr : Expr t) (tp : t) (range : Range)
    | Case (expr : Expr t) (branches : List (Branch t)) (topLevel : Bool) (range : Range)
    | Parens (expr : Expr t) (name : Name) (ext : String) (range : Range)
    | Inject (tp : t) (expr : Expr t) (behind : Bool) (range : Range)
    | Handler (hndlrSort : HandlerSort)
              (hndlrScope : HandlerScope)
              (hndlrOverride : HandlerOverride)
              (hndlrAllowMask : Option Bool)
              (hndlrEffect : Option t)
              (hndlrLocalPars : List (ValueBinder (Option t) Unit))
              (hndlrInitially : Option (Expr t))
              (hndlrReturn : Option (Expr t))
              (hndlrFinally : Option (Expr t))
              (hndlrBranches : List (HandlerBranch t))
              (hndlrDeclRange : Range)
              (hndlrRange : Range)
    deriving Repr

  inductive DefGroup (t : Type) where
    | DefRec (defns : List (Def t))
    | DefNonRec (defn : Def t)
    deriving Repr

  inductive Def (t : Type) where
    | mk (defBinder : ValueBinder Unit (Expr t))
         (defRange  : Range)
         (defVis    : Visibility)
         (defSort   : DefSort)
         (defInline : DefInline)
         (defDoc    : String)
    deriving Repr

  inductive Branch (t : Type) where
    | mk (branchPattern : Pattern t)
         (branchGuards : List (Guard t))
    deriving Repr

  inductive Guard (t : Type) where
    | mk (guardTest : Expr t)
         (guardExpr : Expr t)
    deriving Repr

  inductive Pattern (t : Type) where
    | PatWild (range : Range)
    | PatVar (binder : ValueBinder (Option t) (Pattern t))
    | PatAnn (pat : Pattern t) (tp : t) (range : Range)
    | PatCon (name : Name) (args : List (Option (Name × Range) × Pattern t)) (nameRange : Range) (range : Range)
    | PatParens (pat : Pattern t) (range : Range)
    | PatLit (lit : Lit)
    deriving Repr

  inductive HandlerBranch (t : Type) where
    | mk (hbranchName : Name)
         (hbranchPars : List (ValueBinder (Option t) Unit))
         (hbranchExpr : Expr t)
         (hbranchSort : OperationSort)
         (hbranchNameRange : Range)
         (hbranchPatRange : Range)
    deriving Repr
end

/- --------------------------------------------------------------------------
  Type definition group
-------------------------------------------------------------------------- -/

structure UserCon (t u k : Type) where
  userconName : Name
  userconExists : List (TypeBinder k)
  userconParams : List (Visibility × ValueBinder t (Option (Expr u)))
  userconResult : Option t
  userConLazy : Option (Fip × Expr u)
  userconNameRange : Range
  userconRange : Range
  userconVis : Visibility
  userconDoc : String
  deriving Repr

inductive TypeDef (t u k : Type) where
  | Synonym (typeDefBinder : TypeBinder k)
            (typeDefParams : List (TypeBinder k))
            (typeDefSynonym : t)
            (typeDefRange : Range)
            (typeDefVis : Visibility)
            (typeDefDoc : String)
  | DataType (typeDefBinder : TypeBinder k)
             (typeDefParams : List (TypeBinder k))
             (typeDefConstrs : List (UserCon t u k))
             (typeDefRange : Range)
             (typeDefVis : Visibility)
             (typeDefSort : DataKind)
             (typeDefDef : DataDef)
             (typeDefEffect : DataEffect)
             (typeDefDoc : String)
  deriving Repr

inductive TypeDefGroup (t k : Type) where
  | TypeDefRec (defns : List (TypeDef t t k))
  | TypeDefNonRec (defn : TypeDef t t k)
  deriving Repr

/- --------------------------------------------------------------------------
  External, Program and Helpers
-------------------------------------------------------------------------- -/

inductive External where
  | mk (extName : Name)
       (extType : UserType)
       (extParams : List ParamInfo)
       (extNameRange : Range)
       (extRange : Range)
       (extInline : List (Target × ExternalCall))
       (extVis : Visibility)
       (extFip : Fip)
       (extDoc : String)
  | ExternalImport (extImport : List (Target × List (String × String))) (extRange : Range)
  deriving Repr, Inhabited

structure Import where
  importName          : Name
  importFullName      : Name
  importNameRange     : Range
  importFullNameRange : Range
  importRange         : Range
  importVis           : Visibility
  importOpen          : Bool
  deriving Repr, Inhabited

structure FixDef where
  fixName   : Name
  fixFixity : Fixity
  fixRange  : Range
  fixVis    : Visibility
  deriving Repr, Inhabited

structure Program (t k : Type) where
  programSource     : Source
  programName       : Name
  programNameRange  : Range
  programTypeDefs   : List (TypeDefGroup t k)
  programDefs       : List (DefGroup t)
  programImports    : List Import
  programExternals  : List External
  programFixDefs    : List FixDef
  programDoc        : String
  deriving Repr

abbrev UserProgram := Program UserType UserKind

instance {t k : Type} : Inhabited (Program t k) where
  default := ⟨sourceNull, Name.nameNil, rangeNull, [], [], [], [], [], ""⟩

def Def.defBinder {t : Type} (d : Def t) : ValueBinder Unit (Expr t) :=
  match d with
  | .mk b _ _ _ _ _ => b

def Def.defRange {t : Type} (d : Def t) : Range :=
  match d with
  | .mk _ r _ _ _ _ => r

def Def.defVis {t : Type} (d : Def t) : Visibility :=
  match d with
  | .mk _ _ v _ _ _ => v

def Def.defSort {t : Type} (d : Def t) : DefSort :=
  match d with
  | .mk _ _ _ s _ _ => s

def Def.defInline {t : Type} (d : Def t) : DefInline :=
  match d with
  | .mk _ _ _ _ i _ => i

def Def.defDoc {t : Type} (d : Def t) : String :=
  match d with
  | .mk _ _ _ _ _ d => d

def defName {t : Type} (defn : Def t) : Name := defn.defBinder.binderName

def typeDefName {t u k : Type} (typeDef : TypeDef t u k) : Name :=
  match typeDef with
  | .Synonym b _ _ _ _ _ => b.tbinderName
  | .DataType b _ _ _ _ _ _ _ _ => b.tbinderName

def defIsVal {t : Type} (defn : Def t) : Bool :=
  not (isDefFun defn.defSort)

def guardTrue {t : Type} : Expr t :=
  .Var nameTrue false rangeNull

def defBody {t : Type} (defn : Def t) : Expr t :=
  defn.defBinder.binderExpr

def defType {t : Type} (defn : Def t) : Option t :=
  match defBody defn with
  | .Ann _ tp _ => some tp
  | _ => none

def typeDefNameRange {t u k : Type} (typeDef : TypeDef t u k) : Range :=
  match typeDef with
  | .Synonym b _ _ _ _ _ => b.tbinderNameRange
  | .DataType b _ _ _ _ _ _ _ _ => b.tbinderNameRange

def typeDefBinderNameRange {t u k : Type} (typeDef : TypeDef t u k) : Range :=
  match typeDef with
  | .Synonym b _ _ _ _ _ => b.tbinderRange
  | .DataType b _ _ _ _ _ _ _ _ => b.tbinderRange

class HasName (a : Type) where
  getName : a → Name
  getNameRange : a → Range

def getRName {a : Type} [HasName a] (x : a) : Name × Range :=
  (HasName.getName x, HasName.getNameRange x)

instance {t k : Type} : HasName (Program t k) where
  getName p := p.programName
  getNameRange p := p.programNameRange

instance {k : Type} : HasName (TypeBinder k) where
  getName tb := tb.tbinderName
  getNameRange tb := tb.tbinderNameRange

instance {t u k : Type} : HasName (UserCon t u k) where
  getName uc := uc.userconName
  getNameRange uc := uc.userconNameRange

instance {t u k : Type} : HasName (TypeDef t u k) where
  getName td := typeDefName td
  getNameRange td := typeDefNameRange td

instance {t e : Type} : HasName (ValueBinder t e) where
  getName vb := vb.binderName
  getNameRange vb := vb.binderNameRange

instance {t : Type} : HasName (Def t) where
  getName d := defName d
  getNameRange d := d.defBinder.binderNameRange


/- --------------------------------------------------------------------------
  Ranged instances
-------------------------------------------------------------------------- -/

def getListRange {a : Type} [Ranged a] (xs : List a) : Range :=
  match xs.head?, xs.getLast? with
  | some h, some l => combineRange (Ranged.getRange h) (Ranged.getRange l)
  | _, _ => rangeNull

instance {a : Type} [Ranged a] : Ranged (List a) where
  getRange := getListRange

mutual
  def Expr.getRange {t : Type} [Ranged t] : Expr t → Range
    | .Lam _ _ _ r => r
    | .Let _ _ r => r
    | .Bind _ _ r => r
    | .App _ _ r => r
    | .Var _ _ r => r
    | .Lit lit => Ranged.getRange lit
    | .Ann _ _ r => r
    | .Case _ _ _ r => r
    | .Parens _ _ _ r => r
    | .Handler _ _ _ _ _ _ _ _ _ _ _ r => r
    | .Inject _ _ _ r => r

  def DefGroup.getRange {t : Type} [Ranged t] : DefGroup t → Range
    | .DefRec ds => match ds.head?, ds.getLast? with
        | some d1, some d2 => combineRange (Def.getRange d1) (Def.getRange d2)
        | _, _ => rangeNull
    | .DefNonRec d => Def.getRange d

  def Def.getRange {t : Type} : Def t → Range
    | .mk _ r _ _ _ _ => r

  def Branch.getRange {t : Type} [Ranged t] : Branch t → Range
    | .mk p gs => combineRange (Pattern.getRange p) (combineRanges (gs.map Guard.getRange))

  def Guard.getRange {t : Type} [Ranged t] : Guard t → Range
    | .mk tst expr => combineRange (Expr.getRange tst) (Expr.getRange expr)

  def Pattern.getRange {t : Type} [Ranged t] : Pattern t → Range
    | .PatWild r => r
    | .PatVar vb => vb.binderRange
    | .PatAnn _ _ r => r
    | .PatCon _ _ _ r => r
    | .PatParens _ r => r
    | .PatLit lit => Ranged.getRange lit

  def HandlerBranch.getRange {t : Type} [Ranged t] : HandlerBranch t → Range
    | .mk _ _ expr _ _ pr => combineRange pr (Expr.getRange expr)
end



instance {t : Type} [Ranged t] : Ranged (Expr t) where
  getRange := Expr.getRange

instance {t : Type} [Ranged t] : Ranged (DefGroup t) where
  getRange := DefGroup.getRange

instance {t : Type} : Ranged (Def t) where
  getRange := Def.getRange

instance {t : Type} [Ranged t] : Ranged (Branch t) where
  getRange := Branch.getRange

instance {t : Type} [Ranged t] : Ranged (Guard t) where
  getRange := Guard.getRange

instance {t : Type} [Ranged t] : Ranged (Pattern t) where
  getRange := Pattern.getRange

instance {t : Type} [Ranged t] : Ranged (HandlerBranch t) where
  getRange := HandlerBranch.getRange

instance {t u k : Type} [Ranged t] [Ranged u] [Ranged k] : Ranged (TypeDef t u k) where
  getRange
    | .Synonym _ _ _ r _ _ => r
    | .DataType _ _ _ r _ _ _ _ _ => r

instance {t u k : Type} : Ranged (UserCon t u k) where
  getRange uc := uc.userconRange

/- --------------------------------------------------------------------------
  Program helpers
-------------------------------------------------------------------------- -/

def preludeImport : Import :=
  ⟨nameSystemCore, nameSystemCore, rangeNull, rangeNull, rangeNull, Visibility.Private, false⟩

def programNull {t k : Type} (name : Name) : Program t k :=
  ⟨sourceNull, name, rangeNull, [], [], [preludeImport], [], [], ""⟩

def makeProgram {t k : Type} (name : Name) (typedefs : List (TypeDef t t k)) (defns1 : List (Def t)) : Program t k :=
  ⟨sourceNull, name, rangeNull, [.TypeDefRec typedefs], [.DefRec defns1], [], [], [], ""⟩

def stripExpr {t : Type} : Expr t → Expr t
  | .Parens e _ _ _ => stripExpr e
  | .Ann e _ _      => stripExpr e
  | e                => e

def programAddImports {t k : Type} (program : Program t k) (imports : List Import) : Program t k :=
  { program with programImports := program.programImports ++ imports }

def programAddDefs {t k : Type} (program : Program t k) (ts1 : List (TypeDef t t k)) (defns1 : List (Def t)) : Program t k :=
  let tdefs' := match program.programTypeDefs with
    | [] => [.TypeDefRec ts1]
    | [.TypeDefRec ts] => [.TypeDefRec (ts.filter (λ t => ts1.all (λ t1 => typeDefName t1 != typeDefName t)) ++ ts1)]
    | _ => panic! "Syntax.Syntax: can not add type definitions to processed tree"
  let defs' := match program.programDefs with
    | [] => [.DefRec defns1]
    | [.DefRec ds] => [.DefRec (ds.filter (λ d => defns1.all (λ d1 => defName d1 != defName d)) ++ defns1)]
    | _ => panic! "Syntax.Syntax: can not add definitions to processed tree"
  { program with programTypeDefs := tdefs', programDefs := defs' }

def programRemoveAllDefs {t k : Type} (program : Program t k) : Program t k :=
  { program with programDefs := [] }

def programRemoveDef {t k : Type} (name : Name) (program : Program t k) : Program t k :=
  let filterTDef := λ
    | .TypeDefRec (ts : List (TypeDef t t k)) => .TypeDefRec (ts.filter (λ t => typeDefName t != name))
    | .TypeDefNonRec (t' : TypeDef t t k) => if typeDefName t' != name then .TypeDefNonRec t' else .TypeDefRec []
  let filterDefns := λ
    | .DefRec (ds : List (Def t)) => .DefRec (ds.filter (λ d => defName d != name))
    | .DefNonRec (d : Def t) => if defName d != name then .DefNonRec d else .DefRec []
  { program with
    programTypeDefs := program.programTypeDefs.map filterTDef,
    programDefs := program.programDefs.map filterDefns }

def programFind {t k : Type} [Ranged t] [Ranged k] (name : Name) (program : Program t k) : Option Range :=
  let tdefs : List (Name × Range) := program.programTypeDefs.flatMap (λ
    | .TypeDefRec ts => ts.map (λ t => (typeDefName t, Ranged.getRange t))
    | .TypeDefNonRec t => [(typeDefName t, Ranged.getRange t)])
  let defns : List (Name × Range) := program.programDefs.flatMap (λ
    | .DefRec ds => ds.map (λ d => (defName d, Ranged.getRange d))
    | .DefNonRec d => [(defName d, Ranged.getRange d)])
  (tdefs ++ defns).find? (λ (n, _) => n == name) |>.map Prod.snd

/- --------------------------------------------------------------------------
  Free type variables
-------------------------------------------------------------------------- -/

mutual
  partial def KUserType.freeTypeVars {k : Type} (tp : KUserType k) : NameSet :=
    match tp with
    | .TpQuan _ { tbinderName := name, .. } tp _ => (KUserType.freeTypeVars tp).erase name
    | .TpFun args effect tp _ =>
        let argTypes := args.map Prod.snd
        let ss := (tp :: effect :: argTypes).map KUserType.freeTypeVars
        ss.foldl NameSet.union {}
    | .TpApp tp args _ => (KUserType.freeTypeVars tp).union (NameSet.unions (args.map KUserType.freeTypeVars))
    | .TpVar name _ => NameSet.singleton name
    | .TpCon _ _ => {}
    | .TpParens tp _ => KUserType.freeTypeVars tp
    | .TpAnn tp _ => KUserType.freeTypeVars tp
end

class HasFreeTypeVar (a : Type) where
  freeTypeVars : a → NameSet

instance {k : Type} : HasFreeTypeVar (KUserType k) where
  freeTypeVars := KUserType.freeTypeVars

instance {a : Type} [HasFreeTypeVar a] : HasFreeTypeVar (Option a) where
  freeTypeVars
    | none => {}
    | some x => HasFreeTypeVar.freeTypeVars x

instance {a : Type} [HasFreeTypeVar a] : HasFreeTypeVar (List a) where
  freeTypeVars xs := NameSet.unions (xs.map HasFreeTypeVar.freeTypeVars)

end Koka.Syntax.Syntax
