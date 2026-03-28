/-
  Ported from Haskell Koka:
  File:   src/Common/Error.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Koka.Lib.PPrint
import Koka.Common.Range
import Koka.Common.ColorScheme
import Koka.Common.Message

namespace Koka.Common.Error

open Koka.Lib.PPrint
open Koka.Common.Range
open Koka.Common.ColorScheme
open Koka.Common.Message

-----------------------------------------------------------
-- Error messages
-----------------------------------------------------------

inductive ErrorSeverity
  | SevInfo
  | SevWarning
  | SevError
  deriving Repr, BEq, Inhabited, DecidableEq, Ord

inductive ErrorKind
  | ErrGeneral
  | ErrParse
  | ErrStatic
  | ErrKind
  | ErrType
  | ErrBuild
  | ErrInternal
  deriving Repr, BEq, Inhabited

structure ErrorMessage where
  errRange : Range
  errMessage : Doc
  errSeverity : ErrorSeverity
  errKind : ErrorKind
  deriving Inhabited

structure Errors where
  errors : List ErrorMessage
  deriving Inhabited

abbrev Warnings := Errors

instance : Ranged ErrorMessage where
  getRange err := err.errRange

instance : Ranged Errors where
  getRange errs := combineRanges (errs.errors.map Ranged.getRange)

def isWarning (emsg : ErrorMessage) : Bool :=
  match emsg.errSeverity with
  | .SevInfo | .SevWarning => true
  | .SevError => false

def infoMessageKind (ekind : ErrorKind) (r : Range) (doc : Doc) : ErrorMessage :=
  { errRange := r, errMessage := doc, errSeverity := ErrorSeverity.SevInfo, errKind := ekind }

def warningMessageKind (ekind : ErrorKind) (r : Range) (doc : Doc) : ErrorMessage :=
  { errRange := r, errMessage := doc, errSeverity := ErrorSeverity.SevWarning, errKind := ekind }

def errorMessageKind (ekind : ErrorKind) (r : Range) (doc : Doc) : ErrorMessage :=
  { errRange := r, errMessage := doc, errSeverity := ErrorSeverity.SevError, errKind := ekind }

def warningMessage (r : Range) (doc : Doc) : ErrorMessage :=
  warningMessageKind ErrorKind.ErrGeneral r doc

def errorMessage (r : Range) (doc : Doc) : ErrorMessage :=
  errorMessageKind ErrorKind.ErrGeneral r doc

def errorsNil : Errors :=
  { errors := [] }

def errorsSingle (err : ErrorMessage) : Errors :=
  { errors := [err] }

def errorsAdd (errs : List ErrorMessage) (e : Errors) : Errors :=
  { errors := e.errors ++ errs }

def mergeErrors (e1 e2 : Errors) : Errors :=
  { errors := e1.errors ++ e2.errors }

-----------------------------------------------------------
-- pretty
-----------------------------------------------------------

def ppErrorSeverity (cscheme : ColorScheme) (ekind : ErrorKind) (sev : ErrorSeverity) : Doc :=
  let header (clr : Color) (txt : String) := color clr (textP (ekindTxt ++ txt ++ ":"))
  match sev with
  | .SevError => header cscheme.colorError "error"
  | .SevWarning => header cscheme.colorWarning "warning"
  | .SevInfo => header cscheme.colorWarning "info"
where
  ekindTxt := match ekind with
  | .ErrParse => "parse "
  | .ErrKind => "kind "
  | .ErrType => "type "
  | .ErrBuild => "build "
  | .ErrInternal => "internal "
  | _ => ""

def ppErrorMessage (cwd : String) (endToo : Bool) (cscheme : ColorScheme) (err : ErrorMessage) : Doc :=
  hang 2 (
    ppRange cwd endToo cscheme err.errRange <.> colon <+>
    ppErrorSeverity cscheme err.errKind err.errSeverity <+>
    err.errMessage
  )

def ppErrors (cwd : String) (endToo : Bool) (cscheme : ColorScheme) (errs : Errors) : Doc :=
  vcat (errs.errors.map (ppErrorMessage cwd endToo cscheme))

instance : Pretty ErrorMessage where
  pretty msg := ppErrorMessage "" false defaultColorScheme msg

instance : Pretty Errors where
  pretty errs := ppErrors "" false defaultColorScheme errs

instance : ToString ErrorMessage where
  toString err := displayS (renderCompact (Pretty.pretty err))

instance : ToString Errors where
  toString errs := displayS (renderCompact (Pretty.pretty errs))

def toWarning (ekind : ErrorKind) (twi : Range × Doc) : ErrorMessage :=
  warningMessageKind ekind twi.fst twi.snd

-----------------------------------------------------------
-- Errors monad
-----------------------------------------------------------

inductive ErrorM (b : Type α) (a : Type β)
  | Error (errs : Errors) (m : Option b)
  | Ok (v : a) (w : Warnings) (m : Option b)
  deriving Inhabited

open ErrorM

def checkError {b a} (err : ErrorM b a) : Except Errors (a × Warnings) :=
  match err with
  | Error errs _ => Except.error errs
  | Ok x w _ => Except.ok (x, w)

def checkPartial {b a} (err : ErrorM b a) : Except (Errors × Option b) (a × Warnings × Option b) :=
  match err with
  | Error errs m => Except.error (errs, m)
  | Ok x w m => Except.ok (x, w, m)

def setPartial {c b a} (cv : Option c) (err : ErrorM b a) : ErrorM c a :=
  match err with
  | Error msg _ => Error msg cv
  | Ok x w _ => Ok x w cv

def addPartialResult {b a} (err : ErrorM b a) (m : Option b) : ErrorM b a :=
  match err with
  | Error errs m1 => Error errs (m1 <|> m)
  | Ok x ws m1 => Ok x ws (m1 <|> m)

def handleError {b a} (err : ErrorM b a) (handle : Errors → ErrorM b a) : ErrorM b a :=
  match err with
  | Error errs m => addPartialResult (handle errs) m
  | Ok x w m => Ok x w m

def ok {b a} (x : a) : ErrorM b a :=
  Ok x errorsNil none

def errorMsgs {b a} (errs : List ErrorMessage) : ErrorM b a :=
  Error (Errors.mk errs) none

def errorMsg {b a} (msg : ErrorMessage) : ErrorM b a :=
  Error (errorsSingle msg) none

def errorMsgsPartial {b a} (msgs : List ErrorMessage) (bv : Option b) : ErrorM b a :=
  Error (Errors.mk msgs) bv

def errorMsgPartial {b a} (msg : ErrorMessage) (bv : Option b) : ErrorM b a :=
  Error (errorsSingle msg) bv

def warningMsg {b} (w : ErrorMessage) : ErrorM b Unit :=
  Ok () (errorsSingle w) none

def addErrorMsg {b} (err : ErrorMessage) : ErrorM b Unit :=
  warningMsg err

def warningMsgs {b} (ws : List ErrorMessage) : ErrorM b Unit :=
  Ok () (Errors.mk ws) none

def addWarnings {b a} (ws : List ErrorMessage) (err : ErrorM b a) : ErrorM b a :=
  match ws with
  | [] => err
  | _ =>
    match err with
    | Error errs m => Error (errorsAdd ws errs) m
    | Ok x ws2 m => Ok x (errorsAdd ws ws2) m

def overridePartialResult {b a} (err : ErrorM b a) (m : Option b) : ErrorM b a :=
  match err with
  | Error errs m1 => Error errs (m <|> m1)
  | Ok x ws m1 => Ok x ws (m <|> m1)

def ignoreWarnings {b a} (err : ErrorM b a) : ErrorM b a :=
  match err with
  | Error (Errors.mk errs) m => Error (Errors.mk (errs.filter (not ∘ isWarning))) m
  | Ok x (Errors.mk _ws) m => Ok x errorsNil m

-----------------------------------------------------------
-- instances
-----------------------------------------------------------

instance {b} : Functor (ErrorM b) where
  map f e :=
    match e with
    | Ok x w m => Ok (f x) w m
    | Error msg m => Error msg m

instance {b} : Applicative (ErrorM b) where
  pure x := Ok x errorsNil none
  seq f x :=
    match f with
    | Ok fv w m =>
      match x () with
      | Ok xv w2 m2 => Ok (fv xv) (mergeErrors w w2) (m <|> m2)
      | Error msg m2 => Error (mergeErrors w msg) (m <|> m2)
    | Error msg m => Error msg m

instance {b} : Monad (ErrorM b) where
  bind e f :=
    match e with
    | Ok x (Errors.mk ws) m => addPartialResult (addWarnings ws (f x)) m
    | Error msg m => Error msg m

instance {b} : Alternative (ErrorM b) where
  failure := Error errorsNil none
  orElse e1 e2 :=
    match e1 with
    | Ok _ _ _ => e1
    | Error m1 m11 =>
      match e2 () with
      | Ok xv w2 m2 => addPartialResult (Ok xv w2 m2) m11
      | Error m2 m12 => Error (mergeErrors m1 m2) (m12 <|> m11)

end Koka.Common.Error
