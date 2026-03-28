/-
  Ported from Haskell Koka:
  File:   src/Kind/Pretty.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Koka.Lib.PPrint
import Koka.Common.ColorScheme
import Koka.Common.Name
import Koka.Kind.Kind
import Koka.Common.Failure

namespace Koka.Kind.Pretty

open Koka.Lib.PPrint
open Koka.Common.ColorScheme
open Koka.Common.Name
open Koka.Kind.Kind
open Koka.Common.Failure

def kindColon (colors : ColorScheme) : Doc :=
  color colors.colorSep (textP ":")

def keyword (colors : ColorScheme) (s : String) : Doc :=
  color colors.colorKeyword (textP s)

-- | Precedence
abbrev Prec := Int

def precTop : Prec := 0
def precQuant : Prec := 1
def precArrow : Prec := 2
def precApp : Prec := 3
def precAtom : Prec := 4

def pparens (context prec : Prec) (doc : Doc) : Doc :=
  if context >= prec then parens doc else doc

def collectFunArgs (kind : Kind) : List Kind :=
  match kind with
  | .KApp (.KApp (.KCon name) k1) k2 =>
    if name == newName "->" then
      k1 :: collectFunArgs k2
    else [kind]
  | _ => [kind]

def collectArgs (kind : Kind) : List Kind :=
  match kind with
  | .KApp k1 k2 => collectArgs k1 ++ [k2]
  | _ => [kind]

def commaParens (f : α → Doc) (xs : List α) : Doc :=
  tupled (xs.map f)

partial def ppKind (cscheme : ColorScheme) (prec : Prec) (kind : Kind) : Doc :=
  color cscheme.colorKind (
    match kind with
    | .KCon name => Pretty.pretty name
    | .KApp (.KApp (.KCon name) k1) k2 =>
      if name == newName "->" then
        pparens prec precArrow <|
        match collectFunArgs k2 with
        | [res] => ppKind cscheme precArrow k1 <+> textP "->" <+> ppKind cscheme (precArrow - 1) res
        | args =>
          let k1_and_init := k1 :: args.dropLast
          commaParens (ppKind cscheme precTop) k1_and_init <+> textP "->" <+> ppKind cscheme (precArrow - 1) (args.reverse.head!)
      else
        pparens prec precApp <|
        match collectArgs kind with
        | k :: ks => ppKind cscheme (precApp - 1) k <.> commaParens (ppKind cscheme precTop) ks
        | [] => matchFailure "Kind.Pretty.ppKind.KApp"
    | .KApp _ _ =>
      pparens prec precApp <|
      match collectArgs kind with
      | k :: ks => ppKind cscheme (precApp - 1) k <.> commaParens (ppKind cscheme precTop) ks
      | [] => matchFailure "Kind.Pretty.ppKind.KApp"
  )

def niceKinds (colors : ColorScheme) (kinds : List Kind) : List Doc :=
  kinds.map (ppKind colors precTop)

def prettyKind (cscheme : ColorScheme) (k : Kind) : Doc :=
  ppKind cscheme precTop k

instance : Pretty Kind where
  pretty kind := ppKind defaultColorScheme precTop kind

end Koka.Kind.Pretty
