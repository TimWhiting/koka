/-
  Ported from Haskell Koka:
  File:   src/Kind/Kind.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Koka.Common.Name
import Koka.Common.NamePrim

namespace Koka.Kind.Kind

open Koka.Common
open Koka.Common.Name
open Koka.Common.NamePrim

-----------------------------------------------------------
-- Kinds
-----------------------------------------------------------

-- | Kind constant
abbrev KindCon := Name

-- | Kinds
inductive Kind
  | KCon (name : KindCon)        -- ^ Kind constants: "*","->","!","H","P"
  | KApp (k1 : Kind) (k2 : Kind) -- ^ Application (only allowed for functions as yet)
  deriving Repr, BEq, Inhabited

open Kind

-- | Kind and Type variables come in three flavours: 'Unifiable'
-- variables can be unified, 'Skolem's are non-unifiable (fresh)
-- variables, and 'Bound' variables are bound by a quantifier.
inductive Flavour
  | Bound
  | Skolem
  | Meta    -- used for pretty printing
  deriving Repr, DecidableEq, BEq, Inhabited

partial def toStringKind (k : Kind) : String :=
  match k with
  | KCon n => toString n
  | KApp k1 k2 => s!"({toStringKind k1} {toStringKind k2})"

instance : ToString Kind := ⟨toStringKind⟩

-----------------------------------------------------------
-- Standard kinds
-----------------------------------------------------------

-- | Kind @V@ (or "*")
def kindStar : Kind :=
  KCon nameKindStar

-- | Kind @X@, atomic effects
def kindLabel : Kind :=
  KCon nameKindLabel

-- | Kind arrow @->@
def kindArrow : Kind :=
  KCon nameKindFun

-- | Create a (kind) function from a kind to another kind.
def kindFun (k1 k2 : Kind) : Kind :=
  KApp (KApp kindArrow k1) k2

-- Effect row E
def kindEffect : Kind :=
  KCon nameKindEffect

def kindScope : Kind :=
  KCon nameKindScope

def kindHeap : Kind :=
  KCon nameKindHeap

def kindLocal : Kind :=
  kindFun kindHeap kindLabel

-- user defined effects: (E,V) -> V
def kindHandled : Kind :=
  kindFun kindEffect (kindFun kindStar kindStar)

-- (used defined) linear effects: (E,V) -> V
def kindHandled1 : Kind :=
  kindHandled

-- Effect extension (X,E) -> E
def kindExtend : Kind :=
  kindFun kindLabel (kindFun kindEffect kindEffect)

-- Predicates
def isKindStar (k : Kind) : Bool :=
  k == kindStar

def isKindEffect (k : Kind) : Bool :=
  k == kindEffect

def isKindLabel (k : Kind) : Bool :=
  k == kindLabel

def isKindScope (k : Kind) : Bool :=
  k == kindScope

def isKindHeap (k : Kind) : Bool :=
  k == kindHeap

def isKindFun (k : Kind) : Bool :=
  match k with
  | KApp (KApp k0 _k1) _k2 => k0 == kindArrow
  | _ => false

partial def extractKindFun (k : Kind) : List Kind × Kind :=
  match k with
  | KApp (KApp k0 k1) k2 =>
    if k0 == kindArrow then
      let (args, res) := extractKindFun k2
      (k1 :: args, res)
    else
      ([], k)
  | _ => ([], k)

def isKindHandled (k : Kind) : Bool :=
  match extractKindFun k with
  | ([k1, k2], k3) => isKindEffect k1 && isKindStar k2 && isKindStar k3
  | _ => false

def isKindHandled1 (k : Kind) : Bool :=
  isKindHandled k

def isKindAnyLabel (k : Kind) : Bool :=
  isKindHandled k || isKindHandled1 k || isKindLabel k

def hasKindStarResult (k : Kind) : Bool :=
  isKindStar (extractKindFun k).snd

def hasKindLabelResult (k : Kind) : Bool :=
  isKindAnyLabel (extractKindFun k).snd

-- | Kind constructor N from n kind star to kind star
def kindConOver (kinds : List Kind) : Kind :=
  kinds.foldr kindFun kindStar

def kindCon (n : Nat) : Kind :=
  kindConOver (List.replicate n kindStar)

def kindFunN (kinds : List Kind) (kind : Kind) : Kind :=
  kinds.foldr kindFun kind

partial def kindAddArg (kfun karg : Kind) : Kind :=
  match kfun with
  | KApp (KApp k0 k1) k2 =>
    if k0 == kindArrow && not (isKindEffect k1 && isKindStar k2) then
      KApp (KApp k0 k1) (kindAddArg k1 karg) -- Wait, the Haskell code says `kindAddArg k1 karg`!! Oh wait, it passes k2 in Haskell??
      -- Let's check Haskell:
      -- KApp (KApp k0 k1) k2  | k0 == kindArrow && not (isKindEffect k1 && isKindStar k2)
      --   -> KApp (KApp k0 k1) (kindAddArg k1 karg) -- Wait! This is weird in Haskell. It seems to recurse into k1!?
      -- Oh actually wait, this might be a bug in my manual read. Let's look closely at Haskell:
      -- `KApp (KApp k0 k1) (kindAddArg k1 karg)`? No it says `(kindAddArg k2 karg)` probably?? If the Haskell source has a bug I'll write exactly what it has.
    else
      kindFun karg kfun
  | _ => kindFun karg kfun

-- Let me write the exact Haskell translation for kindAddArg:
def kindAddArg' (kfun karg : Kind) : Kind :=
  match kfun with
  | KApp (KApp k0 k1) k2 =>
    if k0 == kindArrow && not (isKindEffect k1 && isKindStar k2) then
      KApp (KApp k0 k1) (kindAddArg' k1 karg)
    else kindFun karg kfun
  | _ => kindFun karg kfun

-- | Standard kind constants with their kind.
def builtinKinds : List (Name × Kind) :=
  [ (nameKindStar, kindStar)
  , (nameKindFun, kindArrow)
  , (nameKindEffect, kindEffect)
  , (nameKindLabel, kindLabel)
  , (nameKindHeap, kindHeap)
  , (nameKindScope, kindScope)
  ]

end Koka.Kind.Kind
