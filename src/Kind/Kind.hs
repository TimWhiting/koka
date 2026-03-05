------------------------------------------------------------------------------
-- Copyright 2012-2021, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-
    Definition of kinds and helper functions.
-}
-----------------------------------------------------------------------------
module Kind.Kind( -- * Kinds
                    Kind(..)
                  , KindCon
                 -- * Standard kinds
                  , kindStar, kindEffect, kindArrow, kindScope, kindHeap
                  , kindHandled, kindHandled1, kindLocal
                  , kindFun, kindLabel, extractKindFun, kindFunN
                  , builtinKinds
                  , kindCon, kindConOver
                  , isKindFun
                  , isKindStar
                  , isKindEffect, isKindHandled, isKindHandled1, isKindScope, isKindHeap
                  , isKindLabel, isKindAnyLabel
                  , hasKindStarResult, hasKindLabelResult
                  , kindAddArg
                  ) where

import Common.Name
import Common.NamePrim
import Lib.PPrint (Doc, parens, Pretty (..), (<.>), (<+>), text, tupled)
import Common.Failure (matchFailure)

{--------------------------------------------------------------------------
  Kinds
--------------------------------------------------------------------------}
-- | Kinds
data Kind
  = KCon     !KindCon        -- ^ Kind constants: "*","->","!","H","P"
  | KApp     !Kind !Kind      -- ^ Application (only allowed for functions as yet)
  deriving (Eq,Ord)

instance Show Kind where
  show k = show (ppKind2 precTop k)

type Prec2 = Int

precTop, precQuant,precArrow,precApp,precAtom :: Int
precTop   = 0
precQuant = 1
precArrow = 2
precApp   = 3
precAtom  = 4

pparens :: Prec2 -> Prec2 -> Doc -> Doc
pparens context prec doc
  | context >= prec = parens doc
  | otherwise       = doc


ppKind2 :: Prec2 -> Kind -> Doc
ppKind2 prec kind
  = case kind of
      KCon name      -> pretty name
      KApp (KApp (KCon name) k1) k2 | name == newName "->"
                     -> pparens prec precArrow $
                        case collectFunArgs k2 of
                          [res] -> ppKind2 precArrow k1 <+> text "->" <+> ppKind2 (precArrow-1) res
                          (args) -> commaParens (ppKind2 precTop) (k1:init args) <+> text "->" <+> ppKind2 (precArrow-1) (last args)
                          
      KApp k1 k2     -> pparens prec precApp $
                        case collectArgs kind of
                          (k:ks) -> ppKind2 (precApp-1) k <.> commaParens (ppKind2 precTop) ks
                          _     -> matchFailure "Kind.Pretty.ppKind.KApp"

  where
    commaParens f xs
      = tupled (map f xs)

    collectFunArgs kind
      = case kind of
          KApp (KApp (KCon name) k1) k2 | name == newName "->"
            -> k1 : collectFunArgs k2
          _ -> [kind]
          
    collectArgs kind
      = case kind of
          KApp k1 k2  -> collectArgs k1 ++ [k2]
          _           -> [kind]


-- | Kind constant
type KindCon  = Name

-- | Kind and Type variables come in three flavours: 'Unifiable'
-- variables can be unified, 'Skolem's are non-unifiable (fresh)
-- variables, and 'Bound' variables are bound by a quantifier.
data Flavour  = Bound
              | Skolem
              | Meta    -- used for pretty printing
              deriving(Eq, Show)

hasKindStarResult :: Kind -> Bool
hasKindStarResult kind
  = isKindStar (snd (extractKindFun kind))

hasKindLabelResult :: Kind -> Bool
hasKindLabelResult kind
  = isKindAnyLabel (snd (extractKindFun kind))


{--------------------------------------------------------------------------
  Standard kinds
--------------------------------------------------------------------------}
-- | Kind @V@ (or "*")
kindStar :: Kind
kindStar
  = KCon nameKindStar

-- | Kind @X@, atomic effects
kindLabel :: Kind
kindLabel
  = KCon nameKindLabel

-- | Kind arrow @->@
kindArrow :: Kind
kindArrow
  = KCon nameKindFun

kindAddArg :: Kind -> Kind -> Kind
kindAddArg kfun karg
  = case kfun of
      KApp (KApp k0 k1) k2  | k0 == kindArrow && not (isKindEffect k1 && isKindStar k2)
        -> KApp (KApp k0 k1) (kindAddArg k1 karg)
      _ -> kindFun karg kfun

-- Effect row E
kindEffect :: Kind
kindEffect
  = KCon nameKindEffect

kindScope :: Kind
kindScope
  = KCon nameKindScope

kindHeap :: Kind
kindHeap
  = KCon nameKindHeap

kindLocal :: Kind
kindLocal
  = kindFun kindHeap kindLabel

-- user defined effects: (E,V) -> V
kindHandled :: Kind
kindHandled
  = kindFun kindEffect (kindFun kindStar kindStar) -- KCon nameKindHandled

-- (used defined) linear effects: (E,V) -> V
kindHandled1 :: Kind
kindHandled1
  = kindHandled -- KCon nameKindHandled1

-- Effect extension (X,E) -> E
kindExtend :: Kind
kindExtend
  = kindFun kindLabel (kindFun kindEffect kindEffect)

-- | Kind constructor N from n kind star to kind star
kindCon :: Int -> Kind
kindCon n
  = kindConOver (replicate n kindStar)

kindConOver kinds
  = foldr kindFun kindStar kinds


kindFunN :: [Kind] -> Kind -> Kind
kindFunN kinds kind
  = foldr kindFun kind kinds

-- | Create a (kind) function from a kind to another kind.
kindFun :: Kind -> Kind -> Kind
kindFun k1 k2
  = KApp (KApp kindArrow k1) k2

isKindFun :: Kind -> Bool
isKindFun k
  = case k of
      KApp (KApp k0 k1) k2  -> k0 == kindArrow
      _ -> False


extractKindFun :: Kind -> ([Kind],Kind)
extractKindFun k
  = case k of
      KApp (KApp k0 k1) k2 | k0 == kindArrow
        -> let (args,res) = extractKindFun k2
           in (k1:args,res)
      _ -> ([],k)

isKindStar, isKindLabel, isKindEffect, isKindHandled, isKindScope, isKindHeap :: Kind -> Bool
isKindStar k
  = k == kindStar

isKindEffect k
  = k == kindEffect

isKindLabel k
  = k == kindLabel

isKindScope k
  = k == kindScope

isKindHeap k
  = k == kindHeap

isKindHandled1 k
  = isKindHandled k -- k == kindHandled1

isKindHandled k
  = -- k == kindHandled
    case extractKindFun k of
      ([k1,k2],k3) -> isKindEffect k1 && isKindStar k2 && isKindStar k3
      _            -> False




isKindAnyLabel :: Kind -> Bool
isKindAnyLabel k
  = isKindHandled k || isKindHandled1 k || isKindLabel k

-- | Standard kind constants with their kind.
builtinKinds :: [(Name,Kind)]
builtinKinds
  = [(nameKindStar, kindStar)
    ,(nameKindFun, kindArrow)
    ,(nameKindEffect, kindEffect)
    ,(nameKindLabel, kindLabel)
    ,(nameKindHeap, kindHeap)
    ,(nameKindScope, kindScope)
    -- ,(nameKindHandled, kindHandled)
    -- ,(nameKindHandled1, kindHandled1)
    ]
