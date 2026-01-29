-----------------------------------------------------------------------------
-- Copyright 2012-2025, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-  Export Core syntax as S-expressions without types or type applications.
-}
-----------------------------------------------------------------------------

module Core.Sexp( sexpCore, sexpExpr, sexpDef, sexpDefGroup, sexpLit ) where

import Data.Char (isAlphaNum)
import Common.Name
import Common.NamePrim( nameEffectOpen, nameDecreasing )
import Common.Syntax
import Lib.PPrint
import Core.Core
import Data.Maybe (fromJust, isJust)

{--------------------------------------------------------------------------
  S-expression combinators
--------------------------------------------------------------------------}

-- | Create an S-expression list with parens
slist :: [Doc] -> Doc
slist ds = parens (hsep ds)

-- | Create a bracketed list with square brackets
sbracket :: [Doc] -> Doc
sbracket ds = brackets (hsep ds)

-- | Create a multi-line S-expression list
slistV :: [Doc] -> Doc
slistV [] = text "()"
slistV ds = parens (nest 2 (vcat ds))

-- | Create a tagged S-expression with vertical body
staggedV :: String -> [Doc] -> Doc
staggedV tag [] = slist [satom tag]
staggedV tag ds = staggedBlock tag empty ds

-- | Create an atom/symbol
satom :: String -> Doc
satom = text

-- | Create a string literal in S-expression format
sstring :: String -> Doc
sstring s = dquotes (text (escapeString s))
  where
    escapeString = concatMap escapeChar
    escapeChar '\\' = "\\\\"
    escapeChar '"'  = "\\\""
    escapeChar '\n' = "\\n"
    escapeChar '\t' = "\\t"
    escapeChar c    = [c]

-- | Create a tagged S-expression
stagged :: String -> [Doc] -> Doc
stagged tag ds = slist (satom tag : ds)

-- | Create a tagged S-expression with hanging body (for fn, match, let, def)
-- tag first
--   body1
--   body2
staggedHang :: String -> Doc -> [Doc] -> Doc
staggedHang tag first rest = staggedBlock tag (space <.> first) rest

-- | Common implementation for vertical tagged S-expressions
staggedBlock :: String -> Doc -> [Doc] -> Doc
staggedBlock tag first rest
  = text "(" <.> satom tag <.> first <-->
    indent 2 (vcat rest) <.> text ")"

{--------------------------------------------------------------------------
  Core module
--------------------------------------------------------------------------}

-- | Convert a Core module to S-expression
sexpCore :: Core -> Doc
sexpCore (Core modName _imports _fixDefs _typeDefGroups defGroups _externals _doc)
  = staggedV "module" (sexpSym modName : map sexpDef (flattenDefGroups defGroups))

{--------------------------------------------------------------------------
  Definitions
--------------------------------------------------------------------------}

-- | Convert a DefGroup to list of bindings in square brackets
sexpDefGroup :: DefGroup -> [Doc]
sexpDefGroup (DefRec defs) = map sexpBinding defs
sexpDefGroup (DefNonRec def) = [sexpBinding def]

-- | Convert a Def to a binding: [name expr]
sexpBinding :: Def -> Doc
sexpBinding def = sbracket [sexpSym (defName def), sexpExpr (defExpr def)]

-- | Convert a Def to S-expression (for top-level defs)
sexpDef :: Def -> Doc
sexpDef def
  = staggedHang "define" (sexpSym (defName def)) [sexpExpr (defExpr def)]

{--------------------------------------------------------------------------
  Expressions
--------------------------------------------------------------------------}

-- | Convert an Expr to S-expression (skip TypeLam and TypeApp)
sexpExpr :: Expr -> Doc
sexpExpr expr = case expr of
  -- Skip type abstractions - just process the body
  TypeLam _ e -> sexpExpr e

  -- Skip type applications - just process the expression
  TypeApp e _ -> sexpExpr e

  -- Lambda: (λ (params...)
  --           body)
  Lam tnames _eff body ->
    staggedHang "λ" (slist (map sexpTName tnames)) [sexpExpr body]

  -- Variable: just the name
  Var tname _info -> 
    if isSkippableName (getName tname) then error "Open"
    else sexpTName tname

  -- Application: check for @open wrapper first
  App open fn r | isJust $ getOpenArg (App open fn r) ->
    sexpExpr $ fromJust $ getOpenArg (App open fn r)
  App fn args _ ->
    case getOpenArg fn of
      -- If unwrapped function is also skippable (like pretend-decreasing), skip it too
      Just (Var tname _) | isSkippableName (getName tname), [arg] <- args ->
        sexpExpr arg
      Just (TypeApp (Var tname _) _) | isSkippableName (getName tname), [arg] <- args ->
        sexpExpr arg
      Just arg -> slist [sexpExpr arg, slist (map sexpExpr args)]
      Nothing  -> slist [sexpExpr fn, slist (map sexpExpr args)]

  -- Constructor: just the name
  Con tname _repr _ -> sexpTName tname

  -- Literal
  Lit lit -> sexpLit lit

  -- Let binding: (letrec* ([name expr] ...)
  --                body)
  Let defGroups body ->
    staggedHang "letrec*" (slist (concatMap sexpDefGroup defGroups)) [sexpExpr body]

  -- Case/match expression: (match scrutinee
  --                          [pat body] ...)
  Case exprs branches ->
    staggedHang "match" (sexpExpr (head exprs)) (map sexpBranch branches)

{--------------------------------------------------------------------------
  Supporting constructs
--------------------------------------------------------------------------}

-- | Convert a TName to S-expression (just the name as symbol)
sexpTName :: TName -> Doc
sexpTName tname = sexpSym (getName tname)

-- | Convert a Name to a symbol, escaping with pipes if needed
--   Replaces '@' with 'h-' for Racket compatibility (hidden/generated names)
sexpSym :: Name -> Doc
sexpSym name = satom (escapeSymbol (sanitize (showPlain name)))
  where
    sanitize = concatMap (\c -> if c == '@' then "h-" else [c])
    escapeSymbol s
      | needsEscape s = "|" ++ s ++ "|"
      | otherwise     = s
    needsEscape s = null s || any (not . isSymChar) s
    isSymChar c = isAlphaNum c || c `elem` "-_/!?<>=*+.$%^&~"

-- | Check if name is @open or pretend-decreasing
isSkippableName :: Name -> Bool
isSkippableName nm = nm == nameEffectOpen || nm == nameDecreasing

-- | Extract argument from @open or pretend-decreasing application
getOpenArg :: Expr -> Maybe Expr
getOpenArg (App (TypeApp (Var tname _) _) [arg] _)
  | isSkippableName (getName tname) = Just arg
getOpenArg (App (Var tname _) [arg] _)
  | isSkippableName (getName tname) = Just arg
getOpenArg (App (TypeApp e _) args rng) = getOpenArg (App e args rng)
getOpenArg (TypeApp e _) = getOpenArg e
getOpenArg _ = Nothing

-- | Convert a Branch to S-expression: [pattern body]
sexpBranch :: Branch -> Doc
sexpBranch (Branch patterns guards)
  = sbracket
      [ sexpPattern (head patterns)
      , sexpGuard (head guards)
      ]

-- | Convert a Guard to S-expression (just the body)
sexpGuard :: Guard -> Doc
sexpGuard (Guard _test body) = sexpExpr body

-- | Convert a Pattern to S-expression
sexpPattern :: Pattern -> Doc
sexpPattern pat = case pat of
  -- Constructor pattern: (ConName subpat1 subpat2 ...)
  PatCon tname patterns _repr _typeArgs _exists _typeRes _conInfo _skip
    | null patterns -> sexpTName tname
    | otherwise -> slist (sexpTName tname : map sexpPattern patterns)

  -- Variable pattern with wild subpattern: just the name
  PatVar tname PatWild -> sexpTName tname

  -- Variable pattern with actual subpattern: (as name subpat)
  PatVar tname subPat ->
    stagged "as" [sexpTName tname, sexpPattern subPat]

  PatLit lit -> sexpLit lit

  PatWild -> satom "_"

-- | Convert a Lit to S-expression
sexpLit :: Lit -> Doc
sexpLit lit = case lit of
  LitInt i    -> pretty i
  LitFloat d  -> pretty d
  LitChar c   -> stagged "char" [sstring [c]]
  LitString s -> sstring s
