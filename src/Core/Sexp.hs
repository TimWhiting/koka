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
import Data.List (isSuffixOf)
import Common.Name
import Common.NamePrim( nameEffectOpen, nameDecreasing )
import Common.Syntax
import Lib.PPrint
import Core.Core
import Type.Type( Type(..), TypeCon(..), splitFunScheme )
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
  = staggedV "module" (sexpSym modName : map sexpDef (filter (not . isFilteredDef) (flattenDefGroups defGroups)))

-- | Check if a definition should be filtered out (handler internals)
isFilteredDef :: Def -> Bool
isFilteredDef def =
  let n = showPlain (defName def)
  in "/@tag" `isSuffixOf` n || "/@cfc" `isSuffixOf` n

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

  -- Application: check for special cases first
  App open fn r | isJust $ getOpenArg (App open fn r) ->
    sexpExpr $ fromJust $ getOpenArg (App open fn r)

  -- Perform call: (perform label op args...)
  App (TypeApp (Var tname _) tps) args _ | isPerformName (getName tname) ->
    let label = sexpType (last tps)
        -- args: [evv-at-result, select, actual-args...]
        -- Skip evv-at (first arg), get op name from select (second arg)
        opName = getSelectOpName (args !! 1)
        actualArgs = drop 2 args
    in slist (satom "perform" : label : satom opName : map sexpExpr actualArgs)

  -- Handler constructor: (handler ConName [kind name expr] ...)
  -- Skip first arg (tag), use field names from constructor type
  App (Con tname _ _) args _ | isHandlerCon (getName tname) ->
    sexpHandlerCon tname (drop 1 args)

  -- Handler constructor with TypeApp wrapper
  App (TypeApp (Con tname _ _) _) args _ | isHandlerCon (getName tname) ->
    sexpHandlerCon tname (drop 1 args)

  App fn args _ ->
    case getOpenArg fn of
      -- If unwrapped function is also skippable (like pretend-decreasing), skip it too
      Just (Var tname _) | isSkippableName (getName tname), [arg] <- args ->
        sexpExpr arg
      Just (TypeApp (Var tname _) _) | isSkippableName (getName tname), [arg] <- args ->
        sexpExpr arg
      Just arg -> slist (sexpExpr arg : map sexpExpr args)
      Nothing  -> slist (sexpExpr fn : map sexpExpr args)

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

-- | Check if name is a perform function (@perform1, @perform2, etc.)
isPerformName :: Name -> Bool
isPerformName nm = nameModule nm == "std/core/hnd" && "@perform" `isPrefixOf` nameLocal nm
  where
    isPrefixOf prefix str = take (length prefix) str == prefix

-- | Check if a constructor is a handler constructor (@Hnd-*)
isHandlerCon :: Name -> Bool
isHandlerCon nm = "@Hnd-" `isPrefixOf` nameLocal nm
  where
    isPrefixOf prefix str = take (length prefix) str == prefix

-- | Get field names from a constructor's type (raw, not sanitized)
getConFieldNames :: TName -> [String]
getConFieldNames tn =
  case splitFunScheme (typeOf tn) of
    Just (_, params, _, _) -> map (showPlain . fst) params
    Nothing -> []

-- | Format a handler constructor: (handler ConName [kind name expr] ...)
sexpHandlerCon :: TName -> [Expr] -> Doc
sexpHandlerCon tname args =
  let fieldNames = drop 1 (getConFieldNames tname)  -- skip first field (marker)
      pairs = zipWith formatHandlerField fieldNames args
  in slist (satom "handler" : sexpTName tname : pairs)

-- | Format a single handler field: [kind name expr]
-- Detects clause type and strips @fun-/@val-/@ctl- prefix from name
formatHandlerField :: String -> Expr -> Doc
formatHandlerField rawName argExpr =
  let -- Strip @fun-/@val-/@ctl- prefix and determine original kind
      (origKind, baseName) = stripFieldPrefix rawName
      -- Detect actual kind from clause type in argument
      (actualKind, unwrappedExpr) = detectClauseKind argExpr
      -- Use detected kind, or fall back to original if unknown
      kind = if actualKind == "?" then origKind else actualKind
      -- Sanitize the base name (@ -> h-)
      sanitizedName = concatMap (\c -> if c == '@' then "h-" else [c]) baseName
  in sbracket [satom kind, satom sanitizedName, sexpExpr unwrappedExpr]

-- | Strip @fun-/@val-/@ctl- prefix from field name
stripFieldPrefix :: String -> (String, String)
stripFieldPrefix name
  | "@fun-" `isPrefixOf` name = ("fun", drop 5 name)
  | "@val-" `isPrefixOf` name = ("val", drop 5 name)
  | "@ctl-" `isPrefixOf` name = ("ctl", drop 5 name)
  | otherwise = ("?", name)
  where
    isPrefixOf prefix str = take (length prefix) str == prefix

-- | Detect clause kind from expression and unwrap if needed
-- Returns (kind, unwrapped-expr)
detectClauseKind :: Expr -> (String, Expr)
detectClauseKind expr = case unwrapExpr expr of
  -- clause-tail0 is a value, unwrap the application
  App (TypeApp (Var tname _) _) [arg] _ | isClauseTail0 (getName tname) -> ("val", arg)
  App (Var tname _) [arg] _ | isClauseTail0 (getName tname) -> ("val", arg)
  -- Other clause-tail* are functions
  App (TypeApp (Var tname _) _) [arg] _ | isClauseTail (getName tname) -> ("fun", arg)
  App (Var tname _) [arg] _ | isClauseTail (getName tname) -> ("fun", arg)
  -- clause-control* are control operations
  App (TypeApp (Var tname _) _) [arg] _ | isClauseControl (getName tname) -> ("ctl", arg)
  App (Var tname _) [arg] _ | isClauseControl (getName tname) -> ("ctl", arg)
  -- Unknown
  _ -> ("?", expr)
  where
    unwrapExpr (TypeApp e _) = unwrapExpr e
    unwrapExpr (TypeLam _ e) = unwrapExpr e
    unwrapExpr e = e

-- | Check if name is clause-tail0
isClauseTail0 :: Name -> Bool
isClauseTail0 nm = nameModule nm == "std/core/hnd" && nameLocal nm == "clause-tail0"

-- | Check if name is clause-tail* (but not tail0)
isClauseTail :: Name -> Bool
isClauseTail nm = nameModule nm == "std/core/hnd" &&
                  "clause-tail" `isPrefixOf` nameLocal nm &&
                  nameLocal nm /= "clause-tail0"
  where
    isPrefixOf prefix str = take (length prefix) str == prefix

-- | Check if name is clause-control*
isClauseControl :: Name -> Bool
isClauseControl nm = nameModule nm == "std/core/hnd" &&
                     "clause-control" `isPrefixOf` nameLocal nm
  where
    isPrefixOf prefix str = take (length prefix) str == prefix

-- | Extract the operation name from a select function reference
-- The select is typically a Var like "module/effect/@select"
-- We want the local qualified part (the effect/operation name)
getSelectOpName :: Expr -> String
getSelectOpName (Var tname _) =
  let nm = getName tname
      lq = nameLocalQual nm
  in if null lq then nameLocal nm else lq
getSelectOpName (TypeApp e _) = getSelectOpName e
getSelectOpName (App e _ _) = getSelectOpName e
getSelectOpName (Lam _ _ e) = getSelectOpName e  -- unwrap lambda
getSelectOpName (TypeLam _ e) = getSelectOpName e  -- unwrap type lambda
getSelectOpName (Con tname _ _) = showPlain (getName tname)  -- constructor
getSelectOpName (Lit _) = "?lit"
getSelectOpName (Let _ e) = getSelectOpName e  -- unwrap let
getSelectOpName (Case _ _) = "?case"
getSelectOpName _ = "?"

-- | Convert a Type to S-expression (for labels)
-- Extract the label name from a type like TApp (TCon name) [...]
sexpType :: Type -> Doc
sexpType tp = case tp of
  TApp (TCon tc) _ -> satom (showPlain (typeconName tc))
  TCon tc -> satom (showPlain (typeconName tc))
  _ -> satom "?"

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
