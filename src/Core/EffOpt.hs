-----------------------------------------------------------------------------
-- Copyright 2012-2021, Microsoft Research, Steven Fontanella, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
module Core.EffOpt( opt ) where

import Data.List (transpose, foldl', intersect, intersperse)
import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Control.Arrow ((***))
import Data.Monoid((<>), Alt(..), Endo(..))
import Data.Maybe (mapMaybe, fromMaybe, catMaybes, isJust, fromJust)
import Data.Function
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Control.Monad(guard)
import Lib.PPrint
import Common.Failure (failure, HasCallStack)
import Common.File (splitOn)
import Common.Range (rangeNull)
import Common.Syntax
import Common.Unique (HasUnique)
import Common.Name
import Common.NamePrim( nameAlwaysMon, nameNeverMon )
import Common.NameMap (NameMap)
import qualified Common.NameMap  as M
import Common.NameSet (NameSet)
import qualified Common.NameSet as S
import Common.Unique
import Core.Core
import Core.CoreVar
import Core.Pretty ()
import Core.Simplify
import Type.Type (splitFunScheme, splitFunType, splitTypeScheme, Effect, Type(..), TypeVar(..), Flavour(..), eqType, eqTypes, typeFun, typeTotal, tForall)  
import Type.TypeVar
import Type.Pretty
import Kind.Kind (kindStar)
import Lib.Trace
import Core.Inlines
import Core.Uniquefy

import Lib.Trace
import Core.FlowAnalysis.Full.DMCFAR.Monad
import Core.FlowAnalysis.Full.DMCFAR.AbstractValue
import Core.FlowAnalysis.Full.DMCFAR.Syntax (alwaysMon, neverMon)
import Core.FlowAnalysis.StaticContext
import qualified Core.Core as Core
import Compile.Module (moduleNull, Module(..), modCore)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.List as L

data PreprocessedCache = PreprocessedCache {
  alwaysMonCtxs :: [ExprContext],
  neverMonCtxs :: [ExprContext]
}

opt :: Name -> M.Map FixInput FixOutput -> Core.DefGroups -> Core.DefGroups
opt modName analysisCache dgs = 
  let preprocessed = preprocessCache analysisCache
      rootCtxId = ExprContextId (-1) modName
      -- Create a minimal stub module just for context construction (won't be dereferenced)
      stubModule = (moduleNull modName){ modCore = Just $ Core.Core modName [] [] [] [] [] "" }
      rootCtx = ModuleC rootCtxId stubModule modName
      hasResults = not (null (alwaysMonCtxs preprocessed) && null (neverMonCtxs preprocessed))
  in if hasResults then map (optDefGroup preprocessed rootCtx True) dgs
     else dgs

preprocessCache :: M.Map FixInput FixOutput -> PreprocessedCache
preprocessCache cache = 
  let am = alwaysMon cache
      nm = neverMon cache
      amKeys = M.keys am
      nmKeys = M.keys nm
  in PreprocessedCache {
       alwaysMonCtxs = amKeys,
       neverMonCtxs = nmKeys
     }

dummyName :: Name
dummyName = nameNil

dummyCtxId :: Name -> ExprContextId
dummyCtxId mn = ExprContextId (-1) mn

optDefGroup :: PreprocessedCache -> ExprContext -> Bool -> DefGroup -> DefGroup
optDefGroup p ctx hasResults dg = 
  let mn = moduleName (contextId ctx)
      groupCtx = DefCGroup (dummyCtxId mn) ctx (dgTNames dg) dg
  in case dg of
       DefRec defs -> DefRec (zipWith (\i def -> optDef p (DefCRec (dummyCtxId mn) groupCtx i (dgTNames dg)) hasResults def) [0..] defs)
       DefNonRec def -> DefNonRec (optDef p (DefCNonRec (dummyCtxId mn) groupCtx (defTName def)) hasResults def)

optDef :: PreprocessedCache -> ExprContext -> Bool -> Def -> Def
optDef p ctx hasResults def = 
  def { defExpr = optExpr p ctx hasResults (defExpr def) }

optExpr :: PreprocessedCache -> ExprContext -> Bool -> Expr -> Expr
optExpr p ctx hasResults expr = 
  let mn = moduleName (contextId ctx)
  in case expr of
        App f args rng -> 
          let fCtx = AppCLambda (dummyCtxId mn) ctx f
              fTraversed = optExpr p fCtx hasResults f
              fAnnotated = wrapAnnotation p ctx fTraversed
              argsTraversed = zipWith (\i arg -> optExpr p (AppCParam (dummyCtxId mn) ctx i arg) hasResults arg) [0..] args
          in App fAnnotated argsTraversed rng
        Lam params eff body -> 
          let bodyCtx = LamCBody (dummyCtxId mn) ctx params body
          in Lam params eff (optExpr p bodyCtx hasResults body)
        Let dgs body -> 
          let (dgsOptimized, bodyCtx) = optLetGroups p ctx hasResults 0 dgs body
          in Let dgsOptimized (optExpr p bodyCtx hasResults body)
        Case scruts branches -> 
          let scruts' = map (\s -> optExpr p (CaseCScrutinee (dummyCtxId mn) ctx s) hasResults s) scruts
          in Case scruts' (zipWith (\i br -> optBranch p ctx hasResults i br) [0..] branches)
        -- TypeApp wrapping an App: unwrap, annotate the inner function, then re-wrap.
        -- The context for the inner function and args is the same as for the outer TypeApp
        -- because the analysis records the App position, not the TypeApp position.
        TypeApp (App innerF args rng) tps ->
          let fCtx = AppCLambda (dummyCtxId mn) ctx innerF
              fTraversed = optExpr p fCtx hasResults innerF
              fAnnotated = wrapAnnotation p ctx fTraversed
              argsTraversed = zipWith (\i arg -> optExpr p (AppCParam (dummyCtxId mn) ctx i arg) hasResults arg) [0..] args
          in TypeApp (App fAnnotated argsTraversed rng) tps
        TypeApp f tps ->
          TypeApp (optExpr p ctx hasResults f) tps
        TypeLam tvs e -> TypeLam tvs (optExpr p ctx hasResults e)
        _ -> expr

-- Wrap a traversed function with an alwaysMon or neverMon annotation if the
-- current context matches the analysis results. Guards against double-wrapping
-- and non-function types.
wrapAnnotation :: PreprocessedCache -> ExprContext -> Expr -> Expr
wrapAnnotation p ctx fTraversed
  | isAlreadyAnnotated = fTraversed
  | not hasFunType     = fTraversed
  | matchesAlways      = mkAnnotation nameAlwaysMon fTraversed
  | matchesNever       = mkAnnotation nameNeverMon  fTraversed
  | otherwise          = fTraversed
  where
    matchesAlways      = any (matchesExprContext ctx) (alwaysMonCtxs p)
    matchesNever       = any (matchesExprContext ctx) (neverMonCtxs p)
    hasFunType         = case splitFunType (snd (splitTypeScheme (typeOf fTraversed))) of
                           Just _ -> True
                           Nothing -> False
    isAlreadyAnnotated = case fTraversed of
                           App (Var nm _) _ _ -> getName nm == nameAlwaysMon || getName nm == nameNeverMon
                           _                  -> False

mkAnnotation :: Name -> Expr -> Expr
mkAnnotation annName f =
  let fType   = typeOf f
      annType = typeFun [(nameNil, fType)] typeTotal fType
  in App (Var (TName annName annType Nothing) (InfoExternal [(Default,"#1")])) [f] Nothing

-- Mirrors the nested structure created by makeGroups in Monad.hs
optLetGroups :: PreprocessedCache -> ExprContext -> Bool -> Int -> [DefGroup] -> Expr -> ([DefGroup], ExprContext)
optLetGroups p parentCtx hasResults i [] bodyExpr = 
  let mn = moduleName (contextId parentCtx)
      bodyCtx = LetCBody (dummyCtxId mn) parentCtx [] bodyExpr
  in ([], bodyCtx)
optLetGroups p parentCtx hasResults i (dg:dgs) bodyExpr = 
  let mn = moduleName (contextId parentCtx)
      groupCtx = LetCDefGroup (dummyCtxId mn) parentCtx (dgTNames dg) i dg
      optDg = case dg of
        DefRec defs -> DefRec (map (\def -> optDef p (LetCDefRec (dummyCtxId mn) groupCtx (defIndex def defs) (dgTNames dg)) hasResults def) defs)
        DefNonRec def -> DefNonRec (optDef p (LetCDefNonRec (dummyCtxId mn) groupCtx (defTName def)) hasResults def)
      (restDgs, bodyCtx) = optLetGroups p groupCtx hasResults (i + 1) dgs bodyExpr
  in (optDg : restDgs, bodyCtx)
  where
    defIndex d ds = maybe 0 id (L.elemIndex d ds)

-- Structural comparison of ExprContexts (ignoring IDs)
matchesExprContext :: ExprContext -> ExprContext -> Bool
matchesExprContext c1 c2 = case (c1, c2) of
  (ModuleC _ _ n1, ModuleC _ _ n2) -> n1 == n2
  (DefCRec _ p1 i1 ns1, DefCRec _ p2 i2 ns2) -> i1 == i2 && (not (null ns1 || null ns2) && getName (ns1 !! min i1 (length ns1-1)) == getName (ns2 !! min i2 (length ns2-1))) && matchesExprContext p1 p2
  (DefCNonRec _ p1 tn1, DefCNonRec _ p2 tn2) -> getName tn1 == getName tn2 && matchesExprContext p1 p2
  (DefCGroup _ p1 _ _, DefCGroup _ p2 _ _) -> matchesExprContext p1 p2
  (LetCDefRec _ p1 i1 ns1, LetCDefRec _ p2 i2 ns2) -> i1 == i2 && (not (null ns1 || null ns2) && getName (ns1 !! min i1 (length ns1-1)) == getName (ns2 !! min i2 (length ns2-1))) && matchesExprContext p1 p2
  (LetCDefNonRec _ p1 tn1, LetCDefNonRec _ p2 tn2) -> getName tn1 == getName tn2 && matchesExprContext p1 p2
  (LetCDefGroup _ p1 _ i1 _, LetCDefGroup _ p2 _ i2 _) -> i1 == i2 && matchesExprContext p1 p2
  (LetCBody _ p1 _ _, LetCBody _ p2 _ _) -> matchesExprContext p1 p2
  (LamCBody _ p1 _ _, LamCBody _ p2 _ _) -> matchesExprContext p1 p2
  (AppCLambda _ p1 _, AppCLambda _ p2 _) -> matchesExprContext p1 p2
  (AppCParam _ p1 i1 _, AppCParam _ p2 i2 _) -> i1 == i2 && matchesExprContext p1 p2
  (CaseCScrutinee _ p1 _, CaseCScrutinee _ p2 _) -> matchesExprContext p1 p2
  (CaseCBranch _ p1 _ i1 _, CaseCBranch _ p2 _ i2 _) -> i1 == i2 && matchesExprContext p1 p2
  (CaseCGuard _ p1 _ i1 _ _, CaseCGuard _ p2 _ i2 _ _) -> i1 == i2 && matchesExprContext p1 p2
  (CaseCBody _ p1 _ i1 _ _, CaseCBody _ p2 _ i2 _ _) -> i1 == i2 && matchesExprContext p1 p2
  (ExprCBasic _ p1 _, ExprCBasic _ p2 _) -> matchesExprContext p1 p2
  _ -> False

optBranch :: PreprocessedCache -> ExprContext -> Bool -> Int -> Branch -> Branch
optBranch p ctx hasResults branchIdx br@(Branch pats guards) = 
  let mn = moduleName (contextId ctx)
      branchCtx = CaseCBranch (dummyCtxId mn) ctx (branchVars br) branchIdx br
  in Branch pats (zipWith (\i g -> optGuard p branchCtx hasResults br i g) [0..] guards)

optGuard :: PreprocessedCache -> ExprContext -> Bool -> Branch -> Int -> Guard -> Guard
optGuard p ctx hasResults br guardIdx (Guard test body) = 
  let mn = moduleName (contextId ctx)
      bodyCtx = CaseCBody (dummyCtxId mn) ctx [] guardIdx br body
  in Guard test (optExpr p bodyCtx hasResults body)
