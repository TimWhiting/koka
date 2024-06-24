
-----------------------------------------------------------------------------
-- Copyright 2024, Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}

module Core.FlowAnalysis.Demand.Syntax where

import Data.List (intercalate, find)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Maybe (catMaybes, mapMaybe, isJust)
import Data.Set(Set)
import Compile.Module (Module(..))
import qualified Syntax.Syntax as Syn
import qualified Syntax.Syntax as S
import Syntax.Pretty
import Syntax.RangeMap
import qualified Core.Core as C
import Common.Range
import Common.Name (Name(..))
import Core.Core
import Type.Type
import Lib.PPrint
import Compile.BuildMonad (BuildContext, Build)
import Compile.Options (Terminal, Flags)
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Syntax
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.Demand.AbstractValue
import Core.FlowAnalysis.Demand.DemandMonad
import Core.FlowAnalysis.Demand.Primitives
import Core.FlowAnalysis.Demand.DemandAnalysis (query, getAbValueResults)
import Debug.Trace (trace)
import Core.Pretty (prettyExpr)
import Type.Pretty (defaultEnv)
import Data.Foldable (minimumBy)
import Common.Failure (HasCallStack)
import Common.Error (Errors)

getAbResult :: (EnvCtx, AbValue) -> PostFixR x s e (EnvCtx, ([S.UserExpr], [S.UserDef], [S.External], [Syn.Lit], [String], Set Type))
getAbResult (envctx, res) = do
  let vals = [res]
      lams = map fst $ concatMap (S.toList . aclos) vals
      i = concatMap ((mapMaybe toSynLit . M.elems) . intV) vals
      f = concatMap ((mapMaybe toSynLitD . M.elems) . floatV) vals
      c = concatMap ((mapMaybe toSynLitC . M.elems) . charV) vals
      s = concatMap ((mapMaybe toSynLitS . M.elems) . stringV) vals
      topTypes = S.unions $ map topTypesOf vals
      vs = i ++ f ++ c ++ s
      cs = map fst $ concatMap (S.toList . acons) vals
  consts <- mapM toSynConstr cs
  source <- mapM findSourceExpr lams
  let sourceLambdas = map (\(SourceExpr e) -> e) $ filter (\s -> case s of {SourceExpr _ -> True; _ -> False}) source
      sourceDefs = map (\(SourceDef e) -> e) $ filter (\s -> case s of {SourceDef _ -> True; _ -> False}) source
      sourceExterns = map (\(SourceExtern e) -> e) $ filter (\s -> case s of {SourceExtern _ -> True; _ -> False}) source
  -- trace ("eval " ++ concat (map (maybe "nolambda" (\_ -> "lambda")) sourceLambdas)) $ return ()
  -- trace ("eval " ++ concat (map (maybe "nodef" (\_ -> "def")) sourceDefs)) $ return ()
  return $ trace
    ("eval " ++ show envctx ++
     "\nresult:\n----------------------\n" ++ showSimpleAbValue res ++ "\n----------------------\n")
    (envctx, (sourceLambdas, sourceDefs, sourceExterns, vs, catMaybes consts, topTypes))

intV :: AbValue -> M.Map EnvCtx (SLattice Integer)
intV a = fmap intVL (alits a)

floatV :: AbValue -> M.Map EnvCtx (SLattice Double)
floatV a = fmap floatVL (alits a)

charV :: AbValue -> M.Map EnvCtx (SLattice Char)
charV a = fmap charVL (alits a)

stringV :: AbValue -> M.Map EnvCtx (SLattice String)
stringV a = fmap stringVL (alits a)

topTypesOf :: AbValue -> Set Type
topTypesOf ab =
  S.fromList $ catMaybes (
    map maybeTopI (M.elems (intV ab)) ++
    map maybeTopD (M.elems (floatV ab)) ++
    map maybeTopC (M.elems (charV ab)) ++
    map maybeTopS (M.elems (stringV ab))
  )

sourceEnv :: EnvCtx -> PostFixR x s e String
sourceEnv (EnvCtx env tail) = do
  envs <- sourceEnvCtx env
  envt <- sourceEnv tail
  return $ envs ++ ":::" ++ envt
sourceEnv (EnvTail env) = sourceEnvCtx env

sourceEnvCtx :: Ctx -> PostFixR x s e String
sourceEnvCtx ctx =
  case ctx of
    IndetCtx tn -> return $ "?" ++ intercalate "," (map show tn)
    TopCtx -> return "Top"
    BCallCtx c cc -> do
      se <- findSourceExpr c
      e <- sourceEnvCtx cc
      return $ case se of
        SourceExpr se -> show (ppSyntaxExpr se <+> text e)
        SourceDef de -> show (ppSyntaxDef de <+> text e)
        SourceExtern ex -> show (ppSyntaxExtern ex <+> text e)
        SourceNotFound -> "Not found" ++ e

writeDemandDependencyGraph :: forall r e x . M.Map FixInput (FixOutput AFixChange, Integer, [ContX (DEnv e) (State r e x) FixInput FixOutput AFixChange]) -> IO ()
writeDemandDependencyGraph cache = do
  let cache' = M.filterWithKey (\k v -> case k of {QueryInput _ -> True; _ -> False}) cache
  let values = M.foldl (\acc (v, toId, conts) -> acc ++ fmap (\(ContX _ from fromId) -> (v, from, fromId, toId)) conts) [] cache'
  let nodes = M.foldlWithKey (\acc k (v, toId, conts) -> (toId,k,v):acc) [] cache'
  let edges = S.toList $ S.fromList $ fmap (\(v, f, fi, ti) -> (fi, ti)) values
  let dot = "digraph G {\n"
            ++ intercalate "\n" (fmap (\(a, b) -> show a ++ " -> " ++ show b) edges) ++ "\n"
            ++ intercalate "\n" (fmap (\(fi, k, v) -> show fi ++ " [label=\"" ++ label k ++ "\n\n" ++ label v ++ "\"]") nodes)
            ++ "\n 0 [label=\"Start\"]\n"
            ++ "\n}"
  writeFile "scratch/debug/graph.dot" dot
  return ()
  -- TODO: Cluster by definition and module:
  -- 1. Module -> 2. Definition -> 3. Query Ctx -> Query
  -- 1. Environment -> Refinements
  -- TODO: Integrate results with vscode extension proving GOTO like resolution

runEvalQueryFromRangeSource :: BuildContext
  -> TypeChecker -> (Range, RangeInfo) -> Module -> AnalysisKind -> Int
  -> IO ([(EnvCtx, ([S.UserExpr], [S.UserDef], [S.External], [Syn.Lit], [String], Set Type))], BuildContext)
runEvalQueryFromRangeSource bc build rng mod kind m = do
  (lattice, r, bc) <- runQueryAtRange bc build rng mod kind m $ \ctx -> do
    createPrimitives
    let q = EvalQ (ctx, indeterminateStaticCtx m ctx)
    query q False
    addResult q
  return (r, bc)

analyzeEach :: Show d => ExprContext -> (ExprContext -> FixDemandR a b c d) -> FixDemandR a b c d
analyzeEach = analyzeEachChild

runQueryAtRange :: HasCallStack => BuildContext
  -> TypeChecker -> (Range, RangeInfo)
  -> Module -> AnalysisKind -> Int
  -> (ExprContext -> FixDemandR Query () () ())
  -> IO (M.Map FixInput (FixOutput AFixChange), [(EnvCtx, ([S.UserExpr], [S.UserDef], [S.External], [Syn.Lit], [String], Set Type))], BuildContext)
runQueryAtRange bc build (r, ri) mod kind m doQuery = do
  (l, s, (r, bc)) <- do
    (_, s, ctxs) <- runFixFinish (emptyEnv m kind build False ()) (emptyState bc (-1) ()) $
              do runFixCont $ do
                    (_,ctx) <- loadModule (modName mod)
                    withEnv (\e -> e{currentModContext = ctx, currentContext = ctx}) $ do
                      trace ("Context: " ++ show (contextId ctx)) $ return ()
                      res <- analyzeEach ctx (const $ findContext r ri)
                      addResult res
                 getResults
    let s' = transformState (const ()) (const S.empty) (-1) s
    case S.toList ctxs of
      [] -> return (M.empty, s', ([], bc))
      ctxs ->
        do
          let smallestCtx = fst (minimumBy (\a b -> rangeLength (snd a) `compare` rangeLength (snd b)) ctxs)
          runFixFinishC (emptyEnv m kind build True ()) s' $ do
                          runFixCont $ do
                            (_,ctx) <- loadModule (modName mod)
                            trace ("Context: " ++ show (contextId ctx)) $ return ()
                            withEnv (\e -> e{currentModContext = ctx, currentContext = ctx}) $ doQuery smallestCtx
                          queries <- getResults
                          buildc' <- buildc <$> getStateR
                          ress <- mapM getAbValueResults (S.toList queries)
                          let resM = M.fromListWith joinAbValue (concat ress)
                          ress' <- mapM getAbResult (M.toList resM)
                          return (ress', buildc')
  writeDemandDependencyGraph l
  return (M.map (\(x, _, _) -> x) l, r, bc)