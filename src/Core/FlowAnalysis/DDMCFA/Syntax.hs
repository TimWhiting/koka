
-----------------------------------------------------------------------------
-- Copyright 2024, Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Core.FlowAnalysis.DDMCFA.Syntax where

import Data.List (intercalate, find)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Maybe (catMaybes, mapMaybe, isJust, fromJust)
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
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.Syntax
import Core.FlowAnalysis.DDMCFA.DemandMonad
import Core.FlowAnalysis.DDMCFA.AbstractValue
import Core.FlowAnalysis.DDMCFA.Primitives
import Core.FlowAnalysis.DDMCFA.DemandAnalysis (query, analyzeEachChild, getAbValueResults)
import Debug.Trace (trace)
import Core.Pretty (prettyExpr)
import Type.Pretty (defaultEnv, Env (..))
import Data.Foldable (minimumBy)
import Common.Failure (HasCallStack)
import Common.Error (Errors)
import System.Directory (createDirectoryIfMissing)


runEvalQueryFromRangeSource :: BuildContext
  -> TypeChecker -> (Range, RangeInfo) -> Module -> AnalysisKind -> Int -> Bool -> Int
  -> IO ([(String, ([S.UserExpr], [S.UserDef], [S.External], [Syn.Lit], [(String, Maybe Range)], Set Type))], BuildContext)
runEvalQueryFromRangeSource bc build rng mod kind m debug gas = do
  (lattice, r, bc) <- runQueryAtRange bc build rng mod kind m debug gas $ \ctx -> do
    createPrimitives
    let q = EvalQ (ctx, indeterminateStaticCtx m ctx)
    query q False
    addResult q
  return (r, bc)

analyzeEach :: Show d => ExprContext -> (ExprContext -> FixDemandR a b c d) -> FixDemandR a b c d
analyzeEach = analyzeEachChild

runQueryAtRange :: HasCallStack => BuildContext
  -> TypeChecker -> (Range, RangeInfo)
  -> Module -> AnalysisKind -> Int -> Bool -> Int
  -> (ExprContext -> FixDemandR Query () () ())
  -> IO (M.Map FixInput (FixOutput AFixChange), [(String, ([S.UserExpr], [S.UserDef], [S.External], [Syn.Lit], [(String, Maybe Range)], Set Type))], BuildContext)
runQueryAtRange bc build (r, ri) mod kind m debug gas doQuery = do
  (l, s, (r, bc)) <- do
    (_, s, ctxs) <- runFixFinish (emptyEnv m kind build False ()) (emptyState bc (-1) ()) $
              do runFixCont $ do
                    (_,ctx) <- loadModule (modName mod)
                    withEnv (\e -> e{currentModContext = ctx, currentContext = ctx}) $ do
                      -- trace ("Context: " ++ show (contextId ctx)) $ return ()
                      res <- analyzeEach ctx (const $ findContext r ri)
                      addResult res
                 getResults
    let s' = transformState (const ()) (const S.empty) gas s
    case S.toList ctxs of
      [] -> return (M.empty, s', ([], bc))
      ctxs ->
        do
          let smallestCtx = fst (minimumBy (\a b -> rangeLength (snd a) `compare` rangeLength (snd b)) ctxs)
          runFixFinishC (emptyEnv m kind build debug ()) s' $ do
                          runFixCont $ do
                            (_,ctx) <- loadModule (modName mod)
                            trace ("Start context: " ++ show (contextId ctx)) $ return ()
                            withEnv (\e -> e{currentModContext = ctx, currentContext = ctx}) $ doQuery smallestCtx
                          queries <- getResults
                          buildc' <- buildc <$> getStateR
                          ress <- mapM getAbValueResults (S.toList queries)
                          let resM = M.fromListWith joinAbValue (concat ress)
                          ress' <- mapM getAbResult (M.toList resM)
                          return (ress', buildc')
  writeDependencyGraph (moduleNameToPath (modName mod)) l
  return (M.map (\(x, _, _, _) -> x) l, r, bc)

getAbResult :: (EnvCtx, AbValue) -> PostFixR x s e (String, ([S.UserExpr], [S.UserDef], [S.External], [Syn.Lit], [(String, Maybe Range)], Set Type))
getAbResult (envctx, res) = do
  let vals = res
      lams = map fst $ (S.toList . aclos) vals
      i = foldl (\res acc -> res `joinSimple` acc) LBottom (M.elems $ intV vals)
      f = foldl (\res acc -> res `joinSimple` acc) LBottom (M.elems $ floatV vals)
      c = foldl (\res acc -> res `joinSimple` acc) LBottom (M.elems $ charV vals)
      s = foldl (\res acc -> res `joinSimple` acc) LBottom (M.elems $ stringV vals)
      topTypes = S.fromList $ topTypesOf (i, f, c, s)
      vs = syntaxLitsOf (i, f, c, s)
      cs = map fst $ (S.toList . acons) vals
  consts <- mapM toSynConstr cs
  source <- mapM findSourceExpr lams
  let sourceLambdas = map (\(SourceExpr e _) -> e) $ filter (\s -> case s of {SourceExpr{} -> True; _ -> False}) source
      sourceDefs = map (\(SourceDef e _) -> e) $ filter (\s -> case s of {SourceDef{} -> True; _ -> False}) source
      sourceExterns = map (\(SourceExtern e _) -> e) $ filter (\s -> case s of {SourceExtern{} -> True; _ -> False}) source
  -- trace ("eval " ++ concat (map (maybe "nolambda" (\_ -> "lambda")) sourceLambdas)) $ return ()
  -- trace ("eval " ++ concat (map (maybe "nodef" (\_ -> "def")) sourceDefs)) $ return ()
  env <- sourceEnv envctx
  return $ trace
    ("eval " ++ show envctx ++
     "\nresult:\n----------------------\n" ++ showSimpleAbValue res ++ "\n----------------------\n")
    (env, (sourceLambdas, sourceDefs, sourceExterns, vs, S.toList $ S.fromList consts, topTypes))

sourceEnv :: EnvCtx -> PostFixR x s e String
sourceEnv env = do
  envs <- sourceEnvX env
  case envs of
    Just envs -> return $ "<" ++ envs ++ ">"
    Nothing -> return "<>"

sourceEnvX :: EnvCtx -> PostFixR x s e (Maybe String)
sourceEnvX (EnvCtx dctx tail) = do
  envc <- sourceDCtx dctx
  envt <- sourceEnvX tail
  case envt of
    Just envt -> return $ Just $ envc ++ ":::" ++ envt
    Nothing -> return $ Just envc
sourceEnvX (EnvTail env) = return Nothing

sourceDCtx :: DCtx -> PostFixR x s e String
sourceDCtx ctx = do
  env <- sourceDCtxX ctx
  case env of
    Just e -> return $ "[" ++ e ++ "]"
    Nothing -> return "[]"

sourceDCtxX :: DCtx -> PostFixR x s e (Maybe String)
sourceDCtxX ctx =
  case ctx of
    DUnknown ctx -> do
      s <- sourceSCtx ctx      
      return $ Just $ "?(" ++ s ++ ")"
    DTop ctx -> do 
      s <- sourceSCtx ctx 
      return $ Just $ "t(" ++ s ++ ")"
    DDelim e ctx ddctx -> do 
      s <- sourceSCtx ctx
      tail <- sourceDCtxX ddctx
      SourceExpr se rng <- findForApp e (appRng e)
      case tail of 
        Nothing -> return $ Just $ "d(" ++ show se ++ ", " ++ s ++ ")" 
        Just t -> return $ Just $ "d(" ++ show se ++ ", " ++ s ++ "):" ++ t

sourceSCtx :: SCtx -> PostFixR x s e String
sourceSCtx ctx = do
  env <- sourceSCtxX ctx
  case env of
    Just e -> return $ "[" ++ e ++ "]"
    Nothing -> return "[]"

sourceSCtxX :: SCtx -> PostFixR x s e (Maybe String)
sourceSCtxX ctx =
  case ctx of
    IndetCtx tn -> return $ Just $ "?(" ++ intercalate "," (map show tn) ++ ")"
    TopCtx -> return $ Just "(top)"
    CtxEnd -> return Nothing
    BCallCtx c cc -> do
      se <- findForApp c (appRng c)
      -- trace (show $ showCompactRange <$> appRng c) $ return ()
      let head = case se of
                SourceExpr se rng -> show (linkText (ppSyntaxExpr simpleEnv se) (getRange se))
                SourceDef de rng -> show (linkText (ppSyntaxDef simpleEnv de) (getRange de))
                SourceExtern ex rng -> show (linkText (ppSyntaxExtern simpleEnv ex) (S.extRange ex))
                SourceNotFound -> "Not found"
      tail <- sourceSCtxX cc
      case tail of 
        Just t -> return $ Just $ head <> "::" ++ t
        Nothing -> return $ Just head

-- Converting to user visible expressions
toSynLit :: SLattice Integer -> Maybe S.Lit
toSynLit (LSingle i) = Just $ S.LitInt i rangeNull
toSynLit _ = Nothing

toSynLitD :: SLattice Double -> Maybe S.Lit
toSynLitD (LSingle i) = Just $ S.LitFloat i rangeNull
toSynLitD _ = Nothing

toSynLitC :: SLattice Char -> Maybe S.Lit
toSynLitC (LSingle i) = Just $ S.LitChar i rangeNull
toSynLitC _ = Nothing

toSynLitS :: SLattice String -> Maybe S.Lit
toSynLitS (LSingle i) = Just $ S.LitString i rangeNull
toSynLitS _ = Nothing

intV :: AbValue -> M.Map EnvCtx (SLattice Integer)
intV a = fmap intVL (alits a)

floatV :: AbValue -> M.Map EnvCtx (SLattice Double)
floatV a = fmap floatVL (alits a)

charV :: AbValue -> M.Map EnvCtx (SLattice Char)
charV a = fmap charVL (alits a)

stringV :: AbValue -> M.Map EnvCtx (SLattice String)
stringV a = fmap stringVL (alits a)
