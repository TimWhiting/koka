
-----------------------------------------------------------------------------
-- Copyright 2024, Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# LANGUAGE MultiParamTypeClasses #-}

module Core.Demand.Syntax where

import Data.List (intercalate)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Maybe (catMaybes, mapMaybe)
import Data.Set(Set)
import Core.Demand.StaticContext
import Core.Demand.FixpointMonad
import Core.Demand.DemandMonad
import Core.Demand.AbstractValue
import Compile.Module (Module(..))
import qualified Syntax.Syntax as Syn
import qualified Syntax.Syntax as S
import qualified Core.Core as C
import Common.Range
import Syntax.RangeMap
import Common.Name (Name(..))
import Core.Core
import Type.Type
import Debug.Trace (trace)
import Compile.BuildContext (BuildContext)
import Compile.Options (Terminal, Flags)
import Core.Demand.DemandAnalysis (createPrimitives, query, analyzeEachChild, getAbValueResults)

findContext :: Range -> RangeInfo -> FixDemandR x s e ExprContext
findContext r ri = do
  ctx <- currentContext <$> getEnv
  case ctx of
    ExprCBasic _ _ (Var (TName _ _ (Just rng)) _) | r `rangesOverlap` rng ->
      trace ("found overlapping range " ++ showFullRange "" rng ++ " " ++ show ctx) $
        return ctx
    ExprCBasic _ _ (Var (TName _ _ (Just rng)) _) -> -- trace ("var range doesn't overlap "++ show ctx ++ " " ++ showFullRange rng) $
      doBottom
    LetCDef{} -> fromNames ctx [defTName (defOfCtx ctx)]
    -- Hovering over a lambda parameter should query what values that parameter can evaluate to -- need to create an artificial Var expression
    LamCBody _ _ tnames _ -> fromNames ctx tnames
    CaseCBranch _ _ tnames _ _ -> fromNames ctx tnames
    _ -> doBottom
  where fromNames ctx tnames =
          case mapMaybe (\tn -> (case fmap (rangesOverlap r) (originalRange tn) of {Just True -> Just tn; _ -> Nothing})) tnames of
              [tn] -> do
                id <- newContextId
                return $ ExprCBasic id ctx (Var tn InfoNone)
              _ -> doBottom

runEvalQueryFromRangeSource :: BuildContext
  -> Terminal -> Flags -> (Range, RangeInfo) -> Module -> AnalysisKind -> Int
  -> IO ([(EnvCtx, ([S.UserExpr], [S.UserDef], [Syn.Lit], [String], Set Type))], BuildContext)
runEvalQueryFromRangeSource bc term flags rng mod kind m = do
  (lattice, r, bc) <- runQueryAtRange bc term flags rng mod kind m $ \ctx -> do
    createPrimitives
    let q = EvalQ (ctx, indeterminateStaticCtx ctx)
    query q
    addResult q
  return (r, bc)

runQueryAtRange :: BuildContext
  -> Terminal -> Flags -> (Range, RangeInfo)
  -> Module -> AnalysisKind -> Int
  -> (ExprContext -> FixDemand Query () ())
  -> IO (M.Map FixInput (FixOutput AFixChange), [(EnvCtx, ([S.UserExpr], [S.UserDef], [Syn.Lit], [String], Set Type))], BuildContext)
runQueryAtRange bc term flags (r, ri) mod kind m doQuery = do
  let cid = ExprContextId (-1) (modName mod)
      modCtx = ModuleC cid mod (modName mod)
  (l, s, (r, bc)) <-
    runFixFinish (DEnv m term flags kind modCtx modCtx (EnvTail TopCtx) "" "" ())
                 (State bc M.empty 0 M.empty 0 S.empty M.empty M.empty ()) $ do
                    runFixCont $ do
                            ctx <- analyzeEachChild (const $ findContext r ri) modCtx
                            doQuery ctx
                    queries <- getResults
                    buildc' <- buildc <$> getStateR
                    ress <- mapM getAbValueResults (S.toList queries)
                    ress' <- mapM getAbResult (concat ress)
                    return (ress', buildc')
  return (l, r, bc)

getAbResult :: (EnvCtx, AbValue) -> PostFixR x s e (EnvCtx, ([S.UserExpr], [S.UserDef], [Syn.Lit], [String], Set Type))
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
  sourceLams <- mapM findSourceExpr lams
  let (sourceLambdas, sourceDefs) = unzip sourceLams
  return $ trace
    ("eval " ++ showSimpleEnv envctx ++
     "\nresult:\n----------------------\n" ++ showSimpleAbValue res ++ "\n----------------------\n")
    (envctx, (catMaybes sourceLambdas, catMaybes sourceDefs, vs, catMaybes consts, topTypes))

toSynConstr :: ExprContext -> PostFixR x s e (Maybe String)
toSynConstr ctx = do
  app <- findSourceExpr ctx
  return (Just $ show app)

sourceEnv :: EnvCtx -> PostFixR x s e String
sourceEnv (EnvCtx env tail) = do
  envs <- sourceEnvCtx env
  envt <- sourceEnv tail
  return $ envs ++ ":::" ++ envt
sourceEnv (EnvTail env) = sourceEnvCtx env

sourceEnvCtx :: Ctx -> PostFixR x s e String
sourceEnvCtx ctx =
  case ctx of
    IndetCtx tn c -> return $ "?" ++ intercalate "," (map show tn)
    TopCtx -> return "Top"
    BCallCtx c cc -> do
      se <- findSourceExpr c
      e <- sourceEnvCtx cc
      return $ case se of
        (Just se, _) -> showSyntax 0 se ++ " " ++ e
        (_, Just de) -> showSyntaxDef 0 de ++ " " ++ e
        _ -> show c ++ " " ++ e

findSourceExpr :: ExprContext -> PostFixR x s e (Maybe Syn.UserExpr, Maybe (Syn.Def Syn.UserType))
findSourceExpr ctx =
  case maybeExprOfCtx ctx of
    Just (Lam (n:_) _ _) -> findForName n
    Just (TypeLam _ (Lam (n:_) _ _)) -> findForName n
    Just (App (Var tn _) _) -> findForApp tn
    _ ->
      case ctx of
        DefCNonRec{} -> findDef (defOfCtx ctx)
        DefCRec{} -> findDef (defOfCtx ctx)
        LetCDef{} -> findDef (defOfCtx ctx)
        _ ->
          trace ("Unknown lambda type " ++ show ctx ++ ": " ++ show (maybeExprOfCtx ctx)) $ return (Nothing, Nothing)
  where
    findDef d = do
      -- return $! Just $! Syn.Var (defName d) False (defNameRange d)
      program <- modProgram <$> getModuleR (moduleName $ contextId ctx)
      case (program, C.defNameRange d) of
        (Just prog, rng) -> -- trace ("Finding location for " ++ show rng ++ " " ++ show ctx) $ 
          return (Nothing, findDefFromRange prog rng)
        _ -> trace ("No program or rng" ++ show d ++ " " ++ show program) $ return (Nothing, Nothing)
      -- case (program, defNameRange d) of
      --   (Just prog, rng) -> trace ("Finding location for " ++ show rng ++ " " ++ show ctx ++ " in module " ++ show (moduleName $ contextId ctx)) $ return $! findLocation prog rng
      --   _ -> trace ("No program or rng" ++ show (defName d) ++ " " ++ show program) $ return Nothing
    findForName n = do
      program <- modProgram <$> getModuleR (moduleName $ contextId ctx)
      case (program, originalRange n) of
        (Just prog, Just rng) -> -- trace ("Finding location for " ++ show rng ++ " " ++ show ctx) $ 
          return (findLambdaFromRange prog rng, Nothing)
        _ -> trace ("No program or rng" ++ show n ++ " " ++ show program) $ return (Nothing, Nothing)
    findForApp n = do
      program <- modProgram <$> getModuleR (moduleName $ contextId ctx)
      case (program, originalRange n) of
        (Just prog, Just rng) -> -- trace ("Finding application location for " ++ show rng ++ " " ++ show ctx) $ 
          return (findApplicationFromRange prog rng, Nothing)
        _ -> trace ("No program or rng" ++ show n ++ " " ++ show program) $ return (Nothing, Nothing)

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

maybeTopI :: SLattice Integer -> Maybe Type
maybeTopI LTop = Just typeInt
maybeTopI _ = Nothing

maybeTopD :: SLattice Double -> Maybe Type
maybeTopD LTop = Just typeFloat
maybeTopD _ = Nothing

maybeTopC :: SLattice Char -> Maybe Type
maybeTopC LTop = Just typeChar
maybeTopC _ = Nothing

maybeTopS :: SLattice String -> Maybe Type
maybeTopS LTop = Just typeString
maybeTopS _ = Nothing

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
