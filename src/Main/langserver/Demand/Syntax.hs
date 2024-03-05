
-----------------------------------------------------------------------------
-- Copyright 2024, Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# LANGUAGE MultiParamTypeClasses #-}

module Demand.Syntax where

import Data.List (intercalate)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Maybe (catMaybes)
import Data.Set(Set)
import Demand.StaticContext
import Demand.FixpointMonad
import Demand.DemandMonad
import Demand.AbstractValue
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

toSynConstr :: ExprContext -> FixDemandR x s e (Maybe String)
toSynConstr ctx = do
  app <- findSourceExpr ctx
  return (Just $ show app)

sourceEnv :: EnvCtx -> FixDemandR x s e String
sourceEnv (EnvCtx env tail) = do
  envs <- sourceEnvCtx env
  envt <- sourceEnv tail
  return $ envs ++ ":::" ++ envt
sourceEnv (EnvTail env) = sourceEnvCtx env

sourceEnvCtx :: Ctx -> FixDemandR x s e String
sourceEnvCtx ctx =
  case ctx of
    IndetCtx tn c -> return $ "?" ++ intercalate "," (map show tn)
    TopCtx -> return "Top"
    CutKnown -> return "~!~"
    CutUnknown -> return "~?~"
    CallCtx c env -> do
      se <- findSourceExpr c
      e <- sourceEnv env
      return $ case se of
        (Just se, _) -> showSyntax 0 se ++ " <<" ++ e ++ ">>"
        (_, Just de) -> showSyntaxDef 0 de ++ " <<" ++ e ++ ">>"
        _ -> show c ++ " " ++ e
    BCallCtx c cc -> do
      se <- findSourceExpr c
      e <- sourceEnvCtx cc
      return $ case se of
        (Just se, _) -> showSyntax 0 se ++ " " ++ e
        (_, Just de) -> showSyntaxDef 0 de ++ " " ++ e
        _ -> show c ++ " " ++ e

findSourceExpr :: ExprContext -> FixDemandR x s e (Maybe Syn.UserExpr, Maybe (Syn.Def Syn.UserType))
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
      program <- modProgram <$> getModule (moduleName $ contextId ctx)
      case (program, C.defNameRange d) of
        (Just prog, rng) -> -- trace ("Finding location for " ++ show rng ++ " " ++ show ctx) $ 
          return (Nothing, findDefFromRange prog rng)
        _ -> trace ("No program or rng" ++ show d ++ " " ++ show program) $ return (Nothing, Nothing)
      -- case (program, defNameRange d) of
      --   (Just prog, rng) -> trace ("Finding location for " ++ show rng ++ " " ++ show ctx ++ " in module " ++ show (moduleName $ contextId ctx)) $ return $! findLocation prog rng
      --   _ -> trace ("No program or rng" ++ show (defName d) ++ " " ++ show program) $ return Nothing
    findForName n = do
      program <- modProgram <$> getModule (moduleName $ contextId ctx)
      case (program, originalRange n) of
        (Just prog, Just rng) -> -- trace ("Finding location for " ++ show rng ++ " " ++ show ctx) $ 
          return (findLambdaFromRange prog rng, Nothing)
        _ -> trace ("No program or rng" ++ show n ++ " " ++ show program) $ return (Nothing, Nothing)
    findForApp n = do
      program <- modProgram <$> getModule (moduleName $ contextId ctx)
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
