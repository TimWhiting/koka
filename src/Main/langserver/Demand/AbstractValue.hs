-----------------------------------------------------------------------------
-- Copyright 2024, Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# LANGUAGE InstanceSigs #-}
module Demand.AbstractValue(
                          Ctx(..),
                          EnvCtx(..),
                          LiteralLattice(..),
                          LiteralChange(..),
                          AbValue(..),
                          AChange(..),
                          BindInfo(..),
                          PatBinding(..),
                          addChange, injLit, litLattice,
                          showSimpleClosure, showSimpleCtx, showSimpleEnv, showSimpleAbValue, showSimpleAbValueCtx,
                          showNoEnvClosure, showNoEnvAbValue,
                          emptyAbValue,
                          joinAbValue,joinML,
                          subsumes,subsumesCtx,
                          bind,
                          indeterminateStaticCtx,maybeModOfEnv,maybeModOfCtx,
                          refineCtx,
                          limitm,limitmenv,
                          calibratemenv, tryCalibratemenv,
                          ccDeterminedEnv, ccDetermined,
                          envtail,envhead
                        ) where
import Data.Map.Strict as M hiding (map)
import Demand.StaticContext
import Common.Name
import Type.Type
import Data.Set hiding (map, map)
import Data.Set as S hiding (map)
import Core.Core as C
import Syntax.Syntax as S
import Data.List (elemIndex, intercalate)
import Compile.Module
import Debug.Trace (trace)
import Common.Range
import Data.Maybe (fromMaybe, catMaybes, isJust, fromJust)
import GHC.Base (mplus)
import Common.Failure (assertion)
import Demand.FixpointMonad (SimpleLattice(..), Lattice (..), BasicLattice(..), Contains(..), SimpleChange (..), SLattice)
import qualified Demand.FixpointMonad as FM
import Core.CoreVar (bv)
import Data.Foldable (find)

-- TODO: Top Closures (expr, env, but eval results to the top of their type)

data LiteralLattice =
    LiteralLattice{
      intVL :: SLattice Integer,
      floatVL :: SLattice Double,
      charVL :: SLattice Char,
      stringVL :: SLattice String
    } deriving (Eq, Ord)

data LiteralChange =
  LiteralChangeInt (SimpleChange Integer)
  | LiteralChangeFloat (SimpleChange Double)
  | LiteralChangeChar (SimpleChange Char)
  | LiteralChangeString (SimpleChange String)
 deriving (Show, Eq)

instance Show LiteralLattice where
  show (LiteralLattice i f c s) = intercalate "," [show i, show f, show c, show s]

data AChange =
  AChangeClos ExprContext EnvCtx
  | AChangeConstr ExprContext EnvCtx
  | AChangeLit LiteralChange EnvCtx
  | AChangeErr String
  | AChangeNone
  deriving (Show, Eq)

data AbValue =
  AbValue{
    aclos:: !(Set (ExprContext, EnvCtx)),
    acons:: !(Set (ExprContext, EnvCtx)),
    alits:: !(Map EnvCtx LiteralLattice),
    aerr:: Maybe String
  } deriving (Eq, Ord)

instance Semigroup AbValue where
  (<>) :: AbValue -> AbValue -> AbValue
  (<>) = joinAbValue

instance Monoid AbValue where
  mempty = emptyAbValue
  mappend = (<>)

instance Show AbValue where
  show (AbValue cls cntrs lit e) =
    (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
    (if S.null cntrs then "" else " constrs: " ++ show (map show (S.toList cntrs))) ++
    (if M.null lit then "" else " lit: " ++ show (map show (M.toList lit))) ++
    maybe "" (" err: " ++) e

instance Contains AbValue where
  contains :: AbValue -> AbValue -> Bool
  contains (AbValue cls0 cntrs0 lit0 e0) (AbValue cls1 cntrs1 lit1 e1) =
    S.isSubsetOf cls1 cls0 && cntrs1 `S.isSubsetOf` cntrs0 && e1 == e0 && M.isSubmapOfBy (\lit0 lit1 -> lit0 < lit1) lit0 lit1

-- Basic creating of abstract values
showSimpleClosure :: (ExprContext, EnvCtx) -> String
showSimpleClosure (ctx, env) = showSimpleContext ctx ++ " in " ++ showSimpleEnv env

showNoEnvClosure :: (ExprContext, EnvCtx) -> String
showNoEnvClosure (ctx, env) = showSimpleContext ctx

showSimpleEnv :: EnvCtx -> String
showSimpleEnv c =
  "<<" ++ showSimpleEnv_ c ++ ">>"

showSimpleEnv_ :: EnvCtx -> String
showSimpleEnv_ (EnvCtx ctx tail) =
  showSimpleCtx ctx ++ ":::" ++ showSimpleEnv_ tail
showSimpleEnv_ (EnvTail ctx) = showSimpleCtx ctx

showSimpleAbValueCtx :: (EnvCtx, AbValue) -> String
showSimpleAbValueCtx (env, ab) =
  showSimpleEnv env ++ ": " ++ showSimpleAbValue ab ++ "\n"

showSimpleAbValue :: AbValue -> String
showSimpleAbValue (AbValue cls cntrs lit e) =
  (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
  (if S.null cntrs then "" else " constrs: [" ++ intercalate "," (map showSimpleClosure (S.toList cntrs)) ++ "]") ++
  (if M.null lit then "" else " lits: " ++ show (M.toList lit)) ++
  maybe "" (" err: " ++) e

showNoEnvAbValue :: AbValue -> String
showNoEnvAbValue (AbValue cls cntrs lit e) =
  (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
  (if S.null cntrs then "" else " constrs: [" ++ intercalate "," (map showNoEnvClosure (S.toList cntrs)) ++ "]") ++
  (if M.null lit then "" else " lits: " ++ show (map snd (M.toList lit))) ++
  maybe "" (" err: " ++) e

emptyAbValue :: AbValue
emptyAbValue = AbValue S.empty S.empty M.empty Nothing

injLit :: C.Lit -> EnvCtx -> AChange
injLit x env =
  case x of
    C.LitInt i -> (AChangeLit $ LiteralChangeInt $ LChangeSingle i) env
    C.LitFloat f -> (AChangeLit $ LiteralChangeFloat $ LChangeSingle f) env
    C.LitChar c -> (AChangeLit $ LiteralChangeChar $ LChangeSingle c) env
    C.LitString s -> (AChangeLit $ LiteralChangeString $ LChangeSingle s) env

--- JOINING
joinML :: Ord x => M.Map EnvCtx (SLattice x) -> M.Map EnvCtx (SLattice x) -> M.Map EnvCtx (SLattice x)
joinML = M.unionWith join

addChange :: AbValue -> AChange -> AbValue
addChange ab@(AbValue cls cs lit er) change =
  case change of
    AChangeNone -> ab
    AChangeErr err -> AbValue cls cs lit (Just err)
    AChangeClos lam env -> AbValue (S.insert (lam,env) cls) cs lit er
    AChangeConstr c env -> AbValue cls (S.insert (c,env) cs) lit er
    AChangeLit l env -> AbValue cls cs (M.insertWith joinLit env (litLattice l) lit) er

litLattice :: LiteralChange -> LiteralLattice
litLattice lit =
  case lit of
    LiteralChangeInt ch -> LiteralLattice (ch `FM.insert` LBottom) LBottom LBottom LBottom
    LiteralChangeFloat ch -> LiteralLattice LBottom (ch `FM.insert` LBottom) LBottom LBottom
    LiteralChangeChar ch -> LiteralLattice LBottom LBottom (ch `FM.insert` LBottom) LBottom
    LiteralChangeString ch -> LiteralLattice LBottom LBottom LBottom (ch `FM.insert` LBottom)

joinLit :: LiteralLattice -> LiteralLattice -> LiteralLattice
joinLit (LiteralLattice i1 f1 c1 s1) (LiteralLattice i2 f2 c2 s2) = LiteralLattice (i1 `join` i2) (f1 `join` f2) (c1 `join` c2) (s1 `join` s2)

joinAbValue :: AbValue -> AbValue -> AbValue
joinAbValue (AbValue cls0 cs0 lit0 e0) (AbValue cls1 cs1 lit1 e1) = AbValue (S.union cls0 cls1) (S.union cs0 cs1) (M.unionWith joinLit lit0 lit1) (e0 `mplus` e1)

-- Other static information

data PatBinding =
  BoundPatVar C.Pattern -- This is the PatVar variable it is bound to
  -- The variable is bound in the subpattern at the given index with the given constructor
  | BoundConIndex TName Int PatBinding
  | BoundPatIndex Int PatBinding

data BindInfo =
  BoundLam ExprContext EnvCtx Int
  | BoundDef ExprContext ExprContext EnvCtx Int
  | BoundDefRec ExprContext ExprContext EnvCtx Int
  | BoundCase ExprContext ExprContext EnvCtx Int {- which match branch -} PatBinding
  | BoundModule ExprContext EnvCtx
  | BoundGlobal TName VarInfo
  | BoundError ExprContext

-- BIND: The resulting context is not only a nested context focused on a lambda body It is also
-- can be focused on a Let Body or Recursive Let binding It can also be focused on a Recursive Top
-- Level Definition Body It can be bound to a different top level definition It can also be focused on a
-- branch of a match statement BIND requires searching the imported modules for both the name
-- and definition. As such a module import graph should be used. The value of the parameter in the
-- case of unknown definitions is simply the top of the type lattice for the type of the parameter in
-- question. - Additional note: Since Koka uses interface modules to avoid re-parsing user code, we
-- need to determine an appropriate tradeoff in precision and compilation. In particular, a full core
-- file might be an appropriate file to output in addition to the core interface. We only load the core
-- file with the full definitions on demand when we detect that it would increase precision?
bind :: ExprContext -> C.Expr -> EnvCtx -> BindInfo
bind ctx var@(C.Var tname vInfo) env =
  case ctx of
    ModuleC _ mod _ ->
      if lookupDefGroups (coreProgDefs $ fromJust $ modCore mod) tname then BoundModule ctx env
      else trace ("External variable binding " ++ show tname ++ ": " ++ show vInfo) (BoundGlobal tname vInfo) 
    DefCRec _ ctx' names i d -> lookupName (BoundDefRec ctx') names ctx'
    DefCNonRec _ ctx' names d -> lookupName (BoundDef ctx') names ctx'
    LamCBody _ ctx' names _  -> lookupNameNewCtx BoundLam names ctx'
    AppCLambda _ ctx _ -> bind ctx var env
    AppCParam _ ctx _ _ -> bind ctx var env
    LetCDef _ ctx' names i _ -> lookupNameI (BoundDef ctx') (i + 1) names ctx'
    LetCBody _ ctx' names _ -> lookupName (BoundDef ctx') names ctx'
    CaseCMatch _ ctx _ -> bind ctx var env
    CaseCBranch _ ctx' names i b -> caseBinding ctx' names i b
    ExprCBasic _ ctx _ -> bind ctx var env
    ExprCTerm{} -> BoundError ctx
  where
    caseBinding ctx' names i b =
      case find (\(p, i) -> tname `elem` bv p) (zip (branchPatterns b) [0..]) of
        Just (pat, index) -> BoundCase ctx' ctx env i (BoundPatIndex index (findPatBinding pat))
        Nothing -> bind ctx' var env
    findPatBinding :: C.Pattern -> PatBinding
    findPatBinding pat = 
      case pat of
        C.PatVar tn sub -> if tn == tname then BoundPatVar pat else findPatBinding sub
        C.PatCon con fields _ _ _ _ _ _ -> 
          case find (\(p, i) -> tname `elem` bv p) (zip fields [0..]) of
            Just (subPat, i) -> BoundConIndex con i (findPatBinding subPat)
        C.PatLit _ -> error "PatLit should not occur"
        C.PatWild -> error "PatWild should not occur"
    lookupNameNewCtx mk names ctx' =
      case elemIndex tname names
        of Just x -> mk ctx env x
           -- lambdas introduce a new binding context that relates to calls. Other binding expressions do not
           _ -> bind ctx' var (envtail env)
    lookupName mk names ctx' =
      case elemIndex tname names
        of Just x -> mk ctx env x
           _ -> bind ctx' var env
    lookupNameI mk i names ctx' =
      case elemIndex tname names
        of Just x -> mk ctx env i
           _ -> bind ctx' var env


data EnvCtx = EnvCtx Ctx EnvCtx
            | EnvTail Ctx
  deriving (Eq, Ord)

instance Show EnvCtx where
  show c = "<<" ++ showEnvCtx c ++ ">>"

showEnvCtx :: EnvCtx -> String
showEnvCtx (EnvCtx ctx tail) = show ctx ++ ":::" ++ showEnvCtx tail
showEnvCtx (EnvTail ctx) = show ctx

---------------- Environment Based Ctx -------------------
data Ctx =
  IndetCtx [TName] ExprContext
  | CallCtx !ExprContext !EnvCtx
  | BCallCtx !ExprContext !Ctx
  | CutKnown
  | CutUnknown
  | TopCtx
  deriving (Eq, Ord)

instance Show Ctx where
  show ctx =
    case ctx of
      IndetCtx tn c -> "?(" ++ show tn ++ ")"
      CallCtx ctx env -> "call{" ++ showSimpleContext ctx ++ "," ++ show env ++ "}"
      BCallCtx ctx cc -> "bcall{" ++ showSimpleContext ctx ++ "," ++ show cc ++ "}"
      TopCtx -> "Top"
      CutKnown -> "~!~"
      CutUnknown -> "~?~"

showSimpleCtx :: Ctx -> String
showSimpleCtx ctx =
  case ctx of
    IndetCtx tn c -> show tn
    CallCtx ctx env -> "call{" ++ showSimpleContext ctx ++ ", " ++ showSimpleEnv env ++ "}"
    BCallCtx ctx cc -> "bcall{" ++ showSimpleContext ctx ++ ", " ++ showSimpleCtx cc ++ "}"
    TopCtx -> "Top"
    CutKnown -> "~!~"
    CutUnknown -> "~?~"

indeterminateStaticCtx :: ExprContext -> EnvCtx
indeterminateStaticCtx ctx =
  case ctx of
    ModuleC _ mod _ -> EnvTail TopCtx
    DefCRec _ ctx' _ _ _ -> indeterminateStaticCtx ctx'
    DefCNonRec _ ctx' _ _ -> indeterminateStaticCtx ctx'
    LamCBody _ ctx' tn _ ->
      let parent = indeterminateStaticCtx ctx'
      in EnvCtx (IndetCtx tn ctx) parent
    AppCLambda _ ctx _ -> indeterminateStaticCtx ctx
    AppCParam _ ctx _ _ -> indeterminateStaticCtx ctx
    LetCDef _ ctx' _ _ _ -> indeterminateStaticCtx ctx'
    LetCBody _ ctx' _ _ -> indeterminateStaticCtx ctx'
    CaseCMatch _ ctx _ -> indeterminateStaticCtx ctx
    CaseCBranch _ ctx' _ _ _ -> indeterminateStaticCtx ctx'
    ExprCBasic _ ctx _ -> indeterminateStaticCtx ctx
    ExprCTerm{} -> error "Never should occur"

maybeModOfEnv :: EnvCtx -> Maybe ExprContext
maybeModOfEnv env = maybeModOfCtx $ envhead env

maybeModOfCtx :: Ctx -> Maybe ExprContext
maybeModOfCtx ctx =
  case ctx of
    CallCtx ctx env -> modCtx ctx
    BCallCtx ctx cc -> maybeModOfCtx cc -- Could also potentially use indeterminate contexts
    _ -> Nothing

envtail :: EnvCtx -> EnvCtx
envtail (EnvCtx cc tail) = tail
envtail (EnvTail x) = error "envtail on EnvTail"

envhead :: EnvCtx -> Ctx
envhead (EnvCtx cc tail) = cc
envhead (EnvTail cc) = cc

limitmenv :: EnvCtx -> Int -> EnvCtx
limitmenv (EnvCtx e tail) m =
  EnvCtx (limitm e m) (limitmenv tail m)
limitmenv (EnvTail e) m = EnvTail (limitm e m)

limitm :: Ctx -> Int -> Ctx
limitm ctx m =
  if m == 0 then
    case ctx of
      CallCtx{} -> CutKnown
      BCallCtx{} -> CutKnown
      CutKnown -> CutKnown
      TopCtx -> TopCtx
      IndetCtx{} -> CutUnknown
      CutUnknown -> CutUnknown
  else
    case ctx of
      CallCtx c e -> CallCtx c (limitmenv e (m - 1))
      BCallCtx c e -> BCallCtx c (limitm e (m - 1))
      _ -> ctx

-- Environment Subsumption
-- If the first subsumes the second, then the first is more general than the second, and thus any value in the second should also be in the first
subsumes :: EnvCtx -> EnvCtx -> Bool
subsumes p1 p2 =
  case (p1, p2) of
    (EnvCtx ctx1 tail1, EnvCtx ctx2 tail2) -> ctx1 `subsumesCtx` ctx2 && tail1 `subsumes` tail2
    (EnvTail ctx1, EnvTail ctx2) -> ctx1 == ctx2
    _ -> False

subsumesCtx :: Ctx -> Ctx -> Bool
subsumesCtx c1 c2 =
  case (c1, c2) of
    (CutUnknown, CutUnknown) -> True
    (CutKnown, CutKnown) -> True
    (CutKnown, CutUnknown) -> True
    (CutUnknown, CutKnown) -> True
    (TopCtx, TopCtx) -> True
    (IndetCtx tn1 c1, IndetCtx tn2 c2) -> tn1 == tn2 && c1 == c2
    (CallCtx id1 env1, CallCtx id2 env2) -> id1 == id2 && env1 `subsumes` env2
    (BCallCtx id1 env1, BCallCtx id2 env2) -> id1 == id2 && env1 `subsumesCtx` env2
    (IndetCtx{}, CallCtx{}) -> True
    (IndetCtx{}, BCallCtx{}) -> True
    (IndetCtx{}, TopCtx{}) -> True
    -- TODO: More subsumption rules for CutContexts
    _ -> False

refineCtx :: (EnvCtx, EnvCtx) -> EnvCtx -> EnvCtx
refineCtx (c1, c0) c =
  if c == c0 then c1 else
    case c of
      EnvCtx ctx tail -> EnvCtx ctx (refineCtx (c1, c0) tail)
      EnvTail ctx -> EnvTail ctx

calibratemenv :: Int -> EnvCtx -> EnvCtx -> EnvCtx
calibratemenv mlimit (EnvCtx call calls) (EnvCtx ps tail) = do
  EnvCtx (calibratemctx mlimit call ps) (calibratemenv mlimit calls tail)
calibratemenv mlimit (EnvTail call) (EnvTail ctx) = EnvTail $! calibratemctx mlimit call ctx

tryCalibratemenv :: Int -> EnvCtx -> EnvCtx -> Maybe EnvCtx
tryCalibratemenv mlimit (EnvCtx call calls) (EnvCtx ps tail) = do
  ps' <- tryCalibratemctx mlimit call ps
  tail' <- tryCalibratemenv mlimit calls tail
  return $ EnvCtx ps' tail'
tryCalibratemenv mlimit (EnvTail call) (EnvTail ctx) =
  tryCalibratemctx mlimit call ctx >>= (\ctx -> return $ EnvTail ctx)

-- TODO: Degen needs a way to be converted to Indet (calibration makes environments longer (to m))
-- Probably needs more information to determine static context
calibratemctx :: Int -> Ctx -> Ctx -> Ctx
calibratemctx mlimit call p =
  if mlimit == 0 then
    case p of
      CallCtx{} -> CutKnown
      BCallCtx{} -> CutKnown
      CutKnown -> CutKnown
      TopCtx -> TopCtx
      IndetCtx{} -> CutUnknown
      CutUnknown -> CutUnknown
  else case p of
    IndetCtx tn c -> IndetCtx tn c
    CutKnown -> call
    CutUnknown -> call
    CallCtx c p' -> CallCtx c (calibratemenv (mlimit - 1) (indeterminateStaticCtx c) p')
    BCallCtx c p' -> BCallCtx c (calibratemctx (mlimit - 1) (envhead $ indeterminateStaticCtx c) p')
    x -> x


-- TODO: Degen needs a way to be converted to Indet (calibration makes environments longer (to m))
-- Probably needs more information to determine static context
tryCalibratemctx :: Int -> Ctx -> Ctx -> Maybe Ctx
tryCalibratemctx mlimit call p =
  if mlimit == 0 then
    case p of
      CallCtx{} -> Just CutKnown
      BCallCtx{} -> Just CutKnown
      CutKnown -> Just CutKnown
      TopCtx -> Just TopCtx
      IndetCtx{} -> Just CutUnknown
      CutUnknown -> Just CutUnknown
  else case p of
    IndetCtx tn c -> Just $ IndetCtx tn c
    CutKnown -> Nothing -- We cut a previously known context, so we can't reconstruct it without doing a full expr / refinement
    CutUnknown -> Just call
    CallCtx c p' -> Just $ CallCtx c (calibratemenv (mlimit - 1) (indeterminateStaticCtx c) p')
    BCallCtx c p' -> Just $ BCallCtx c (calibratemctx (mlimit - 1) (envhead $ indeterminateStaticCtx c) p')
    x -> Just x

ccDeterminedEnv :: EnvCtx -> Bool
ccDeterminedEnv env =
  case env of
    EnvCtx cc tail -> ccDetermined cc && ccDeterminedEnv tail
    EnvTail cc -> ccDetermined cc

ccDetermined :: Ctx -> Bool
ccDetermined ctx =
  case ctx of
    IndetCtx{} -> False
    CallCtx c env -> ccDeterminedEnv env
    TopCtx -> True
    CutKnown -> False
    CutUnknown -> True
    BCallCtx c rst -> ccDetermined rst