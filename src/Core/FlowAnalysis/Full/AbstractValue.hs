-----------------------------------------------------------------------------
-- Copyright 2024, Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# LANGUAGE InstanceSigs #-}
module Core.FlowAnalysis.Full.AbstractValue where
import Data.Map.Strict as M hiding (map)
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
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.FixpointMonad (SimpleLattice(..), Lattice (..), Contains(..), SimpleChange (..), SLattice)
import qualified Core.FlowAnalysis.FixpointMonad as FM
import Core.CoreVar (bv)
import Data.Foldable (find)
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.Literals
    ( LiteralChange(..),
      LiteralLattice(LiteralLattice),
      litLattice,
      joinLit )

-- TODO: Top Closures (expr, env, but eval results to the top of their type)

type Addr = (TName, Int)
type VEnv = M.Map TName Addr

data AChange =
  AChangeClos ExprContext VEnv
  | AChangePrim Name ExprContext VEnv
  | AChangeClosApp ExprContext ExprContext VEnv -- This is a closure that has a different application for it's calling context abstraction
  | AChangeConstr ExprContext VEnv
  | AChangeLit LiteralChange VEnv
  deriving (Eq, Ord)

callOfClos :: AChange -> ExprContext
callOfClos res = 
  case res of
    AChangeClos c e -> c
    AChangeClosApp _ c e -> c

envOfClos :: AChange -> VEnv
envOfClos res =
  case res of
    AChangeClos c e -> e
    AChangeClosApp _ c e -> e

ctxOfClos :: AChange -> ExprContext
ctxOfClos res = 
  case res of
    AChangeClos c e -> c
    AChangeClosApp c _ e -> c

instance Show AChange where
  show (AChangeClos expr env) =
    showNoEnvClosure (expr, env)
  show (AChangePrim name expr env) =
    showNoEnvClosure (expr, env)
  show (AChangeClosApp expr _ env) =
    showNoEnvClosure (expr, env)
  show (AChangeConstr expr env) =
    showNoEnvClosure (expr, env)
  show (AChangeLit lit env) =
    show lit

data AbValue =
  AbValue{
    aclos:: !(Set (ExprContext, VEnv)),
    aclosapps:: !(Set (ExprContext, ExprContext, VEnv)),
    acons:: !(Set (ExprContext, VEnv)),
    alits:: !(Map VEnv LiteralLattice)
  } deriving (Eq, Ord)

changes :: AbValue -> [AChange]
changes (AbValue clos clsapp constrs lits) =
  closs ++ closapps ++ constrss ++ litss
  where
    closs = map (uncurry AChangeClos) $ S.toList clos
    closapps = map (\(a, b, c) -> AChangeClosApp a b c) $ S.toList clsapp
    constrss = map (uncurry AChangeConstr) $ S.toList constrs
    litss = concatMap (\(env,lat) -> changesLit lat env) $ M.toList lits

changesLit :: LiteralLattice -> VEnv -> [AChange]
changesLit (LiteralLattice ints floats chars strings) env =
  intChanges ++ floatChanges ++ charChanges ++ stringChanges
  where
    intChanges = map (\x -> AChangeLit (LiteralChangeInt x) env) $ FM.elems ints
    floatChanges = map (\x -> AChangeLit (LiteralChangeFloat x) env) $ FM.elems floats
    charChanges = map (\x -> AChangeLit (LiteralChangeChar x) env) $ FM.elems chars
    stringChanges = map (\x -> AChangeLit (LiteralChangeString x) env) $ FM.elems strings

changeIn :: AChange -> AbValue -> Bool
changeIn (AChangeClos ctx env) (AbValue clos _ _ _) = S.member (ctx,env) clos
changeIn (AChangeClosApp ctx app env) (AbValue _ closapps _ _) = S.member (ctx,app,env) closapps
changeIn (AChangeConstr ctx env) (AbValue _ _ constr _) = S.member (ctx,env) constr
changeIn (AChangeLit lit env) (AbValue _ _ _ lits) =
  case M.lookup env lits of
    Just (LiteralLattice ints floats chars strings) ->
      case lit of
        LiteralChangeInt i -> i `lte` ints
        LiteralChangeFloat f -> f `lte` floats
        LiteralChangeChar c -> c `lte` chars
        LiteralChangeString s -> s `lte` strings
    Nothing -> False

instance Semigroup AbValue where
  (<>) :: AbValue -> AbValue -> AbValue
  (<>) = joinAbValue

instance Monoid AbValue where
  mempty = emptyAbValue
  mappend = (<>)

instance Show AbValue where
  show (AbValue cls clsapp cntrs lit) =
    (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
    (if S.null cntrs then "" else " constrs: " ++ show (map show (S.toList cntrs))) ++
    (if M.null lit then "" else " lit: " ++ show (map show (M.toList lit)))

instance Contains AbValue where
  contains :: AbValue -> AbValue -> Bool
  contains (AbValue cls0 clsa0 cntrs0 lit0) (AbValue cls1 clsa1 cntrs1 lit1) =
    S.isSubsetOf cls1 cls0 && S.isSubsetOf clsa1 clsa0 && cntrs1 `S.isSubsetOf` cntrs0 && M.isSubmapOfBy (\lit0 lit1 -> lit0 < lit1) lit0 lit1

-- Basic creating of abstract values
showSimpleClosure :: (ExprContext, VEnv) -> String
showSimpleClosure (ctx, env) = showSimpleContext ctx ++ " in " ++ showSimpleEnv env

showNoEnvClosure :: (ExprContext, VEnv) -> String
showNoEnvClosure (ctx, env) = showSimpleContext ctx

showSimpleEnv :: VEnv -> String
showSimpleEnv c =
  "<<" ++ show c ++ ">>"

showSimpleAbValueCtx :: (VEnv, AbValue) -> String
showSimpleAbValueCtx (env, ab) =
  showSimpleEnv env ++ ": " ++ showSimpleAbValue ab ++ "\n"

showSimpleAbValue :: AbValue -> String
showSimpleAbValue (AbValue cls clsa cntrs lit) =
  (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
  (if S.null cntrs then "" else " constrs: [" ++ intercalate "," (map showSimpleClosure (S.toList cntrs)) ++ "]") ++
  (if M.null lit then "" else " lits: " ++ show (M.toList lit))

showNoEnvAbValue :: AbValue -> String
showNoEnvAbValue (AbValue cls clsa cntrs lit) =
  (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
  (if S.null cntrs then "" else " constrs: [" ++ intercalate "," (map showNoEnvClosure (S.toList cntrs)) ++ "]") ++
  (if M.null lit then "" else " lits: " ++ show (map snd (M.toList lit)))

emptyAbValue :: AbValue
emptyAbValue = AbValue S.empty S.empty S.empty M.empty

injLit :: C.Lit -> VEnv -> AChange
injLit x env =
  case x of
    C.LitInt i -> (AChangeLit $ LiteralChangeInt $ LChangeSingle i) env
    C.LitFloat f -> (AChangeLit $ LiteralChangeFloat $ LChangeSingle f) env
    C.LitChar c -> (AChangeLit $ LiteralChangeChar $ LChangeSingle c) env
    C.LitString s -> (AChangeLit $ LiteralChangeString $ LChangeSingle s) env

--- JOINING
joinML :: Ord x => M.Map VEnv (SLattice x) -> M.Map VEnv (SLattice x) -> M.Map VEnv (SLattice x)
joinML = M.unionWith join

addChange :: AbValue -> AChange -> AbValue
addChange ab@(AbValue cls clsapp cs lit) change =
  case change of
    AChangeClos lam env -> AbValue (S.insert (lam,env) cls) clsapp cs lit
    AChangeClosApp lam app env -> AbValue cls (S.insert (lam,app,env) clsapp) cs lit
    AChangeConstr c env -> AbValue cls clsapp (S.insert (c,env) cs) lit
    AChangeLit l env -> AbValue cls clsapp cs (M.insertWith joinLit env (litLattice l) lit)

joinAbValue :: AbValue -> AbValue -> AbValue
joinAbValue (AbValue cls0 clsa0 cs0 lit0) (AbValue cls1 clsa1 cs1 lit1) = AbValue (S.union cls0 cls1) (S.union clsa0 clsa1) (S.union cs0 cs1) (M.unionWith joinLit lit0 lit1)
