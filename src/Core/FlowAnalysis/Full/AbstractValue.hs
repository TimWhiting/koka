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
import Common.Failure (assertion, HasCallStack)
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.FixpointMonad (SimpleLattice(..), Lattice (..), Contains(..), SimpleChange (..), SLattice, FixT, doBottom, each)
import qualified Core.FlowAnalysis.FixpointMonad as FM
import Core.CoreVar (bv)
import Data.Foldable (find)
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.Literals

-- TODO: Top Closures (expr, env, but eval results to the top of their type)
  
type VStore = M.Map Addr AbValue

storeLookup :: (Ord i, Show c, Show (o c), Lattice o c, HasCallStack) => TName -> VEnv -> VStore -> FixAR r s e i o c AChange
storeLookup x env store = do
  case M.lookup x env of
    Just addr -> do
      case M.lookup addr store of
        Just value -> eachValue value
        Nothing -> error ("storeLookup: " ++ show addr ++ " not found")
    Nothing -> do
      -- trace ("storeLookup: " ++ show x ++ " not found") $ return ()
      lam <- bindExternal x
      case lam of
        Nothing -> doBottom
        Just lam -> do
          return $ AChangeClos lam M.empty

storeGet :: (Ord i, Show c, Show (o c), Lattice o c, HasCallStack) => VStore -> Addr -> FixAR r s e i o c AChange
storeGet store addr = do
  case M.lookup addr store of
    Just value -> eachValue value
    Nothing -> error $ "storeGet: " ++ show addr ++ " not found"

eachValue :: (Ord i, Show d, Show (l d), Lattice l d) => AbValue -> FixT e s i l d AChange
eachValue ab = each $ map return (changes ab)

tnamesCons :: Int -> [TName]
tnamesCons n = map (\i -> TName (newName ("con" ++ show i)) typeAny Nothing) [0..n]

limitEnv :: VEnv -> S.Set TName -> VEnv
limitEnv env fvs = M.filterWithKey (\k _ -> k `S.member` fvs) env

limitStore :: VStore -> S.Set Addr -> VStore
limitStore store fvs = M.filterWithKey (\k _ -> k `S.member` fvs) store

extendStore :: VStore -> (TName,ExprContextId) -> AChange -> VStore
extendStore store i v =
  M.alter (\oldv -> case oldv of {Nothing -> Just (addChange emptyAbValue v); Just ab -> Just (addChange ab v)}) i store

extendEnv :: VEnv -> [TName] -> [(TName,ExprContextId)] -> VEnv
extendEnv env args addrs = M.union (M.fromList $ zip args addrs) env -- Left biased will take the new

type Addr = (TName, ExprContextId)
type VEnv = M.Map TName Addr

data AChange =
  AChangeClos ExprContext VEnv
  | AChangePrim Name ExprContext VEnv
  | AChangeClosApp ExprContext ExprContext VEnv -- This is a closure that has a different application for it's calling context abstraction
  | AChangeConstr ExprContext VEnv
  | AChangeLit LiteralChange
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
    show name
  show (AChangeClosApp expr _ env) =
    showNoEnvClosure (expr, env)
  show (AChangeConstr expr env) =
    showNoEnvClosure (expr, env)
  show (AChangeLit lit) =
    show lit

data AbValue =
  AbValue{
    aclos:: !(Set (ExprContext, VEnv)),
    aclosapps:: !(Set (ExprContext, ExprContext, VEnv)),
    acons:: !(Set (ExprContext, VEnv)),
    alits:: !LiteralLattice
  } deriving (Eq, Ord)

changes :: AbValue -> [AChange]
changes (AbValue clos clsapp constrs lits) =
  closs ++ closapps ++ constrss ++ litss
  where
    closs = map (uncurry AChangeClos) $ S.toList clos
    closapps = map (\(a, b, c) -> AChangeClosApp a b c) $ S.toList clsapp
    constrss = map (uncurry AChangeConstr) $ S.toList constrs
    litss = changesLit lits

changesLit :: LiteralLattice -> [AChange]
changesLit (LiteralLattice ints floats chars strings) =
  intChanges ++ floatChanges ++ charChanges ++ stringChanges
  where
    intChanges = map (\x -> AChangeLit (LiteralChangeInt x)) $ FM.elems ints
    floatChanges = map (\x -> AChangeLit (LiteralChangeFloat x)) $ FM.elems floats
    charChanges = map (\x -> AChangeLit (LiteralChangeChar x)) $ FM.elems chars
    stringChanges = map (\x -> AChangeLit (LiteralChangeString x)) $ FM.elems strings

changeIn :: AChange -> AbValue -> Bool
changeIn (AChangeClos ctx env) (AbValue clos _ _ _) = S.member (ctx,env) clos
changeIn (AChangeClosApp ctx app env) (AbValue _ closapps _ _) = S.member (ctx,app,env) closapps
changeIn (AChangeConstr ctx env) (AbValue _ _ constr _) = S.member (ctx,env) constr
changeIn (AChangeLit lit) (AbValue _ _ _ (LiteralLattice ints floats chars strings)) =
  case lit of
    LiteralChangeInt i -> i `lte` ints
    LiteralChangeFloat f -> f `lte` floats
    LiteralChangeChar c -> c `lte` chars
    LiteralChangeString s -> s `lte` strings

instance Semigroup AbValue where
  (<>) :: AbValue -> AbValue -> AbValue
  (<>) = joinAbValue

instance Monoid AbValue where
  mempty = emptyAbValue
  mappend = (<>)

instance Contains AbValue where
  contains :: AbValue -> AbValue -> Bool
  contains (AbValue cls0 clsa0 cntrs0 lit0) (AbValue cls1 clsa1 cntrs1 lit1) =
    S.isSubsetOf cls1 cls0 && S.isSubsetOf clsa1 clsa0 && cntrs1 `S.isSubsetOf` cntrs0 && lit0 `litContainsLattice` lit1

instance Show AbValue where
  show (AbValue cls clsapp cntrs lit) =
    (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
    (if S.null cntrs then "" else " constrs: " ++ show (map show (S.toList cntrs))) ++
    (if litIsBottom lit then "" else " lit: " ++ show lit)

showSimpleAbValue :: AbValue -> String
showSimpleAbValue (AbValue cls clsa cntrs lit) =
  (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
  (if S.null cntrs then "" else " constrs: [" ++ intercalate "," (map showSimpleClosure (S.toList cntrs)) ++ "]") ++
  (if litIsBottom lit then "" else " lits: " ++ show lit)

showNoEnvAbValue :: AbValue -> String
showNoEnvAbValue (AbValue cls clsa cntrs lit) =
  (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
  (if S.null cntrs then "" else " constrs: [" ++ intercalate "," (map showNoEnvClosure (S.toList cntrs)) ++ "]") ++
  (if litIsBottom lit then "" else " lits: " ++ show lit)

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

emptyAbValue :: AbValue
emptyAbValue = AbValue S.empty S.empty S.empty litBottom

injLit :: C.Lit -> VEnv -> AChange
injLit x env =
  case x of
    C.LitInt i -> AChangeLit $ LiteralChangeInt $ LChangeSingle i
    C.LitFloat f -> AChangeLit $ LiteralChangeFloat $ LChangeSingle f
    C.LitChar c -> AChangeLit $ LiteralChangeChar $ LChangeSingle c
    C.LitString s -> AChangeLit $ LiteralChangeString $ LChangeSingle s

--- JOINING
joinML :: Ord x => M.Map VEnv (SLattice x) -> M.Map VEnv (SLattice x) -> M.Map VEnv (SLattice x)
joinML = M.unionWith join

addChange :: AbValue -> AChange -> AbValue
addChange ab@(AbValue cls clsapp cs lit) change =
  case change of
    AChangeClos lam env -> AbValue (S.insert (lam,env) cls) clsapp cs lit
    AChangeClosApp lam app env -> AbValue cls (S.insert (lam,app,env) clsapp) cs lit
    AChangeConstr c env -> AbValue cls clsapp (S.insert (c,env) cs) lit
    AChangeLit l -> AbValue cls clsapp cs (joinLit (litLattice l) lit)

joinAbValue :: AbValue -> AbValue -> AbValue
joinAbValue (AbValue cls0 clsa0 cs0 lit0) (AbValue cls1 clsa1 cs1 lit1) = AbValue (S.union cls0 cls1) (S.union clsa0 clsa1) (S.union cs0 cs1) (joinLit lit0 lit1)
