-----------------------------------------------------------------------------
-- Copyright 2024, Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# LANGUAGE InstanceSigs #-}
module Core.FlowAnalysis.Full.AbstractValue where
import Data.Map.Strict as M hiding (foldl, map)
import Common.Name
import Type.Type
import Data.Set hiding (foldl, map, map)
import Data.Set as S hiding (foldl, map)
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
import Lib.PPrint (Pretty (..), hcat, text, vcat, (<.>))
import Type.Pretty (ppType, defaultEnv)

-- TODO: Top Closures (expr, env, but eval results to the top of their type)

instance Pretty AbValue where
  pretty ab = text $ showSimpleAbValue ab

instance Pretty TName where
  pretty (TName n t _) = hcat [pretty n, text ":", ppType defaultEnv t]

instance Pretty Time where
  pretty (KTime local ctxs) = text ("KTime " ++ maybe "" (showSimpleCtxId . contextId) local) <.> pretty ctxs

instance Pretty ExprContextId where
  pretty id = text $ showSimpleCtxId id

showSimpleCtxId ctxId =
  case ctxId of
    ExprContextId id mod -> show id

type VStore = M.Map Addr AbValue

newtype Contour = KContour [ExprContext] deriving (Eq, Ord)

instance Show Contour where
  show (KContour ctxs) = intercalate "," (map (showSimpleCtxId . contextId) ctxs)

instance Pretty Contour where
  pretty (KContour ctxs) = text $ intercalate "," (map (showSimpleCtxId . contextId) ctxs)

data Time =
  KTime (Maybe ExprContext) Contour
  deriving (Eq, Ord)

instance Show Time where
  show (KTime local ctxs) = "KTime " ++ maybe "" (showSimpleCtxId . contextId) local ++ " " ++ show ctxs

instance Show KAddr where
  show (KAddr (ctx, env, time)) = show (contextId ctx) ++ " in " ++ show env ++ " at " ++ show time
  show KEnd = "KEnd"

instance Show MKAddr where
  show (MKAddr (ctx, env, time)) = show (contextId ctx) ++ " in " ++ show env ++ " at " ++ show time
  show MKEnd = "MKEnd"

type Addr = (TName, ExprContextId, Contour)
type VEnv = M.Map TName Addr

data KAddr = KAddr (ExprContext, VEnv, Contour) | KEnd deriving (Eq, Ord)
data MKAddr = MKAddr (ExprContext, VEnv, Contour) | MKEnd deriving (Eq, Ord)

showStore store = show $ pretty store

instance (Pretty k, Pretty v)=> Pretty (M.Map k v) where
  pretty amap =
      vcat $ map (\(k,v) -> hcat [pretty k, text " -> ", pretty v]) $ M.toList amap

data AChange =
  AChangeClos ExprContext VEnv
  | AChangePrim TName ExprContext VEnv
  | AChangeConstr ExprContext VEnv
  | AChangeOp Name ExprContext VEnv -- AChangeOp
  | AChangeLit LiteralChange
  | AChangeKont KAddr MKAddr -- Where to return to and where to extend the return continuation
  deriving (Eq, Ord)

envOfClos :: AChange -> VEnv
envOfClos res =
  case res of
    AChangeClos c e -> e
    AChangeOp _ c e -> e

ctxOfClos :: AChange -> ExprContext
ctxOfClos res =
  case res of
    AChangeClos c e -> c
    AChangeOp _ c e -> c

instance Show AChange where
  show (AChangeClos expr env) = showNoEnvClosure (expr, env)
  show (AChangeOp nm expr env) = showNoEnvClosure (expr, env)
  show (AChangeConstr expr env) = showSimpleClosure (expr, env)
  show (AChangePrim name expr env) = show name
  show (AChangeKont k _) = show k
  show (AChangeLit lit) = show lit

data AbValue =
  AbValue{
    aclos:: !(Set (ExprContext, VEnv)),
    aops:: !(Set (Name, ExprContext, VEnv)),
    acons:: !(Set (ExprContext, VEnv)),
    akonts:: !(Set (KAddr, MKAddr)),
    alits:: !LiteralLattice
  } deriving (Eq, Ord)

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
        Nothing -> error ("storeLookup: " ++ show x ++ " not found")
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
limitStore store fvs =
  let res' = M.filterWithKey (\k _ -> k `S.member` fvs) store in res'
  -- if M.size res' == S.size fvs then res' 
  -- else error $ "limitStore: not all addresses found \n" ++ show fvs ++ "\n" ++ show store

extendStore :: VStore -> (TName,ExprContextId,Contour) -> AChange -> VStore
extendStore store i v =
  M.alter (\oldv -> case oldv of {Nothing -> Just (addChange emptyAbValue v); Just ab -> Just (addChange ab v)}) i store

extendStoreAll :: VStore -> [(TName,ExprContextId,Contour)] -> [AChange] -> VStore
extendStoreAll store addrs changes = foldl (\acc (addr, ch) -> extendStore acc addr ch) store (zip addrs changes)

extendEnv :: VEnv -> [TName] -> [(TName,ExprContextId,Contour)] -> VEnv
extendEnv env args addrs = M.union (M.fromList $ zip args addrs) env -- Left biased will take the new

changes :: AbValue -> [AChange]
changes (AbValue clos clsops constrs konts lits) =
  closs ++ closops ++ constrss ++ ckonts ++ litss
  where
    closs = map (uncurry AChangeClos) $ S.toList clos
    closops = map (\(nm,ctx,env) -> AChangeOp nm ctx env) $ S.toList clsops
    ckonts = map (uncurry AChangeKont) $ S.toList konts
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
changeIn (AChangeClos ctx env) (AbValue clos _ _ _ _) = S.member (ctx,env) clos
changeIn (AChangeOp nm ctx env) (AbValue _ closops _ _ _) = S.member (nm,ctx,env) closops
changeIn (AChangeConstr ctx env) (AbValue _ _ constr _ _) = S.member (ctx,env) constr
changeIn (AChangeKont kont kontret) (AbValue _ _ _ konts _) = S.member (kont, kontret) konts
changeIn (AChangeLit lit) (AbValue _ _ _ _ (LiteralLattice ints floats chars strings)) =
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
  contains (AbValue cls0 clsa0 cntrs0 konts0 lit0) (AbValue cls1 clsa1 cntrs1 konts1 lit1) =
    S.isSubsetOf cls1 cls0 && S.isSubsetOf clsa1 clsa0 && cntrs1 `S.isSubsetOf` cntrs0 && lit0 `litContainsLattice` lit1 && konts0 `S.isSubsetOf` konts1

instance Show AbValue where
  show (AbValue cls clsapp cntrs konts lit) =
    (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
    (if S.null cntrs then "" else " constrs: " ++ show (map show (S.toList cntrs))) ++
    (if S.null konts then "" else " konts: " ++ show (map show (S.toList konts))) ++
    (if litIsBottom lit then "" else " lit: " ++ show lit)

showSimpleAbValue :: AbValue -> String
showSimpleAbValue (AbValue cls clsa cntrs konts lit) =
  (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
  (if S.null cntrs then "" else " constrs: [" ++ intercalate "," (map showSimpleClosure (S.toList cntrs)) ++ "]") ++
  (if S.null konts then "" else " konts: " ++ show (map show (S.toList konts))) ++
  (if litIsBottom lit then "" else " lits: " ++ show lit)

showNoEnvAbValue :: AbValue -> String
showNoEnvAbValue (AbValue cls clsa cntrs konts lit) =
  (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
  (if S.null cntrs then "" else " constrs: [" ++ intercalate "," (map showNoEnvClosure (S.toList cntrs)) ++ "]") ++
  (if S.null konts then "" else " konts: " ++ show (map show (S.toList konts))) ++
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
emptyAbValue = AbValue S.empty S.empty S.empty S.empty litBottom

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
addChange ab@(AbValue cls clsapp cs konts lit) change =
  case change of
    AChangeClos lam env -> AbValue (S.insert (lam,env) cls) clsapp cs konts lit
    AChangeOp nm app env -> AbValue cls (S.insert (nm,app,env) clsapp) cs konts lit
    AChangeConstr c env -> AbValue cls clsapp (S.insert (c,env) cs) konts lit
    AChangeKont k kr -> AbValue cls clsapp cs (S.insert (k,kr) konts) lit
    AChangeLit l -> AbValue cls clsapp cs konts (joinLit (litLattice l) lit)

joinAbValue :: AbValue -> AbValue -> AbValue
joinAbValue (AbValue cls0 clsa0 cs0 konts0 lit0) (AbValue cls1 clsa1 cs1 konts1 lit1) = AbValue (S.union cls0 cls1) (S.union clsa0 clsa1) (S.union cs0 cs1) (S.union konts0 konts1) (joinLit lit0 lit1)
