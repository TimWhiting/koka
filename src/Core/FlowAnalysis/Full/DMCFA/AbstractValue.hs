-----------------------------------------------------------------------------
-- Copyright 2024, Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# LANGUAGE InstanceSigs #-}
module Core.FlowAnalysis.Full.DMCFA.AbstractValue where
import Data.Map.Strict as M hiding (take, foldl, map)
import Common.Name
import Type.Type
import Data.Set hiding (take, foldl, map, map)
import qualified Data.Set as S hiding (take)
import Core.Core as C
import Syntax.Syntax as S hiding (Handler)
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
import Core.Core (Expr)
import Data.Hashable

showSimpleCtxId ctxId =
  case ctxId of
    ExprContextId id mod -> show id

data Call =
  CallTop
  | CallDelim
  | CallApp ExprContextId
  deriving (Eq, Ord)

instance Show Call where
  show CallTop = "top"
  show CallDelim = "delim"
  show (CallApp ctxId) = "a" ++ showSimpleCtxId ctxId

data StaticCtx = 
  TKTop [Call]
  | TKDelim [Call]
  deriving (Eq, Ord)
instance Show StaticCtx where
  show (TKTop calls) = "t_" ++ show calls
  show (TKDelim calls) = "d_" ++ show calls

type DynamicCtx = [((ExprContextId, Name), StaticCtx)]

data CombinedCtx = CombinedCtx {
  static :: StaticCtx,
  dynamic :: DynamicCtx
  } deriving (Eq, Ord)
instance Show CombinedCtx where
  show (CombinedCtx static dynamic) =
    show static ++ "@" ++ show dynamic

ctxHnd :: CombinedCtx -> (ExprContextId, Name)
ctxHnd (CombinedCtx _ (((id, nm), _): rst)) = (id, nm)
ctxHnd (CombinedCtx _ []) = (ExprContextId (-5000) (newName "hnd"), newName "hnd")

addCall :: Int -> CombinedCtx -> ExprContextId -> CombinedCtx
addCall m (CombinedCtx (TKDelim static) dyn) call = CombinedCtx (TKDelim $ take m $ CallApp call : static) dyn
addCall m (CombinedCtx (TKTop static) dyn) call = CombinedCtx (TKTop $ take m $ CallApp call : static) dyn

addDelim :: Int -> CombinedCtx -> ExprContextId -> Name -> DynamicCtx
addDelim d (CombinedCtx static dyn) delim name = take d $ ((delim, name), static) : dyn

delimCtx m ctx = TKDelim $ take m [CallDelim] -- take m ctx -- take m [CallDelim]

newDelim d m (CombinedCtx static dyn) delim name = CombinedCtx (delimCtx m static) $ take d $ ((delim, name), static) : dyn

type VEnv = M.Map TName CombinedCtx

data DelimitedVal = 
  DVal {
      dLabel :: Name,
      dOpName :: Name,
      dExpr :: ExprContext,
      dArgs :: [Addr],
      dCtx :: CombinedCtx
  } deriving (Eq, Ord, Show)

data DelimitedFrame =
  DFrame {
      dframeVEnv :: VEnv,
      dframeBodId :: ExprContextId,
      dframeHnd :: Handler
  } | DFrameLocal {
      dflVEnv :: VEnv,
      dflBodId :: ExprContextId,
      dflVarName :: TName,
      dflValAddr :: Addr
  } | DFrameDone 
  | DFrameNone -- Don't use DelimFrames
  deriving (Eq, Ord, Show)

data Addr =
  BindingAddr !CombinedCtx !TName
  | UnitAddr
  | EndVAddr
  | EndKAddr
  | KAddr !Frame !StaticCtx !DelimitedFrame !DelimitedVal
  | ImplicitAddr !CombinedCtx !VEnv !ExprContextId
  | ImplicitLAddr !CombinedCtx !CombinedCtx !Name !Name !VEnv !ExprContextId
  | BindImplicitAddr !CombinedCtx !VEnv !ExprContextId
  | ConImplicitAddr !Name !CombinedCtx !ExprContextId
  deriving (Eq, Ord)
instance Show Addr where
  show (BindingAddr ctx name) = "B@(" ++ show name ++ ":" ++ show ctx ++ ")"
  show UnitAddr = "UnitAddr"
  show EndVAddr = "EndVAddr"
  show EndKAddr = "EndKAddr"
  show (KAddr frame ctx dframe dval) = "K@(" ++ show frame ++ "," ++ show ctx ++ "," ++ show dframe ++ "," ++ show dval ++ ")"
  show (ImplicitAddr ctx env ctxId) = "AI@(" ++ showSimpleCtxId ctxId ++ ":" ++ show ctx ++ ")"
  show (ImplicitLAddr _ ctx nm _ env ctxId) = "IL@(" ++ showSimpleCtxId ctxId ++ ":" ++ show ctx ++ ")"
  show (BindImplicitAddr ctx env ctxId) = "BI@(" ++ showSimpleCtxId ctxId ++ ":" ++ show ctx ++ ")"
  show (ConImplicitAddr nm ctx ctxId) = "CI@(" ++ show nm ++ " " ++ showSimpleCtxId ctxId ++ ":" ++ show ctx ++ ")"

data RValue = 
  RVAddr Addr 
  | ROp DelimitedVal StaticCtx Frame DelimitedFrame Addr 
  deriving (Eq, Ord, Show)

kaddrEnv :: Addr -> VEnv 
kaddrEnv (ImplicitAddr _ env _) = env

kaddrId :: Addr -> ExprContextId
kaddrId (ImplicitAddr _ _ ctxId) = ctxId

data Frame =
  FrameDone
  | FScrut {
      parent :: ExprContext,
      branches :: [ExprContext],
      env :: VEnv
    }
  | FOp {
      effName :: Name,
      totalArgs :: Int,
      leftArgs :: [ExprContext],
      resolvedArgs :: [Addr],
      parent :: ExprContext,
      env :: VEnv
    }
  | FApp {
      totalArgs :: Int,
      leftArgs :: [ExprContext],
      resolvedArgs :: [Addr],
      parent :: ExprContext,
      env :: VEnv
    }
  | FLet {
        groupIdx :: Int,
        numGroups :: Int,
        bindingIdx :: Int,
        numBindings :: Int,
        name :: TName,
        resolved :: [Addr],
        parent :: ExprContext,
        env :: VEnv
      }
  | FDollar {
      vaddr :: Addr -- Precise closure address
  }
  | FResume {
      rframe :: Frame,
      rretCtx :: StaticCtx,
      vaddr :: Addr,
      venv :: VEnv,
      rHnd :: Handler,
      rCtx :: ExprContextId
  }
  | FStore {
      vaddr :: Addr
  }
  | FRestoreDelim {
     dframe :: DelimitedFrame
  }
  | FMask
  | FCall
  deriving (Eq, Ord, Show)


nextLetFrame :: Frame -> CombinedCtx -> Frame
nextLetFrame
  (FLet groupIdx numGroups bindingIdx numBindings name resolved parent
        env) ctx
  | bindingIdx < numBindings - 1 = FLet groupIdx numGroups (bindingIdx + 1) numBindings (letBindingName groupIdx bindingIdx parent) resolved parent env
  | groupIdx < numGroups - 1 =
      let C.Let dgs _ = exprOfCtx parent
          gidx = groupIdx + 1
          idx = 0
          defs = defsOf (dgs !! gidx)
          newEnv = foldl (\acc x -> M.insert (defTName x) ctx acc) env defs in
      FLet gidx numGroups idx (length defs) (letBindingName gidx idx parent) resolved parent newEnv
  | otherwise = error ("No next let frame for: " ++ show (groupIdx, numGroups, bindingIdx, numBindings, resolved, parent, env))


data Kont =
  KEnd
  | KNext { knext :: Addr }
  | KLocal { kLocalNext :: Addr }
  | KLink { kLinkNext :: Addr }
  deriving (Eq, Ord, Show)

data Handler =
  Handler { hLabel :: Name, ops :: Addr, hReturnExpr :: Maybe ExprContext, hReturn :: Maybe Frame }
  deriving (Eq, Ord, Show)

startStaticCtx = [CallTop]
startDelimCtx = [CallDelim]
startDynCtx = []
startEnv = M.empty

lookupEnv :: HasCallStack => TName -> VEnv -> Maybe Addr
lookupEnv x env =
  case M.lookup x env of
    Just ctx -> Just $ BindingAddr ctx x
    Nothing -> Nothing

showStore store = show $ pretty store

instance (Pretty k, Pretty v)=> Pretty (M.Map k v) where
  pretty amap =
      vcat $ map (\(k,v) -> hcat [pretty k, text " -> ", pretty v]) $ M.toList amap

data AChange =
  AChangeClos ExprContext VEnv
  | AChangePrim TName ExprContext
  | AChangeConstr ExprContext [Name]
  | AChangeObj ExprContext TName [(Name,Addr)]
  | AChangeLit LiteralChangeX
  | AChangeKont StaticCtx Frame Name Addr VEnv Handler -- Where to return to and where to extend the return continuation
  deriving (Eq, Ord)
  
vcontextId change = 
  case change of 
    AChangeClos e _ -> contextId e 
    AChangePrim _ e -> contextId e
    AChangeConstr e _ -> contextId e
    AChangeObj e _ _ -> contextId e
    AChangeLit e -> litEx e
    AChangeKont _ _ _ _ _ h@(Handler _ _ e _) -> contextId $ fromJust e

envOfClos :: AChange -> VEnv
envOfClos res =
  case res of
    AChangeClos c e -> e

ctxOfClos :: AChange -> ExprContext
ctxOfClos res =
  case res of
    AChangeClos c e -> c

instance Show AChange where
  show (AChangeClos expr env) = showNoEnvClosure (expr, env)
  show (AChangeConstr expr params) = showSimpleClosure (expr, startEnv)
  show (AChangeObj e name args) = show name ++ "(" ++ show args ++ ")"
  show (AChangePrim name expr) = show name
  show (AChangeKont ctx frame name addr env handler) = "Kont" ++ show (ctx, frame, name, addr, env, handler)
  show (AChangeLit lit) = show lit

data AbValue =
  AbValue{
    aclos:: !(Set (ExprContext, VEnv)),
    acons:: !(Set (ExprContext, [Name])),
    aprims :: !(Set (TName, ExprContext)),
    aobjs :: !(Set (ExprContext, TName, [(Name,Addr)])),
    akonts:: !(Set (StaticCtx, Frame, Name, Addr, VEnv, Handler)),
    alits:: !LiteralLatticeX
  } deriving (Eq, Ord)

sizeOf :: AbValue -> Int
sizeOf (AbValue cls cntrs prims objs konts lit) =
  length cls + length cntrs + length prims + length objs + length konts + sizeLitX lit

sizeLitX :: LiteralLatticeX -> Int
sizeLitX (LiteralLatticeX sint sfloat schar strings) =
  sizeLit sint + sizeLit sfloat + sizeLit schar + sizeLit strings

sizeLit :: SLattice a -> Int
sizeLit LBottom = 0
sizeLit LTop = 2
sizeLit LSingle{} = 1

addrs :: AbValue -> [Addr]
addrs (AbValue _ _ _ objs _ _) = concatMap (\(_, _, args) -> map snd args) objs

changes :: AbValue -> [AChange]
changes (AbValue clos constrs prims objs konts lits) =
  closs ++ constrss ++ primss ++ objss ++ kontss ++ litss
  where
    closs = map (uncurry AChangeClos) $ S.toList clos
    constrss = map (uncurry AChangeConstr) $ S.toList constrs
    primss = map (uncurry AChangePrim) $ S.toList prims
    objss = map (\(e, n, a) -> AChangeObj e n a) $ S.toList objs
    kontss = map (\(ctx, frame, name, addr, env, handler) -> AChangeKont ctx frame name addr env handler) $ S.toList konts
    litss = changesLit lits

changesLit :: LiteralLatticeX -> [AChange]
changesLit (LiteralLatticeX sint sfloat schar strings) =
  [AChangeLit (LiteralChangeIntX int) | int <- FM.elems sint] ++
  [AChangeLit (LiteralChangeFloatX float) | float <- FM.elems sfloat] ++
  [AChangeLit (LiteralChangeCharX char) | char <- FM.elems schar] ++
  [AChangeLit (LiteralChangeStringX string) | string <- FM.elems strings]

changeIn :: AChange -> AbValue -> Bool
changeIn (AChangeClos ctx env) (AbValue clos _ _ _ _ _) = S.member (ctx,env) clos
changeIn (AChangeConstr ctx params) (AbValue _ constr _ _ _ _) = S.member (ctx,params) constr
changeIn (AChangePrim name expr) (AbValue _ _ prims _ _ _) = S.member (name, expr) prims
changeIn (AChangeObj exp name args) (AbValue _ _ _ objs _ _) = S.member (exp, name, args) objs
changeIn (AChangeKont ctx frame name addr env handler) (AbValue _ _ _ _ konts _) = S.member (ctx, frame, name, addr, env, handler) konts
changeIn (AChangeLit lit) (AbValue _ _ _ _ _ (LiteralLatticeX ints floats chars strings)) =
  case lit of
    LiteralChangeIntX i -> i `lteX` ints
    LiteralChangeFloatX f -> f `lteX` floats
    LiteralChangeCharX c -> c `lteX` chars
    LiteralChangeStringX s -> s `lteX` strings
instance Semigroup AbValue where
  (<>) :: AbValue -> AbValue -> AbValue
  (<>) = joinAbValue

instance Monoid AbValue where
  mempty = emptyAbValue
  mappend = (<>)

instance Show AbValue where
  show (AbValue cls cntrs prims objs konts lit) =
    (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
    (if S.null cntrs then "" else " constrs: " ++ show (map show (S.toList cntrs))) ++
    (if S.null objs then "" else " objs: " ++ show (map show (S.toList objs))) ++
    (if S.null prims then "" else " prims: " ++ show (map show (S.toList prims))) ++
    (if S.null konts then "" else " konts: " ++ show (map show (S.toList konts))) ++
    (" lit: " ++ show lit)

instance Contains AbValue where
  contains :: AbValue -> AbValue -> Bool
  contains (AbValue cls0 cntrs0 prims0 objs0 konts0 lit0) (AbValue cls1 cntrs1 prims1 objs1 konts1 lit1) =
    S.isSubsetOf cls1 cls0 && cntrs1 `S.isSubsetOf` cntrs0 && prims1 `S.isSubsetOf` prims0 && objs1 `S.isSubsetOf` objs0 && konts1 `S.isSubsetOf` konts0 && lit0 < lit1

eachValue :: (Ord i, Show d, Show l, Lattice l d) => AbValue -> FixT e s i l d AChange
eachValue ab = each $ map return (changes ab)

tnamesCons :: Int -> [TName]
tnamesCons n = map (\i -> TName (newName ("con" ++ show i)) typeAny Nothing) [0..n]

limitEnv :: VEnv -> S.Set TName -> VEnv
limitEnv env fvs = M.filterWithKey (\k _ -> k `S.member` fvs) env

showSimpleAbValue :: AbValue -> String
showSimpleAbValue (AbValue cls cntrs prims objs konts lit) =
  (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
  (if S.null cntrs then "" else " constrs: [" ++ intercalate "," (map (showSimpleContext . fst) (S.toList cntrs)) ++ "]") ++
  (if S.null prims then "" else " prims: [" ++ intercalate "," (map (showSimpleContext . snd) (S.toList prims)) ++ "]") ++
  (if S.null objs then "" else " objs: [" ++ intercalate "," (map show (S.toList objs)) ++ "]") ++
  (if S.null konts then "" else " konts: " ++ show (map show (S.toList konts))) ++
  (if litIsBottomX lit then "" else " lits: " ++ show lit)

showNoEnvAbValue :: AbValue -> String
showNoEnvAbValue (AbValue cls cntrs prims objs konts lit) =
  (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
  (if S.null cntrs then "" else " constrs: [" ++ intercalate "," (map (showSimpleContext . fst) (S.toList cntrs)) ++ "]") ++
  (if S.null prims then "" else " prims: [" ++ intercalate "," (map (showSimpleContext . snd) (S.toList prims)) ++ "]") ++
  (if S.null objs then "" else " objs: [" ++ intercalate "," (map show (S.toList objs)) ++ "]") ++
  (if S.null konts then "" else " konts: " ++ show (map show (S.toList konts))) ++
  (if litIsBottomX lit then "" else " lits: " ++ show lit)

-- Basic creating of abstract values
showSimpleClosure :: (ExprContext, VEnv) -> String
showSimpleClosure (ctx, env) = showSimpleContext ctx ++ " in " ++ showSimpleEnv env

showNoEnvClosure :: (ExprContext, VEnv) -> String
showNoEnvClosure (ctx, env) = showSimpleContext ctx

showSimpleEnv :: VEnv -> String
showSimpleEnv c =
  "<<" ++ show (M.toList c) ++ ">>"

showSimpleAbValueCtx :: (VEnv, AbValue) -> String
showSimpleAbValueCtx (env, ab) =
  showSimpleEnv env ++ ": " ++ showSimpleAbValue ab ++ "\n"

emptyAbValue :: AbValue
emptyAbValue = AbValue S.empty S.empty S.empty S.empty S.empty litBottomX

injLit :: ExprContextId -> C.Lit -> AChange
injLit e x =
  case x of
    C.LitInt i -> AChangeLit $ LiteralChangeIntX $ LChangeSingle (e, i)
    C.LitFloat f -> AChangeLit $ LiteralChangeFloatX $ LChangeSingle (e, f)
    C.LitChar c -> AChangeLit $ LiteralChangeCharX $ LChangeSingle (e, c)
    C.LitString s -> AChangeLit $ LiteralChangeStringX $ LChangeSingle (e, s)

--- JOINING
-- joinML :: Ord x => M.Map VEnv (SLattice x) -> M.Map VEnv (SLattice x) -> M.Map VEnv (SLattice x)
-- joinML = M.unionWith join

addChange :: AbValue -> AChange -> (AChange, AbValue)
addChange ab@(AbValue cls cs prims objs konts lit) change =
  case change of
    AChangeClos lam env -> (change, AbValue (S.insert (lam,env) cls) cs prims objs konts lit)
    AChangePrim name expr -> (change, AbValue cls cs (S.insert (name, expr) prims) objs konts lit)
    AChangeObj exp name addrs -> (change, AbValue cls cs prims (S.insert (exp, name, addrs) objs) konts lit)
    AChangeConstr c params -> (change, AbValue cls (S.insert (c,params) cs) prims objs konts lit)
    AChangeKont ctx frame name addr env handler -> (change, AbValue cls cs prims objs (S.insert (ctx, frame, name, addr, env, handler) konts) lit)
    AChangeLit l ->
      let (change, newLattice) = joinLitX l lit
      in (AChangeLit change, AbValue cls cs prims objs konts newLattice)

joinAbValue :: AbValue -> AbValue -> AbValue
joinAbValue (AbValue cls0 cs0 prims0 objs0 konts0 lit0) (AbValue cls1 cs1 prims1 objs1 konts1 lit1) =
  AbValue (S.union cls0 cls1) (S.union cs0 cs1) (S.union prims0 prims1) (S.union objs0 objs1) (S.union konts0 konts1) (joinLitLatticeX lit0 lit1)

intV :: AbValue -> SLattice Integer
intV a = lat $ intVLX (alits a)

floatV :: AbValue -> SLattice Double
floatV a = lat $ floatVLX (alits a)

charV :: AbValue -> SLattice Char
charV a = lat $ charVLX (alits a)

stringV :: AbValue -> SLattice String
stringV a = lat $ stringVLX (alits a)