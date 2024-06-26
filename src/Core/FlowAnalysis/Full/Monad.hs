{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
module Core.FlowAnalysis.Full.Monad where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Reader (lift)
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.Full.AbstractValue
import Core.FlowAnalysis.Literals
import Core.Core
import Data.Int (Int)
import Common.Name
import Debug.Trace (trace)
import Common.NamePrim (nameOpen, nameEffectOpen)
import Data.Maybe (fromJust)
import Compile.Module (Module(..))
import Common.Failure (HasCallStack)
import Type.Type (splitFunType, typeAny)
import Control.Monad (foldM)
import GHC.Base (when)
import Core.CoreVar (HasExpVar(fv), bv)
import Lib.PPrint (vcat, text)

type VStore = M.Map Addr AbValue
data FixInput =
  Eval ExprContext VEnv VStore KClos LocalKont Kont MetaKont
  | Cont LocalKont Kont MetaKont AChange VStore KClos
  | KStoreGet ExactContext
  | CStoreGet MetaKont
  | Pop LocalKont Kont
  | NoTop LocalKont Kont
  deriving (Eq, Ord)

data FixOutput a =
  A AbValue
  | K (S.Set (LocalKont, Kont))
  | C (S.Set (LocalKont, Kont, MetaKont))
  | B (S.Set Bool)
  | Bottom
  deriving (Eq, Ord)

data FixChange =
  AC AChange
  | KC LocalKont Kont
  | CC LocalKont Kont MetaKont
  | BC Bool
  | ChangeBottom
  deriving (Eq, Ord)

type FixAACR r s e a = FixAR r s e FixInput FixOutput FixChange a
type FixAAC r s e = FixAACR r s e (FixOutput FixChange)
type PostFixAACR r s e a = PostFixAR r s e FixInput FixOutput FixChange a
type PostFixAAC r s e = PostFixAACR r s e (FixOutput FixChange)

data Frame =
  EndProgram
  | EndCall
  | AppL Int ExprContext VEnv -- Length of args and parent expression
  | AppM AChange [Addr] ExprContext Int Int VEnv -- This environment is the one in which the args are evaluated
  | AppR AChange [Addr]
  | LetL Int Int Int Int [Addr] ExprContext VEnv -- Binding group index, num binding groups, binding index, num bindings, addresses for binding group, parent expresion, parent env
  | CaseR ExprContext VEnv
  deriving (Eq, Ord)

instance Show Frame where
  show EndProgram = "EndProgram"
  show EndCall = "EndCall"
  show (AppL nargs e p) = "AppL " ++ show nargs ++ " " ++ showSimpleEnv p
  show (AppM ch chs e n t p) = "AppL " ++ show n ++ " " ++ show t
  show (AppR ch chs) = "AppR " ++ show ch ++ " " ++ show chs
  show (CaseR e p) = "CaseR"
  show (LetL bgi bgn bi bn addrs e p) = "LetL " ++ show bgi ++ " " ++ show bgn ++ " " ++ show bi ++ " " ++ show bn ++ " " ++ showSimpleContext e ++ " " ++ showSimpleEnv p

type LocalKont = [Frame]

type ApproxContext = (ExprContext, VEnv, Addr)
type ExactContext = (ExprContext, VEnv, VStore, KClos)
data Kont =
  KPrecise ExactContext
  | KApprox ApproxContext
  | KEnd
  deriving (Eq, Ord)

instance Show Kont where
  show (KPrecise (e, v, s, k)) = "KPrecise " ++ showSimpleContext e ++ " " ++ showSimpleEnv v
  show (KApprox (e, v, a)) = "KApprox " ++ showSimpleContext e ++ " " ++ showSimpleEnv v ++ " " ++ show a
  show KEnd = "KEnd"

data KontA =
  KAppr LocalKont ApproxContext
  | KPrec LocalKont
  deriving (Eq, Ord, Show)

type KClos = M.Map Addr (S.Set VStore)
data MetaKont =
  MReset ExprContext VEnv VStore KClos
  | MApply KontA AChange VStore KClos
  | MEnd
  deriving (Eq, Ord, Show)

approximate :: Addr -> KClos -> LocalKont -> Kont -> (KClos, KontA)
approximate a x l KEnd = (x, KPrec l)
approximate a x l (KPrecise (f, v, st, x1)) = ((x `unionK` x1) `unionK` M.singleton a (S.singleton st), KAppr l (f, v, a))
approximate a x l (KApprox (f, v, b)) = let Just !xx = M.lookup b x in (x, KAppr l (f, v, a))

unionK :: KClos -> KClos -> KClos
unionK = M.unionWith S.union

addKont :: ExactContext -> LocalKont -> Kont -> FixAACR r s e ()
addKont c lk mk = lift $ push (KStoreGet c) (KC lk mk)

addMetaKont :: MetaKont -> LocalKont -> Kont -> MetaKont -> FixAACR r s e ()
addMetaKont c lk mk mmk = lift $ push (CStoreGet c) (CC lk mk mmk)

storeLookup :: HasCallStack => TName -> VEnv -> VStore -> FixAACR r s e AChange
storeLookup x env store = do
  case M.lookup x env of
    Just addr -> do
      let value = store M.! addr
      eachValue value
    Nothing -> do
      lam <- bindExternal x
      case lam of
        Nothing -> doBottom
        Just lam -> do
          return $ AChangeClos lam M.empty

storeGet :: HasCallStack => VStore -> Addr -> FixAACR r s e AChange
storeGet store addr = do
  case M.lookup addr store of
    Just value -> eachValue value
    Nothing -> error $ "storeGet: " ++ show addr ++ " not found"

tnamesCons :: Int -> [TName]
tnamesCons n = map (\i -> TName (newName ("con" ++ show i)) typeAny Nothing) [0..n]

eachValue :: (Ord i, Show d, Show (l d), Lattice l d) => AbValue -> FixT e s i l d AChange
eachValue ab = each $ map return (changes ab)

extendStore :: VStore -> (TName,ExprContextId) -> AChange -> VStore
extendStore store i v =
  M.alter (\oldv -> case oldv of {Nothing -> Just (addChange emptyAbValue v); Just ab -> Just (addChange ab v)}) i store

limitEnv :: VEnv -> S.Set TName -> VEnv
limitEnv env fvs = M.filterWithKey (\k _ -> k `S.member` fvs) env

limitStore :: VStore -> S.Set Addr -> VStore
limitStore store fvs = M.filterWithKey (\k _ -> k `S.member` fvs) store

llEnv :: VEnv -> S.Set Addr
llEnv env = S.fromList $ M.elems env

llLKont :: LocalKont -> S.Set Addr
llLKont l = S.unions (map llFrame l)

-- TODO: Live locations for other continuations

llFrame :: Frame -> S.Set Addr
llFrame EndProgram = S.empty
llFrame EndCall = S.empty
llFrame (AppL _ _ env) = llEnv env
llFrame (AppM v addrs _ _ _ env) = S.unions [llEnv env, S.fromList addrs, llV v]
llFrame (AppR v addrs) = S.union (llV v) (S.fromList addrs)
llFrame (LetL _ _ _ _ addrs _ env) = S.union (llEnv env) (S.fromList addrs)
llFrame (CaseR _ env) = llEnv env

llV :: AChange -> S.Set Addr
llV achange =
  case achange of
    AChangeClos _ env -> llEnv env
    AChangePrim _ _ env -> llEnv env
    AChangeClosApp _ _ env -> llEnv env
    AChangeConstr _ env -> llEnv env
    AChangeLit _ env -> S.empty

llAbValue :: AbValue -> S.Set Addr
llAbValue ab = S.unions $ map llV $ changes ab

llA :: Addr -> VStore -> S.Set Addr
llA a store = maybe S.empty llAbValue (M.lookup a store)

liveAddrs :: VStore -> S.Set Addr -> S.Set Addr
liveAddrs store frontier =
  recur frontier S.empty
  where recur frontier marked =
          if null frontier then marked
          else
            let (next, frontier') = S.deleteFindMin frontier in
            recur (S.union (llA next store) frontier') (S.insert next marked)


extendEnv :: VEnv -> [TName] -> [(TName,ExprContextId)] -> VEnv
extendEnv env args addrs = M.union (M.fromList $ zip args addrs) env -- Left biased will take the new


instance Show (FixOutput a) where
  show (A x) = show x
  show (K x) = show x
  show (C x) = show x
  show (B x) = show x
  show Bottom = "Bottom"

instance Show FixChange where
  show (AC x) = show x
  show (KC l k) = show l ++ " " ++ show k
  show (CC l k c) = show l ++ " " ++ show k ++ " " ++ show c
  show (BC b) = show b
  show ChangeBottom = "Bottom"

instance Show FixInput where
  show (Eval expr env store kclos local kont meta) = "Eval " ++ showSimpleContext expr ++ " " ++ showSimpleEnv env ++ show store ++ show local
  show (Cont local kont meta achange store kclos) = "Cont " ++ show local ++ " " ++ show kont ++ " " ++ show meta ++ " " ++ show achange
  show (KStoreGet ctx) = "KStoreGet"
  show (CStoreGet meta) = "CStoreGet"
  show (Pop local kont) = "Pop"
  show (NoTop local kont) = "NoTop"

instance Lattice FixOutput FixChange where
  bottom = Bottom
  isBottom Bottom = True
  isBottom _ = False
  insert (AC a) Bottom = A $ addChange emptyAbValue a
  insert (AC a) (A x) = A $ addChange x a
  insert (KC l k) (K x) = K $ S.insert (l, k) x
  insert (KC l k) Bottom = K $ S.singleton (l, k)
  insert (CC l k c) (C x) = C $ S.insert (l, k, c) x
  insert (CC l k c) Bottom = C $ S.singleton (l, k, c)
  insert (BC b) (B x) = B $ S.insert b x
  insert (BC b) Bottom = B $ S.singleton b
  insert ChangeBottom a = a
  join Bottom Bottom = Bottom
  join Bottom x = x
  join x Bottom = x
  join (A x) (A y) = A (joinAbValue x y)
  join (K x) (K y) = K (S.union x y)
  join (C x) (C y) = C (S.union x y)
  join (B x) (B y) = B (S.union x y)
  lte ChangeBottom _ = True
  lte _ Bottom = False
  lte (CC l k c) (C y) = (l, k, c) `S.member` y
  lte (KC l k) (K y) = (l, k) `S.member` y
  lte (AC x) (A y) = x `changeIn` y
  lte (BC x) (B y) = x `elem` y
  lte x y = error ("lte: " ++ show x ++ " " ++ show y)
  elems (A a) = map AC $ changes a
  elems (K x) = map (uncurry KC) $ S.toList x
  elems (C x) = map (\(l,k,c) -> CC l k c) $ S.toList x
  elems (B x) = map BC $ S.toList x
  elems Bottom = []