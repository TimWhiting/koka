{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Core.FlowAnalysis.Full.AAC.Monad where
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
import Lib.PPrint (vcat, text, Pretty(..), hcat, Doc, indent)

data FixInput =
  Eval ExprContext VEnv VStore KClos LocalKont Kont MetaKont
  | Cont LocalKont Kont MetaKont AChange VStore KClos
  | KStoreGet ExactContext
  | KApproxGet (AChange, AChange, VStore) -- Reverse lookup all the addresses 
  | CStoreGet MetaKont
  deriving (Eq, Ord)

data FixOutput a =
  A AbValue
  | K (S.Set (LocalKont, Kont))
  | C (S.Set (LocalKont, Kont, MetaKont))
  | KK (S.Set (LocalKont, Kont, KClos))
  | B (S.Set Bool)
  | Bottom
  deriving (Eq, Ord)

data FixChange =
  AC AChange
  | KC LocalKont Kont
  | KKC LocalKont Kont KClos
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

type LocalKont = [Frame]

type ApproxContext = (AChange, AChange, Addr)
type ExactContext = (AChange, AChange, VStore, KClos)
data Kont =
  KPrecise ExactContext
  | KApprox ApproxContext
  | KEnd
  deriving (Eq, Ord)

instance Show Kont where
  show (KPrecise (e, v, s, k)) = "KPrecise " ++ show e ++ " " ++ show v
  show (KApprox (e, v, a)) = "KApprox " ++ show e ++ " " ++ show v ++ " " ++ show a
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
addKont ctx@(clos, arg, store, kclos) lk mk = do
  lift $ push (KStoreGet ctx) (KC lk mk)
  lift $ push (KApproxGet (clos, arg, store)) (KKC lk mk kclos)

addMetaKont :: MetaKont -> LocalKont -> Kont -> MetaKont -> FixAACR r s e ()
addMetaKont c lk mk mmk = lift $ push (CStoreGet c) (CC lk mk mmk)

entails :: KClos -> KClos -> Bool
entails a b =
  M.isSubmapOfBy (\a b -> S.isSubsetOf a b) b a

konts :: ApproxContext -> KClos -> FixAACR r s e [(LocalKont, Kont)]
konts (e, env, a) kclos = do
  ress' <- mapM (\store -> memoFull (KApproxGet (e, env, store)) doBottom) (S.toList $ kclos M.! a)
  let res = S.unions (map (\(KK k) -> k) ress')
  return $ map (\(l,k,kc) -> (l,k)) $ filter (\(l,k, kclos') -> kclos `entails` kclos') (S.toList res)

llEnv :: VEnv -> S.Set Addr
llEnv env = S.fromList $ M.elems env

llLKont :: LocalKont -> S.Set Addr
llLKont l = S.unions (map llFrame l)

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
    AChangeConstr _ env -> llEnv env
    AChangeLit _ -> S.empty

llAbValue :: AbValue -> S.Set Addr
llAbValue ab = S.unions $ map llV $ changes ab

llA :: Addr -> VStore -> S.Set Addr
llA a store = maybe S.empty llAbValue (M.lookup a store)

liveAddrs :: VStore -> S.Set Addr -> S.Set Addr
liveAddrs store frontier =
  recur frontier S.empty
  where recur left marked =
          if null left then marked
          else
            let (next, nextLeft) = S.deleteFindMin left
                newMarked = S.insert next marked
                newFrontier = S.union (llA next store) nextLeft `S.difference` marked in
            recur newFrontier newMarked

llKont :: Kont -> KClos -> S.Set Kont -> FixAACR r s e (S.Set Addr)
llKont kont kclos seen =
  if kont `S.member` seen then return S.empty
  else do
    case kont of
      KEnd -> return S.empty
      KPrecise ctx@(clos, arg, store, xclos) -> do
        -- trace ("ClosV " ++ show (llV clos)) $ return ()
        -- trace ("ClosEnv " ++ show (envOfClos clos)) $ return ()
        K lks <- memoFull (KStoreGet ctx) doBottom
        -- trace ("Konts: " ++ show lks) $ return ()
        (seen, addrs) <- foldM (\(seen, addrs) (l, k) -> do
              addrs <- llKont k kclos seen
              return (S.insert k seen, S.union addrs (llLKont l))
          ) (S.insert kont seen, S.union (llV clos) (llV arg)) lks
        return $ S.union (S.fromList $ M.keys store) addrs
      KApprox ctx@(clos, arg, a) -> do
        reckaddrs <- llApprox ctx kclos (S.insert kont seen)
        return $ S.unions [llV clos, llV arg, reckaddrs]

llApprox:: ApproxContext -> KClos -> S.Set Kont -> FixAACR r s e (S.Set Addr)
llApprox appr@(e, env, a) kclos seen = do
  let stores = M.lookup a kclos
  lks <- konts appr kclos
  res <- foldM (\acc (l,k) -> do
    kaddrs <- llKont k kclos seen
    return $ S.unions [acc, llLKont l, kaddrs]
    ) (S.singleton a) lks
  let transitiveclosure = case stores of
        Just stores -> S.unions $ map (\s -> liveAddrs s res) $ S.toList stores
        Nothing -> S.empty
  return $ S.unions [res, transitiveclosure]

llKontA :: KontA -> KClos -> FixAACR r s e (S.Set Addr)
llKontA (KAppr l k) kclos = do
  llK <- llApprox k kclos S.empty
  return $ S.union llK (llLKont l)
llKontA (KPrec l) kclos = return $ llLKont l

llMeta :: MetaKont -> KClos -> S.Set MetaKont -> FixAACR r s e (S.Set Addr)
llMeta kont kclos seen =
  if kont `S.member` seen then return S.empty
  else do
    case kont of
      MEnd -> return S.empty
      MApply ka v store kclos' -> do
        llKA <- llKontA ka kclos'
        let vaddrs = llV v
        rest <- other
        return $ S.unions [llKA, vaddrs, rest]
      MReset e env store kclos' -> do
        let envAddrs = llEnv env
        rest <- other
        return $ S.unions [envAddrs, rest]
  where other = do
          C res <- memoFull (CStoreGet kont) doBottom
          foldM (\acc (l, k, m) -> do
            kaddrs <- llKont k kclos S.empty
            maddrs <- llMeta m kclos (S.insert kont seen)
            return $ S.union acc (S.unions [llLKont l, kaddrs, maddrs])
            ) S.empty (S.toList res)

gc :: FixInput ->  FixAACR r s e FixInput
gc (Eval e env store kclos klocal kont meta) = do
  -- trace ("\n\nGC:\n" ++ showSimpleContext e ++ "\n") $ return ()
  let env' = limitEnv env (fv (exprOfCtx e))
  -- trace ("GC Env:\n" ++ show (pretty env) ++ "\n=>\n" ++ show (pretty env) ++ "\n") $ return ()
  let laddrs = llLKont klocal
  kaddrs <- llKont kont kclos S.empty
  maddrs <- llMeta meta kclos S.empty
  let live = liveAddrs store (S.unions [llEnv env', laddrs, kaddrs, maddrs])
  -- trace ("GC LocalAddrs:\n" ++ show laddrs ++ "\n") $ return ()
  -- trace ("GC KontAddrs:\n" ++ show kaddrs ++ show kont ++ "\n") $ return ()
  let store' = limitStore store live
  -- trace ("GC Store:\n" ++ show (pretty store) ++ "\n=>\n" ++ show (pretty store') ++ "\n") $ return ()
  return $ Eval e env' store' kclos klocal kont meta
gc (Cont l kont meta achange store kclos) = do
  let laddrs = llLKont l
  let vaddrs = llV achange
  -- trace "\n\nGC Cont:\n" $ return ()
  kaddrs <- llKont kont kclos S.empty
  maddrs <- llMeta meta kclos S.empty
  -- trace ("GC LocalAddrs:\n" ++ show laddrs ++ "\n") $ return ()
  -- trace ("GC KontAddrs:\n" ++ show kaddrs ++ show kont ++ "\n") $ return ()
  let live = liveAddrs store (S.unions [vaddrs, laddrs, kaddrs, maddrs])
  let store' = limitStore store live
  -- trace ("GC Store:\n" ++ show (pretty store) ++ "\n=>\n" ++ show (pretty store') ++ "\n") $ return ()
  return $ Cont l kont meta achange store' kclos

showStore store = show $ pretty store

instance (Pretty k, Pretty v)=> Pretty (M.Map k v) where
  pretty amap =
      vcat $ map (\(k,v) -> hcat [pretty k, text " -> ", pretty v]) $ M.toList amap

instance Pretty AbValue where
  pretty ab = text $ showSimpleAbValue ab

instance Pretty TName where
  pretty (TName n t _) = hcat [pretty n, text ":", pretty t]

instance Pretty ExprContextId where
  pretty id = text $ show id

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

prettyLocal :: LocalKont -> Doc
prettyLocal l = vcat $ map (text . show) (reverse l)


instance Show Frame where
  show EndProgram = "EndProgram"
  show EndCall = "EndCall"
  show (AppL nargs e p) = "AppL " ++ showSimpleContext e ++ " nargs: " ++ show nargs
  show (AppM ch chs e n t p) = "AppM " ++ show ch ++ " arg: " ++ show n
  show (AppR ch chs) = "AppR " ++ show ch
  show (CaseR e p) = "CaseR " ++ showSimpleContext e
  show (LetL bgi bgn bi bn addrs e p) = "LetL " ++ show bgi ++ " " ++ show bgn ++ " " ++ show bi ++ " " ++ show bn ++ " " ++ showSimpleContext e ++ " "

instance Show FixInput where
  show (Eval expr env store kclos local kont meta) = show $ vcat [text "Eval", indent 2 (vcat [prettyLocal local, text (showSimpleContext expr), pretty env, pretty store])]
  show (Cont local kont meta achange store kclos) = show $ vcat [text "Cont", indent 2 (vcat [prettyLocal local, text (show kont), text (show meta), text (show achange), pretty store])]
  show (KStoreGet ctx) = "KStoreGet"
  show (CStoreGet meta) = "CStoreGet"

instance Lattice FixOutput FixChange where
  bottom = Bottom
  isBottom Bottom = True
  isBottom _ = False
  insert (AC a) Bottom = A $ addChange emptyAbValue a
  insert (AC a) (A x) = A $ addChange x a
  insert (KC l k) (K x) = K $ S.insert (l, k) x
  insert (KC l k) Bottom = K $ S.singleton (l, k)
  insert (KKC l k kclos) (KK x) = KK $ S.insert (l, k, kclos) x
  insert (KKC l k kclos) Bottom = KK $ S.singleton (l, k, kclos)
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
  join (KK x) (KK y) = KK (S.union x y)
  join (C x) (C y) = C (S.union x y)
  join (B x) (B y) = B (S.union x y)
  lte ChangeBottom _ = True
  lte _ Bottom = False
  lte (CC l k c) (C y) = (l, k, c) `S.member` y
  lte (KC l k) (K y) = (l, k) `S.member` y
  lte (KKC l k kclos) (KK y) = (l, k, kclos) `S.member` y
  lte (AC x) (A y) = x `changeIn` y
  lte (BC x) (B y) = x `elem` y
  lte x y = error ("lte: " ++ show x ++ " " ++ show y)
  elems (A a) = map AC $ changes a
  elems (K x) = map (uncurry KC) $ S.toList x
  elems (KK x) = map (\(l,k,c) -> KKC l k c) $ S.toList x
  elems (C x) = map (\(l,k,c) -> CC l k c) $ S.toList x
  elems (B x) = map BC $ S.toList x
  elems Bottom = []