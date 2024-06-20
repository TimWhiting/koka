{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
module Core.FlowAnalysis.Full.AAC where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Reader (lift)
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.Full.AbstractValue
import Core.Core
import Data.Int (Int)
import Common.Name
import Debug.Trace (trace)
import Common.NamePrim (nameOpen, nameEffectOpen)

type VStore = M.Map Addr AbValue
data FixInput =
  Eval ExprContext VEnv VStore KClos LocalKont (Maybe Kont) (Maybe MetaKont)
  | Cont LocalKont (Maybe Kont) (Maybe MetaKont) AChange VStore KClos
  | KStoreGet ExactContext
  | CStoreGet MetaKont
  | Pop LocalKont (Maybe Kont)
  | NoTop LocalKont (Maybe Kont)
  deriving (Eq, Ord)

data FixOutput a =
  A AbValue
  | K (S.Set (LocalKont, Maybe Kont))
  | C (S.Set (LocalKont, Maybe Kont, Maybe MetaKont))
  | B (S.Set Bool)
  | Bottom
  deriving (Eq, Ord)

data FixChange =
  AC AChange
  | KC LocalKont (Maybe Kont)
  | CC LocalKont (Maybe Kont) (Maybe MetaKont)
  | BC Bool
  | ChangeBottom
  deriving (Eq, Ord)

type FixAACR r s e a = FixAR r s e FixInput FixOutput FixChange a
type FixAAC r s e = FixAACR r s e (FixOutput FixChange)
type PostFixAACR r s e a = PostFixAR r s e FixInput FixOutput FixChange a
type PostFixAAC r s e = PostFixAACR r s e (FixOutput FixChange)

data Frame =
  End
  | AppL [AChange] ExprContext Int Int VEnv
  | AppR [AChange]
  | LetL ExprContext VEnv
  deriving (Eq, Ord, Show)
type LocalKont = [Frame]

type ApproxContext = (ExprContext, VEnv, Addr)
type ExactContext = (ExprContext, VEnv, VStore, KClos)
data Kont =
  MPrecise ExactContext
  | MApprox ApproxContext
  deriving (Eq, Ord, Show)

data KontA =
  KApprox LocalKont ApproxContext
  | KExact LocalKont
  deriving (Eq, Ord, Show)

type KClos = M.Map Addr (S.Set VStore)
data MetaKont =
  MReset ExprContext VEnv VStore KClos
  | MApply KontA AChange VStore KClos
  deriving (Eq, Ord, Show)


eachValue :: (Ord i, Show d, Show (l d), Lattice l d) => AbValue -> FixT e s i l d AChange
eachValue ab = each $ map return (changes ab)

storeUpdate :: VStore -> [Int] -> [AChange] -> VStore
storeUpdate store [] [] = store
storeUpdate store (i:is) (v:vs) =
  let updated = M.alter (\oldv -> case oldv of {Nothing -> Just (addChange emptyAbValue v); Just ab -> Just (addChange ab v)}) i store
  in storeUpdate updated is vs

limitEnv :: VEnv -> S.Set TName -> VEnv
limitEnv env fvs = M.filterWithKey (\k _ -> k `S.member` S.map getName fvs) env

extendEnv :: VEnv -> [TName] -> [Int] -> VEnv
extendEnv env args addrs = M.union (M.fromList $ zip (map getName args) addrs) env -- Left biased will take the new

doStep :: FixInput -> FixAACR r s e FixChange
doStep i = do
  memo i $ do
    trace ("Step: " ++ show i) $ return ()
    case i of
      Eval expr env store xclos local kont meta ->
        case exprOfCtx expr of
          Var x _ -> do -- TODO: Eval top defs to a closure?
            let addr  = env M.! getName x
                value = store M.! addr
            v <- eachValue value
            doStep $ Cont local kont meta v store xclos
          App (TypeApp (Var name _) _) args _ | nameEffectOpen == getName name -> do
            f <- focusChild 1 expr
            doStep $ Eval f env store xclos local kont meta
          App f args _ -> do
            f <- focusChild 0 expr
            doStep $ Eval f env store xclos (AppL [] expr 0 (length args) env : local) kont meta
          Lam args eff body -> do
            doStep $ Cont local kont meta (AChangeClos expr env) store xclos
          _ -> doBottom
      Cont [] Nothing Nothing achange store xclos -> return $ AC achange
      Cont [] kont meta achange store xclos -> do
        -- Need no-top?
        doBottom
      Cont lc kont meta achange store xclos -> do
        KC l k <- doStep (Pop lc kont)
        case l of
          AppL chs e n t p:ls -> do
            arge <- focusChild (n + 1) e -- TODO: Assert the first value is a function
            if n == t - 1 then doStep (Eval arge p store xclos (AppR (achange:chs):ls) k meta)
            else doStep (Eval arge p store xclos (AppL (achange:chs) e (n + 1 ) t p:ls) k meta)
          (AppR (AChangeClos clos env:argvs)):ls -> do
            -- TODO: Alloc & GC
            body <- focusBody clos
            let args = lamArgNames clos
                free = fvs clos
                addrs = [0..(length argvs - 1)]
            doStep (Eval body (extendEnv (limitEnv env free) args addrs) (storeUpdate store addrs argvs) xclos [] k meta)
      KStoreGet ctx -> doBottom
      CStoreGet meta -> doBottom
      Pop (l:ls) kont -> return $ KC (l:ls) kont
      Pop [] Nothing -> return $ KC [] Nothing
      Pop [] (Just (MPrecise ctx)) -> do
        KC l k <- doStep (KStoreGet ctx)
        doStep (Pop l k)
      -- Pop [] (Just approx@KApprox ctx) = do
      --   precise <- forT ctx
      --   doStep (Pop l k)
      NoTop [] Nothing -> return $ BC True
      NoTop (l:ls) k -> return $ BC False
      NoTop [] k -> do
        KC l k <- doStep (Pop [] k)
        doStep (NoTop l k) -- TODO: can we assume no new values get added & get a set and use (or)

approximate :: Addr -> KClos -> LocalKont -> Maybe Kont -> (KClos, KontA)
approximate a x l Nothing = (x, KExact l)
approximate a x l (Just (MPrecise (f, v, st, x1))) = ((x `unionK` x1) `unionK` M.singleton a (S.singleton st), KApprox l (f, v, a))
approximate a x l (Just (MApprox (f, v, b))) = let Just !xx = M.lookup b x in (x, KApprox l (f, v, a))

unionK :: KClos -> KClos -> KClos
unionK = M.unionWith S.union

addKont :: ExactContext -> LocalKont -> Maybe Kont -> FixAACR r s e ()
addKont c lk mk = lift $ push (KStoreGet c) (KC lk mk)

addMetaKont :: MetaKont -> LocalKont -> Maybe Kont -> Maybe MetaKont -> FixAACR r s e ()
addMetaKont c lk mk mmk = lift $ push (CStoreGet c) (CC lk mk mmk)

-- forKont :: KClos -> ExprContext -> VEnv -> Addr -> FixAACR r s e ExactContext
-- forKont kclos expr venv a = do
--   let store = kclos M.! a
--   doStep (KStoreGet )
-- Actually need to introspect the full KStore....

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
  show (Eval expr env store kclos local kont meta) = "Eval " ++ showSimpleContext expr
  show (Cont local kont meta achange store kclos) = "Cont"

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
  lte (AC x) Bottom = False
  lte (CC l k c) (C y) = (l, k, c) `S.member` y
  lte (KC l k) (K y) = (l, k) `S.member` y
  lte (AC x) (A y) = x `changeIn` y
  lte (BC x) (B y) = x `elem` y
  elems (A a) = map AC $ changes a
  elems (K x) = map (uncurry KC) $ S.toList x
  elems (C x) = map (\(l,k,c) -> CC l k c) $ S.toList x
  elems (B x) = map BC $ S.toList x
  elems Bottom = []



