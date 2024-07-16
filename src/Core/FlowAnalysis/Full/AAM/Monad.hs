{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Core.FlowAnalysis.Full.AAM.Monad where
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
import Type.Type (splitFunType, typeAny, Effect)
import Control.Monad (foldM)
import GHC.Base (when, VecCount)
import Core.CoreVar (HasExpVar(fv), bv)
import Lib.PPrint (vcat, text, Pretty(..), hcat, Doc, indent)
import Type.Pretty (defaultEnv, ppType)

type KStore = (M.Map KAddr (S.Set ([Frame], KAddr)), M.Map MKAddr (S.Set ([Frame], KAddr, MKAddr)))

data FixInput =
  Eval ExprContext VEnv VStore KStore [Frame] KAddr MKAddr Time
  | Cont AChange VStore KStore [Frame] KAddr MKAddr Time
  deriving (Eq, Ord)

data FixOutput a =
  A AbValue
  | Bottom
  deriving (Eq, Ord)

data FixChange =
  AC AChange
  | ChangeBottom
  deriving (Eq, Ord)

type FixAAMR r s e a = FixAR r s e FixInput FixOutput FixChange a
type FixAAM r s e = FixAAMR r s e (FixOutput FixChange)
type PostFixAAMR r s e a = PostFixAR r s e FixInput FixOutput FixChange a
type PostFixAAM r s e = PostFixAAMR r s e (FixOutput FixChange)

kstoreExtend :: KAddr -> [Frame] -> KAddr -> KStore -> KStore
kstoreExtend k frames addr (kstore, mkstore) =
  case M.lookup k kstore of
    Just oldFrames -> (M.insert k (S.insert (frames, addr) oldFrames) kstore, mkstore)
    Nothing -> (M.insert k (S.singleton (frames, addr)) kstore, mkstore)

mkstoreExtend :: MKAddr -> [Frame] -> KAddr -> MKAddr -> KStore -> KStore
mkstoreExtend mk fr k mknext (kstore, mkstore) =
  case M.lookup mk mkstore of
    Just oldKs -> (kstore, M.insert mk (S.insert (fr, k, mknext) oldKs) mkstore)
    Nothing -> (kstore, M.insert mk (S.singleton (fr, k, mknext)) mkstore)

data Frame =
  EndProgram
  | EndCall
  | EndHandle
  | KResume
  | AppL Int ExprContext VEnv -- Length of args and parent expression
  | AppM AChange [Addr] ExprContext Int Int VEnv -- This environment is the one in which the args are evaluated
  | AppR AChange [Addr] ExprContext
  | HandleL [AChange] Effect ExprContext VEnv -- The handle expression (changes are the tag, the handler object, the return closure, and the action closure)
  | HandleR [AChange] Effect ExprContext VEnv -- The handle expression (changes are the tag, the handler object, the return closure, and the action closure)
  | OpL ExprContext VEnv Int Effect
  | OpL1 ExprContext VEnv Int Effect
  | OpL2 ExprContext VEnv Int AChange [AChange] Effect
  | Shift0k AChange VEnv Int Effect -- selector 
  | Shift0h AChange VEnv Int Effect
  | Shift0Select AChange VEnv Int Effect
  | Shift0Fn AChange VEnv
  | OpR ExprContext [AChange] Effect ([Frame], KAddr, MKAddr)
  | LetL Int Int Int Int [Addr] ExprContext VEnv -- Binding group index, num binding groups, binding index, num bindings, addresses for binding group, parent expresion, parent env
  | CaseR ExprContext VEnv
  deriving (Eq, Ord)

data AnyAddr =
  VA Addr
  | KA KAddr
  deriving (Eq, Ord)

llEnv :: VEnv -> S.Set AnyAddr
llEnv env = S.fromList $ map VA $ M.elems env

llFrame :: KStore -> S.Set KAddr -> Frame -> S.Set AnyAddr
llFrame kstore seen f =
  case f of
    EndProgram -> S.empty
    EndCall -> S.empty
    EndHandle -> S.empty
    KResume -> S.empty
    CaseR _ env -> llEnv env
    AppL _ _ env -> llEnv env
    AppR v addrs _ -> S.union (llV kstore seen v) (S.fromList $ map VA addrs)
    AppM v addrs _ _ _ env -> S.unions [llEnv env, S.fromList $ map VA addrs, llV kstore seen v]
    LetL _ _ _ _ addrs _ env -> S.union (llEnv env) (S.fromList $ map VA addrs)
    HandleL changes ef e env -> S.unions (llEnv env:map (llV kstore seen) changes)
    HandleR changes ef e env -> S.unions (llEnv env:map (llV kstore seen) changes)
    OpR expr changes eff (ll, k, mk) -> S.unions (map (llV kstore seen) changes ++ [llKont k kstore seen, llLKont ll kstore (S.insert k seen)])
    OpL expr env n eff -> llEnv env
    OpL1 expr env n eff -> S.unions [llEnv env]
    OpL2 expr env n ch changes eff -> S.unions $ llV kstore seen ch : llEnv env : map (llV kstore seen) changes

llV :: KStore -> S.Set KAddr -> AChange -> S.Set AnyAddr
llV kstore seen achange  =
  case achange of
    AChangeClos _ env -> llEnv env
    AChangePrim _ _ env -> llEnv env
    AChangeOp _ _ env -> llEnv env
    AChangeKont k mk -> S.insert (KA k) $ llKont k kstore seen
    AChangeConstr _ env -> llEnv env
    AChangeLit _ -> S.empty

llAbValue :: KStore -> S.Set KAddr -> AbValue -> S.Set AnyAddr
llAbValue kstore seen ab = S.unions $ map (llV kstore seen) $ changes ab

llA :: Addr -> VStore -> KStore -> S.Set KAddr -> S.Set AnyAddr
llA a store kstore seen = maybe S.empty (llAbValue kstore seen) (M.lookup a store)

llKont :: KAddr -> KStore -> S.Set KAddr -> S.Set AnyAddr
llKont kaddr store konts =
  if S.member kaddr konts then
    S.empty
  else
    case M.lookup kaddr (fst store) of
      Just rest -> S.insert (KA kaddr) $ S.unions $ 
        map (\(ll, k) -> 
          let konts' = S.union (S.fromList [kaddr, k]) konts in 
            llLKont ll store konts' `S.union` llKont k store (S.insert kaddr konts)) 
           (S.toList rest)
      Nothing -> S.empty

llLKont :: [Frame] -> KStore -> S.Set KAddr -> S.Set AnyAddr
llLKont kont store konts = S.unions $ map (llFrame store konts) kont

liveAddrs :: KStore -> VStore -> S.Set AnyAddr -> S.Set AnyAddr
liveAddrs kstore store frontier =
  recur frontier S.empty
  where
    recur :: S.Set AnyAddr -> S.Set AnyAddr -> S.Set AnyAddr
    recur left marked =
          if null left then marked
          else
            let (next, nextLeft) = S.deleteFindMin left
                newMarked = S.insert next marked
                newFrontier = case next of
                  VA a -> S.union (llA a store kstore S.empty) nextLeft `S.difference` newMarked
                  KA a -> S.union (llKont a kstore S.empty) nextLeft `S.difference` newMarked
            in recur newFrontier newMarked

vaddrs :: S.Set AnyAddr -> S.Set Addr
vaddrs = S.map (\(VA a) -> a) . S.filter (\a -> case a of {(VA _) -> True; _ -> False})

kaddrs :: S.Set AnyAddr -> S.Set KAddr
kaddrs = S.map (\(KA a) -> a) . S.filter (\a -> case a of {(KA _) -> True; _ -> False})

limitKStore :: KStore -> S.Set KAddr -> KStore
limitKStore (kstore, mkstore) live = (M.filterWithKey (\k _ -> k `S.member` live) kstore, mkstore)

limitMKStore :: KStore -> S.Set MKAddr -> KStore
limitMKStore (kstore, mkstore) live = (kstore, M.filterWithKey (\k _ -> k `S.member` live) mkstore)

gc :: FixInput -> FixAAMR r s e FixInput
gc (Eval e env store kstore lkont kont mkont ktime) = do
  -- trace ("\n\nGC:\n" ++ showSimpleContext e ++ "\n") $ return ()
  let env' = limitEnv env (fv (exprOfCtx e))
      live = liveAddrs kstore store (S.unions [llEnv env', llLKont lkont kstore S.empty, llKont kont kstore S.empty])
      store' = limitStore store (vaddrs live)
      kstore' = limitKStore kstore (kaddrs live)
  -- trace ("GC Env:\n" ++ show (pretty env) ++ "\n=>\n" ++ show (pretty env) ++ "\n") $ return ()\
  -- trace ("GC LocalAddrs:\n" ++ show laddrs ++ "\n") $ return ()
  -- trace ("GC KontAddrs:\n" ++ show kaddrs ++ show kont ++ "\n") $ return ()
  -- trace ("GC Store:\n" ++ show (pretty store) ++ "\n=>\n" ++ show (pretty store') ++ "\n") $ return ()
  return $ Eval e env' store' kstore lkont kont mkont ktime
gc (Cont achange store kstore lkont kont mkont ktime) = do
  let live = liveAddrs kstore store (S.unions [llV kstore S.empty achange, llLKont lkont kstore S.empty, llKont kont kstore S.empty])
      store' = limitStore store (vaddrs live)
      kstore' = limitKStore kstore (kaddrs live)
  -- trace ("GC KontAddrs:\n" ++ show kaddrs ++ show kont ++ "\n") $ return ()
  -- trace ("GC Store:\n" ++ show (pretty store) ++ "\n=>\n" ++ show (pretty store') ++ "\n") $ return ()
  return $ Cont achange store' kstore' lkont kont mkont ktime

instance Show (FixOutput a) where
  show (A x) = show x
  show Bottom = "Bottom"

instance Show FixChange where
  show (AC x) = show x
  show ChangeBottom = "Bottom"

instance Show Frame where
  show EndProgram = "EndProgram"
  show EndCall = "EndCall"
  show EndHandle = "EndHandle"
  show KResume = "KResume "
  show (AppL nargs e p) = "AppL " ++ showSimpleContext e ++ " nargs: " ++ show nargs
  show (AppM ch chs e n t p) = "AppM " ++ show ch ++ " arg: " ++ show n
  show (AppR ch chs _) = "AppR " ++ show ch
  show (OpL expr env n eff) = "Op " ++ show (ppType defaultEnv eff)
  show (OpL1 expr env n eff) = "Op1L " ++ show n ++ " " ++ show (ppType defaultEnv eff)
  show (OpL2 expr env n ch changes eff) = "Op2L " ++ show (length changes) ++ " " ++ show n ++ " " ++ show (ppType defaultEnv eff)
  show (OpR expr changes eff (l,k,m)) = "OpR " ++ show changes
  show (HandleL changes ef e p) = "HandleL " ++ show (vcat $ map (text . show) changes) ++ showSimpleContext e
  show (HandleR changes ef e p) = "HandleL " ++ show (vcat $ map (text . show) changes) ++ showSimpleContext e
  show (CaseR e p) = "CaseR " ++ showSimpleContext e
  show (LetL bgi bgn bi bn addrs e p) = "LetL " ++ show bgi ++ " " ++ show bgn ++ " " ++ show bi ++ " " ++ show bn ++ " " ++ showSimpleContext e ++ " "

instance Show FixInput where
  show (Eval expr env store kstore lkont kont mkont ktime) = show $ vcat
    [text $ "Eval " ++ show ktime,
     indent 2 (vcat [vcat (map (text . show) (reverse lkont)), text $ show kont, text $ show mkont, pretty store, text " ",
     text (showSimpleContext expr), pretty env, text " ", text " "])]
  show (Cont achange store kstore lkont kont mkont ktime) = show $ vcat
    [text $ "Cont " ++ show ktime,
     indent 2 (vcat [vcat (map (text . show) (reverse lkont)), text $ show kont, text $ show mkont, pretty store, text " ",
     text (show achange), text " ", text " "])]

instance Lattice FixOutput FixChange where
  bottom = Bottom
  isBottom Bottom = True
  isBottom _ = False
  insert (AC a) Bottom = A $ addChange emptyAbValue a
  insert (AC a) (A x) = A $ addChange x a
  insert ChangeBottom a = a
  join Bottom Bottom = Bottom
  join Bottom x = x
  join x Bottom = x
  join (A x) (A y) = A (joinAbValue x y)
  lte ChangeBottom _ = True
  lte _ Bottom = False
  lte (AC x) (A y) = x `changeIn` y
  elems (A a) = map AC $ changes a
  elems Bottom = []