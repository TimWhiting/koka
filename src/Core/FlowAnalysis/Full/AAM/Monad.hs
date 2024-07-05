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

type KStore = M.Map KAddr (S.Set [Frame])

data FixInput =
  Eval ExprContext VEnv VStore KStore [Frame]
  | Cont AChange VStore KStore [Frame]
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

kstoreExtend :: KAddr -> [Frame] -> KStore -> KStore
kstoreExtend k frames store =
  case M.lookup k store of
    Just oldFrames -> M.insert k (S.insert frames oldFrames) store
    Nothing -> M.insert k (S.singleton frames) store

data Frame =
  EndProgram
  | EndCall KAddr
  | AppL Int ExprContext VEnv -- Length of args and parent expression
  | AppM AChange [Addr] ExprContext Int Int VEnv -- This environment is the one in which the args are evaluated
  | AppR AChange [Addr]
  | HandleL [AChange] Effect ExprContext VEnv -- The handle expression (changes are the tag, the handler object, the return closure, and the action closure)
  | HandleR [AChange] Effect ExprContext VEnv -- The handle expression (changes are the tag, the handler object, the return closure, and the action closure)
  | OpL ExprContext VEnv Int Effect KAddr
  | OpL1 ExprContext VEnv Int Effect KAddr
  | OpL2 ExprContext VEnv Int AChange [AChange] Effect KAddr
  | KResume KAddr
  | OpR [AChange] Effect KAddr
  | LetL Int Int Int Int [Addr] ExprContext VEnv -- Binding group index, num binding groups, binding index, num bindings, addresses for binding group, parent expresion, parent env
  | CaseR ExprContext VEnv
  deriving (Eq, Ord)

llEnv :: VEnv -> S.Set Addr
llEnv env = S.fromList $ M.elems env

llFrame :: KStore -> S.Set KAddr -> Frame -> S.Set Addr
llFrame kstore seen f =
  case f of 
    EndProgram -> S.empty
    EndCall kont -> llKont kont kstore seen
    KResume kont -> llKont kont kstore seen
    CaseR _ env -> llEnv env
    AppL _ _ env -> llEnv env
    AppR v addrs -> S.union (llV kstore seen v) (S.fromList addrs)
    AppM v addrs _ _ _ env -> S.unions [llEnv env, S.fromList addrs, llV kstore seen v]
    LetL _ _ _ _ addrs _ env -> S.union (llEnv env) (S.fromList addrs)
    HandleL changes ef e env -> S.unions (llEnv env:map (llV kstore seen) changes)
    HandleR changes ef e env -> S.unions (llEnv env:map (llV kstore seen) changes)
    OpR changes eff kont -> S.unions $ llKont kont kstore seen : map (llV kstore seen) changes
    OpL expr env n eff kont -> llKont kont kstore seen `S.union` llEnv env
    OpL1 expr env n eff kont -> S.unions [llKont kont kstore seen, llEnv env]
    OpL2 expr env n ch changes eff kont -> S.unions $ llKont kont kstore seen : llV kstore seen ch : llEnv env : map (llV kstore seen) changes

llV :: KStore -> S.Set KAddr -> AChange -> S.Set Addr
llV kstore seen achange  =
  case achange of
    AChangeClos _ env -> llEnv env
    AChangePrim _ _ env -> llEnv env
    AChangeOp _ _ env -> llEnv env
    AChangeKont k -> llKont k kstore seen
    AChangeConstr _ env -> llEnv env
    AChangeLit _ -> S.empty

llAbValue :: KStore -> S.Set KAddr -> AbValue -> S.Set Addr
llAbValue kstore seen ab = S.unions $ map (llV kstore seen) $ changes ab

llA :: Addr -> VStore -> KStore -> S.Set KAddr -> S.Set Addr
llA a store kstore seen = maybe S.empty (llAbValue kstore seen) (M.lookup a store)

liveAddrs :: KStore -> VStore -> S.Set Addr -> S.Set Addr
liveAddrs kstore store frontier =
  recur frontier S.empty
  where recur left marked =
          if null left then marked
          else
            let (next, nextLeft) = S.deleteFindMin left
                newMarked = S.insert next marked
                newFrontier = S.union (llA next store kstore S.empty) nextLeft `S.difference` marked in
            recur newFrontier newMarked

llKont :: KAddr -> KStore -> S.Set KAddr -> S.Set Addr
llKont kaddr store konts =
  if S.member kaddr konts then
    S.empty
  else
    case M.lookup kaddr store of
      Just frames -> S.unions $ map (llFrame store (S.insert kaddr konts)) $ concat $ S.toList frames
      Nothing -> S.empty

llLKont :: [Frame] -> KStore -> S.Set KAddr -> S.Set Addr
llLKont kont store konts = S.unions $ map (llFrame store konts) kont

gc :: FixInput -> FixAAMR r s e FixInput
gc (Eval e env store kstore kont) = do
  -- trace ("\n\nGC:\n" ++ showSimpleContext e ++ "\n") $ return ()
  let env' = limitEnv env (fv (exprOfCtx e))
  -- trace ("GC Env:\n" ++ show (pretty env) ++ "\n=>\n" ++ show (pretty env) ++ "\n") $ return ()\
  let live = liveAddrs kstore store (S.unions [llEnv env', llLKont kont kstore S.empty])
  -- trace ("GC LocalAddrs:\n" ++ show laddrs ++ "\n") $ return ()
  -- trace ("GC KontAddrs:\n" ++ show kaddrs ++ show kont ++ "\n") $ return ()
  let store' = limitStore store live
  -- trace ("GC Store:\n" ++ show (pretty store) ++ "\n=>\n" ++ show (pretty store') ++ "\n") $ return ()
  return $ Eval e env' store' kstore kont
gc (Cont achange store kstore kont) = do
  let vaddrs = llV kstore S.empty achange
  -- trace ("GC LocalAddrs:\n" ++ show laddrs ++ "\n") $ return ()
  -- trace ("GC KontAddrs:\n" ++ show kaddrs ++ show kont ++ "\n") $ return ()
  let live = liveAddrs kstore store (S.unions [vaddrs, llLKont kont kstore S.empty])
  let store' = limitStore store live
  -- trace ("GC Store:\n" ++ show (pretty store) ++ "\n=>\n" ++ show (pretty store') ++ "\n") $ return ()
  return $ Cont achange store' kstore kont

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
  show Bottom = "Bottom"

instance Show FixChange where
  show (AC x) = show x
  show ChangeBottom = "Bottom"

instance Show Frame where
  show EndProgram = "EndProgram"
  show (EndCall _) = "EndCall"
  show (AppL nargs e p) = "AppL " ++ showSimpleContext e ++ " nargs: " ++ show nargs
  show (AppM ch chs e n t p) = "AppM " ++ show ch ++ " arg: " ++ show n
  show (AppR ch chs) = "AppR " ++ show ch
  show (OpL expr env n eff r) = "Op " ++ show (ppType defaultEnv eff) ++ " " ++ show r
  show (OpL1 expr env n eff r) = "Op1L " ++ show n ++ " " ++ show (ppType defaultEnv eff) ++ " " ++ show r
  show (OpL2 expr env n ch changes eff r) = "Op2L " ++ show (length changes) ++ " " ++ show n ++ " " ++ show (ppType defaultEnv eff) ++ " " ++ show r
  show (OpR changes eff r) = "OpR " ++ show changes ++ " " ++ show r
  show (HandleL changes ef e p) = "HandleL " ++ show (vcat $ map (text . show) changes) ++ showSimpleContext e
  show (HandleR changes ef e p) = "HandleL " ++ show (vcat $ map (text . show) changes) ++ showSimpleContext e
  show (CaseR e p) = "CaseR " ++ showSimpleContext e
  show (LetL bgi bgn bi bn addrs e p) = "LetL " ++ show bgi ++ " " ++ show bgn ++ " " ++ show bi ++ " " ++ show bn ++ " " ++ showSimpleContext e ++ " "
  show (KResume k) = "KResume " ++ show k

instance Show FixInput where
  show (Eval expr env store kstore kont) = show $ vcat [text "Eval", indent 2 (vcat [text (showSimpleContext expr), pretty env, pretty store])]
  show (Cont achange store kstore kont) = show $ vcat [text "Cont", indent 2 (vcat [vcat (map (text . show) kont), text (show achange), pretty store])]

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