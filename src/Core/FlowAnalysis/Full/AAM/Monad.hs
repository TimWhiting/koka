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
import Type.Type (splitFunType, typeAny)
import Control.Monad (foldM)
import GHC.Base (when)
import Core.CoreVar (HasExpVar(fv), bv)
import Lib.PPrint (vcat, text, Pretty(..), hcat, Doc, indent)

type KStore = M.Map Kont (S.Set [Frame])

data FixInput =
  Eval ExprContext VEnv VStore KStore [Frame]
  | Cont AChange VEnv VStore KStore [Frame]
  deriving (Eq, Ord)

newtype Kont = Kont (ExprContext, VEnv) deriving (Eq, Ord, Show)

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

kstoreExtend :: Kont -> [Frame] -> KStore -> KStore
kstoreExtend k frames store =
  case M.lookup k store of
    Just oldFrames -> M.insert k (S.insert frames oldFrames) store
    Nothing -> M.insert k (S.singleton frames) store

data Frame =
  EndProgram
  | EndCall Kont
  | AppL Int ExprContext VEnv -- Length of args and parent expression
  | AppM AChange [Addr] ExprContext Int Int VEnv -- This environment is the one in which the args are evaluated
  | AppR AChange [Addr]
  | LetL Int Int Int Int [Addr] ExprContext VEnv -- Binding group index, num binding groups, binding index, num bindings, addresses for binding group, parent expresion, parent env
  | CaseR ExprContext VEnv
  deriving (Eq, Ord)

llEnv :: VEnv -> S.Set Addr
llEnv env = S.fromList $ M.elems env

llFrame :: Frame -> KStore -> S.Set Addr
llFrame EndProgram store = S.empty
llFrame (EndCall kont) store = llKont kont store
llFrame (AppL _ _ env) store = llEnv env
llFrame (AppM v addrs _ _ _ env) store = S.unions [llEnv env, S.fromList addrs, llV v]
llFrame (AppR v addrs) store = S.union (llV v) (S.fromList addrs)
llFrame (LetL _ _ _ _ addrs _ env) store = S.union (llEnv env) (S.fromList addrs)
llFrame (CaseR _ env) store = llEnv env

llV :: AChange -> S.Set Addr
llV achange =
  case achange of
    AChangeClos _ env -> llEnv env
    AChangePrim _ _ env -> llEnv env
    AChangeClosApp _ _ env -> llEnv env
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

llKont :: Kont -> KStore -> S.Set Addr
llKont kaddr store = 
  case M.lookup kaddr store of
    Just frames -> S.unions $ map (\f -> llFrame f store) $ concat $ S.toList frames
    Nothing -> S.empty

llLKont :: [Frame] -> KStore -> S.Set Addr
llLKont kont store = S.unions $ map (\f -> llFrame f store) kont

gc :: FixInput -> FixAAMR r s e FixInput
gc (Eval e env store kstore kont) = do
  -- trace ("\n\nGC:\n" ++ showSimpleContext e ++ "\n") $ return ()
  let env' = limitEnv env (fv (exprOfCtx e))
  -- trace ("GC Env:\n" ++ show (pretty env) ++ "\n=>\n" ++ show (pretty env) ++ "\n") $ return ()\
  let live = liveAddrs store (S.unions [llEnv env', llLKont kont kstore])
  -- trace ("GC LocalAddrs:\n" ++ show laddrs ++ "\n") $ return ()
  -- trace ("GC KontAddrs:\n" ++ show kaddrs ++ show kont ++ "\n") $ return ()
  let store' = limitStore store live
  -- trace ("GC Store:\n" ++ show (pretty store) ++ "\n=>\n" ++ show (pretty store') ++ "\n") $ return ()
  return $ Eval e env' store' kstore kont
gc (Cont achange env store kstore kont) = do
  let vaddrs = llV achange
  -- trace ("GC LocalAddrs:\n" ++ show laddrs ++ "\n") $ return ()
  -- trace ("GC KontAddrs:\n" ++ show kaddrs ++ show kont ++ "\n") $ return ()
  let live = liveAddrs store (S.unions [vaddrs, llEnv env, llLKont kont kstore])
  let store' = limitStore store live
  -- trace ("GC Store:\n" ++ show (pretty store) ++ "\n=>\n" ++ show (pretty store') ++ "\n") $ return ()
  return $ Cont achange env store' kstore kont 

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
  show (CaseR e p) = "CaseR " ++ showSimpleContext e
  show (LetL bgi bgn bi bn addrs e p) = "LetL " ++ show bgi ++ " " ++ show bgn ++ " " ++ show bi ++ " " ++ show bn ++ " " ++ showSimpleContext e ++ " "

instance Show FixInput where
  show (Eval expr env store kstore kont) = show $ vcat [text "Eval", indent 2 (vcat [text (showSimpleContext expr), pretty env, pretty store])]
  show (Cont achange env store kstore kont) = show $ vcat [text "Cont", indent 2 (vcat [text (show kont), text (show achange), pretty store])]

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