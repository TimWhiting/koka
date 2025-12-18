{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Core.FlowAnalysis.Full.DMCFA.Monad where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Reader (lift)
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.Full.DMCFA.AbstractValue
import Core.FlowAnalysis.Literals
import Core.Core
import Data.Int (Int)
import Common.Name
import Debug.Trace (trace)
import Common.NamePrim (nameOpen, nameEffectOpen)
import Data.Maybe (fromJust)
import Compile.Module (Module(..))
import Common.Failure (HasCallStack)
import Type.Type (splitFunType, typeAny, Effect, typeUnit)
import Control.Monad (foldM)
import GHC.Base (when, VecCount)
import Core.CoreVar (HasExpVar(fv), bv)
import Lib.PPrint (vcat, text, Pretty(..), hcat, Doc, indent)
import Type.Pretty (defaultEnv, ppType)

data Conf =
  CEval ExprContext VEnv CombinedCtx -- expr, env, ctx
  | CApply Addr Addr DynamicCtx -- kont, vaddr, dynctx
  | CDone
  deriving (Eq, Ord, Show)

mLimit :: FixAAMR r s e Int
mLimit = contextLength <$> getEnv

dLimit :: FixAAMR r s e Int
dLimit = delimContextLength <$> getEnv
startCombinedCtx = do
  m <- mLimit
  d <- dLimit
  return $ CombinedCtx (TKTop $ take m startStaticCtx) (take d startDynCtx)

inject :: ExprContext -> FixAAMR r s e FixInput
inject ctx = do
  c <- startCombinedCtx
  return $ Step (CEval ctx M.empty c)

data FixInput =
  Step Conf
  | VStore Addr
  | KStore Addr
  deriving (Eq, Ord, Show)

data RValue = 
  RVAddr Addr 
  | ROp 
  deriving (Eq, Ord, Show)

data FixOutput =
  RValue (S.Set RValue)
  | SValue AbValue
  | KValue (S.Set Kont)
  | Bottom
  deriving (Eq, Ord, Show)

data FixChange =
  RV RValue
  | SV AChange
  | KV Kont
  | ChangeBottom
  deriving (Eq, Ord, Show)

type FixAAMR r s e a = FixAR r s e FixInput FixOutput FixChange a
type FixAAM r s e = FixAAMR r s e FixOutput
type PostFixAAMR r s e a = PostFixAR r s e FixInput FixOutput FixChange a
type PostFixAAM r s e = PostFixAAMR r s e FixOutput

mapChange :: (c, n) -> (c -> d) -> (n -> m) -> (d, m)
mapChange (c, n) f g = (f c, g n)

instance Lattice FixOutput FixChange where
  bottom = Bottom
  isBottom Bottom = True
  isBottom _ = False
  insert ChangeBottom a = (ChangeBottom, a)
  insert (RV v) Bottom = (RV v, RValue (S.singleton v))
  insert (RV v) (RValue vs) = (RV v, RValue (S.insert v vs))
  insert (SV change) Bottom = mapChange (addChange emptyAbValue change) SV SValue
  insert (SV change) (SValue sv) = mapChange (addChange sv change) SV SValue
  insert (KV kont) Bottom = (KV kont, KValue $ S.singleton kont)
  insert (KV kont) (KValue konts) = (KV kont, KValue $ S.insert kont konts)
  insert v a = error ("insert: unexpected case " ++ show v ++ " " ++ show a)
  lte ChangeBottom _ = True
  lte _ Bottom = False
  lte (RV v) (RValue vs) = S.member v vs
  lte (SV change) (SValue sv) = change `changeIn` sv
  lte (KV kont) (KValue konts) = S.member kont konts
  elems (SValue a) = map SV $ changes a
  elems (KValue ks) = map KV $ S.toList ks
  elems (RValue rs) = map RV $ S.toList rs
  elems Bottom = []