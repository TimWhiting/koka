{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE TypeSynonymInstances #-}
module Core.FlowAnalysis.Full.DMCFAR.Monad where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad.Reader (lift)
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.Full.DMCFAR.AbstractValue
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
  CEval ExprContext Addr Addr CombinedCtx
  | CApply Addr Addr Addr DynamicCtx
  | CUnwind Name Name ExprContext Addr Addr [Addr] CombinedCtx
  | CDone
  deriving (Eq, Ord, Show)

mLimit :: FixAAMR r s e Int
mLimit = contextLength <$> getEnv

dLimit :: FixAAMR r s e Int
dLimit = delimContextLength <$> getEnv

startCombinedCtx = do 
  m <- mLimit
  d <- dLimit 
  return $ CombinedCtx S.empty (take m startStaticCtx) (take d startDynCtx)

inject :: ExprContext -> FixAAMR r s e FixInput
inject ctx = do
  c <- startCombinedCtx
  return $ Step (CEval ctx EndKAddr EndMKAddr c)

data FixInput =
  Step Conf
  | VStore Addr
  | KStore Addr
  | MKStore Addr
  deriving (Eq, Ord, Show)

data FixOutput a =
  Next (S.Set Conf)
  | SValue AbValue
  | KValue (S.Set Kont)
  | MKValue (S.Set MKont)
  | Bottom
  deriving (Eq, Ord, Show)

data FixChange =
  N Conf
  | SV AChange
  | KV Kont
  | MKV MKont 
  | ChangeBottom
  deriving (Eq, Ord, Show)

type FixAAMR r s e a = FixAR r s e FixInput FixOutput FixChange a
type FixAAM r s e = FixAAMR r s e (FixOutput FixChange)
type PostFixAAMR r s e a = PostFixAR r s e FixInput FixOutput FixChange a
type PostFixAAM r s e = PostFixAAMR r s e (FixOutput FixChange)

mapChange :: (c, n) -> (c -> d) -> (n -> m) -> (d, m)
mapChange (c, n) f g = (f c, g n)

instance Lattice FixOutput FixChange where
  bottom = Bottom
  isBottom Bottom = True
  isBottom _ = False
  insert ChangeBottom a = (ChangeBottom, a)
  insert (N conf) Bottom = (N conf, Next $ S.singleton conf)
  insert (N conf) (Next confs) = (N conf, Next $ S.insert conf confs)
  insert (SV change) Bottom = mapChange (addChange emptyAbValue change) SV SValue
  insert (SV change) (SValue av) = mapChange (addChange av change) SV SValue
  insert (KV kont) Bottom = (KV kont, KValue $ S.singleton kont)
  insert (KV kont) (KValue konts) = (KV kont, KValue $ S.insert kont konts)
  insert (MKV mKont) Bottom = (MKV mKont, MKValue $ S.singleton mKont)
  insert (MKV mKont) (MKValue mKonts) = (MKV mKont, MKValue $ S.insert mKont mKonts)
  insert v a = error ("insert: unexpected case " ++ show v ++ " " ++ show a)
  lte ChangeBottom _ = True
  lte _ Bottom = False
  lte (N conf) (Next confs) = S.member conf confs
  lte (SV change) (SValue av) = change `changeIn` av
  lte (KV kont) (KValue konts) = S.member kont konts
  lte (MKV mKont) (MKValue mKonts) = S.member mKont mKonts
  elems (SValue a) = map SV $ changes a
  elems (KValue ks) = map KV $ S.toList ks
  elems (MKValue mks) = map MKV $ S.toList mks
  elems (Next confs) = map N $ S.toList confs
  elems Bottom = []