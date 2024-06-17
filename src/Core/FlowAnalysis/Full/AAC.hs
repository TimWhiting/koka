{-# LANGUAGE MultiParamTypeClasses #-}
module Core.FlowAnalysis.Full.AAC where
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.AbstractValue
import Core.FlowAnalysis.StaticContext

type FixInput = (ExprContextId, EnvCtx)
data FixOutput a = 
  A AbValue
  | N

data FixChange = 
  AC AChange
  | B

type FixAACR r s e a = FixAR r s e FixInput FixOutput FixChange a
type FixAAC r s e = FixAACR r s e (FixOutput FixChange)
type PostFixAACR r s e a = PostFixAR r s e FixInput FixOutput FixChange a
type PostFixAAC r s e = PostFixAACR r s e (FixOutput FixChange)

doStep :: FixInput -> FixAACR r s e FixChange
doStep i = do
  memo i $ do
    case i of
      _ -> doBottom
  
instance Show (FixOutput a) where
  show (A x) = show x

instance Show FixChange where
  show (AC x) = show x
  show B = "B"

instance Lattice FixOutput FixChange where
  bottom = N
  isBottom N = True
  isBottom _ = False
  insert (AC a) N = A $ addChange emptyAbValue a
  insert (AC a) (A x) = A $ addChange x a
  insert B a = a
  join (A x) (A y) = A (joinAbValue x y)
  join (A x) N = A x
  join N (A x) = A x
  join N N = N
  lte B _ = True
  lte (AC x) N = False
  lte (AC x) (A y) = x `changeIn` y
  elems (A a) = map AC $ changes a


    
