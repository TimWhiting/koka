{-# LANGUAGE MultiParamTypeClasses #-}
module Core.FlowAnalysis.Full.AAC where
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.AbstractValue
import Core.FlowAnalysis.StaticContext
import Core.Core
import Data.Int (Int)
import Common.Name

data FixInput =
  Eval ExprContext VEnv VStore LocalKont Kont MetaKont
  | Cont LocalKont Kont MetaKont AChange VStore
  deriving (Eq, Ord)

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

data Frame =
  End
  | AppL ExprContext VEnv
  | AppR AChange
  | LetL ExprContext VEnv
  deriving (Eq, Ord, Show)

type Addr = Int
type VStore = M.Map Addr AbValue
type VEnv = M.Map Name Addr
type KClos = M.Map Addr (S.Set Kont)
type Context = (ExprContext, VEnv, Addr)
type ExactContext = (ExprContext, VEnv, VStore, KClos)
data Kont =
  MPrecise ExactContext
  | MApprox Context
  deriving (Eq, Ord, Show)

data KontA =
  KApprox LocalKont Context
  | KExact LocalKont
  deriving (Eq, Ord, Show)

data MetaKont =
  MReset ExprContext VEnv VStore KClos
  | MApply KontA AChange VStore KClos
  deriving (Eq, Ord, Show)

type LocalKont = [Frame]
eachValue :: (Ord i, Show d, Show (l d), Lattice l d) => AbValue -> FixT e s i l d FixChange
eachValue ab = each $ map (return . AC) (changes ab)
doStep :: FixInput -> FixAACR r s e FixChange
doStep i = do
  memo i $ do
    case i of
      Eval expr env store local kont meta ->
        case exprOfCtx expr of
          Var x _ ->
            let addr = env M.! getName x
                value = store M.! addr 
            in eachValue value
          _ -> doBottom
      Cont local kont meta achange store -> doBottom

instance Show (FixOutput a) where
  show (A x) = show x

instance Show FixChange where
  show (AC x) = show x
  show B = "B"

instance Show FixInput where
  show (Eval expr env store local kont meta) = "Eval"
  show (Cont local kont meta achange store) = "Cont"

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



