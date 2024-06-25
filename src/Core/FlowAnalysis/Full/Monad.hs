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
  | AppL Int ExprContext VEnv -- Length of args and parent expression
  | AppM AChange [Addr] ExprContext Int Int VEnv -- This environment is the one in which the args are evaluated
  | AppR AChange [Addr]
  | LetL Int Int Int Int [Addr] ExprContext VEnv -- Binding group index, num binding groups, binding index, num bindings, addresses for binding group, parent expresion, parent env
  | CaseR ExprContext VEnv
  deriving (Eq, Ord)

instance Show Frame where
  show End = "End"
  show (AppL nargs e p) = "AppL " ++ show nargs ++ " " ++ showSimpleEnv p
  show (AppM ch chs e n t p) = "AppL " ++ show n ++ " " ++ show t
  show (AppR ch chs) = "AppR " ++ show ch ++ " " ++ show chs
  show (CaseR e p) = "CaseR"
  show (LetL bgi bgn bi bn addrs e p) = "LetL " ++ show bgi ++ " " ++ show bgn ++ " " ++ show bi ++ " " ++ show bn ++ " " ++ showSimpleContext e ++ " " ++ showSimpleEnv p

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


storeLookup :: HasCallStack => TName -> VEnv -> VStore -> FixAACR r s e AChange
storeLookup x env store = do
  case M.lookup x env of
    Just addr -> do
      let value = store M.! addr
      eachValue value
    Nothing -> do
      mdef <- bindExternal x
      case mdef of
        Nothing -> doBottom
        Just def -> do
          lam <- focusChild 0 def
          return $ AChangeClos lam M.empty


tnamesCons :: Int -> [TName]
tnamesCons n = map (\i -> TName (newName ("con" ++ show i)) typeAny Nothing) [0..n]

eachValue :: (Ord i, Show d, Show (l d), Lattice l d) => AbValue -> FixT e s i l d AChange
eachValue ab = each $ map return (changes ab)

extendStore :: VStore -> (TName,Int) -> AChange -> VStore
extendStore store i v =
  M.alter (\oldv -> case oldv of {Nothing -> Just (addChange emptyAbValue v); Just ab -> Just (addChange ab v)}) i store

limitEnv :: VEnv -> S.Set TName -> VEnv
limitEnv env fvs = M.filterWithKey (\k _ -> k `S.member` fvs) env

extendEnv :: VEnv -> [TName] -> [(TName,Int)] -> VEnv
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