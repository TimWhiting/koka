module Interpreter.AbstractMachine (interpMain) where
import Core.Core
import Data.Map.Strict as M
import Common.Name
import Kind.Constructors (ConInfo)
import Compile.Module
import Compile.BuildContext (BuildContext (buildcModules))
import Compile.BuildMonad (buildcLookupModule)
import Data.Maybe (fromJust)
import Core.FlowAnalysis.StaticContext
import Debug.Trace

newtype Marker = Mark Int deriving (Show)

data Ev = Ev Env Handler Marker Evv deriving (Show)

data Handler = Handler {
  label:: Label,
  ops:: M.Map OpName Expr,
  ret:: Expr
} deriving (Show)
type Evv = [Ev]
type Kont = [KontFrame]
type PureKont = [PureKontFrame]
type Env = M.Map Var Val
type Var = Name
type Label = String
type OpName = Name

data Val =
  VLit Lit
  | VCon ConInfo [Val]
  | VFun Expr Env
  | VKont Kont
  deriving (Show)

data State =
  Eval Expr Env Kont Evv
  | Apply Kont Val Evv
  | FindPrompt Kont Marker OpName Val Kont
  | ApplyKont Kont Val Kont Evv
  | Halt Val
  deriving (Show)

data KontFrame = KF PureKont KontDelim deriving (Show)
data KontDelim = KHnd Ev | KMask Label deriving (Show)

data PureKontFrame =
  FLet Env Var Expr
  | FApp [Val] [Expr]
  | FOp OpName [Val] [Expr]
  deriving (Show)

interpMain :: BuildContext -> Name -> IO Val
interpMain ctx exprName =
  case buildcLookupModule (qualifier exprName) ctx of
    Just m ->
      case lookupModDef exprName (fromJust $ modCore m) of
        Just e -> do
          res <- interpExpr (buildcModules ctx) (lamBody e)
          trace (show res) $ return res

lamBody :: Expr -> Expr
lamBody (Lam _ _ e) = lamBody e
lamBody (TypeLam _ e) = lamBody e
lamBody (TypeApp e _) = lamBody e
lamBody e = e

lookupModDef :: Name -> Core -> Maybe Expr
lookupModDef name core = lookupDG (coreProgDefs core)
  where
    lookupDG [] = Nothing
    lookupDG (df:dgs) =
      case df of 
        DefRec dfs -> 
          case lookupD dfs of
            Just e -> Just e
            Nothing -> lookupDG dgs
        DefNonRec d -> if defName d == name then Just (defExpr d) else lookupDG dgs
    lookupD [] = Nothing
    lookupD (d:ds) = if defName d == name then Just (defExpr d) else lookupD ds

interpExpr :: Modules -> Expr -> IO Val
interpExpr modules e = do
  trace (show e) $ return ()
  let start = Eval e M.empty [] []
      loop :: State -> IO Val
      loop state = do
        res <- interpret modules state 
        case res of
          Halt v -> return v
          res -> loop res
  loop start

interpret :: Modules -> State -> IO State
interpret modules s =
  case s of
    Eval e@Lam{} env k evv -> return $ Apply k (VFun e env) evv
    Eval e@(Lit l) env k evv -> return $ Apply k (VLit l) evv
    -- TODO: Open call next
    Apply [] v evv -> return $ Halt v
    x -> error $ "interpret: " ++ show x
