module Interpreter.AbstractMachine (interpMain) where
import Core.Core
import Data.Map.Strict as M hiding (map)
import Common.Name
import Kind.Constructors (ConInfo)
import Compile.Module
import Compile.BuildContext (BuildContext (buildcModules))
import Compile.BuildMonad (buildcLookupModule)
import Data.Maybe (fromJust)
import Core.FlowAnalysis.StaticContext
import Debug.Trace
import Common.NamePrim (nameEffectOpen, nameUnit, nameUnsafeTotal)
import Type.Type (typeUnit)

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
type Var = TName
type Label = String
type OpName = TName

data Val =
  VLit Lit
  | VCon TName [Val]
  | VConI TName
  | VFun Expr Env
  | VKont Kont
  | VNamed Ev
  | VPrim Name
  deriving (Show)

data State =
  Eval Expr Env Kont Evv
  | Apply Kont Val Evv
  | FindPrompt Kont Marker OpName Val Kont
  | ApplyKont Kont Val Kont Evv
  | Halt Val
  deriving (Show)

data KontFrame = KF PureKont KontDelim deriving (Show)
data KontDelim = KHnd Ev | KMask Label | KTop deriving (Show)

data PureKontFrame =
  FLet Env Var Expr Env
  | FApp [Val] [Expr] Env
  | FOp TName [Val] [Expr] Env
  deriving (Show)

interpMain :: BuildContext -> Name -> IO Val
interpMain ctx exprName =
  case lookupBCDef ctx exprName of
    Just e -> do
      res <- interpExpr ctx (lamBody e)
      trace (show res) $ return res

lookupBCDef :: BuildContext -> Name -> Maybe Expr
lookupBCDef ctx name =
  case buildcLookupModule (qualifier name) ctx of
    Just m -> lookupModDef name (fromJust $ modCore m)
    Nothing -> Nothing

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

interpExpr :: BuildContext -> Expr -> IO Val
interpExpr bc e = do
  let start = Eval e M.empty [KF [] KTop] []
      loop :: State -> IO Val
      loop state = do
        res <- interpret bc state
        case res of
          Halt v -> return v
          res -> loop res
  loop start

primitives = [
  nameEffectOpen, nameConsoleUnsafeNoState,
  nameCorePrint, nameCorePrintln, nameCoreTrace, nameCorePrints, nameCorePrintsln,
  nameCoreIntExternShow
  ]

interpret :: BuildContext -> State -> IO State
interpret bc s =
  -- trace (show s) $
  case s of
    Eval e@Lam{} env k evv ->
      -- trace "Lam" $
      return $ Apply k (VFun e env) evv
    Eval e@(Lit l) env k evv ->
      -- trace "Lit" $
      return $ Apply k (VLit l) evv
    Eval e@(Var v@(TName n _ _) _) env k evv ->
      -- trace "VAR" $
      if n `elem` primitives then return $ Apply k (VPrim n) evv
      else
        case M.lookup v env of
          Just v -> return $ Apply k v evv
          Nothing ->
            case lookupBCDef bc n of
              Just e -> return $ Apply k (VFun e M.empty) evv
              Nothing -> error $ "interpret var: " ++ show v
    Eval e@(Con c cr) env k evv -> return $ Apply k (VConI c) evv
    Eval e@(App e1 es _) env (KF pk kd:k) evv ->
      -- trace "APP" $
      return $ Eval e1 env (KF (FApp [] es env:pk) kd:k) evv
    Eval e@(TypeApp e1 _) env k evv ->
      -- trace "TyApp" $
      return $ Eval e1 env k evv
    Eval e@(TypeLam _ e1) env k evv ->
      -- trace "TyLam" $ 
      return $ Eval e1 env k evv
    Apply (KF (FApp vs es env:pk) kd:k) v evv ->
      -- trace "Apply APP" $
      let vals = vs ++ [v] in
      case es of
        [] ->
          let fn:args = vals in
          case fn of
            VFun e env ->
              -- trace (show "Entering fun " ++ show e) $
              let env' = M.union env (M.fromList $ zip (lamExprArgNames e) args)
                  k' = KF pk kd:k
              in return $ Eval (lamBody e) env' k' evv
            VPrim n -> do
              if n == nameEffectOpen || n == nameConsoleUnsafeNoState || n == nameUnsafeTotal || n == nameUnsafeTotalCast then return $ Apply (KF pk kd:k) v evv
              else if n == nameCoreIntExternShow then
                let VLit (LitInt i) = v in
                return $ Apply (KF pk kd:k) (VLit (LitString (show i))) evv
              else if n == nameCorePrint  || n == nameCorePrintln || n == nameCoreTrace || n == nameCorePrints || n == nameCorePrintsln then do
                trace (show (map show args)) $ return ()
                return $ Apply (KF pk kd:k) (VCon (TName nameUnit typeUnit Nothing) []) evv
              else error $ "interpret prim: " ++ show n
        e:es -> return $ Eval e env (KF (FApp vals es env:pk) kd:k) evv
    -- TODO: Open call next
    Apply [KF [] KTop] v evv -> trace "HALT" return $ Halt v
    x -> error $ "interpret: " ++ show x
