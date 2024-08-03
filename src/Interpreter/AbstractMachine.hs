module Interpreter.AbstractMachine (interpMain) where
import Core.Core
import Data.Map.Strict as M hiding (map)
import Common.Name
import Kind.Constructors (ConInfo)
import Compile.Module
import Compile.BuildContext (BuildContext (buildcModules))
import Compile.BuildMonad (buildcLookupModule)
import Data.Maybe (fromJust, isJust)
import Core.FlowAnalysis.StaticContext
import Debug.Trace
import Common.NamePrim
import Type.Type (typeUnit, typeBool)
import Data.List (intercalate)

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
  FLet [Val] [TName] [Def] [DefGroup] Expr Env
  | FApp [Val] [Expr] Env
  | FOp TName [Val] [Expr] Env
  | FCase [Branch] Env
  deriving (Show)

interpMain :: BuildContext -> Name -> IO Val
interpMain ctx exprName =
  case lookupBCDef ctx exprName of
    Just e -> do
      interpExpr ctx (lamBody e)
    Nothing -> error $ "interpMain: could not find " ++ show exprName

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

primitives =
  [
  nameEffectOpen, nameConsoleUnsafeNoState,
  nameCorePrint, nameCorePrintln, nameCoreTrace, nameCorePrints, nameCorePrintsln,
  nameCoreIntExternShow,
  nameIntAdd, nameIntMul, nameIntDiv, nameIntMod, nameIntSub,
  nameIntEq, nameIntLt, nameIntLe, nameIntGt, nameIntGe,
  nameVectorSepJoin, nameVector, nameCoreTypesExternAppend

  ]

interpret :: BuildContext -> State -> IO State
interpret bc s =
  -- trace (show s) $
  case s of
    Eval e@Lam{} env k evv ->
      -- trace "Lam" $
      return $ Apply k (VFun e env) evv
    Eval (Lit l) env k evv ->
      -- trace "Lit" $
      return $ Apply k (VLit l) evv
    Eval (Var v@(TName n _ _) _) env k evv ->
      -- trace "VAR" $
      if n `elem` primitives then return $ Apply k (VPrim n) evv
      else
        case M.lookup v env of
          Just v -> return $ Apply k v evv
          Nothing ->
            case lookupBCDef bc n of
              Just e -> return $ Apply k (VFun e M.empty) evv
              Nothing -> error $ "interpret var: " ++ show v
    Eval (Con c cr) env k evv -> return $ Apply k (if conNoFields cr then VCon c [] else VConI c) evv
    Eval (App e1 es _) env (KF pk kd:k) evv ->
      -- trace "APP" $
      return $ Eval e1 env (KF (FApp [] es env:pk) kd:k) evv
    Eval (TypeApp e1 _) env k evv ->
      -- trace "TyApp" $
      return $ Eval e1 env k evv
    Eval (TypeLam _ e1) env k evv ->
      -- trace "TyLam" $ 
      return $ Eval e1 env k evv
    Eval (Let defgrps e2) env (KF pk kd:k) evv -> do
      let defgrp:defgrps' = defgrps
      let def:defs' = defsOf defgrp
      return $ Eval (defExpr def) env (KF (FLet [] (map defTName (defsOf defgrp)) defs' defgrps' e2 env:pk) kd:k) evv
    Eval (Case [e1] bs) env (KF pk kd:k) evv ->
      return $ Eval e1 env (KF (FCase bs env:pk) kd:k) evv
    Apply (KF (FApp vs es env:pk) kd:k) v evv ->
      -- trace "Apply APP" $
      let vals = vs ++ [v] in
      case es of
        -- Evaluate the rest of the arguments
        e:es -> return $ Eval e env (KF (FApp vals es env:pk) kd:k) evv
        [] -> -- Evaluate the application
          let kont = KF pk kd:k
              fn:args = vals in
          case fn of
            VConI c -> return $ Apply kont (VCon c args) evv
            VFun e env ->
              -- trace (show "Entering fun " ++ show e) $
              let env' = M.union env (M.fromList $ zip (lamExprArgNames e) args)
              in return $ Eval (lamBody e) env' kont evv
            VPrim n -> do
              if n == nameEffectOpen || n == nameConsoleUnsafeNoState || n == nameUnsafeTotal || n == nameUnsafeTotalCast then return $ Apply kont v evv
              else if n == nameCoreIntExternShow then
                let VLit (LitInt i) = v in
                return $ Apply kont (VLit (LitString (show i))) evv
              else if n == nameCorePrint  || n == nameCorePrintln || n == nameCoreTrace || n == nameCorePrints || n == nameCorePrintsln then do
                trace (tostring v) $ return ()
                return $ Apply kont unitCon evv
              else if n == nameIntAdd then intBinaryOp (+) kont evv args
              else if n == nameIntMul then intBinaryOp (*) kont evv args
              else if n == nameIntDiv then intBinaryOp div kont evv args
              else if n == nameIntMod then intBinaryOp mod kont evv args
              else if n == nameIntSub then intBinaryOp (-) kont evv args
              else if n == nameIntEq then intCmpOp (==) kont evv args
              else if n == nameIntLt then intCmpOp (<) kont evv args
              else if n == nameIntLe then intCmpOp (<=) kont evv args
              else if n == nameIntGt then intCmpOp (>) kont evv args
              else if n == nameIntGe then intCmpOp (>=) kont evv args
              else if n == nameVectorSepJoin then
                case args of
                  [VCon vec args, VLit (LitString sep)] -> return $ Apply kont (VLit (LitString (intercalate sep (map tostring args)))) evv
              else if n == nameVector then
                let newargs args = 
                      case args of 
                        VCon cons [arg, rst] -> arg : newargs rst
                        VCon nil [] -> [] in
                return $ Apply kont (VCon (TName nameVector typeUnit Nothing) (newargs (head args))) evv
              else if n == nameCoreTypesExternAppend then
                case args of
                  [VLit (LitString s1), VLit (LitString s2)] -> return $ Apply kont (VLit (LitString (s1 ++ s2))) evv
              else error $ "interpret prim: " ++ show n

    Apply ((KF (FCase (Branch [p] [Guard gd body]:bs) env:pk) kd):k) v evv ->
      case v `patMatches` p of
        Just binds -> do
          if isExprTrue gd then
            let env' = M.union env (M.fromList binds) in
            return $ Eval body env' (KF pk kd:k) evv
          else -- TODO: Guard frame, with rest guards / branches
            error "Guard not supported"
        Nothing -> return $ Apply (KF (FCase bs env:pk) kd:k) v evv
    Apply (KF (FLet vs defnames defs defgrps e env:pk) kd:k) v evv ->
      -- trace "Apply Let" $
      case defs of
        def:defs' -> -- Evaluate the next def
          return $ Eval (defExpr def) env (KF (FLet (vs ++ [v]) defnames defs' defgrps e env:pk) kd:k) evv
        [] ->
          case defgrps of -- TODO: Handle recursive environments, by adjusting all of the closure values' environments How? No mutation :(
            defgrp:defgrps' -> do -- Evaluate the next defgroup, after binding the names in the group
              let def:defs' = defsOf defgrp
                  env' = M.union env (M.fromList $ zip defnames (vs ++ [v]))
                  defnames' = map defTName (defsOf defgrp)
              return $ Eval (defExpr def) env' (KF (FLet [] defnames' defs' defgrps' e env':pk) kd:k) evv
            [] -> do -- Evaluate the body
              let env' = M.union env (M.fromList $ zip defnames (vs ++ [v]))
              return $ Eval e env' (KF pk kd:k) evv
    Apply [KF [] KTop] v evv -> trace "HALT" return $ Halt v
    Apply (KF (pkf:_) _:k) v _ -> error $ "interpret: " ++ show pkf ++ " " ++ show v

intBinaryOp :: (Integer -> Integer -> Integer) -> Kont -> Evv -> [Val] -> IO State
intBinaryOp op k evv [VLit (LitInt i1), VLit (LitInt i2)] = return $ Apply k (VLit (LitInt (op i1 i2))) evv

intCmpOp :: (Integer -> Integer -> Bool) -> Kont -> Evv -> [Val] -> IO State
intCmpOp op k evv [VLit (LitInt i1), VLit (LitInt i2)] = return $ Apply k (fromBool (i1 `op` i2)) evv

unitCon = VCon (TName nameUnit typeUnit Nothing) []
trueCon = VCon (TName nameTrue typeBool Nothing) []
falseCon = VCon (TName nameFalse typeBool Nothing) []
fromBool True = trueCon
fromBool False = falseCon

patMatches :: Val -> Pattern -> Maybe [(TName, Val)]
patMatches v (PatVar k sub) =
  case patMatches v sub of
    Just binds -> Just (binds ++ [(k,v)])
    Nothing -> Nothing
patMatches (VCon c vs) (PatCon c' subs _ _ _ _ _ _) =
  if c == c' then -- TODO: Match types as well?
    let matches = zipWith patMatches vs subs in
    if all isJust matches then
      Just $ concatMap fromJust matches
    else Nothing
  else Nothing
patMatches (VLit l) (PatLit l') =
  if l == l' then Just []
  else Nothing
patMatches v PatWild = Just []
patMatches _ _ = Nothing

tostring :: Val -> String
tostring (VLit (LitString s)) = s
tostring (VLit (LitInt i)) = show i
tostring (VLit (LitChar c)) = show c
tostring (VLit (LitFloat f)) = show f
tostring (VCon c vs) = error "tostring con"
tostring (VFun e env) = error "tostring fun"
