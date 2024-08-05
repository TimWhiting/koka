module Interpreter.AbstractMachine (interpMain) where
import Core.Core
import Data.Map.Strict as M hiding (take, map)
import Common.Name
import Kind.Constructors (ConInfo)
import Compile.Module
import Compile.BuildContext (BuildContext (buildcModules))
import Compile.BuildMonad (buildcLookupModule)
import Data.Maybe (fromJust, isJust)
import Core.FlowAnalysis.StaticContext
import Debug.Trace
import Common.NamePrim
import Type.Type (typeUnit, typeBool, Type (..), TypeCon (TypeCon, typeconName))
import Data.List (intercalate)
import Control.Monad.ST.Strict (ST)
import Control.Monad.State (StateT (runStateT), evalStateT, gets, modify)
import Type.Pretty (ppType, defaultEnv)
import Common.Syntax (DefSort(..), isDefFun)
import Common.File (splitOn)

newtype Marker = Mark Int deriving (Show)


data Handler = Handler {
  label:: Label,
  ops:: M.Map OpName Expr,
  ret:: Expr
} deriving (Show)
type Evv = [Val]
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
  | VNamed Marker
  | VPrim Name
  | VEvv Evv
  | VMarker Marker
  deriving (Show)

data State =
  Eval Expr Env Kont Evv
  | Apply Kont Val Evv
  | FindPrompt Kont Marker OpName Val Kont
  | ApplyKont Kont Val Kont Evv
  | Halt Val
  deriving (Show)

showSimple :: State -> String
showSimple (Eval e _ _ _) = "Eval " ++ showSimpleExpr e
showSimple (Apply k v _) = "Apply " ++ show v ++ " " ++ showSimpleK k
showSimple (FindPrompt _ m _ v _) = "FindPrompt " ++ show m ++ " " ++ show v
showSimple (ApplyKont _ v _ _) = "ApplyKont " ++ show v

showSimpleK :: Kont -> String
showSimpleK [] = ""
showSimpleK (kf:k) = showSimpleKF kf ++ " " ++ showSimpleK k

showSimpleKF :: KontFrame -> String
showSimpleKF (KF pk kd) = showSimplePK pk ++ " " ++ showSimpleKD kd

showSimplePK :: PureKont -> String
showSimplePK [] = ""
showSimplePK (kf:k) = showSimplePF kf ++ " " ++ showSimplePK k

showSimplePF :: PureKontFrame -> String
showSimplePF (FLet _ _ _ _ e _) = "FLet ... " ++ showSimpleExpr e 
showSimplePF (FApp _ es _) = "FApp " ++ maybe "" showSimpleExpr (case es of [] -> Nothing; e:es -> Just e)
showSimplePF (FOp _ _ _ _) = "FOp"
showSimplePF (FCase _ _) = "FCase"
showSimplePF (FTyApp _) = "FTyApp"

showSimpleKD :: KontDelim -> String
showSimpleKD (KHnd v) = "KHnd " ++ show v
showSimpleKD (KMask l) = "KMask " ++ l
showSimpleKD KTop = "KTop"

data GlobalState =
  GlobalState {
    markerUnique :: Int,
    namedMarkerUnique :: Int
  } deriving (Show)

data KontFrame = KF PureKont KontDelim deriving (Show)
data KontDelim = KHnd Val | KMask Label | KTop deriving (Show)

data PureKontFrame =
  FLet [Val] [TName] [Def] [DefGroup] Expr Env
  | FApp [Val] [Expr] Env
  | FOp TName [Val] [Expr] Env
  | FCase [Branch] Env
  | FTyApp [Type]
  deriving (Show)

interpMain :: BuildContext -> Name -> IO Val
interpMain ctx exprName =
  case lookupBCDef ctx exprName of
    Just e -> do
      evalStateT ( interpExpr ctx (lamBody (defExpr e))) (GlobalState 1 (-1))
    Nothing -> error $ "interpMain: could not find " ++ show exprName

lookupBCDef :: BuildContext -> Name -> Maybe Def
lookupBCDef ctx name =
  case buildcLookupModule (qualifier name) ctx of
    Just m -> lookupModDef name (fromJust $ modCore m)
    Nothing -> Nothing

lamBody :: Expr -> Expr
lamBody (Lam _ _ e) = lamBody e
lamBody (TypeLam _ e) = lamBody e
lamBody (TypeApp e _) = lamBody e
lamBody e = e

lookupModDef :: Name -> Core -> Maybe Def
lookupModDef name core = lookupDG (coreProgDefs core)
  where
    lookupDG [] = Nothing
    lookupDG (df:dgs) =
      case df of
        DefRec dfs ->
          case lookupD dfs of
            Just e -> Just e
            Nothing -> lookupDG dgs
        DefNonRec d -> if defName d == name then Just d else lookupDG dgs
    lookupD [] = Nothing
    lookupD (d:ds) = if defName d == name then Just d else lookupD ds

interpExpr :: BuildContext -> Expr -> StateT GlobalState IO Val
interpExpr bc e = do
  let start = Eval e M.empty [KF [] KTop] []
      loop :: State -> StateT GlobalState IO Val
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
  nameVectorSepJoin, nameVector, nameCoreTypesExternAppend,
  nameCastEv0, nameCastEv1, nameCastEv2, nameCastEv3, nameCastEv4, nameCastEv5,
  nameEvvGet, nameEvvAt, nameFreshMarker, nameFreshMarkerNamed, nameEvvInsert, nameEvvSet,
  nameInternalSSizeT, nameCastClause0, nameCastClause1, nameCastClause2
  ]

idPrims = [nameEffectOpen, nameConsoleUnsafeNoState, nameUnsafeTotal, nameUnsafeTotalCast, 
  nameCastEv0, nameCastEv1, nameCastEv2, nameCastEv3, nameCastEv4, nameCastEv5,
  nameInternalSSizeT, nameCastClause0, nameCastClause1, nameCastClause2]


findFirstEv :: Evv -> Type -> Val
findFirstEv [] tp = error "findEvv: empty"
findFirstEv (v:vs) tp = 
  case v of
    VCon (TName n _ _) [h, m, hnd, hevv] | n == nameTpEv && h `hndMatchesTp` tp -> 
      trace ("Found ev: " ++ show h) v
    _ -> findFirstEv vs tp

hndMatchesTp :: Val -> Type -> Bool
hndMatchesTp (VCon (TName n tp1 _) [VLit (LitString hndName)]) (TCon (TypeCon{typeconName = tp2})) = 
  head (splitOn (== '@') hndName) == nameStem tp2
hndMatchesTp x _ = error $ "hndMatchesTp: " ++ show x

interpret :: BuildContext -> State -> StateT GlobalState IO State
interpret bc s =
  trace ("\n\n\n" ++ showSimple s) $
  case s of
    Eval e@Lam{} env k evv ->
      -- trace "Lam" $
      return $ Apply k (VFun e env) evv
    Eval (Lit l) env k evv ->
      -- trace "Lit" $
      return $ Apply k (VLit l) evv
    Eval (Var v@(TName n tp _) _) env k evv ->
      -- trace "VAR" $
      if n `elem` primitives then 
        trace ("Primitive: " ++ show n ++ " " ++ show (ppType defaultEnv tp)) $
        return $ Apply k (VPrim n) evv
      else
        case M.lookup v env of
          Just v -> return $ Apply k v evv
          Nothing ->
            case lookupBCDef bc n of
              Just d -> 
                if isDefFun (defSort d) then
                  return $ Apply k (VFun (defExpr d) M.empty) evv
                else
                  return $ Eval (defExpr d) M.empty k evv
              Nothing -> error $ "interpret var: " ++ show v
    Eval (Con c cr) env k evv -> 
      trace ("Con: " ++ show c ++ " " ++ show cr ++ " " ++ show (conNoFields cr)) $
      return $ Apply k (if conNoFields cr then VCon c [] else VConI c) evv
    Eval (TypeApp (Var (TName n _ _) _) [tp]) env (KF (pk1:pk2:pk) kd:k) evv | n == nameEvvAt ->
      return $ Apply (KF pk kd:k) (findFirstEv evv tp) evv
    Eval (App e1 es _) env (KF pk kd:k) evv ->
      -- trace "APP" $
      return $ Eval e1 env (KF (FApp [] es env:pk) kd:k) evv
    Eval (TypeApp e1 tps) env (KF pk kd:k) evv ->
      -- trace "TyApp" $
      return $ Eval e1 env (KF (FTyApp tps: pk) kd:k)evv
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
            VConI c -> 
              trace ("ConI: " ++ show args)
              return $ Apply kont (VCon c args) evv
            VFun e env ->
              -- trace (show "Entering fun " ++ show e) $
              let env' = M.union env (M.fromList $ zip (lamExprArgNames e) args)
              in return $ Eval (lamBody e) env' kont evv
            VPrim n -> do
              if n `elem` idPrims then return $ Apply kont v evv
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
              else if n == nameEvvGet then return $ Apply kont (VEvv evv) evv
              else if n == nameEvvAt then 
                -- TODO: 
                error "Evv at not implemented"
              else if n == nameFreshMarker then do
                m <- gets markerUnique
                let marker = Mark m
                modify $ \st -> st { markerUnique = m + 1 }
                return $ Apply kont (VMarker marker) evv
              else if n == nameFreshMarkerNamed then do
                m <- gets namedMarkerUnique
                let marker = Mark m
                modify $ \st -> st { namedMarkerUnique = m - 1 }
                return $ Apply kont (VMarker marker) evv
              else if n == nameEvvInsert then
                let [VEvv vs, v] = args in
                return $ Apply kont (VEvv (v : vs)) evv
              else if n == nameEvvSet then
                let [VEvv vs] = args in 
                return $ Apply kont unitCon vs
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
            _ -> error $ "interpret app: " ++ show fn ++ "\nargs:" ++ show args
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
    Apply (KF (FTyApp tps:pk) kd:k) v evv ->
      case v of
        VCon (TName n tp _) vs -> return $ Apply (KF pk kd:k) (VCon (TName n (TApp tp tps)  Nothing) vs) evv
        VConI (TName n tp _)  -> return $ Apply (KF pk kd:k) (VConI (TName n (TApp tp tps) Nothing)) evv
        _ -> return $ Apply (KF pk kd:k) v evv
    Apply [KF [] KTop] v evv -> trace "HALT" return $ Halt v
    Apply (KF (pkf:_) _:k) v _ -> error $ "interpret: " ++ show pkf ++ " " ++ show v
    _ -> error $ "interpret: " ++ show s

intBinaryOp :: (Integer -> Integer -> Integer) -> Kont -> Evv -> [Val] -> StateT GlobalState IO State
intBinaryOp op k evv [VLit (LitInt i1), VLit (LitInt i2)] = return $ Apply k (VLit (LitInt (op i1 i2))) evv

intCmpOp :: (Integer -> Integer -> Bool) -> Kont -> Evv -> [Val] -> StateT GlobalState IO State
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
