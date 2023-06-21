-----------------------------------------------------------------------------
-- Copyright 2012-2023, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-
    Check if a constructor context is well formed, and create a context path
-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE InstanceSigs #-}

module Core.DemandAnalysis(
                          AbstractLattice(..),
                          CallCache(..),EvalCache(..),ExprContext(..),
                          analyzeProgram,
                        ) where


import Control.Monad
import Common.Name
import Data.Set as S hiding (findIndex, filter, map)
import Core.Core (Expr (..), CorePhase, liftCorePhaseUniq, DefGroups, Def (..), DefGroup (..), liftCorePhaseRes, Branch (..), Guard(..), Pattern(..), TName (..), defsTNames, defGroupTNames, mapDefGroup, Core (..), VarInfo (..))
import Data.Map hiding (findIndex, filter, map)
-- import Debug.Trace (trace)
import Core.Pretty
import Type.Type (isTypeInt, isTypeInt32, Type (..), expandSyn, TypeCon (..), ConInfo (..))
import Data.Sequence (mapWithIndex, fromList)
import qualified Data.Sequence as Seq
import Data.Maybe (mapMaybe, isJust, fromJust)
import Data.List (find, findIndex, elemIndex, union)
import Debug.Trace
import Compiler.Module (Loaded (..), Module (..))
import Lib.PPrint (Pretty(..))
import Type.Pretty (ppType, defaultEnv)
import Kind.Kind (Kind(..))

data AbstractLattice =
  AbBottom | AbTop

-- trace:: String -> a -> a
-- trace x y = y
-- Uniquely identifies expressions despite naming
data ExprContext =
  -- Current expression context
  ModuleC ExprContextId Name -- Module context
  | TopCDef ExprContextId Int DefGroup -- Top context, Just an index into a definition group
  | DefCRec ExprContextId ExprContext Int Def -- A recursive definition context, working on the index'th definition
  | DefCNonRec ExprContextId ExprContext Def -- In a non recursive definition context, working on Def
  | LamCBody ExprContextId ExprContext [TName] Expr -- Inside a lambda body expression
  | AppCLambda ExprContextId ExprContext Expr -- Application context inside function context
  | AppCParam ExprContextId ExprContext Int Expr -- Application context inside param context
  | LetCDef ExprContextId ExprContext Int DefGroup -- In a let definition context working on a particular defgroup
  | LetCBody ExprContextId ExprContext Expr -- In a let body expression
  | CaseCMatch ExprContextId ExprContext Expr -- In a case match context working on the match expression (assumes only one)
  | CaseCBranch ExprContextId ExprContext Int Branch -- Which branch currently inspecting, as well as the Case context
  | ExprCBasic ExprContextId ExprContext Expr -- A basic expression context that has no sub expressions
  deriving (Show)

exprOfCtx :: ExprContext -> Expr
exprOfCtx ctx =
  case ctx of
    ModuleC _ _ -> error "ModuleC is a multi Expression Context"
    TopCDef {} -> error "TopCDef is a multi Expression Context"
    DefCRec _ _ _ d -> defExpr d
    DefCNonRec _ _ d -> defExpr d
    LamCBody _ _ _ e -> e
    AppCLambda _ _ f -> f
    AppCParam _ _ _ param -> param
    LetCDef _ _ _ dg -> error "LetCDef has no single expr"
    LetCBody _ _ e -> e
    CaseCMatch _ _ e -> e
    CaseCBranch _ _ _ b -> guardExpr (head (branchGuards b))
    ExprCBasic _ _ e -> e

contextId :: ExprContext -> ExprContextId
contextId ctx =
  case ctx of
    ModuleC c _ -> c
    TopCDef c _ _ -> c
    DefCRec c _ _ _ -> c
    DefCNonRec c _ _ -> c
    LamCBody c _ _ _ -> c
    AppCLambda c _ _ -> c
    AppCParam c _ _ _ -> c
    LetCDef c _ _ _ -> c
    LetCBody c _ _ -> c
    CaseCMatch c _ _ -> c
    CaseCBranch c _ _ _ -> c
    ExprCBasic c _ _ -> c

branchContainsBinding :: Branch -> Name -> Bool
branchContainsBinding (Branch pat guards) name =
  any (`patternContainsBinding` name) pat

patternContainsBinding :: Pattern -> Name -> Bool
patternContainsBinding PatCon{patConPatterns} name = any (`patternContainsBinding` name) patConPatterns
patternContainsBinding (PatVar tname' _) name = name == getName tname'
patternContainsBinding PatWild name = False
patternContainsBinding PatLit{} name = False

data ExprContextId = ExprContextId{
  id:: Int,
  moduleName:: Name,
  topDef:: Name,
  topDefType:: Type
} deriving (Ord, Eq, Show)

instance Ord Type where
  compare tp1 tp2 = compare (show $ ppType defaultEnv tp1) (show $ ppType defaultEnv tp2)

instance Eq Def where
  def1 == def2 = defName def1 == defName def2 && defType def1 == defType def2

newtype CallCache = CallCache {
  calls :: Map ExprContextId ExpressionSet
}

newtype EvalCache = EvalCache {
  evals :: Map ExprContextId ExpressionSet
}

type ExpressionSet = Set ExprContextId

newtype AEnv a = AEnv (Env -> State -> Result a)
data State = State{intStates :: Set ExprContextId, states :: Map ExprContextId ExprContext, childrenIds :: Map ExprContextId (Set ExprContextId), callCache :: CallCache, evalCache :: EvalCache}
data Result a = Ok a State

data Env = Env{
  loaded :: Loaded,
  currentContext :: !ExprContext,
  currentContextId :: ExprContextId
}

instance Functor AEnv where
  fmap f (AEnv c)  = AEnv (\env st -> case c env st of
                                        Ok x st' -> Ok (f x) st')
instance Applicative AEnv where
  pure x = AEnv (\env st -> Ok x st)
  (<*>)  = ap

instance Monad AEnv where
  -- return = pure
  (AEnv c) >>= f = AEnv (\env st -> case c env st of
                                      Ok x st' -> case f x of
                                                    AEnv d -> d env st')

withEnv :: (Env -> Env) -> AEnv a -> AEnv a
withEnv f (AEnv c)
  = AEnv (c . f)

getEnv :: AEnv Env
getEnv = AEnv Ok

getState :: AEnv State
getState = AEnv (\env st -> Ok st st)

updateEnvState :: (Env -> State -> (Env, State)) ->  AEnv a -> AEnv a
updateEnvState update (AEnv continuation) = do
  st <- AEnv (\env st -> Ok st st)
  env <- getEnv
  let (newEnv, newState) = update env st
  AEnv (\env state -> continuation newEnv newState)

analyzeProgram :: Loaded -> CorePhase Int
analyzeProgram loaded = do
  liftCorePhaseRes $ \uniq defs ->
    let x = fst . runAnalysis loaded defs $ do
          ctx <- currentContext <$> getEnv
          analyzeCtx analyzer ctx
          getState
    in (S.size $ intStates x, uniq)

analyzeCtx :: (ExprContext -> AEnv()) -> ExprContext -> AEnv ()
analyzeCtx analyze ctx = do
  parentId <- currentContextId <$> getEnv
  addContext parentId ctx $ do
    id <- currentContextId <$> getEnv
    -- trace ("Analyzing context " ++ show id) $ return ()
    analyze ctx
    children <- createChildrenContexts ctx
    mapM_ (analyzeCtx analyze) children

moduleDummyType :: Type
moduleDummyType = TCon $ TypeCon (newName "dummy") (KCon (newName "dummy"))

runAnalysis :: Loaded -> DefGroups -> AEnv State -> (State, DefGroups)
runAnalysis loaded defs continuation =
  let result = case defGroupResult (loadedModule loaded) loaded defs continuation of
            AEnv f ->
              let cid = ExprContextId 0 (modName $ loadedModule loaded) (newName "module") moduleDummyType in
              let c = ModuleC cid (modName $ loadedModule loaded) in
               f (Env loaded c cid) (State S.empty Data.Map.empty Data.Map.empty (CallCache Data.Map.empty) (EvalCache Data.Map.empty))
  in case result of
    Ok a st -> trace ("Analysis of defs " ++ show defs) (st, defs)

defResult :: Loaded -> Module -> Def -> Int -> DefGroup -> AEnv a -> AEnv a
defResult loaded mod def i defGroup continuation =
  let id = ExprContextId 0 (newName (nameModule (defName def))) (defName def) (defType def) in
  let defCtx = TopCDef id i defGroup in
  updateEnvState (\env state -> (env{currentContext = defCtx, currentContextId = id}, state)) continuation

defGroupResult :: Module -> Loaded -> DefGroups -> AEnv a -> AEnv [a]
defGroupResult mod loaded dgs continuation = -- Need more generic accumulator of results from different def groups so that runAnalysis can be more general
   zipWithM (\i dg -> defResult loaded mod (head $ defsOf dg) i dg continuation) [0..] dgs

analyzer :: ExprContext -> AEnv ()
analyzer ctx =
  case ctx of
    ExprCBasic _ _ expr ->
      case expr of
        Var tname _ | isTypeInt (tnameType tname) -> trace (show (getName tname)) addIntContext
                    | otherwise -> case bind ctx expr of
                          Just x -> trace "Local binding" $ return ()
                          Nothing -> trace ("External binding " ++ show tname) $ do
                            loaded <- loaded <$> getEnv
                            def <- findTopDefRef tname
                            case def of
                              Just (mod, def, i, dg) -> defResult loaded mod def i dg $ do
                                cc <- currentContext <$> getEnv
                                analyzeCtx analyzer cc
                              Nothing -> error "Reference should resolve to something"
          -- analyzeResult (currentContextId <$> getEnv)
        _ -> return ()
    _ -> return ()


bind :: ExprContext -> Expr -> Maybe ExprContext
bind ctx var@(Var tname vInfo) =
  case ctx of
    TopCDef _ _ defg -> if lookupDefGroup defg tname then Just ctx else trace ("External variable binding " ++ show tname ++ ": " ++ show vInfo) Nothing
    DefCRec _ _ _ d -> if lookupDef d tname then Just ctx else bind ctx var -- TODO Consider other definitions in the recursive defs
    DefCNonRec _ _ d -> if lookupDef d tname then Just ctx else bind ctx var
    LamCBody _ _ names _  -> if isJust $ find (== tname) names then Just ctx else bind ctx var
    AppCLambda{} -> bind ctx var
    AppCParam{} -> bind ctx var
    LetCDef _ _ _ defg -> if lookupDefGroup defg tname then Just ctx else bind ctx var
    LetCBody{} -> bind ctx var
    CaseCMatch{} -> bind ctx var
    CaseCBranch _ _ _ b -> if branchContainsBinding b (getName tname) then Just ctx else bind ctx var
    ExprCBasic{} -> bind ctx var

-- gather / generate constraints and then solve them
-- Constraints are of the form: 
-- 1. lhs <= rhs
-- 2. {t} <= rhs' => lhs <= rhs, where
-- rhs ::= C(l)-- call label | r(x) -reference to x and
-- lhs ::= C(l) | r(x) | {t} where {t} denotes a closure
-- 2 is often read as ({t} <= rhs' => lhs) <= rhs
-- so the forms are unified with rhs being the only rhs and the lhs being either
-- lhs or ({t} <= rhs' => lhs)


findUsage :: Expr -> ExprContext -> AEnv (Set ExprContextId)
findUsage  expr@Var{varName=TName{getName = name}} ctx =
  let nameEq = (== name)
      empty = return S.empty
      childrenUsages = do
        children <- childrenCtxs ctx
        usageIds <- mapM (findUsage expr) children
        return $ S.unions usageIds in
  case ctx of
    TopCDef _ _ d -> if any (nameEq . defName) (defsOf d) then empty else childrenUsages
    DefCRec _ _ _ d -> if nameEq $ defName d then empty else childrenUsages -- TODO: Consider index
    DefCNonRec _ _ d -> if nameEq $ defName d then empty else childrenUsages
    LamCBody _ _ names _ -> if any (nameEq . getName) names then empty else childrenUsages
    LetCDef _ _ _ d -> if any (nameEq . defName) (defsOf d) then empty else childrenUsages
    LetCBody{} -> childrenUsages
    CaseCMatch{} -> childrenUsages
    CaseCBranch _ _ _ b -> if branchContainsBinding b name then empty else childrenUsages 
    ExprCBasic id _ Var{varName=TName{getName=name2}} ->
      if nameEq name2 then
        return $ S.singleton id
      else empty
    _ -> do
      children <- childrenCtxs ctx
      usageIds <- mapM (findUsage expr) children
      return $ S.unions usageIds  -- TODO ????

addIntContext :: AEnv ()
addIntContext = do
  updateEnvState (\env state -> (env, state{intStates = S.insert (currentContextId env) $ intStates state})) (return ())

addToSet :: ExprContextId -> ExprContextId -> EvalCache -> EvalCache
addToSet id expr (EvalCache cache) =
  let s = Data.Map.findWithDefault S.empty id cache
  in EvalCache $ Data.Map.insert id (S.insert expr s) cache

addToCallSet :: ExprContextId -> ExprContextId -> CallCache -> CallCache
addToCallSet id expr (CallCache cache) =
  let s = Data.Map.findWithDefault S.empty id cache
  in CallCache $ Data.Map.insert id (S.insert expr s) cache

addEvalResult :: ExprContextId -> AEnv ()
addEvalResult expr = do
  updateEnvState (\env state -> (env, state{evalCache = addToSet (currentContextId env) expr $ evalCache state})) (return ())

addCallResult :: ExprContextId -> AEnv ()
addCallResult expr = do
  updateEnvState (\env state -> (env, state{callCache = addToCallSet (currentContextId env) expr $ callCache state})) (return ())

allModules :: Loaded -> [Module]
allModules loaded = loadedModule loaded : loadedModules loaded

getModule :: String -> AEnv Module
getModule name = do
  modules <- allModules . loaded <$> getEnv
  return $ head $ filter (\mod -> (nameModule . modName) mod == name) modules

getDefAndGroup :: Module -> TName -> DefGroups -> Maybe (Module, Def, Int, DefGroup)
getDefAndGroup mod tname defGs =
  let def = find (\def -> defName def == getName tname && defType def == tnameType tname) (concatMap defsOf defGs)
  in case def of
    Just d -> let group = head $ filter (\dg -> tname `elem` defGroupTNames dg) defGs in
                Just (mod, d, fromJust (elemIndex d (defsOf group)), group)
    Nothing -> Nothing

findTopDefRef :: TName -> AEnv (Maybe (Module, Def, Int, DefGroup))
findTopDefRef tname = do
  loaded <- loaded <$> getEnv
  mod <- getModule (nameModule (getName tname))
  let defs = coreProgDefs . modCore $ mod
  return $ getDefAndGroup mod tname defs

mergeStates :: [State] -> State -- TODO: Ensure this doesn't need to be unionsWith
mergeStates sts = State (S.unions $ map intStates sts) (Data.Map.unions $ map states sts) (Data.Map.unions $ map childrenIds sts) (CallCache $ Data.Map.unions $ map (calls . callCache) sts) (EvalCache $ Data.Map.unions $ map (evals . evalCache) sts)

newContextId :: AEnv ExprContextId
newContextId = do
  state <- getState
  id <- currentContextId <$> getEnv
  return $ ExprContextId (Data.Map.size $ states state) (moduleName id) (topDef id) (topDefType id)

addContext :: ExprContextId -> ExprContext -> AEnv () -> AEnv ()
addContext parentCtx context c = do
  let newId = contextId context
  updateEnvState (\env state ->
    let children = childrenIds state
        childSet = Data.Map.findWithDefault S.empty parentCtx children
        newChildren = Data.Map.insert parentCtx (S.insert newId childSet) children
        newStates = Data.Map.insert newId context $ states state in
    (env{currentContext = context, currentContextId = newId}, state{states = newStates, childrenIds = newChildren})) c

basicExprOf :: ExprContext -> Maybe Expr
basicExprOf ctx =
  case ctx of
    ExprCBasic _ ctx e -> Just e
    _ -> Nothing

childrenCtxs :: ExprContext -> AEnv [ExprContext]
childrenCtxs ctx = do
  children <- childrenIds <$> getState
  let childIds = Data.Map.findWithDefault S.empty (contextId ctx) children
  states <- states <$> getState
  return $ map (states Data.Map.!) (S.toList childIds)


defsOf :: DefGroup -> [Def]
defsOf (DefNonRec d) = [d]
defsOf (DefRec ds) = ds

lookupDefGroup :: DefGroup -> TName -> Bool
lookupDefGroup dg tname = tname `elem` defGroupTNames dg

lookupDef :: Def -> TName -> Bool
lookupDef def tname = defName def == getName tname && tnameType tname == defType def

addContextId :: (ExprContextId -> a) -> AEnv a
addContextId f = do
  f <$> newContextId

childrenOfExpr :: ExprContext -> Expr -> AEnv [ExprContext]
childrenOfExpr ctx expr =
  case expr of
    Lam names eff e -> addContextId (\newId -> [LamCBody newId ctx names e])
    App f vs -> do
      x <- addContextId (\newId -> AppCLambda newId ctx f )
      rest <- zipWithM (\i x -> addContextId (\newId -> AppCParam newId ctx i x)) [0..] vs
      return $ x : rest
    Let defs result -> do
      defs <- zipWithM (\i x -> addContextId (\newId -> LetCDef newId ctx i x)) [0..] defs
      result <- addContextId (\newId -> [LetCBody newId ctx result])
      return $ defs ++ result
    Case exprs branches -> do
      match <- addContextId (\newId -> CaseCMatch newId ctx (head exprs))
      branches <- zipWithM (\i x -> addContextId (\newId -> CaseCBranch newId ctx i x)) [0..] branches
      return $ match : branches
    Var name info -> addContextId (\newId -> [ExprCBasic newId ctx expr ])
    TypeLam tvars expr -> childrenOfExpr ctx expr
    TypeApp expr tps -> childrenOfExpr ctx expr
    Con name repr -> addContextId (\newId -> [ExprCBasic newId ctx expr])
    Lit lit -> addContextId (\newId -> [ExprCBasic newId ctx expr])

childrenOfDef :: ExprContext -> DefGroup -> AEnv [ExprContext]
childrenOfDef ctx def =
  case def of
    DefNonRec d -> addContextId (\newId -> [DefCNonRec newId ctx d])
    DefRec ds -> zipWithM (\i d -> addContextId (\newId -> DefCRec newId ctx i d)) [0..] ds

createChildrenContexts :: ExprContext -> AEnv [ExprContext]
createChildrenContexts ctx =
  case ctx of
    TopCDef _ idx defg -> childrenOfDef ctx defg
    DefCRec _ _ _ d -> childrenOfExpr ctx (defExpr d)
    DefCNonRec _ _ d -> childrenOfExpr ctx (defExpr d)
    LamCBody _ _ names body -> childrenOfExpr ctx body
    AppCLambda _ _ f -> childrenOfExpr ctx f
    AppCParam _ _ _ param -> childrenOfExpr ctx param
    LetCDef _ _ _ defg -> childrenOfDef ctx defg
    LetCBody _ _ e -> childrenOfExpr ctx e
    CaseCMatch _ _ e -> childrenOfExpr ctx e
    CaseCBranch _ _ _ b -> do
      x <- mapM (childrenOfExpr ctx . guardExpr) $ branchGuards b -- TODO Better context for branch guards
      return $ concat x
    ExprCBasic{} -> return []
