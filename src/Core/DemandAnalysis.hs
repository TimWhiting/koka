-----------------------------------------------------------------------------
-- Copyright 2012-2023, Microsoft Research, Daan Leijen. Brigham Young University, Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

{-
    Check if a constructor context is well formed, and create a context path
-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE NamedFieldPuns #-}

module Core.DemandAnalysis(
  fixedEval,fixedExpr,fixedCall,loop,qcall,qexpr,qeval,
  doForClosures,doForConstructors,doForConstructorsJoin,doForLits,doForLitsJoin,
  FixDemandR,FixDemand,State(..),DEnv(..),FixInput(..),AFixOutput(..),FixOutput,Query(..),AnalysisKind(..),
  toAbValue,toAbValue2,
  refineQuery,queryCtx,queryEnv,queryKind,queryKindCaps,getEnv,withEnv,
  getQueryString,getState,setState,updateState,setResult,getUnique,
  childrenContexts,analyzeCtx,findContext,visitChildrenCtxs,
  runEvalQueryFromRangeSource,
                        ) where
import GHC.IO (unsafePerformIO)
import Control.Monad hiding (join)
import Control.Monad.Reader (lift, ReaderT (runReaderT), local, ask)
import Control.Monad.Trans.Cont (ContT(runContT), resetT, shiftT, mapContT, evalContT, callCC, liftLocal)
import Control.Monad.State (StateT (..), MonadState (..), gets)
import Control.Monad.Identity (IdentityT, Identity (..))
import Control.Monad.Trans
import Data.Set as S hiding (findIndex, filter, map)
import qualified Data.Sequence as Seq
import qualified Data.Map.Strict as M
import Data.Sequence (mapWithIndex, fromList)
import Data.Maybe (mapMaybe, isJust, fromJust, maybeToList, fromMaybe, catMaybes)
import Data.List (find, findIndex, elemIndex, union, intercalate)
import Common.Name
import Common.Range (Range, rangesOverlap, showFullRange, rangeNull)
import Common.NamePrim (nameOpen, nameEffectOpen)
import Lib.PPrint (Pretty(..))
import Debug.Trace
import Core.Core as C
import Core.StaticContext
import Core.AbstractValue
import Core.FixpointMonad
import Core.Pretty
import Core.CoreVar
import Type.Pretty (ppType, defaultEnv, Env (..))
import Type.Type (isTypeInt, isTypeInt32, Type (..), expandSyn, TypeCon (..), ConInfo (..), Flavour (Bound), TypeVar (TypeVar), effectEmpty)
import Kind.Kind (Kind(..), kindFun, kindStar)
import Compiler.Module (Loaded (..), Module (..), ModStatus (LoadedIface), addOrReplaceModule)
import Syntax.RangeMap (RangeInfo)
import Syntax.Syntax (UserExpr, UserProgram, UserDef, Program (..), DefGroups, UserType, DefGroup (..), Def (..), ValueBinder (..), UserValueBinder)
import qualified Syntax.Syntax as Syn

data State a x = State{
  loaded :: Loaded,
  states :: M.Map ExprContextId ExprContext,
  maxContextId :: Int,
  childrenIds :: M.Map ExprContextId (Set ExprContextId),
  unique :: Int,
  finalResult :: Maybe a,
  additionalState :: x
}

getState :: FixDemandR x s e (State x s)
getState = gets snd

setState :: State x s -> FixDemandR x s e ()
setState x = do
  st <- get
  put (fst st, x)

data AnalysisKind = BasicEnvs | LightweightEnvs | HybridEnvs deriving (Eq, Ord, Show)

data DEnv x = DEnv{
  contextLength :: Int,
  analysisKind :: AnalysisKind,
  currentContext :: !ExprContext,
  currentModContext :: !ExprContext,
  currentEnv :: EnvCtx,
  currentQuery :: String,
  queryIndentation :: String,
  loadModuleFromSource :: Module -> IO Module,
  additionalEnv :: x
}

withEnv :: (DEnv e -> DEnv e) -> FixDemandR x s e a -> FixDemandR x s e a
withEnv = local

getEnv :: FixDemandR x s e (DEnv e)
getEnv = ask

type FixDemand x s e = FixTS FixInput BasicLattice (State x s) (DEnv e) AFixOutput
type FixDemandR x s e a = FixTR FixInput BasicLattice (State x s) (DEnv e) AFixOutput a

-- A query type representing the mutually recursive queries we can make that result in an abstract value
data Query =
  CallQ (ExprContext, EnvCtx) |
  ExprQ (ExprContext, EnvCtx) |
  EvalQ (ExprContext, EnvCtx) deriving (Eq, Ord)

instance Show Query where
  show q = queryKindCaps q ++ ": " ++ showSimpleEnv (queryEnv q) ++ " " ++ showSimpleContext (queryCtx q)

-- The fixpoint input is either a query to get an abstract value result, or an environment to get a set of refined environments
data FixInput =
  QueryInput Query
  | EnvInput EnvCtx deriving (Ord, Eq, Show)

-- The output of the fixpoint is either a value, or set of environments 
-- (depending on whether the input is a query or wanting the refined environments for a particular environment)
data AFixOutput =
  A AbValue
  | E (S.Set EnvCtx)
  | N deriving (Show, Eq)

-- The real output however is a basic lattice of the above
type FixOutput = BasicLattice AFixOutput

-- Implement the needed operations for the output to be a lattice
instance Semigroup AFixOutput where
  (<>) (A a) (A b) = A (a <> b)
  (<>) (E e) (E e1) = E (e <> e1)
  (<>) N x = x
  (<>) x N = x
  (<>) x y = error $ "Unexpected semigroup combination " ++ show x ++ " " ++ show y

instance Contains AFixOutput where
  contains (A (BL a)) (A (BL b)) = a `contains` b
  contains (E e) (E e1) = e1 `isSubsetOf` e
  contains _ N = True
  contains _ _ = False

instance Monoid AFixOutput where
  mempty = N

-- Convenience functions to set up the mutual recursion between the queries and unwrap the result
qcall :: (ExprContext, EnvCtx) -> FixDemandR x s e AbValue
qcall = toAbValue . loop . QueryInput . CallQ
qexpr :: (ExprContext, EnvCtx) -> FixDemandR x s e AbValue
qexpr = toAbValue . loop . QueryInput . ExprQ
qeval :: (ExprContext, EnvCtx) -> FixDemandR x s e AbValue
qeval = toAbValue . loop . QueryInput . EvalQ

-- Takes in a fixpoint computation and returns a fixpoint computation that unwraps an abstract value result
toAbValue :: FixDemand x s e -> FixDemandR x s e AbValue
toAbValue c = toAbValue2 <$> c

toAbValue2 :: BasicLattice AFixOutput -> AbValue
toAbValue2 c =
  case c of
    BL (A x) -> x
    BL N -> emptyAbValue
    _ -> error $ "toAbValue: " ++ show c

-- Unwraps query pieces
queryCtx :: Query -> ExprContext
queryCtx (CallQ (ctx, _)) = ctx
queryCtx (ExprQ (ctx, _)) = ctx
queryCtx (EvalQ (ctx, _)) = ctx

queryEnv :: Query -> EnvCtx
queryEnv (CallQ (_, env)) = env
queryEnv (ExprQ (_, env)) = env
queryEnv (EvalQ (_, env)) = env

queryKind :: Query -> String
queryKind (CallQ _) = "call"
queryKind (ExprQ _) = "expr"
queryKind (EvalQ _) = "eval"

queryKindCaps :: Query -> String
queryKindCaps (CallQ _) = "CALL"
queryKindCaps (ExprQ _) = "EXPR"
queryKindCaps (EvalQ _) = "EVAL"

-- Refines a query given a more specific environment
refineQuery :: Query -> EnvCtx -> Query
refineQuery (CallQ (ctx, env0)) env = CallQ (ctx, env)
refineQuery (ExprQ (ctx, env0)) env = ExprQ (ctx, env)
refineQuery (EvalQ (ctx, env0)) env = EvalQ (ctx, env)

------------------------ Navigating the syntax tree ----------------------------------
focusParam :: Maybe Int -> ExprContext -> FixDemandR x s e (Maybe ExprContext)
focusParam index e = do
  children <- childrenContexts e
  query <- getQueryString
  return $ case index of
    Just x | x + 1 < length children -> Just $ children !! (x + 1) -- Parameters are the not the first child of an application (that is the function)
    _ -> trace (query ++ "Children looking for param " ++ show children ++ " in " ++ show e ++ " index " ++ show index) Nothing

focusBody :: ExprContext -> FixDemandR x s e (Maybe ExprContext)
focusBody e = do
  children <- childrenContexts e
  query <- getQueryString
  return $ case find (\x -> case x of
              LamCBody{} -> True
              _ -> False) children of
    Just x -> Just x
    Nothing -> trace (query ++ "Children looking for body " ++ show children) Nothing

focusFun :: ExprContext -> FixDemandR x s e (Maybe ExprContext)
focusFun e = do
  children <- childrenContexts e
  query <- getQueryString
  return $ case find (\x -> case x of
                AppCLambda{} -> True
                ExprCBasic _ _ Var{} -> True
                _ -> False) children of
    Just x -> Just x
    Nothing -> trace (query ++ "Children looking for lambda " ++ show children) Nothing


focusChild :: ExprContext -> Int -> FixDemandR x s e (Maybe ExprContext)
focusChild e index = do
  children <- childrenContexts e
  query <- getQueryString
  return $ if index < length children then
    -- trace (query ++ "Focused child " ++ show (children !! index) ++ " " ++ show index ++ " " ++ show children) $
      Just (children !! index)
    else trace (query ++ "Children looking for child at " ++ show index ++ " " ++ show children) Nothing

focusLetBinding :: Maybe Int -> ExprContext -> FixDemandR x s e (Maybe ExprContext)
focusLetBinding index e = do
  children <- childrenContexts e
  query <- getQueryString
  return $ case index of
    Just x | x < length children -> Just $ children !! x
    _ -> trace (query ++ "Children looking for let binding " ++ show children) Nothing

------------------ State and Environment Helpers -----------------------------------

-- Gets a string representing the current query
getQueryString :: FixDemandR x s e String
getQueryString = do
  env <- getEnv
  return $ queryIndentation env ++ currentQuery env ++ show (contextId $ currentContext env) ++ " "

getUnique :: FixDemandR x s e Int
getUnique = do
  st <- getState
  let u = unique st
  setState st{unique = u + 1}
  return u

updateState :: (State x s -> State x s) -> FixDemandR x s e ()
updateState update = do
  st <- getState
  setState $ update st

setResult :: x -> FixDemand x s e
setResult x = do
  updateState (\st -> st{finalResult = Just x})
  return $ BL N

------------------------------ Environment FIXPOINT -----------------------------------

instantiate :: String -> EnvCtx -> EnvCtx -> FixDemandR x s e ()
instantiate query c1 c0 = if c1 == c0 then return () else do
  trace (query ++ "INST: " ++ showSimpleEnv c0 ++ " to " ++ showSimpleEnv c1) $ return ()
  loop (EnvInput c0)
  push (EnvInput c0) (BL (E (S.singleton c1)))
  return ()

calibratem :: EnvCtx -> FixDemandR x s e EnvCtx
calibratem env = do
  length <- contextLength <$> getEnv
  return $ calibratemenv length env

calibratemenv :: Int -> EnvCtx -> EnvCtx
calibratemenv mlimit (EnvCtx ps tail) = do
  EnvCtx (calibratemctx mlimit ps) (calibratemenv mlimit tail)
calibratemenv mlimit (EnvTail ctx) = EnvTail $! calibratemctx mlimit ctx

-- TODO: Degen needs a way to be converted to Indet (calibration makes environments longer (to m))
-- Probably needs more information to determine static context
calibratemctx :: Int -> Ctx -> Ctx
calibratemctx mlimit p =
  if mlimit == 0 then
    case p of 
      CallCtx{} -> CutKnown
      BCallCtx{} -> CutKnown
      CutKnown -> CutKnown
      TopCtx -> TopCtx
      IndetCtx{} -> CutUnknown
      CutUnknown -> CutUnknown
  else case p of
    IndetCtx tn c -> IndetCtx tn c
    -- TODO: Get previous call context and look up the lexically enclosing lambda to get the correct IndetCtx
    CutKnown -> let id = ExprContextId (-1) (newName "_err") in IndetCtx [] (ExprCTerm id "Err") 
    CutUnknown -> let id = ExprContextId (-1) (newName "_err") in IndetCtx [] (ExprCTerm id "Err") 
    CallCtx c p' -> CallCtx c (calibratemenv (mlimit - 1) p')
    BCallCtx c p' -> BCallCtx c (calibratemctx (mlimit - 1) p')
    x -> x

succAEnv :: ExprContext -> EnvCtx -> FixDemandR x s e Ctx
succAEnv newctx p' = do
  length <- contextLength <$> getEnv
  kind <- analysisKind <$> getEnv
  case kind of
    BasicEnvs -> return $ limitm (BCallCtx newctx (envhead p')) length
    _ -> return $ CallCtx newctx (calibratemenv (length - 1) p')

ccDeterminedEnv :: EnvCtx -> Bool
ccDeterminedEnv env =
  case env of
    EnvCtx cc tail -> ccDetermined cc && ccDeterminedEnv tail
    EnvTail cc -> ccDetermined cc

ccDetermined :: Ctx -> Bool
ccDetermined ctx =
  case ctx of
    IndetCtx{} -> False
    CallCtx c env -> ccDeterminedEnv env
    TopCtx -> True
    CutKnown -> False
    CutUnknown -> True
    BCallCtx c rst -> ccDetermined rst

getEnvs :: FixDemand x s e -> FixDemandR x s e (Set EnvCtx)
getEnvs c = do
  res <- c
  case res of
    BL (E x) -> return x
    BL N -> return S.empty
    _ -> error $ "getEnvs: " ++ show res

getRefines1 :: EnvCtx -> FixDemandR x s e (Set EnvCtx)
getRefines1 env =
  case env of
    EnvCtx cc tail -> do
      curRefine <- if ccDetermined cc then return S.empty else getEnvs (loop (EnvInput env))
      tailRefines <- getRefines1 tail
      return $ curRefine `S.union` S.fromList (fmap (EnvCtx cc) (S.toList tailRefines))
    EnvTail cc -> getEnvs (loop (EnvInput env))

----------------- Unwrap/iterate over values within an abstract value and join results of subqueries ----------------------
doMaybeAbValue :: AbValue -> Maybe a -> (a -> FixDemandR x s e AbValue) -> FixDemandR x s e AbValue
doMaybeAbValue init l doA = do
  case l of
    Just x -> doA x
    Nothing -> return init

doForClosures :: AbValue -> AbValue -> ((ExprContext, EnvCtx) -> FixDemandR x s e AbValue) -> FixDemandR x s e AbValue
doForClosures init l doA = do
  foldM (\res x -> do
    res' <- doA x
    return $! join res res') init (S.toList $ closures l)

doForConstructors :: AbValue -> AbValue -> ((EnvCtx, ConstrContext) -> FixDemandR x s e AbValue) -> FixDemandR x s e AbValue
doForConstructors init l doA = do
  foldM (\res x -> do
    res' <- doA x
    return $! join res res') init (concatMap (\(f,s) -> map (\s -> (f, s)) $ S.toList s) (M.toList $ constrs l))

doForConstructorsJoin :: a -> AbValue -> (a -> a -> a) -> ((EnvCtx, ConstrContext) -> FixDemandR x s e a) -> FixDemandR x s e a
doForConstructorsJoin init l join doA = do
  foldM (\res x -> do
    res' <- doA x
    return $! join res res') init (concatMap (\(f,s) -> map (\s -> (f, s)) $ S.toList s) (M.toList $ constrs l))

doForLits :: AbValue -> AbValue -> ((EnvCtx, LiteralContext) -> FixDemandR x s e AbValue) -> FixDemandR x s e AbValue
doForLits init l doA = do
  foldM (\res x -> do
    res' <- doA x
    return $! join res res') init (M.toList $ lits l)

doForLitsJoin :: a -> AbValue -> (a -> a -> a) -> ((EnvCtx, LiteralContext) -> FixDemandR x s e a) -> FixDemandR x s e a
doForLitsJoin init l join doA = do
  foldM (\res x -> do
    res' <- doA x
    return $! join res res') init (M.toList $ lits l)

--------------------------- TOP LEVEL QUERIES: RUNNING THE FIXPOINT ------------------------------
fixedEval :: ExprContext -> EnvCtx -> FixDemandR x s e [(EnvCtx, AbValue)]
fixedEval e env = do
  let q = EvalQ (e, env)
  res <- loop (QueryInput q)
  refines <- getRefines1 env
  res2 <- mapM (\env -> do
    res <- loop (QueryInput (EvalQ (e, env)))
    return (env, res))
      (S.toList refines)
  trace "Finished eval" $ return ()
  return $ map (\(f, s) -> (f, toAbValue2 s)) ((env,res):res2)

fixedExpr :: ExprContext -> EnvCtx -> FixDemandR x s e [(ExprContext, EnvCtx)]
fixedExpr e env = do
  let q = ExprQ (e, env)
  res <- loop (QueryInput q)
  trace "Finished eval" $ return ()
  return (S.toList $ closures $ toAbValue2 res)

fixedCall :: ExprContext -> EnvCtx -> FixDemandR x s e [(ExprContext, EnvCtx)]
fixedCall e env = do
  let q = CallQ (e, env)
  res <- loop (QueryInput q)
  trace "Finished eval" $ return ()
  return (S.toList $ closures $ toAbValue2 res)

--- Wraps a computation with a new environment that represents the query indentation and dependencies for easier following and debugging
newQuery :: Query -> (String -> FixDemandR x s e AbValue) -> FixDemandR x s e FixOutput
newQuery q d = do
  unique <- getUnique
  withEnv (\env -> env{currentContext = queryCtx q, currentEnv = queryEnv q, currentQuery = "q" ++ show unique ++ "(" ++ queryKindCaps q ++ ")" ++ ": ", queryIndentation = queryIndentation env ++ " "}) $ do
    query <- getQueryString
    res <- d query
    return $ BL $ A res

loop :: FixInput -> FixDemand x s e 
loop fixinput = do
  memo fixinput $ \i ->
    case i of
      QueryInput cq ->
        case cq of
          EvalQ{} -> do
            newQuery cq (\queryStr -> do
                res <- doEval cq queryStr
                refines <- getRefines1 (queryEnv cq)
                res2 <- foldM (\res env -> do
                    x <- doEval (EvalQ (queryCtx cq, env)) queryStr
                    return $ res `join` x
                  ) res refines
                trace (queryStr ++ "RESULT: " ++ showNoEnvAbValue res2) $ return res2
              )
          CallQ{} -> do
            newQuery cq (\queryStr -> do
                res <- doCall cq queryStr
                refines <- getRefines1 (queryEnv cq)
                res2 <- foldM (\res env -> do
                    x <- doCall (CallQ (queryCtx cq, env)) queryStr
                    return $ res `join` x
                  ) res refines
                trace (queryStr ++ "RESULT: " ++ showNoEnvAbValue res2) $ return res2
              )
          ExprQ{} -> do
            newQuery cq (\queryStr -> do
                res <- doExpr cq queryStr
                refines <- getRefines1 (queryEnv cq)
                res2 <- foldM (\res env -> do
                    x <- doExpr (ExprQ (queryCtx cq, env)) queryStr
                    return $ res `join` x
                  ) res refines
                trace (queryStr ++ "RESULT: " ++ showNoEnvAbValue res2) $ return res2
              )
      EnvInput env ->
        return $ BL $ E S.empty


bindExternal :: Expr -> FixDemandR x s e (Maybe (ExprContext, Maybe Int))
bindExternal var@(Var tn@(TName name tp _) vInfo) = do
  deps <- loadedModules . loaded <$> getState
  let x = find (\m -> modName m == newName (nameModule name)) deps
  case x of
    Just mod -> do
      ctxId <- newModContextId mod
      mod' <- if modStatus mod == LoadedIface then do
        -- TODO: set some level of effort / time required for loading externals, but potentially load all core modules on startup
                load <- loadModuleFromSource <$> getEnv
                let mod' = unsafePerformIO $ load mod
                updateState (\state ->
                  let ld = loaded state
                  in state{loaded = ld{loadedModules = addOrReplaceModule mod' (loadedModules ld) }})
                return mod'
              else return mod
      return $ if lookupDefGroups (coreProgDefs $ modCoreNoOpt mod') tn then Just (ModuleC ctxId mod' (modName mod'), Nothing) else trace ("External variable binding " ++ show tn ++ ": " ++ show vInfo) Nothing
    _ -> return Nothing

-- TODO: Consider static overloading
-- finds usages of a variable expression within a (context,env) and returns the set of (context,env) pairs that reference it
findUsage :: Bool -> Expr -> ExprContext -> EnvCtx -> FixDemandR x s e (Set (ExprContext, EnvCtx))
findUsage first expr@Var{varName=tname@TName{getName = name}} ctx env = do
  trace ("Looking for usages of " ++ show name ++ " in " ++ show ctx ++ " in env " ++ show env ++ " first " ++ show first) $ return ()
  let nameEq = (== name)
      empty = return S.empty
      childrenNoShadow tn =
        if first || tname `notElem` tn then childrenUsages else empty
      childrenUsages = do
        -- trace ("Looking for " ++ show name ++ " in " ++ show ctx ++ " in env " ++ show env) $ return ()
        visitChildrenCtxs S.unions ctx $ do 
          -- visitChildrenCtxs sets the currentContext
          childCtx <- currentContext <$> getEnv
          findUsage False expr childCtx env in
    case ctx of
      LetCDef _ _ _ i d -> childrenNoShadow [defTName $ defOfCtx ctx]
      LetCBody _ _ tn _ -> childrenNoShadow tn
      DefCNonRec _ _ _ d -> childrenNoShadow [defTName $ defOfCtx ctx]
      DefCRec _ _ tn _ _ -> childrenNoShadow tn
      LamCBody _ _ tn _ ->
        -- No adding an IndetCtx because we are starting our search in the body itself
        if first then childrenUsages
        -- No usages if the name is shadowed
        else if tname `elem` tn then 
          empty
        else
          visitChildrenCtxs S.unions ctx $ do
            childCtx <- currentContext <$> getEnv
            m <- contextLength <$> getEnv
            findUsage False expr childCtx (limitmenv (EnvCtx (IndetCtx tn ctx) env) m)
      ExprCBasic _ _ (Var{varName=TName{getName=name2}}) ->
        if nameEq name2 then do
          query <- getQueryString
          return $! trace (query ++ "Found usage in " ++ show ctx) $
            S.singleton (ctx, env)
        else
          -- trace ("Not found usage in " ++ show ctx ++ " had name " ++ show name2 ++ " expected " ++ show name) $ empty
          empty
      ModuleC{} -> do
        visitChildrenCtxs S.unions ctx $ do 
          -- visitChildrenCtxs sets the currentContext
          childCtx <- currentContext <$> getEnv
          findUsage first expr childCtx env 
      _ -> childrenUsages

doEval :: Query -> String -> FixDemandR x s e AbValue
doEval cq@(EvalQ (ctx, env)) query = do
   trace (query ++ show cq) $ do
    case maybeExprOfCtx ctx of
      Nothing -> return $ injErr "doEval: can't find expression"
      Just expr ->
        case expr of
          Lam{} -> -- LAM CLAUSE
            -- trace (query ++ "LAM: " ++ show ctx) $
            return $! injClosure ctx env
          v@(Var n _) | getName n == nameEffectOpen -> do -- TODO: Reevaluate eventually
            -- trace (query ++ "OPEN: " ++ show ctx) $ return []
            newId <- newContextId
            -- newLamId <- newContextId
            modCtx <- currentModContext <$> getEnv
            let tvar = TypeVar 0 (kindFun kindStar kindStar) Bound
                x = TName (newName "x") (TVar tvar) Nothing
                lamExpr = Lam [x] effectEmpty (Var x InfoNone)
                def = makeDef nameEffectOpen (TypeLam [tvar] lamExpr)
                newCtx = DefCNonRec newId modCtx [defTName def] (C.DefNonRec def)
                -- newLamCtx = LamCBody newLamId newCtx [x] lamExpr
            -- addChildrenContexts (contextId modCtx) [newCtx]
            -- addChildrenContexts (contextId newCtx) [newLamCtx]
            return $! injClosure newCtx (EnvTail TopCtx)
          v@(Var tn _) -> do -- REF CLAUSE
          -- TODO: Consider static overloading
            -- trace (query ++ "REF: " ++ show ctx) $ return []
    -- REF: 
    --  - When the binding is focused on a lambda body, we need to find the callers of the lambda, and proceed as original formulation. 
    --  - When the binding is in the context of a Let Body we can directly evaluate the let binding as the value of the variable being bound (indexed to match the binding).
    --  - When the binding is in the context of a Let binding, it evaluates to that binding or the indexed binding in a mutually recursive group 
    --  - When the binding is a top level definition - it evaluates to that definition 
    --  - When the binding is focused on a match body then we need to issue a sub-query for the evaluation of the match expression that contributes to the binding, 
    --         and then consider the abstract value and find all abstract values that match the pattern of the branch in question 
    --         and only consider the binding we care about. 
    --         This demonstrates one point where a context sensitive shape analysis could propagate more interesting information along with the sub-query to disregard traces that don’t contribute
            -- trace (query ++ "REF: " ++ show ctx) $ return []
            let binded = bind ctx v env
            -- trace (query ++ "REF: " ++ show tn ++ " bound to " ++ show binded) $ return []
            case binded of
              Just ((lambodyctx@LamCBody{}, bindedenv), Just index) -> do
                calls <- qcall (lambodyctx, bindedenv)
                doForClosures emptyAbValue calls (\(appctx, appenv) -> do
                  -- trace (query ++ "REF: found application " ++ showSimpleContext appctx ++ " " ++ showSimpleEnv appenv ++ " param index " ++ show index) $ return []
                  param <- focusParam (Just index) appctx
                  doMaybeAbValue emptyAbValue param (\param -> qeval (param, appenv)))
              Just ((letbodyctx@LetCBody{}, bindedenv), index) -> do
                param <- focusChild (fromJust $ contextOf letbodyctx) (fromJust index)
                doMaybeAbValue emptyAbValue param (\ctx -> qeval (ctx, bindedenv))
              Just ((letdefctx@LetCDef{}, bindedenv), index) -> do
                param <- focusChild (fromJust $ contextOf letdefctx) (fromJust index)
                doMaybeAbValue emptyAbValue param (\ctx -> qeval (ctx, bindedenv))
              Just ((CaseCBranch _ c _ _ (Branch pat guard), bindedenv), index) -> do
                mscrutinee <- focusChild c 0
                case mscrutinee of
                  Nothing -> return $! injErr $ "REF: can't find scrutinee of case " ++ show ctx
                  Just scrutinee -> evalPatternRef scrutinee bindedenv (head pat) tn
              Just ((modulectx@ModuleC{}, bindedenv), index) -> do
                lamctx <- getTopDefCtx modulectx (getName tn)
                -- Evaluates just to the lambda
                qeval (lamctx, EnvTail TopCtx)
              Just ((defctx@DefCNonRec{}, bindedenv), Just index) -> do
                calls <- qcall (defctx, bindedenv)
                doForClosures emptyAbValue calls (\(appctx, appenv) -> do
                  -- trace (query ++ "REF: found application " ++ showSimpleContext appctx ++ " " ++ showSimpleEnv appenv ++ " param index " ++ show index) $ return []
                  param <- focusParam (Just index) appctx
                  doMaybeAbValue emptyAbValue param (\param -> qeval (param, appenv)))
              Just ((ctxctx, bindedenv), index) -> do
                children <- childrenContexts ctxctx
                let msg = query ++ "REF: unexpected context in result of bind: " ++ show v ++ " " ++ show ctxctx ++ " children: " ++ show children
                trace msg $ return $! injErr msg
              Nothing -> do
                ext <- bindExternal v
                case ext of
                  Just (modulectx@ModuleC{}, index) -> do
                    lamctx <- getTopDefCtx modulectx (getName tn)
                    -- Evaluates just to the lambda
                    qeval (lamctx, EnvTail TopCtx)
                  _ -> return $! injErr $ "REF: can't find what the following refers to " ++ show ctx
          App (TypeApp (Con nm repr) _) args -> do
            trace (query ++ "APPCon: " ++ show ctx) $ return []
            children <- childrenContexts ctx
            return $ injCon nm (conTypeName repr) (tail children) env
          App (Con nm repr) args -> do
            trace (query ++ "APPCon: " ++ show ctx) $ return []
            children <- childrenContexts ctx
            return $ injCon nm (conTypeName repr) children env
          App f tms -> do
            trace (query ++ "APP: " ++ show ctx) $ return []
            fun <- focusChild ctx 0
            doMaybeAbValue emptyAbValue fun (\fun -> do
                -- trace (query ++ "APP: Lambda Fun " ++ show fun) $ return []
                lamctx <- qeval (fun, env)
                doForClosures emptyAbValue lamctx (\(lam, lamenv) -> do
                  -- trace (query ++ "APP: Lambda is " ++ show lamctx) $ return []
                  bd <- focusBody lam
                  doMaybeAbValue emptyAbValue bd (\bd -> do
                    -- trace (query ++ "APP: Lambda body is " ++ show lamctx) $ return []
                    childs <- childrenContexts ctx
                    -- In the subevaluation if a binding for the parameter is requested, we should return the parameter in this context, 
                    succ <- succAEnv ctx env
                    let newEnv = EnvCtx succ lamenv
                    result <- qeval (bd, newEnv)
                    qeval (bd, newEnv)
                    )
                  )
              )
          TypeApp{} ->
            trace (query ++ "TYPEAPP: " ++ show ctx) $
            case ctx of
              DefCNonRec{} -> return $! injClosure ctx env
              DefCRec{} -> return $! injClosure ctx env
              _ -> do
                ctx' <- focusChild ctx 0
                doMaybeAbValue emptyAbValue ctx' (\ctx -> qeval (ctx,env))
          TypeLam{} ->
            trace (query ++ "TYPE LAM: " ++ show ctx) $
            case ctx of
              DefCNonRec{} -> return $! injClosure ctx env-- Don't further evaluate if it is just the definition / lambda
              DefCRec{} -> return $! injClosure ctx env-- Don't further evaluate if it is just the definition / lambda
              _ -> do
                ctx' <- focusChild ctx 0
                doMaybeAbValue emptyAbValue ctx' (\ctx -> qeval (ctx,env))
          Lit l -> return $! injLit l env
          Let defs e -> do
            trace (query ++ "LET: " ++ show ctx) $ return []
            ex <- focusChild ctx 0 -- Lets have their return expression as first child
            doMaybeAbValue emptyAbValue ex (\ex -> qeval (ex, env))
          Case expr branches -> do
            trace (query ++ "CASE: " ++ show ctx) $ return []
            e <- focusChild ctx 0
            doMaybeAbValue emptyAbValue e (\e -> do
                scrutinee <- qeval (e, env)
                -- trace (query ++ "CASE: scrutinee is " ++ showNoEnvAbValue scrutinee) $ return []
                -- return emptyAbValue
                res <- doForConstructors emptyAbValue scrutinee (\(cenv, con) -> do
                    -- trace (query ++ "CASE: Looking for branch matching " ++ show con) $ return ()
                    branches <- findBranch con ctx cenv
                    -- trace (query ++ "CASE: branches are " ++ show branches) $ return []
                    -- TODO: Consider just the first branch that matches? Need to make sure that works with approximation
                    foldM (\acc branch -> do
                        res <- qeval (branch, cenv)
                        return $! join acc res
                      ) emptyAbValue branches
                  )
                -- trace (query ++ "CASE: result is " ++ show res) $ return []
                res' <- doForLits res scrutinee (\(cenv, lit) -> do
                    branches <- findBranchLit lit ctx
                    -- trace (query ++ "CASE: branches' are " ++ show branches) $ return []
                    foldM (\acc branch -> do
                        res <- qeval (branch, cenv)
                        return $! join acc res
                      ) emptyAbValue branches
                    )
                -- trace (query ++ "CASE: result' is " ++ show res') $ return []
                if res' == emptyAbValue then
                  return $ injErr $ "No branches matched in case statement:\n\n" ++ show (exprOfCtx ctx)
                else return res'
              )
          Con nm repr -> return $! injCon nm (conTypeName repr) [] env -- TODO: Check that the constructor is a singleton

--------------------------------- PATTERN EVALUATION HELPERS -----------------------------------------------
evalPatternRef :: ExprContext -> EnvCtx -> Pattern -> TName -> FixDemandR x s e AbValue
evalPatternRef expr env pat tname = do
  case pat of
    PatVar tn pat' ->
      if tn == tname then qeval (expr, env)
      else evalPatternRef expr env pat' tname
    PatLit{} -> return emptyAbValue
    PatWild{} -> qeval (expr, env)
    PatCon{patConName=name, patConPatterns=pats} -> do
      exprV <- qeval (expr, env)
      doForConstructors emptyAbValue exprV (\(cenv, con) ->
          if constrName con /= name then
            return emptyAbValue
          else do
            let x = selectPatternExpr (constrParams con) pats tname
            case x of
              Nothing -> return emptyAbValue
              Just (pat, expr) -> evalPatternRef expr cenv pat tname
        )

matchesPattern :: ConstrContext -> Pattern -> Maybe (EnvCtx, [ExprContext], [Pattern])
matchesPattern cc pat =
  -- trace ("Matching " ++ show pat ++ " against " ++ show cc) $
  case pat of
    PatCon{patConName} ->
      if patConName == constrName cc then -- trace "Found constr" 
        Just (constrEnv cc, constrParams cc, patConPatterns pat)
      else Nothing
    PatVar _ p -> matchesPattern cc p
    PatWild -> Just (constrEnv cc, constrParams cc, [])
    _ -> Nothing

matchesPatternCtx :: ConstrContext -> Pattern -> FixDemandR x s e Bool
matchesPatternCtx cc pat = do
  let childMatches = matchesPattern cc pat
  case childMatches of
    Just (_, _, []) -> return True -- No need to evaluate further (Pattern is a wildcard)
    Just (env, cp, xs) -> matchesPatternsCtx cp xs env
    Nothing -> return False

findPath :: [Pattern] -> TName -> Maybe Int
findPath pats tname =
  findIndex (\pat ->
    case pat of
      PatVar tn p -> tname == tn || isJust (findPath [p] tname)
      PatCon{patConPatterns = patterns} -> isJust $ findPath patterns tname
      _ -> False
    ) pats

selectPatternExpr :: [ExprContext] -> [Pattern] -> TName -> Maybe (Pattern, ExprContext)
selectPatternExpr expr pats tname = do
  path <- findPath pats tname
  return (pats !! path, expr !! path)

matchesPatternsCtx :: [ExprContext] -> [Pattern] -> EnvCtx -> FixDemandR x s e Bool
matchesPatternsCtx childrenCC pats env = do
  childrenEval <- mapM (\cc -> qeval (cc, env)) childrenCC
  res <- zipWithM (\abv subPat -> do
    litMatch <- doForLitsJoin True abv (&&) (\(cenv, lit) -> return $ isJust $ matchesPatternLit lit subPat)
    conMatch <- doForConstructorsJoin True abv (&&) (\(cenv, con) -> matchesPatternCtx con subPat)
    return $ litMatch || conMatch) childrenEval pats
  return $ and res

matchesPatternLit :: LiteralContext -> Pattern -> Maybe [Pattern]
matchesPatternLit litc pat =
  case pat of
    PatLit{} | pat `patSubsumed` litc -> Just []
    PatVar _ p -> matchesPatternLit litc p
    PatWild -> Just []
    _ -> Nothing

patSubsumed :: Pattern -> LiteralContext -> Bool
patSubsumed (PatLit (LitInt i)) (LiteralContext (LSingle x) _ _ _) = i == x
patSubsumed (PatLit (LitFloat i)) (LiteralContext _ (LSingle x) _ _) = i == x
patSubsumed (PatLit (LitChar i)) (LiteralContext _ _ (LSingle x) _) = i == x
patSubsumed (PatLit (LitString i)) (LiteralContext _ _ _ (LSingle x)) = i == x
patSubsumed (PatLit (LitInt i)) (LiteralContext LTop _ _ _) = True
patSubsumed (PatLit (LitFloat i)) (LiteralContext _ LTop _ _) = True
patSubsumed (PatLit (LitChar i)) (LiteralContext _ _ LTop _) = True
patSubsumed (PatLit (LitString i)) (LiteralContext _ _ _ LTop) = True
patSubsumed _ _ = False

findBranchLit :: LiteralContext -> ExprContext -> FixDemandR x s e [ExprContext]
findBranchLit litc ctx = do
  let Case e branches = exprOfCtx ctx
  children <- childrenContexts ctx
  let childMatches = zipWith (\i (Branch [p] _ ) -> case matchesPatternLit litc p of {Just x -> Just (x, i); Nothing -> Nothing}) [0..] branches
  case catMaybes childMatches of
    [] -> return []
    [([], i)] -> return [children !! (i + 1)] -- +1 to skip the scrutinee
    matches -> do -- Many, should never happen
      return []

findBranch :: ConstrContext -> ExprContext -> EnvCtx -> FixDemandR x s e [ExprContext]
findBranch cc ctx env = do
  let Case e branches = exprOfCtx ctx
  children <- childrenContexts ctx
  let childMatches = catMaybes $ zipWith (\i (Branch [p] _ ) -> case matchesPattern cc p of {Just x -> Just (x, i); Nothing -> Nothing}) [0..] branches
  -- trace ("Found matching branch patterns " ++ show childMatches) $ return ()
  case childMatches of
    [] -> return []
    [((_, _, _), i)] -> -- trace ("matching expr context" ++ show (children !! (i + 1))) 
      return [children !! (i + 1)] -- +1 to skip the scrutinee
    matches -> do -- Many, need to evaluate sub-pieces and match nested sub-expressions
      res <- mapM (\((env, cp, pats), i) -> do
          x <- matchesPatternsCtx cp pats env
          return $ if x then Just i else Nothing
        ) matches
      case catMaybes res of
        [] -> return []
        xs -> return $ map (\i -> children !! (i + 1)) xs -- +1 to skip the scrutinee
      return []

newErrTerm :: String -> FixDemandR x s e [(ExprContext, EnvCtx)]
newErrTerm s = do
  newId <- newContextId
  return [(ExprCTerm newId ("Error: " ++ s), EnvTail CutUnknown)]

doExpr :: Query -> String -> FixDemandR x s e AbValue
doExpr cq@(ExprQ (ctx,env)) query = do
  trace (query ++ show cq) $ do
    case ctx of
      AppCLambda _ c e -> -- RATOR Clause
        -- trace (query ++ "OPERATOR: Application is " ++ showCtxExpr c) $
        return $ injClosure c env
      AppCParam _ c index e -> do -- RAND Clause 
        -- trace (query ++ "OPERAND: Expr is " ++ showCtxExpr ctx) $ return []
        fn <- focusFun c
        case fn of
          Just fn -> do
            -- trace (query ++ "OPERAND: Evaluating To Closure " ++ showCtxExpr fn) $ return []
            ctxlam <- qeval (fn, env)
            doForClosures emptyAbValue ctxlam (\(lam, lamenv) -> do
              -- trace (query ++ "OPERAND: Closure is: " ++ showCtxExpr lam) $ return []
              bd <- focusBody lam
              case bd of
                Nothing -> return emptyAbValue
                Just bd -> do
                  -- trace (query ++ "OPERAND: Closure's body is " ++ showCtxExpr bd) $ return ()
                  -- trace (query ++ "OPERAND: Looking for usages of operand bound to " ++ show (lamVar index lam)) $ return []
                  succ <- succAEnv c env
                  m <- contextLength <$> getEnv
                  ctxs <- findUsage True (lamVar index lam) bd (EnvCtx succ lamenv)
                  -- trace (query ++ "RAND: Usages are " ++ show ctxs) $ return []
                  ress <- mapM qexpr (S.toList ctxs)
                  let result = Prelude.foldl join emptyAbValue ress
                  -- trace (query ++ "OPERAND RESULT: Callers of operand bound to are " ++ show result) $ return []
                  return result
              )
          Nothing -> return emptyAbValue
      LamCBody _ _ _ e -> do -- BODY Clause
        -- trace (query ++ "BODY: Looking for locations the returned closure is called " ++ show ctx) $ return []
        res <- qcall (ctx, env)
        -- trace (query ++ "BODY RESULT: Callers of returned closure are " ++ show res) $ return []
        ress <- mapM qexpr (S.toList $ closures res)
        let result = Prelude.foldl join emptyAbValue ress
        -- trace (query ++ "BODY RESULT: Callers of returned closure are " ++ show result) $ return []
        return result
      ExprCTerm{} ->
        -- trace (query ++ "ends in error " ++ show ctx)
        -- return [(ctx, env)]
        return $ injErr $ "Exprs led to ExprCTerm" ++ show ctx
      DefCNonRec _ c index _ -> do
        trace (query ++ "DEF NonRec: Env is " ++ show env) $ return []
        let df = defOfCtx ctx
        ctxs <- case c of
          LetCDef{} -> do
            trace (query ++ "DEF NonRec: In let binding " ++ show c++ " looking for usages of " ++ show (lamVarDef df)) $ return ()
            findUsage True (lamVarDef df) (fromJust $ contextOf c) env
          _ -> do
            trace (query ++ "DEF NonRec: In other binding " ++ show c ++ " looking for usages of " ++ show (lamVarDef df)) $ return ()
            findUsage True (lamVarDef df) c env
        -- trace (query ++ "DEF: Usages are " ++ show ctxs) $ return []
        ress <- mapM qexpr (S.toList ctxs)
        let result =  Prelude.foldl join emptyAbValue ress
        -- trace (query ++ "DEF: Calls are " ++ show result) $ return []
        return result
      DefCRec _ c _ _ _ -> do
        trace (query ++ "DEF Rec: Env is " ++ show env) $ return []
        let df = defOfCtx ctx
        ctxs <- case c of
          LetCDef{} -> do
            trace (query ++ "DEF Rec: In let binding " ++ show c++ " looking for usages of " ++ show (lamVarDef df)) $ return ()
            findUsage True (lamVarDef df) (fromJust $ contextOf c) env
          _ -> do
            trace (query ++ "DEF Rec: In other binding " ++ show c ++ " looking for usages of " ++ show (lamVarDef df)) $ return ()
            findUsage True (lamVarDef df) c env
        -- trace (query ++ "DEF: Usages are " ++ show ctxs) $ return []
        ress <- mapM qexpr (S.toList ctxs)
        let result =  Prelude.foldl join emptyAbValue ress
        -- trace (query ++ "DEF: Calls are " ++ show result) $ return []
        return result
      ExprCBasic _ c _ -> qexpr (c, env)
      _ ->
        case contextOf ctx of
          Just c ->
            case enclosingLambda c of
              Just c' -> qexpr (c', env)
              _ -> return $ injErr $ "Exprs has no enclosing lambda, so is always demanded (top level?) " ++ show ctx
          Nothing -> return $ injErr $ "expressions where " ++ show ctx ++ " is demanded (should never happen)"

doCall :: Query -> String -> FixDemandR x s e AbValue
doCall cq@(CallQ(ctx, env)) query =
  trace (query ++ show cq) $ do
      case ctx of
          LamCBody _ c _ _-> do
            kind <- analysisKind <$> getEnv
            case kind of
              BasicEnvs -> do
                let cc0 = envhead env
                    p = envtail env
                calls <- qexpr (c, p)
                doForClosures emptyAbValue calls (\(callctx, callenv) -> do
                    m <- contextLength <$> getEnv
                    cc1 <- succAEnv callctx callenv
                    if cc1 == cc0 then
                      trace (query ++ "KNOWN CALL: " ++ showSimpleCtx cc1 ++ " " ++ showSimpleCtx cc0)
                      return $! injClosure callctx callenv
                    else if cc0 `subsumesCtx` cc1 then do
                      trace (query ++ "UNKNOWN CALL: " ++ showSimpleCtx cc1 ++ " " ++ showSimpleCtx cc0) $ return ()
                      instantiate query (EnvCtx cc1 p) env
                      return emptyAbValue
                    else do
                      trace (query ++ "CALL IS NOT SUBSUMED:") $ return () -- \n\nFIRST:" ++ show cc1 ++ "\n\nSECOND:" ++ show cc0) $ return ()
                      return emptyAbValue
                  )
              LightweightEnvs -> do
                -- Lightweight Version
                case envhead env of
                  (CallCtx callctx p') -> do
                    trace (query ++ "Known: " ++ show callctx) $ return ()
                    pnew <- calibratem p'
                    return $ injClosure callctx pnew
                  _ -> do
                    trace (query ++ "Unknown") $ return ()
                    qexpr (c, envtail env)
          _ -> return $ injErr $ "CALL not implemented for " ++ show ctx


--------------------------------------- ExprContext Helpers -------------------------------------

allModules :: Loaded -> [Module]
allModules loaded = loadedModule loaded : loadedModules loaded

getTopDefCtx :: ExprContext -> Name -> FixDemandR x s e ExprContext
getTopDefCtx ctx name = do
  children <- childrenContexts ctx
  case find (\dctx -> case dctx of
      DefCNonRec{} | defName (defOfCtx dctx) == name -> True
      DefCRec{} | defName (defOfCtx dctx) == name -> True
      _ -> False
      ) children of
    Just dctx -> do
      -- lamctx <- focusChild dctx 0 -- Actually focus the lambda
      return dctx
    Nothing -> error $ "getTopDefCtx: " ++ show ctx ++ " " ++ show name

getModule :: Name -> FixDemandR x s e Module
getModule name = do
  deps <- loadedModules . loaded <$> getState
  let x = find (\m -> modName m == name) deps
  case x of
    Just mod -> return mod
    _ -> error $ "getModule: " ++ show name

addChildrenContexts :: ExprContextId -> [ExprContext] -> FixDemandR x s e ()
addChildrenContexts parentCtx contexts = do
  state <- getState
  let newIds = map contextId contexts
      newChildren = M.insert parentCtx (S.fromList newIds) (childrenIds state)
   -- trace ("Adding " ++ show childStates ++ " previously " ++ show (M.lookup parentCtx (childrenIds state))) 
  setState state{childrenIds = newChildren}

newContextId :: FixDemandR x s e ExprContextId
newContextId = do
  state <- getState
  id <- currentContext <$> getEnv
  let newCtxId = maxContextId state + 1
  updateState (\s -> s{maxContextId = newCtxId})
  return $! ExprContextId newCtxId (moduleName (contextId id))

newModContextId :: Module -> FixDemandR x s e ExprContextId
newModContextId mod = do
  state <- getState
  let newCtxId = maxContextId state + 1
  updateState (\s -> s{maxContextId = newCtxId})
  return $! ExprContextId newCtxId (modName mod)

addContextId :: (ExprContextId -> ExprContext) -> FixDemandR x s e ExprContext
addContextId f = do
  newId <- newContextId
  state <- getState
  let x = f newId
  setState state{states=M.insert newId x (states state)}
  return x

childrenOfExpr :: ExprContext -> Expr -> FixDemandR x s e [ExprContext]
childrenOfExpr ctx expr =
  case expr of
    Lam names eff e -> addContextId (\newId -> LamCBody newId ctx names e) >>= single
    App f vs -> do
      x <- addContextId (\newId -> AppCLambda newId ctx f )
      rest <- zipWithM (\i x -> addContextId (\newId -> AppCParam newId ctx i x)) [0..] vs
      return $! x : rest
    Let defs result -> do
      let defNames = map defTName (concatMap defsOf defs)
      defs <- zipWithM (\i x -> addContextId (\newId -> LetCDef newId ctx defNames i x)) [0..] defs
      result <- addContextId (\newId -> LetCBody newId ctx defNames result)
      return $! result:defs
    Case exprs branches -> do
      match <- addContextId (\newId -> CaseCMatch newId ctx (head exprs))
      branches <- zipWithM (\i x -> addContextId (\newId -> CaseCBranch newId ctx (branchVars x) i x)) [0..] branches
      return $! match : branches
    Var name info -> addContextId (\newId -> ExprCBasic newId ctx expr ) >>= single
    TypeLam tvars expr -> childrenOfExpr ctx expr
    TypeApp expr tps -> childrenOfExpr ctx expr
    Con name repr -> addContextId (\newId -> ExprCBasic newId ctx expr) >>= single
    Lit lit -> addContextId (\newId -> ExprCBasic newId ctx expr) >>= single
  where single x = return [x]

childrenOfDef :: ExprContext -> C.DefGroup -> FixDemandR x s e [ExprContext]
childrenOfDef ctx def =
  case def of
    C.DefNonRec d -> addContextId (\newId -> DefCNonRec newId ctx [defTName d] def) >>= (\x -> return [x])
    C.DefRec ds -> zipWithM (\i d -> addContextId (\newId -> DefCRec newId ctx (map defTName ds) i def)) [0..] ds

childrenContexts :: ExprContext -> FixDemandR x s e [ExprContext]
childrenContexts ctx = do
  withEnv (\env -> env{currentContext = ctx, currentModContext = case ctx of {ModuleC{} -> ctx; _ -> currentModContext env}}) $ do
    let parentCtxId = contextId ctx
    children <- childrenIds <$> getState
    let childIds = M.lookup parentCtxId children
    case childIds of
      Nothing -> do
          -- trace ("No children for " ++ show ctx) $ return ()
          newCtxs <- case ctx of
                ModuleC _ mod _ -> do
                  res <- mapM (childrenOfDef ctx) (coreProgDefs $ modCoreNoOpt mod)
                  return $! concat res
                DefCRec _ _ _ _ d -> childrenOfExpr ctx (exprOfCtx ctx)
                DefCNonRec _ _ _ d -> childrenOfExpr ctx (exprOfCtx ctx)
                LamCBody _ _ names body -> childrenOfExpr ctx body
                AppCLambda _ _ f -> childrenOfExpr ctx f
                AppCParam _ _ _ param -> childrenOfExpr ctx param
                LetCDef _ _ _ i defg -> childrenOfExpr ctx (exprOfCtx ctx)
                LetCBody _ _ _ e -> childrenOfExpr ctx e
                CaseCMatch _ _ e -> childrenOfExpr ctx e
                CaseCBranch _ _ _ _ b -> do
                  x <- mapM (childrenOfExpr ctx . guardExpr) $ branchGuards b -- TODO Better context for branch guards
                  return $! concat x
                ExprCBasic{} -> return []
                ExprCTerm{} -> return []
          addChildrenContexts parentCtxId newCtxs
          return newCtxs
      Just childIds -> do
        -- trace ("Got children for " ++ show ctx ++ " " ++ show childIds) $ return ()
        states <- states <$> getState
        return $! map (states M.!) (S.toList childIds)

visitChildrenCtxs :: ([a] -> a) -> ExprContext -> FixDemandR x s e a -> FixDemandR x s e a
visitChildrenCtxs combine ctx analyze = do
  children <- childrenContexts ctx
  -- trace ("Got children of ctx " ++ show ctx ++ " " ++ show children) $ return ()
  res <- mapM (\child -> withEnv (\e -> e{currentContext = child}) analyze) children
  return $! combine res

--------------------------- CONVERTING RESULTS TO HUMAN READABLE STRINGS AND RUNNING THE QUERIES -----------------------------------------

toSynConstr :: ConstrContext -> FixDemandR x s e (Maybe String)
toSynConstr (ConstrContext nm tp args env) = do
  args' <- mapM findSourceExpr args
  return (Just $ nameId (getName nm))

sourceEnv :: EnvCtx -> FixDemandR x s e String
sourceEnv (EnvCtx env tail) = do
  envs <- sourceEnvCtx env
  envt <- sourceEnv tail
  return $ envs ++ ":::" ++ envt
sourceEnv (EnvTail env) = sourceEnvCtx env

sourceEnvCtx :: Ctx -> FixDemandR x s e String
sourceEnvCtx ctx =
  case ctx of
    IndetCtx tn c -> return $ "?" ++ intercalate "," (map show tn)
    TopCtx -> return "Top"
    CutKnown -> return "~!~"
    CutUnknown -> return "~?~"
    CallCtx c env -> do
      se <- findSourceExpr c
      e <- sourceEnv env
      return $ case se of
        (Just se, _) -> showSyntax 0 se ++ " <<" ++ e ++ ">>"
        (_, Just de) -> showSyntaxDef 0 de ++ " <<" ++ e ++ ">>"
        _ -> show c ++ " " ++ e
    BCallCtx c cc -> do
      se <- findSourceExpr c
      e <- sourceEnvCtx cc
      return $ case se of
        (Just se, _) -> showSyntax 0 se ++ " " ++ e
        (_, Just de) -> showSyntaxDef 0 de ++ " " ++ e
        _ -> show c ++ " " ++ e

findSourceExpr :: ExprContext -> FixDemandR x s e (Maybe UserExpr, Maybe (Syn.Def UserType))
findSourceExpr ctx =
  case maybeExprOfCtx ctx of
    Just (Lam (n:_) _ _) -> findForName n
    Just (TypeLam _ (Lam (n:_) _ _)) -> findForName n
    Just (App (Var tn _) _) -> findForApp tn
    _ ->
      case ctx of
        DefCNonRec _ _ _ d -> findDef (defOfCtx ctx)
        DefCRec _ _ _ _ d -> findDef (defOfCtx ctx)
        LetCDef _ _ _ i d -> findDef (defOfCtx ctx)
        _ ->
          trace ("Unknown lambda type " ++ show ctx ++ ": " ++ show (maybeExprOfCtx ctx)) $ return (Nothing, Nothing)
  where
    findDef d = do
      -- return $! Just $! Syn.Var (defName d) False (defNameRange d)
      program <- modProgram <$> getModule (moduleName $ contextId ctx)
      case (program, C.defNameRange d) of
        (Just prog, rng) -> -- trace ("Finding location for " ++ show rng ++ " " ++ show ctx) $ 
          return (Nothing, findDefFromRange prog rng)
        _ -> trace ("No program or rng" ++ show d ++ " " ++ show program) $ return (Nothing, Nothing)
      -- case (program, defNameRange d) of
      --   (Just prog, rng) -> trace ("Finding location for " ++ show rng ++ " " ++ show ctx ++ " in module " ++ show (moduleName $ contextId ctx)) $ return $! findLocation prog rng
      --   _ -> trace ("No program or rng" ++ show (defName d) ++ " " ++ show program) $ return Nothing
    findForName n = do
      program <- modProgram <$> getModule (moduleName $ contextId ctx)
      case (program, originalRange n) of
        (Just prog, Just rng) -> -- trace ("Finding location for " ++ show rng ++ " " ++ show ctx) $ 
          return (findLambdaFromRange prog rng, Nothing)
        _ -> trace ("No program or rng" ++ show n ++ " " ++ show program) $ return (Nothing, Nothing)
    findForApp n = do
      program <- modProgram <$> getModule (moduleName $ contextId ctx)
      case (program, originalRange n) of
        (Just prog, Just rng) -> -- trace ("Finding application location for " ++ show rng ++ " " ++ show ctx) $ 
          return (findApplicationFromRange prog rng, Nothing)
        _ -> trace ("No program or rng" ++ show n ++ " " ++ show program) $ return (Nothing, Nothing)

getAbResult :: (EnvCtx, AbValue) -> FixDemandR x s e (EnvCtx, ([UserExpr], [UserDef], [Syn.Lit], [String], Set Type, Set String))
getAbResult (envctx, res) = do
  let vals = [res]
      lams = map fst $ concatMap (S.toList . closures) vals
      i = concatMap ((mapMaybe toSynLit . M.elems) . intV) vals
      f = concatMap ((mapMaybe toSynLitD . M.elems) . floatV) vals
      c = concatMap ((mapMaybe toSynLitC . M.elems) . charV) vals
      s = concatMap ((mapMaybe toSynLitS . M.elems) . stringV) vals
      topTypes = unions $ map topTypesOf vals
      vs = i ++ f ++ c ++ s
      cs = concatMap S.toList $ concatMap (M.elems . constrs) vals
      errs = S.fromList $ mapMaybe err vals
  consts <- mapM toSynConstr cs
  sourceLams <- mapM findSourceExpr lams
  let (sourceLambdas, sourceDefs) = unzip sourceLams
  return $ trace ("eval result:\n----------------------\n" ++ showSimpleAbValue res ++ "\n----------------------\n") (envctx, (catMaybes sourceLambdas, catMaybes sourceDefs, vs, catMaybes consts, topTypes, errs))

runEvalQueryFromRangeSource :: Loaded -> (Module -> IO Module) -> (Range, RangeInfo) -> Module -> ([(EnvCtx, ([UserExpr], [UserDef], [Syn.Lit], [String], Set Type, Set String))], Loaded)
runEvalQueryFromRangeSource ld loadModuleFromSource rng mod =
  let (r, lattice, Just x) = runQueryAtRange ld loadModuleFromSource rng mod $ \exprctxs ->
        case exprctxs of
          exprctx:rst -> do
            trace ("evaluating " ++ show exprctx) $ return ()
            ress <- fixedEval exprctx (indeterminateStaticCtx exprctx)
            res' <- mapM getAbResult ress
            loaded1 <- loaded <$> getState
            setResult (res', loaded1)
          _ ->
            setResult ([(EnvTail CutUnknown, ([],[],[],[],S.empty,S.empty))], ld)
  in trace (show lattice) x


runQueryAtRange :: Loaded -> (Module -> IO Module) -> (Range, RangeInfo) -> Module -> ([ExprContext] -> FixDemand x () ()) -> (FixOutput, (M.Map FixInput (BasicLattice AFixOutput)), Maybe x)
runQueryAtRange loaded loadModuleFromSource (r, ri) mod query =
  let cid = ExprContextId (-1) (modName mod)
      modCtx = ModuleC cid mod (modName mod)
      focalContext = analyzeCtx (\parentRes childRes -> case concat childRes of {x:_ -> [x]; _ -> parentRes}) (const $ findContext r ri) modCtx
      result = runFix (focalContext >>= query) (DEnv 1 BasicEnvs modCtx modCtx (EnvTail TopCtx)  "" "" loadModuleFromSource ()) (State loaded M.empty 0 M.empty 0 Nothing ())
  in case result of
    (a, b, s) -> (a, b, finalResult s)

findContext :: Range -> RangeInfo -> FixDemandR x s e [ExprContext]
findContext r ri = do
  ctx <- currentContext <$> getEnv
  case ctx of
    ExprCBasic _ _ (Var (TName _ _ (Just rng)) _) | r `rangesOverlap` rng -> trace ("found overlapping range " ++ showFullRange rng ++ " " ++ show ctx) $ return [ctx]
    ExprCBasic _ _ (Var (TName _ _ (Just rng)) _) -> -- trace ("var range doesn't overlap "++ show ctx ++ " " ++ showFullRange rng) $
      return []
    LetCDef _ _ _ i dg -> fromNames ctx [defTName (defsOf dg !! i)]
    -- Hovering over a lambda parameter should query what values that parameter can evaluate to -- need to create an artificial Var expression
    LamCBody _ _ tnames _ -> fromNames ctx tnames
    CaseCBranch _ _ tnames _ _ -> fromNames ctx tnames
    _ -> return []
  where fromNames ctx tnames =
          case mapMaybe (\tn -> (case fmap (rangesOverlap r) (originalRange tn) of {Just True -> Just tn; _ -> Nothing})) tnames of
              [tn] -> do
                id <- newContextId
                return [ExprCBasic id ctx (Var tn InfoNone)]
              _ -> return []

analyzeCtx :: (a -> [a] -> a) -> (ExprContext -> FixDemandR x s e a) -> ExprContext -> FixDemandR x s e a
analyzeCtx combine analyze ctx = do
  -- id <- currentContext <$> getEnv
  -- trace ("Analyzing ctx " ++ show ctx ++ " with id " ++ show (exprId id)) $ return ()
  res <- analyze ctx
  visitChildrenCtxs (combine res) ctx $ do
    childCtx <- currentContext <$> getEnv
    analyzeCtx combine analyze childCtx