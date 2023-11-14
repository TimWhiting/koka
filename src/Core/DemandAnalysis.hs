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
{-# LANGUAGE BangPatterns #-}

module Core.DemandAnalysis(
                          AbstractLattice(..),
                          ExprContext(..),
                          runEvalQueryFromRange,
                          runEvalQueryFromRangeSource,
                        ) where

import Control.Monad hiding (join)
import Common.Name
import Data.Set as S hiding (findIndex, filter, map)
import Core.Core as C
import Core.StaticContext
import Core.AbstractValue
import qualified ListT as L
-- import Debug.Trace (trace)
import Core.Pretty
import Type.Type (isTypeInt, isTypeInt32, Type (..), expandSyn, TypeCon (..), ConInfo (..), Flavour (Bound), TypeVar (TypeVar), effectEmpty)
import Data.Sequence (mapWithIndex, fromList)
import qualified Data.Sequence as Seq
import Data.Maybe (mapMaybe, isJust, fromJust, maybeToList, fromMaybe, catMaybes)
import Data.List (find, findIndex, elemIndex, union, intercalate)
import Debug.Trace
import Compiler.Module (Loaded (..), Module (..), ModStatus (LoadedIface), addOrReplaceModule)
import Lib.PPrint (Pretty(..))
import Type.Pretty (ppType, defaultEnv, Env (..))
import Kind.Kind (Kind(..), kindFun, kindStar)
import Control.Monad.Trans
import ListT (ListT)
import Common.Range (Range, rangesOverlap, showFullRange, rangeNull)
import Syntax.RangeMap (RangeInfo)
import Common.NamePrim (nameOpen, nameEffectOpen)
import Core.CoreVar
import GHC.IO (unsafePerformIO)
import Syntax.Syntax (UserExpr, UserProgram, UserDef, Program (..), DefGroups, UserType, DefGroup (..), Def (..), ValueBinder (..), UserValueBinder)
import qualified Syntax.Syntax as Syn
import qualified Data.Map.Strict as M

newtype AEnv a = AEnv (DEnv -> State -> Result a)
data State = State{
  loaded :: Loaded,
  states :: M.Map ExprContextId ExprContext,
  maxContextId:: Int,
  childrenIds :: M.Map ExprContextId (Set ExprContextId),
  evalCacheGeneration :: Int,
  memoCache :: M.Map String (M.Map ExprContextId (EnvCtxLattice AbValue)),
  instantiateCache :: Set (Query, Ctx, Ctx),
  reachable :: M.Map Query (Set Query),
  unique :: Int
}
data Result a = Ok a State

data DEnv = DEnv{
  contextLength :: Int,
  basicEnvs :: Bool,
  currentContext :: !ExprContext,
  currentEnv:: EnvCtx,
  currentQuery:: String,
  queryIndentation:: String,
  loadModuleFromSource :: Module -> IO Module
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

instance MonadFail AEnv where
  fail _ = error "fail"

withEnv :: (DEnv -> DEnv) -> AEnv a -> AEnv a
withEnv f (AEnv c)
  = AEnv (c . f)

getEnv :: AEnv DEnv
getEnv = AEnv Ok

getState :: AEnv State
getState = AEnv (\env st -> Ok st st)

setState :: State -> AEnv ()
setState st = AEnv (\env _ -> Ok () st)

paramIndex e =
  case e of
    AppCParam _ _ i _ -> i

focusParam :: Maybe Int -> ExprContext -> AEnv (Maybe ExprContext)
focusParam index e = do
  children <- childrenContexts e
  query <- getQueryString
  return $ case index of
    Just x | x + 1 < length children -> Just $ children !! (x + 1) -- Parameters are the not the first child of an application (that is the function)
    _ -> trace (query ++ "Children looking for param " ++ show children ++ " in " ++ show e ++ " index " ++ show index) Nothing

focusBody :: ExprContext -> AEnv (Maybe ExprContext)
focusBody e = do
  children <- childrenContexts e
  query <- getQueryString
  return $ case find (\x -> case x of
              LamCBody{} -> True
              _ -> False) children of
    Just x -> Just x
    Nothing -> trace (query ++ "Children looking for body " ++ show children) Nothing

focusFun :: ExprContext -> AEnv (Maybe ExprContext)
focusFun e = do
  children <- childrenContexts e
  query <- getQueryString
  return $ case find (\x -> case x of
                AppCLambda{} -> True
                ExprCBasic _ _ Var{} -> True
                _ -> False) children of
    Just x -> Just x
    Nothing -> trace (query ++ "Children looking for lambda " ++ show children) Nothing


focusChild :: ExprContext -> Int -> AEnv (Maybe ExprContext)
focusChild e index = do
  children <- childrenContexts e
  query <- getQueryString
  return $ if index < length children then
    trace (query ++ "Focused child " ++ show (children !! index) ++ " " ++ show index ++ " " ++ show children) $
      Just (children !! index)
    else trace (query ++ "Children looking for child at " ++ show index ++ " " ++ show children) Nothing

focusLetBinding :: Maybe Int -> ExprContext -> AEnv (Maybe ExprContext)
focusLetBinding index e = do
  children <- childrenContexts e
  query <- getQueryString
  return $ case index of
    Just x | x < length children -> Just $ children !! x
    _ -> trace (query ++ "Children looking for let binding " ++ show children) Nothing


getQueryString :: AEnv String
getQueryString = do
  env <- getEnv
  return $ queryIndentation env ++ currentQuery env ++ show (contextId $ currentContext env) ++ " "

getContext :: ExprContextId -> AEnv ExprContext
getContext id = do
  st <- getState
  case M.lookup id (states st) of
    Just x -> return x
    _ -> error $ "Context not found " ++ show id

getUnique :: AEnv Int
getUnique = do
  st <- getState
  let u = unique st
  setState st{unique = u + 1}
  return u

updateState :: (State -> State) -> AEnv ()
updateState update = do
  st <- getState
  setState $ update st

runEvalQueryFromRange :: Loaded -> (Module -> IO Module) -> (Range, RangeInfo) -> Module -> [(EnvCtx, AbValue)]
runEvalQueryFromRange loaded loadModuleFromSource rng mod =
  runQueryAtRange loaded loadModuleFromSource rng mod $ \exprctxs ->
    case exprctxs of
      exprctx:rst -> do
        res <- fixedEval exprctx (indeterminateStaticCtx exprctx)
        trace ("eval result:\n----------------------\n" ++ intercalate "\n\n" (map show res) ++ "\n----------------------\n") $ return res
      _ -> return []

runEvalQueryFromRangeSource :: Loaded -> (Module -> IO Module) -> (Range, RangeInfo) -> Module -> ([UserExpr], [UserDef], [Syn.Lit], [String], Set Type, Loaded)
runEvalQueryFromRangeSource ld loadModuleFromSource rng mod =
  runQueryAtRange ld loadModuleFromSource rng mod $ \exprctxs ->
    case exprctxs of
      exprctx:rst -> do
        res <- fixedEval exprctx (indeterminateStaticCtx exprctx)
        let vals = map snd res
            lams = map fst $ concatMap (S.toList . closures) vals
            i = concatMap ((mapMaybe toSynLit . M.elems) . intV) vals
            f = concatMap ((mapMaybe toSynLitD . M.elems) . floatV) vals
            c = concatMap ((mapMaybe toSynLitC . M.elems) . charV) vals
            s = concatMap ((mapMaybe toSynLitS . M.elems) . stringV) vals
            topTypes = unions $ map topTypesOf vals
            vs = i ++ f ++ c ++ s
            cs = concatMap S.toList $ concatMap (M.elems . constrs) vals
        consts <- mapM toSynConstr cs
        sourceLams <- mapM findSourceExpr lams
        let (sourceLambdas, sourceDefs) = unzip sourceLams
        loaded1 <- loaded <$> getState
        trace ("eval result:\n----------------------\n" ++ intercalate "\n----\n" (map showSimpleAbValueCtx res) ++ "\n----------------------\n") $ return (catMaybes sourceLambdas, catMaybes sourceDefs, vs, catMaybes consts, topTypes, loaded1)
      _ -> return ([],[],[],[],S.empty, ld)

toSynConstr :: ConstrContext -> AEnv (Maybe String)
toSynConstr (ConstrContext nm tp args) = do
  args' <- mapM findSourceExpr args
  return (Just $ nameId (getName nm))



sourceEnv :: EnvCtx -> AEnv String
sourceEnv (EnvCtx env) = do
  envs <- mapM sourceEnvCtx env
  return $ "<" ++ intercalate "," envs ++ ">"


------------------- Basic Ctx Abstraction ------------------
sourceEnvCtx :: Ctx -> AEnv String
sourceEnvCtx ctx =
  case ctx of
    IndetCtx tn c -> return $ "?" ++ intercalate "," (map show tn)
    TopCtx -> return "T"
    DegenCtx -> return "~"
    CallCtx c env -> do
      se <- findSourceExpr c
      e <- sourceEnv env
      return $ case se of
        (Just se, _) -> showSyntax 0 se ++ " " ++ e
        (_, Just de) -> showSyntaxDef 0 de ++ " " ++ e
        _ -> show c ++ " " ++ e
    BCallCtx c cc -> do
      se <- findSourceExpr c
      e <- sourceEnvCtx cc
      return $ case se of
        (Just se, _) -> showSyntax 0 se ++ " " ++ e
        (_, Just de) -> showSyntaxDef 0 de ++ " " ++ e
        _ -> show c ++ " " ++ e

succAEnv :: ExprContext -> EnvCtx -> AEnv Ctx
succAEnv newctx p'@(EnvCtx (cc:_)) = do
  length <- contextLength <$> getEnv
  basic <- basicEnvs <$> getEnv
  if basic then 
    return $ succm (BCallCtx newctx cc) length
  else
    return $ succm (CallCtx newctx p') length

------------------- Env Ctx Abstraction ------------------
-- succAEnv :: (EnvCtx -> Ctx) -> EnvCtx -> AEnv Ctx
-- succAEnv newctx env = do
--   length <- contextLength <$> getEnv
--   return $! succm (newctx env) length

------------------- End Env Ctx Abstraction ------------------

findSourceExpr :: ExprContext -> AEnv (Maybe UserExpr, Maybe (Syn.Def UserType))
findSourceExpr ctx =
  case maybeExprOfCtx ctx of
    Just (Lam (n:_) _ _) -> findForName n
    Just (TypeLam _ (Lam (n:_) _ _)) -> findForName n
    Just (App (Var tn _) _) -> findForApp tn
    _ ->
      case ctx of
        DefCNonRec _ _ _ d -> findDef d
        DefCRec _ _ _ _ d -> findDef d
        LetCDef _ _ _ i d -> findDef (defsOf d !! i)
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

runQueryAtRange :: Loaded -> (Module -> IO Module) -> (Range, RangeInfo) -> Module -> ([ExprContext] -> AEnv a) -> a
runQueryAtRange loaded loadModuleFromSource (r, ri) mod query =
  let cid = ExprContextId (-1) (modName mod)
      modCtx = ModuleC cid mod (modName mod)
      focalContext = analyzeCtx (\a l -> a ++ concat l) (const $ findContext r ri) modCtx
      result = case focalContext >>= query of
        AEnv f -> f (DEnv 3 True modCtx (EnvCtx []) "" "" loadModuleFromSource) (State loaded M.empty 0 M.empty 0 (M.fromList [("call", M.empty), ("expr", M.empty), ("eval", M.empty)]) S.empty M.empty 0)
  in case result of
    Ok a st -> a

findContext :: Range -> RangeInfo -> AEnv [ExprContext]
findContext r ri = do
  ctx <- currentContext <$> getEnv
  case ctx of
    ExprCBasic _ _ (Var (TName _ _ (Just rng)) _) | r `rangesOverlap` rng -> trace ("found overlapping range " ++ showFullRange rng ++ " " ++ show ctx) $ return [ctx]
    ExprCBasic _ _ (Var (TName _ _ (Just rng)) _) -> -- trace ("var range doesn't overlap "++ show ctx ++ " " ++ showFullRange rng) $
      return []
    LetCDef _ _ _ i dg -> fromNames ctx [defTName (defsOf dg !! i)]
    -- Hovering over a lambda parameter should query what values that parameter can evaluate to -- need to create an artificial Var expression
    LamCBody _ _ tnames _ -> fromNames ctx tnames      
    _ -> return []
  where fromNames ctx tnames =
          case mapMaybe (\tn -> (case fmap (rangesOverlap r) (originalRange tn) of {Just True -> Just tn; _ -> Nothing})) tnames of
              [tn] -> do
                id <- newContextId
                return [ExprCBasic id ctx (Var tn InfoNone)]
              _ -> return []

analyzeCtx :: (a -> [a] -> a) -> (ExprContext -> AEnv a) -> ExprContext -> AEnv a
analyzeCtx combine analyze ctx = do
  -- id <- currentContext <$> getEnv
  -- trace ("Analyzing ctx " ++ show ctx ++ " with id " ++ show (exprId id)) $ return ()
  res <- analyze ctx
  visitChildrenCtxs (combine res) ctx $ do
    childCtx <- currentContext <$> getEnv
    analyzeCtx combine analyze childCtx

bindExternal :: Expr -> AEnv (Maybe (ExprContext, Maybe Int))
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

findUsage :: Expr -> ExprContext -> EnvCtx -> AEnv (Set (ExprContext, EnvCtx))
findUsage expr@Var{varName=tname@TName{getName = name}} ctx env@(EnvCtx cc) =
  let nameEq = (== name)
      empty = return S.empty
      childrenUsages =
        visitChildrenCtxs S.unions ctx $ do -- visitChildrenCtxs sets the currentContext
          childCtx <- currentContext <$> getEnv
          -- trace ("Looking for usages of " ++ show name ++ " in " ++ show ctx) $ return empty
          findUsage expr childCtx env in
  case maybeExprOfCtx ctx of
    Just (Lam params _ _) ->
      let paramNames = map getName params in
      if name `elem` paramNames then -- shadowing
        empty
      else
        visitChildrenCtxs S.unions ctx $ do
          childCtx <- currentContext <$> getEnv
          findUsage expr childCtx (EnvCtx (IndetCtx params ctx:cc))
    Just (Var{varName=TName{getName=name2}}) ->
      if nameEq name2 then do
        query <- getQueryString
        return $! trace (query ++ "Found usage in " ++ show ctx) $ 
          S.singleton (ctx, env)
      else
        -- trace ("Not found usage in " ++ show ctx ++ " had name " ++ show name2 ++ " expected " ++ show name) $ empty
        empty
    _ -> childrenUsages -- TODO Avoid shadowing let bindings

newQuery :: Query -> (String -> AEnv a) -> AEnv a
newQuery q d = do
  unique <- getUnique
  withEnv (\env -> env{currentContext = queryCtx q, currentEnv = queryEnv q, currentQuery = "q" ++ show unique ++ "(" ++ queryKindCaps q ++ ")" ++ ": ", queryIndentation = queryIndentation env ++ " "}) $ do
    query <- getQueryString
    d query

instantiate ::  (Query -> AEnv AbValue) -> Query -> Ctx -> Ctx -> AEnv ()
instantiate loop q c1 c0 = do
  trace ("instantiating " ++ show q ++ " " ++ showSimpleCtx c0 ++ " to " ++ showSimpleCtx c1) $ return ()
  st <- getState
  if S.member (q, c1, c0) (instantiateCache st) then return ()
  else do
    updateState (\state -> state{instantiateCache = S.insert (q, c1, c0) (instantiateCache state)})
    let reach = reachable st M.! q
    -- trace back through reachable, adding reachable relations and instantiating / evaluating them
    mapM_ (\query -> do -- Instantiate Reachable / Instantiate
        if q == query || c1 == c0 then return ()
        else do
          instantiate loop query c1 c0
          case query of
            EvalQ (ctx, env) -> do
              let newEnv@(EnvCtx p') = (c1, c0) `refine` env
              if newEnv == env then return ()
              else do
                loop $ EvalQ (ctx, newEnv)
                return ()
            ExprQ (ctx, env) -> do
              let newEnv = (c1, c0) `refine` env
              if newEnv == env then return ()
              else do
                loop $ ExprQ (ctx, newEnv)
                return ()
            CallQ (ctx, env) -> do
              let newEnv = (c1, c0) `refine` env
              if newEnv == env then return ()
              else do
                loop $ CallQ (ctx, newEnv)
                return ()
      ) reach

memoJoin :: Query -> AEnv AbValue -> AEnv AbValue
memoJoin q f = do
  state <- getState
  let cache = memoCache state M.! kind
      version = evalCacheGeneration state
  case M.lookup (contextId ctx) cache of
    Just (EnvCtxLattice x) ->
      case M.lookup env x of
        Just (v, x) ->
          if version == v then return $! x
          else runAndUpdate
        _ -> do
          let cache = memoCache state M.! kind
          let newCache = M.insert (contextId ctx) (EnvCtxLattice $ M.singleton env (version, emptyAbValue)) cache
          setState state{memoCache = M.insert kind newCache (memoCache state)}
          runAndUpdate
    _ -> do
      -- trace ("Pre memo " ++ show name ++ " " ++ show ctx ++ " " ++ show env) $ return () 
      let cache = memoCache state M.! kind
      let newCache = M.insert (contextId ctx) (EnvCtxLattice $ M.singleton env (version, emptyAbValue)) cache
      setState state{memoCache = M.insert kind newCache (memoCache state)}
      runAndUpdate
  where
    ctx = queryCtx q
    env = queryEnv q
    kind = queryKind q
    runAndUpdate = do
      res <- f
      state <- getState
      query <- getQueryString
      -- trace (query ++ "RESULT: [" ++ show res ++ "]") $ return ()
      -- trace ("Post memo " ++ show name ++ " " ++ show ctx ++ " " ++ show env) $ return () 
      let cache = memoCache state M.! kind
      let (changed, s, newCache) = addJoin (cache M.! contextId ctx) (evalCacheGeneration state + 1) env res
      let newGen = if changed then evalCacheGeneration state + 1 else evalCacheGeneration state
      let newCache' = M.insert (contextId ctx) newCache cache
      setState state{memoCache = M.insert kind newCache' (memoCache state), evalCacheGeneration = newGen}
      return res


doMaybeAbValue :: AbValue -> Maybe a -> (a -> AEnv AbValue) -> AEnv AbValue
doMaybeAbValue init l doA = do
  case l of
    Just x -> doA x
    Nothing -> return init

doForList :: AbValue -> AbValue -> ((ExprContext, EnvCtx) -> AEnv AbValue) -> AEnv AbValue
doForList init l doA = do
  foldM (\res x -> do
    res' <- doA x
    return $! join res res') init (S.toList $ closures l)

makeReachable :: Query -> Query -> AEnv ()
makeReachable q1 q2 = -- Query q2 is reachable from q1
  updateState (\state -> state{reachable = M.insertWith S.union q2 (S.singleton q1) $ reachable state})

loop :: (Query -> Query -> AEnv AbValue) -> Query -> Query -> AEnv AbValue
loop l parentQuery currentQuery = do
  makeReachable parentQuery currentQuery
  let memo = memoJoin currentQuery
  let loop = l currentQuery
  case currentQuery of
    EvalQ{} -> memo $ doEval loop parentQuery currentQuery
    CallQ{} -> memo $ doCall loop parentQuery currentQuery
    ExprQ{} -> memo $ doExpr loop parentQuery currentQuery

instance Show Query where
  show q = (queryKindCaps q ++ ": " ++ showSimpleEnv (queryEnv q) ++ " " ++ showSimpleContext (queryCtx q))

doEval :: (Query -> AEnv AbValue) -> Query -> Query -> AEnv AbValue
doEval loop pq cq@(EvalQ (ctx, env)) = newQuery cq (\query -> do
   trace (query ++ show cq) $ do
    case exprOfCtx ctx of
      Lam{} -> -- LAM CLAUSE
        -- trace (query ++ "LAM: " ++ show ctx) $
        return $! injClosure ctx env
      v@(Var n _) | getName n == nameEffectOpen -> do -- TODO: Reevaluate eventually
        -- trace (query ++ "OPEN: " ++ show ctx) $ return []
        newId <- newContextId
        let tvar = TypeVar 0 (kindFun kindStar kindStar) Bound
            x = TName (newName "x") (TVar tvar) Nothing
            def = makeDef nameEffectOpen (TypeLam [tvar] (Lam [x] effectEmpty (Var x InfoNone)))
            newCtx = DefCNonRec newId ctx [defTName def] def
        return $! injClosure newCtx (EnvCtx [TopCtx])
      v@(Var tn _) -> do -- REF CLAUSE
-- REF: 
--  - When the binding is focused on a lambda body, we need to find the callers of the lambda, and proceed as original formulation. 
--  - When the binding is in the context of a Let Body we can directly evaluate the let binding as the value of the variable being bound (indexed to match the binding).
--  - When the binding is in the context of a Let binding, it evaluates to that binding or the indexed binding in a mutually recursive group 
--  - When the binding is a top level definition - it evaluates to that definition 
--  - When the binding is focused on a match body then we need to issue a subquery for the evaluation of the match expression that contributes to the binding, 
--         and then consider the abstract value and find all abstract values that match the pattern of the branch in question 
--         and only consider the binding we care about. 
--         This demonstrates one point where a context sensitive shape analysis could propagate more interesting information along with the subquery to disregard traces that don’t contribute
        -- trace (query ++ "REF: " ++ show ctx) $ return []
        let binded = bind ctx v env
        trace (query ++ "REF: bound to " ++ show binded) $ return []
        case binded of
          Just ((lambodyctx@LamCBody{}, bindedenv), Just index) -> do
            calls <- loop $ CallQ (lambodyctx, bindedenv)
            doForList emptyAbValue calls (\(appctx, appenv) -> do
              -- trace (query ++ "REF: found application " ++ show appctx ++ " " ++ show appenv ++ " param index " ++ show index) $ return []
              param <- focusParam (Just index) appctx
              doMaybeAbValue emptyAbValue param (\param ->
                  loop $ EvalQ (param, appenv))
              )
          Just ((letbodyctx@LetCBody{}, bindedenv), index) -> do
            param <- focusChild (fromJust $ contextOf letbodyctx) (fromJust index)
            doMaybeAbValue emptyAbValue param (\ctx -> loop $ EvalQ (ctx, bindedenv))
          Just ((letdefctx@LetCDef{}, bindedenv), index) -> do
            param <- focusChild (fromJust $ contextOf letdefctx) (fromJust index)
            doMaybeAbValue emptyAbValue param (\ctx -> loop $ EvalQ (ctx, bindedenv))
          Just ((CaseCBranch _ c _ _ (Branch pat guard), bindedenv), index) -> do
            scrutinee <- focusChild c 0
            doMaybeAbValue emptyAbValue scrutinee (\scrutinee -> do
                scruinteeval <- loop $ EvalQ (scrutinee, bindedenv)
                let msg = query ++ "REF: TODO: Match body context " ++ show v ++ " " ++ show binded ++ " val " ++ show scruinteeval
                trace msg $ return $! injErr msg

              )
          Just ((modulectx@ModuleC{}, bindedenv), index) -> do
            lamctx <- getDefCtx modulectx (getName tn)
            -- Evaluates just to the lambda
            loop $ EvalQ (lamctx, EnvCtx [TopCtx])
          Just ((ctxctx, bindedenv), index) -> do
            children <- childrenContexts ctxctx
            let msg = query ++ "REF: unexpected context in result of bind: " ++ show v ++ " " ++ show ctxctx ++ " children: " ++ show children
            trace msg $ return $! injErr msg
          Nothing -> do
            ext <- bindExternal v
            case ext of
              Just (modulectx@ModuleC{}, index) -> do
                lamctx <- getDefCtx modulectx (getName tn)
                -- Evaluates just to the lambda
                loop (EvalQ (lamctx, EnvCtx [TopCtx]))
              _ -> return $! injErr $ "REF: can't find what the following refers to " ++ show ctx
      App (Con nm repr) args -> do
        children <- childrenContexts ctx
        return $ injCon nm (conTypeName repr) children env
      App f tms -> do
        fun <- focusChild ctx 0
        doMaybeAbValue emptyAbValue fun (\fun -> do
            -- trace (query ++ "APP: Lambda Fun " ++ show fun) $ return []
            lamctx <- loop $ EvalQ (fun, env)
            doForList emptyAbValue lamctx (\(lam, EnvCtx lamenv) -> do
              -- trace (query ++ "APP: Lambda is " ++ show lamctx) $ return []
              bd <- focusBody lam
              doMaybeAbValue emptyAbValue bd (\bd -> do
                -- trace (query ++ "APP: Lambda body is " ++ show lamctx) $ return []
                childs <- childrenContexts ctx
                -- In the subevaluation if a binding for the parameter is requested, we should return the parameter in this context, 
                -- TODO: How does this affect any recursive contexts? (a local find from the body of the lambda)
                succ <- succAEnv ctx env
                let newEnv = EnvCtx (succ:lamenv)
                loop $ EvalQ (bd, newEnv)
                instantiate loop cq succ (IndetCtx (lamNames lam) lam)
                loop $ EvalQ (bd, newEnv)
                )
              )
          )
      TypeApp{} ->
        case ctx of
          DefCNonRec{} -> return $! injClosure ctx env
          DefCRec{} -> return $! injClosure ctx env
          _ -> do
            ctx' <- focusChild ctx 0
            doMaybeAbValue emptyAbValue ctx' (\ctx -> loop $ EvalQ (ctx,env))
      TypeLam{} ->
        case ctx of
          DefCNonRec{} -> return $! injClosure ctx env-- Don't further evaluate if it is just the definition / lambda
          DefCRec{} -> return $! injClosure ctx env-- Don't further evaluate if it is just the definition / lambda
          _ -> do
            ctx' <- focusChild ctx 0
            doMaybeAbValue emptyAbValue ctx' (\ctx -> loop $ EvalQ (ctx,env))
      Lit l -> return $! injLit l env
      Case e branches -> do
        trace (query ++ "CASE: " ++ show ctx) $ return []
        e <- focusChild ctx 0
        doMaybeAbValue emptyAbValue e (\e -> do 
            scrutinee <- loop $ EvalQ (e, env)
            trace (query ++ "CASE: scrutinee is " ++ show scrutinee) $ return []
            let msg = "Case not implemented"
            return $! trace msg $! injErr msg
          )
      Con nm repr -> return $! injCon nm (conTypeName repr) [] env -- TODO: Check that the constructor is a singleton
      _ ->
        let msg =  (query ++ "TODO: Not Handled Eval: " ++ show ctx ++ " expr: " ++ show (exprOfCtx ctx)) in
        trace msg $! return $! injErr msg
  )

newErrTerm :: String -> AEnv [(ExprContext, EnvCtx)]
newErrTerm s = do
  newId <- newContextId
  return [(ExprCTerm newId ("Error: " ++ s), EnvCtx [DegenCtx])]

doExpr loop pq cq@(ExprQ (ctx,env)) = newQuery cq (\query -> do
  trace (query ++ show cq) $ do
    case ctx of
      AppCLambda _ c e -> -- RATOR Clause
        trace (query ++ "OPERATOR: Application is " ++ showCtxExpr c) $
        return $ injClosure c env
      AppCParam _ c index e -> do -- RAND Clause 
        trace (query ++ "OPERAND: Expr is " ++ showCtxExpr ctx) $ return []
        fn <- focusFun c
        case fn of
          Just fn -> do
            trace (query ++ "OPERAND: Evaluating To Closure " ++ showCtxExpr fn) $ return []
            ctxlam <- loop $ EvalQ (fn, env)
            doForList emptyAbValue ctxlam (\(lam, EnvCtx lamenv) -> do
              trace (query ++ "OPERAND: Closure is: " ++ showCtxExpr lam) $ return []
              bd <- focusBody lam
              case bd of
                Nothing -> return emptyAbValue
                Just bd -> do
                  trace (query ++ "OPERAND: Closure's body is " ++ showCtxExpr bd) $ return ()
                  trace (query ++ "OPERAND: Looking for usages of operand bound to " ++ show (lamVar index lam)) $ return []
                  succ <- succAEnv c env
                  ctxs <- findUsage (lamVar index lam) bd (EnvCtx $ succ:lamenv)
                  -- trace (query ++ "RAND: Usages are " ++ show ctxs) $ return []
                  ress <- mapM (\ctx -> loop $ ExprQ ctx) (S.toList ctxs)
                  let result = Prelude.foldl join emptyAbValue ress
                  trace (query ++ "OPERAND RESULT: Callers of operand bound to are " ++ show result) $ return []
                  instantiate loop cq succ (IndetCtx (lamNames lam) lam)
                  return result
              )
          Nothing -> return emptyAbValue
      LamCBody _ _ _ e -> do -- BODY Clause
        trace (query ++ "BODY: Looking for locations the returned closure is called " ++ show ctx) $ return []
        res <- loop $ CallQ (ctx, env)
        trace (query ++ "BODY RESULT: Callers of returned closure are " ++ show res) $ return []
        ress <- mapM (\ctx -> loop $ ExprQ ctx) (S.toList $ closures res)
        let result = Prelude.foldl join emptyAbValue ress
        trace (query ++ "BODY RESULT: Callers of returned closure are " ++ show result) $ return []
        return result
      ExprCTerm{} ->
        -- trace (query ++ "ends in error " ++ show ctx)
        -- return [(ctx, env)]
        return $ injErr $ "Exprs led to ExprCTerm" ++ show ctx
      DefCNonRec _ c index df -> do
        trace (query ++ "DEF: Env is " ++ show env) $ return []
        ctxs <- case c of
          LetCDef{} -> findUsage (lamVarDef df) (fromJust $ contextOf c) env
          _ -> findUsage (lamVarDef df) c env
        trace (query ++ "DEF: Usages are " ++ show ctxs) $ return []
        ress <- mapM (\ctx -> loop $ ExprQ ctx) (S.toList ctxs)
        let result =  Prelude.foldl join emptyAbValue ress
        trace (query ++ "DEF: Calls are " ++ show result) $ return []
        return result
      ExprCBasic _ c _ -> loop $ ExprQ (c, env)
      _ ->
        case contextOf ctx of
          Just c ->
            case enclosingLambda c of
              Just c' -> loop $ ExprQ (c', env)
              _ -> return $ injErr $ "Exprs has no enclosing lambda, so is always demanded (top level?) " ++ show ctx
          Nothing -> return $ injErr $ "expressions where " ++ show ctx ++ " is demanded (should never happen)"
  )

doCall loop pq cq@(CallQ(ctx, env@(EnvCtx cc@(cc0:p)))) =
  newQuery cq (\query ->
  trace (query ++ show cq) $ do
      case ctx of
          LamCBody _ c _ _-> do
            calls <- loop $ ExprQ (c, envtail env)
            doForList emptyAbValue calls (\(callctx, callenv) -> do
                cc1 <- succAEnv callctx callenv
                if cc1 == cc0 then
                  trace (query ++ "KNOWN CALL: " ++ showSimpleCtx cc1 ++ " " ++ showSimpleCtx cc0)
                  return $! injClosure callctx callenv
                else if cc0 `subsumesCtx` cc1 then do
                  trace (query ++ "UNKNOWN CALL: " ++ showSimpleCtx cc1 ++ " " ++ showSimpleCtx cc0) $ return ()                  
                  result <- loop $ CallQ (ctx, EnvCtx (cc1:p))
                  instantiate loop cq cc1 cc0
                  loop $ CallQ (ctx, EnvCtx (cc1:p))
                else do
                  trace (query ++ "CALL IS NOT SUBSUMED: " ++ showSimpleCtx cc1 ++ " " ++ showSimpleCtx cc0) $ return ()
                  return emptyAbValue
              )
            -- Lightweight Version
            -- case cc of
            --   (CallCtx callctx p'):p -> do
            --     trace (query ++ "Known: " ++ show callctx) $ return ()
            --     pnew <- calibratem p'
            --     return $ injClosure callctx pnew
            --   _ -> do
            --     trace (query ++ "Unknown") $ return ()
            --     loop $ ExprQ (c, envtail env)
          -- ExprCTerm{} ->
          --   trace (query ++ "ends in error " ++ show ctx)
          --   return $! injClosure ctx env
          -- DefCNonRec _ c _ d -> do
          --   ctx' <- findUsage2 query (lamVarDef d) c
          --   L.fromFoldable ctx' >>= expr
          _ -> return $ injErr $ "CALL not implemented for " ++ show ctx
    )

data Query =
  CallQ (ExprContext, EnvCtx) |
  ExprQ (ExprContext, EnvCtx) |
  EvalQ (ExprContext, EnvCtx) deriving (Eq, Ord)

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

fix :: (a -> a) -> a
fix f = f (fix f)

fixedEval :: ExprContext -> EnvCtx -> AEnv [(EnvCtx, AbValue)]
fixedEval e env = do
  let q = EvalQ (e, env)
  let doLoop = fix loop
  doLoop q q
  trace "Finished eval" $ return ()
  state <- getState
  let cache = memoCache state M.! "eval"
  case M.lookup (contextId e) cache of
    Just (EnvCtxLattice res) ->
      let !result = map (\(k, (_, v)) -> (k, v)) (M.assocs res)
      in return result
    Nothing -> do
      let msg = "fixedEval: " ++ show e ++ " not in cache " ++ show (M.keys cache)
      trace msg $ return [(EnvCtx [], injErr msg)]

fixedExpr :: ExprContext -> EnvCtx -> AEnv [(ExprContext, EnvCtx)]
fixedExpr e env = do
  res <- fix loop (ExprQ (e, env)) (ExprQ (e, env))
  return $ S.toList $ closures $ res
fixedCall :: ExprContext -> EnvCtx -> AEnv [(ExprContext, EnvCtx)]
fixedCall e env = do
  res <- fix loop (CallQ (e, env)) (CallQ (e, env))
  return $ S.toList $ closures $ res

allModules :: Loaded -> [Module]
allModules loaded = loadedModule loaded : loadedModules loaded

getDefCtx :: ExprContext -> Name -> AEnv ExprContext
getDefCtx ctx name = do
  children <- childrenContexts ctx
  case find (\dctx -> case dctx of
      DefCNonRec _ _ _ d | defName d == name -> True
      DefCRec _ _ _ _ d | defName d == name -> True
      _ -> False
      ) children of
    Just dctx -> do
      -- lamctx <- focusChild dctx 0 -- Actually focus the lambda
      return dctx
    Nothing -> error $ "getDefCtx: " ++ show ctx ++ " " ++ show name

getModule :: Name -> AEnv Module
getModule name = do
  deps <- loadedModules . loaded <$> getState
  let x = find (\m -> modName m == name) deps
  case x of
    Just mod -> return mod
    _ -> error $ "getModule: " ++ show name

addChildrenContexts :: ExprContextId -> [ExprContext] -> AEnv ()
addChildrenContexts parentCtx contexts = do
  state <- getState
  let newIds = map contextId contexts
      newChildren = M.insert parentCtx (S.fromList newIds) (childrenIds state)
   -- trace ("Adding " ++ show childStates ++ " previously " ++ show (M.lookup parentCtx (childrenIds state))) 
  setState state{childrenIds = newChildren}

newContextId :: AEnv ExprContextId
newContextId = do
  state <- getState
  id <- currentContext <$> getEnv
  let newCtxId = maxContextId state + 1
  updateState (\s -> s{maxContextId = newCtxId})
  return $! ExprContextId newCtxId (moduleName (contextId id))

newModContextId :: Module -> AEnv ExprContextId
newModContextId mod = do
  state <- getState
  let newCtxId = maxContextId state + 1
  updateState (\s -> s{maxContextId = newCtxId})
  return $! ExprContextId newCtxId (modName mod)

addContextId :: (ExprContextId -> ExprContext) -> AEnv ExprContext
addContextId f = do
  newId <- newContextId
  state <- getState
  let x = f newId
  setState state{states=M.insert newId x (states state)}
  return x

childrenOfExpr :: ExprContext -> Expr -> AEnv [ExprContext]
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

childrenOfDef :: ExprContext -> C.DefGroup -> AEnv [ExprContext]
childrenOfDef ctx def =
  case def of
    C.DefNonRec d -> addContextId (\newId -> DefCNonRec newId ctx [defTName d] d) >>= (\x -> return [x])
    C.DefRec ds -> zipWithM (\i d -> addContextId (\newId -> DefCRec newId ctx (map defTName ds) i d)) [0..] ds

childrenContexts :: ExprContext -> AEnv [ExprContext]
childrenContexts ctx = do
  withEnv (\env -> env{currentContext = ctx}) $ do
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
                DefCRec _ _ _ _ d -> childrenOfExpr ctx (defExpr d)
                DefCNonRec _ _ _ d -> childrenOfExpr ctx (defExpr d)
                LamCBody _ _ names body -> childrenOfExpr ctx body
                AppCLambda _ _ f -> childrenOfExpr ctx f
                AppCParam _ _ _ param -> childrenOfExpr ctx param
                LetCDef _ _ _ _ defg -> childrenOfDef ctx defg
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

visitChildrenCtxs :: ([a] -> a) -> ExprContext -> AEnv a -> AEnv a
visitChildrenCtxs combine ctx analyze = do
  children <- childrenContexts ctx
  -- trace ("Got children of ctx " ++ show ctx ++ " " ++ show children) $ return ()
  res <- mapM (\child -> withEnv (\e -> e{currentContext = child}) analyze) children
  return $! combine res