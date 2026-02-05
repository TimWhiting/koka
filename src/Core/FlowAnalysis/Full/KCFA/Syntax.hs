{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant return" #-}
{-# HLINT ignore "Redundant if" #-}
module Core.FlowAnalysis.Full.KCFA.Syntax where

import Data.List (intercalate, find, minimumBy, groupBy, sort, permutations)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Maybe (catMaybes, mapMaybe, isJust, fromJust)
import Data.Set(Set)
import Compile.Module (Module(..))
import qualified Syntax.Syntax as Syn
import qualified Syntax.Syntax as S
import Syntax.Pretty
import Syntax.RangeMap (RangeInfo (..), rmFindFirst)
import qualified Core.Core as C
import Core.Core
import Type.Type
import Lib.PPrint
import Compile.BuildMonad (BuildContext, Build)
import Compile.Options (Terminal, Flags)
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Literals
import Core.FlowAnalysis.Syntax
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.Full.KCFA.KCFA
import Core.FlowAnalysis.Full.KCFA.AbstractValue
import Core.FlowAnalysis.Full.KCFA.Monad
import Common.Failure (HasCallStack)
import Common.NamePrim (nameMain)
import Common.Name (Name(..))
import Common.Range
import Debug.Trace (trace)
import Common.File (startsWith)
import Control.Monad (unless)
import Data.Time (getCurrentTime, diffUTCTime)
import System.Timeout (timeout)
import Data.Fixed (showFixed)
import Data.Time.Clock (nominalDiffTimeToSeconds)
import Core.FlowAnalysis.Full.Report (StoreMetrics(..), PolyVariantMetrics (PolyVariantMetrics))
import Data.Aeson
import System.Directory (createDirectoryIfMissing)
import qualified Data.ByteString.Lazy as BS


analyzeEach :: Show d => ExprContext -> (ExprContext -> FixAAMR a b c d) -> FixAAMR a b c d
analyzeEach = analyzeEachChild

debug = False

runQueryAtRange :: HasCallStack => BuildContext
  -> TypeChecker
  -> Module -> Int
  -> (ExprContext -> FixAAMR FixChange () () ())
  -> IO Bool
runQueryAtRange bc build mod m doQuery =
  let runId = show m ++ "-" ++ show 0 in
  do
    (_, s, ctxs) <- runFixFinish (emptyBasicEnv m 0 build False ()) (emptyBasicState bc ()) $
              do runFixCont $ do
                    (_,ctx) <- loadModule (modName mod)
                    withEnv (\e -> e{currentModContext = ctx, currentContext = ctx}) $ do
                      -- trace ("Context: " ++ show (contextId ctx)) $ return ()
                      res <- analyzeEach ctx (const findMainBody)
                      addResult res
                 getResults
    let s' = transformBasicState (const ()) (const S.empty) s
        values = collectPrograms (S.toList ctxs)
        recur :: [AProgram] -> IO (Int, Int)
        recur l =
          case l of
            [] -> if nameModule (modName mod) `startsWith` "std/core" then
                return (0, 0)
              else
                -- trace ("No analysis context found in " ++ nameModule (modName mod)) $
                return (0, 0)
            (AProgram name mainCtx resCtx):rest ->
              do
                result <- do
                  mbRes <- do
                        let once = do
                              timeout 500000000 $ do
                                  tstart <- getCurrentTime
                                  -- trace (" Analyzing " ++ show name) $ return ()
                                  (l, _, analysisResult) <- runFixFinishC (emptyBasicEnv m 0 build True ()) s' $ do
                                                  runFixCont $ do
                                                    (_,ctx) <- loadModule (modName mod)
                                                    -- trace ("Context: " ++ show (contextId ctx)) $ return ()
                                                    withEnv (\e -> e{currentModContext = ctx, currentContext = ctx}) $ doQuery mainCtx
                                                  ress' <- getAbResult
                                                  -- trace ("result': " ++ show ress') $ return ()
                                                  return ress'
                                  tend <- getCurrentTime
                                  return (l, analysisResult, nominalDiffTimeToSeconds $ diffUTCTime tend tstart)
                        first <- once
                        case first of
                          Just (l, res, time1) -> do
                            if debug then return $ Just (l, res, [time1])
                            else do
                              Just (_, _, time2) <- once
                              Just (_, _, time3) <- once
                              return $ Just (l, res, [time1, time2, time3])
                          Nothing -> return Nothing
                  let dir = "benchmarks/results/kcfa/" ++ show 0 ++ "/" ++ show m ++ "/" ++ nameModule (modName mod)
                  createDirectoryIfMissing True dir
                  case mbRes of
                    Just (l, analysisResult, times) -> do
                      -- trace ("Evaluating expected result for " ++ show name) $ return ()
                      (_, _, expectedResult) <- runFixFinishC (emptyBasicEnv m 0 build True ()) s' $ do
                                      runFixCont $ do
                                        (_,ctx) <- loadModule (modName mod)
                                        -- trace ("Context: " ++ show (contextId ctx)) $ return ()
                                        withEnv (\e -> e{currentModContext = ctx, currentContext = ctx}) $ doQuery resCtx
                                      ress' <- getAbResult
                                      -- trace ("expected': " ++ show ress') $ return ()
                                      return ress'

                      let !result = (if compareResult analysisResult expectedResult S.empty then 1 else 0)
                      let (_, _, (evals, applies, kSizes, sSizes), metrics) = analysisResult

                      -- writeSimpleDependencyGraph (moduleNameToPath (modName mod)) l
                      let value = PolyVariantMetrics "kcfa" 0 m (nameModule (modName mod) ++ "/" ++ name) times False (Just metrics)
                      BS.writeFile (dir ++ "/" ++ name ++ ".json") (encode (toJSON value))
                      -- trace ("dmcfa," ++ nameModule (modName mod) ++ "/" ++ name ++ "," ++ show d ++ "," ++ show m ++ "," ++
                      --         show result ++ "," 
                      --         ++ show (length evals) ++ "," ++ show (sum evals) ++ "," ++ show (count (== 1) evals) ++ "," 
                      --         ++ show (length applies) ++ "," ++ show (sum applies) ++ "," ++ show (count (== 1) applies) ++ ","
                      --         ++ show (length kSizes) ++ "," ++ show (sum kSizes) ++ "," ++ show (count (== 1) kSizes) ++ ","
                      --         ++ show (length sSizes) ++ "," ++ show (sum sSizes) ++ "," ++ show (count (== 1) sSizes) ++ ","
                      --         ++ showFixed True time1 ++ "," ++ showFixed True time2 ++ "," ++ showFixed True time3) $ return ()
                      return $ Just result
                    Nothing -> do
                      let value = PolyVariantMetrics "dmcfa" 0 m (nameModule (modName mod) ++ "/" ++ name) [] True Nothing
                      BS.writeFile (dir ++ "/" ++ name ++ ".json") (encode (toJSON value))

                      -- trace ("dmcfa," ++ nameModule (modName mod) ++ "/" ++ name ++ "," ++ show d ++ "," ++ show m ++
                      --          ",timeout,0,0,0,0,0,0,0,0,0,0,timeout,timeout,timeout") $ 
                      return Nothing
                (total, timeouts) <- recur rest
                case result of
                  Just res -> return (res + total, timeouts)
                  Nothing -> return (total, timeouts + 1)

    -- tstart <- getCurrentTime
    (r, timeouts) <- recur values
    -- tend <- getCurrentTime
    -- let x :: Double
    --     x = fromIntegral r / fromIntegral (length values)
    -- unless (null values) $ do
    --   trace ("d=" ++ show d ++ ",m=" ++ show m) $ return ()
    --   trace ("Result " ++ show r ++ " / " ++ show (length values)) $ return ()
    --   trace ("Result " ++ show (truncate' (x * 100) 2) ++ "%, time: " ++ show (diffUTCTime tend tstart)) $ return ()
    -- trace ("l: " ++ show (length l)) $ return ()
    return $ not (null values)

truncate' :: Double -> Int -> Double
truncate' x n = fromIntegral (floor (x * t)) / t
    where t = 10^n

average :: [Int] -> Double
average xs = if null xs then 0 else fromIntegral (sum xs) / fromIntegral (length xs)

type CacheInfo = ([Int], [Int], [Int], [Int])

compareResult :: (AbValue, M.Map Addr AbValue, CacheInfo, StoreMetrics) -> (AbValue, M.Map Addr AbValue, CacheInfo, StoreMetrics) -> S.Set (AbValue, AbValue) -> Bool
compareResult (result, rMap, aci, sm1) (expected, eMap, bci, sm2) checked = do
  let objMatch :: (Name, [(Name, Addr)]) -> (Name, [(Name, Addr)]) -> Bool
      objMatch (name, args) (name2, args2) =
         let argsMatch = zipWith (\(n, a) (n2, a2) ->
                  let arg1 = fromJust $ M.lookup a rMap
                      arg2 = fromJust $ M.lookup a2 eMap in
                  n == n2 && compareResult (arg1, rMap, aci, sm1) (arg2, eMap, bci, sm2) (S.insert (result, expected) checked)) args args2
         in name == name2 && and argsMatch
      conMatch :: (Name, [Name]) -> (Name, [Name]) -> Bool
      conMatch (name, args) (name2, args2) = name == name2
  if S.member (result, expected) checked then
    True
  else if alits result `litXEquiv` alits expected then
        -- Make sure that all the result values are in the expected, no more.
    let matches = all (\obj -> any (objMatch obj) (S.toList $ aobjs expected)) (S.toList $ aobjs result)
        matchesx = matches && all (\con -> any (conMatch con) (S.toList $ acons expected)) (S.toList $ acons result)
     in matchesx -- trace ("passed: " ++ show matchesx ++ "\n" ++ show result ++ "\n" ++ show expected) $ matchesx
  else
    -- trace (" FAILED:\nGot: " ++ show result ++ "\nExpected:\n" ++ show expected) 
    False

isAppExpr :: Expr -> Bool
isAppExpr e =
    case e of
      C.App{} -> True
      C.TypeApp e _ -> isAppExpr e
      C.TypeLam _ e -> isAppExpr e
      _ -> False
isApp :: ExprContext -> Bool
isApp e =
  case maybeExprOfCtx e of
    Just e -> isAppExpr e
    _ -> False

isIndirectAppFun :: ExprContext -> Bool
isIndirectAppFun e =
  case e of
    AppCLambda _ _ (C.Var _ _) -> True
    AppCLambda _ _ (C.TypeApp (C.Var _ _) _) -> True
    _ -> False

extractMetrics :: M.Map FixInput FixOutput -> StoreMetrics
extractMetrics cache =
  let
    -- Lookup helpers
    lookupVal :: Addr -> AbValue
    lookupVal UnitAddr = emptyAbValue -- Approximation
    lookupVal addr = case M.lookup (VStore addr) cache of
      Just (SValue v) -> v
      _ -> emptyAbValue

    resolveRValue :: S.Set RValue -> AbValue
    resolveRValue rvals = mconcat [ lookupVal addr | RVAddr addr <- S.toList rvals ]

    -- Store Subsets
    vEntries = M.toList $ M.filterWithKey (\k _ -> case k of VStore _ -> True; _ -> False) cache
    kEntries = M.toList $ M.filterWithKey (\k _ -> case k of KStore _ -> True; _ -> False) cache

    -- Metrics
    numStore = length vEntries + length kEntries
    numLit = count (\(_, SValue val) -> not (litIsBottomX (alits val))) vEntries
    literalTopCount = count (\(_, SValue val) -> litIsTopX (alits val)) vEntries
    numStruct = count (\(_, SValue val) -> semSizeOf val >= 1) vEntries
    numCont = length kEntries

    valSemSingletons = count (\(_, SValue val) -> semSizeOf val == 1) vEntries
    contSemSingletons = count (\(_, KValue ks) -> S.size ks == 1) kEntries

    abStructuralSize (AbValue cls cons prims objs _ _) =
       S.size (S.map fst cls) + S.size (S.map fst cons) + S.size prims + S.size (S.map fst objs)

    valStrSingletons = count (\(_, SValue val) -> abStructuralSize val == 1) vEntries

    kStructuralSize ks = S.size $ S.map (\k -> case k of { KAddr frame _ _ _ -> frame; EndKAddr -> FCount }) ks
    contStrSingletons = count (\(_, KValue ks) -> kStructuralSize ks == 1) kEntries

    -- Returns
    callSites = [ (ctx, S.map fst val, e) | (Step (CEval e _ ctx), RValue val) <- M.toList cache, isApp e]
    callTargets = [(ctx, S.map fst val, e) | (Step (CEval e _ ctx), RValue val) <- M.toList cache, isIndirectAppFun e]
    callTargetCount = S.size $ S.fromList (map (\(_, _, e) -> e) callTargets)

    semReturnSingletons = count (\(_, val, _) -> semSizeOf (resolveRValue val) == 1) callSites
    strReturnSingletons = count (\(_, val, _) -> abStructuralSize (resolveRValue val) == 1) callSites

    semTargetSingletons = count (\(_, val, _) -> semSizeOf (resolveRValue val) == 1) callTargets
    strTargetSingletons = count (\(_, val, _) -> abStructuralSize (resolveRValue val) == 1) callTargets

    -- Maps
    exprToValSemSizes = M.fromListWith (++) [ (show $ contextId c, [semSizeOf (resolveRValue (S.map fst vs))]) | (Step (CEval c _ _), RValue vs) <- M.toList cache, 0 /= semSizeOf (resolveRValue (S.map fst vs))]
    exprToValStrSizes = M.fromListWith (++) [ (show $ contextId c, [abStructuralSize (resolveRValue (S.map fst vs))]) | (Step (CEval c _ _), RValue vs) <- M.toList cache , 0 /= abStructuralSize (resolveRValue (S.map fst vs))]
    callToSemRetSizes = M.fromListWith (++) [ (show $ contextId c, [semSizeOf (resolveRValue vs)]) | (ctx, vs, c) <- callSites, 0 /= semSizeOf (resolveRValue vs) ]
    applyContSemSizes = M.fromListWith (++) [ (show $ kAddrId c, [semSizeOf (resolveRValue (S.map fst vs))]) | (Step (CApply c _ _), RValue vs) <- M.toList cache, 0 /= semSizeOf (resolveRValue (S.map fst vs)) ]
    applyContStrSizes = M.fromListWith (++) [ (show $ kAddrId c, [abStructuralSize (resolveRValue (S.map fst vs))]) | (KStore c, RValue vs) <- M.toList cache, 0 /= abStructuralSize (resolveRValue (S.map fst vs)) ]
    applyContRetSizes = M.fromListWith (++) [ (show $ kAddrId c, [abStructuralSize (resolveRValue (S.map fst vs))]) | (Step (CApply c _ _), RValue vs) <- M.toList cache, 0 /= abStructuralSize (resolveRValue (S.map fst vs))  ]
    callTargetSemSizes = M.fromListWith (++) [ (show $ contextId c, [semSizeOf (resolveRValue (S.map fst vs))]) | (Step (CEval c _ _), RValue vs) <- M.toList cache, isIndirectAppFun c, 0 /= semSizeOf (resolveRValue (S.map fst vs))]
    callTargetStrSizes = M.fromListWith (++) [ (show $ contextId c, [abStructuralSize (resolveRValue (S.map fst vs))]) | (Step (CEval c _ _), RValue vs) <- M.toList cache, isIndirectAppFun c, 0 /= abStructuralSize (resolveRValue (S.map fst vs)) ]

    -- TODO: Literal values 
    
    -- Histograms
    ctxsPerExpr = M.fromListWith S.union [(e, S.singleton ctx) | (Step (CEval e _ ctx), RValue val) <- M.toList cache]
    ctxsPerApply = M.fromListWith S.union [(kAddrId k, S.singleton ctx) | (Step (CApply k _ ctx), RValue val) <- M.toList cache]
    
    -- Total FixInput states
    numTotalFixInput = M.size cache
  in StoreMetrics
      numStore numLit numStruct numCont callTargetCount numTotalFixInput
      valSemSingletons contSemSingletons valStrSingletons contStrSingletons
      semReturnSingletons strReturnSingletons semTargetSingletons strTargetSingletons
      literalTopCount
      exprToValSemSizes applyContSemSizes callToSemRetSizes
      applyContRetSizes exprToValStrSizes applyContStrSizes
      callTargetSemSizes callTargetStrSizes

getAbResult :: PostFixAAMR x s e (AbValue, M.Map Addr AbValue, ([Int], [Int], [Int], [Int]), StoreMetrics)
getAbResult = do
  cache <- getCache
  -- ... existing cacheInfo calculation ...
  let cacheInfo = M.foldlWithKey (\acc@(evals, applies, ksizes, ssizes) k v -> case k of
                        VStore BindingAddr{} -> case v of SValue res -> (evals, applies, ksizes, semSizeOf res : ssizes)
                                                          Bottom -> (evals, applies, ksizes, ssizes)
                        VStore BindImplicitAddr{} -> case v of SValue res -> (evals, applies, ksizes, semSizeOf res : ssizes)
                                                               Bottom -> (evals, applies, ksizes, ssizes)
                        VStore BindKImplicitAddr{} -> case v of SValue res -> (evals, applies, ksizes, semSizeOf res : ssizes)
                                                                Bottom -> (evals, applies, ksizes, ssizes)
                        VStore ConImplicitAddr{} -> case v of SValue res -> (evals, applies, ksizes, semSizeOf res : ssizes)
                                                              Bottom -> (evals, applies, ksizes, ssizes)
                        VStore EndVAddr -> case v of SValue res -> (evals, applies, ksizes, semSizeOf res : ssizes)
                                                     Bottom -> (evals, applies, ksizes, ssizes)
                        VStore UnitAddr -> (evals, applies, ksizes, ssizes)
                        KStore KAddr{} -> case v of KValue res -> (evals, applies, length res : ksizes, ssizes)
                                                    Bottom -> (evals, applies, ksizes, ssizes)
                        KStore EndKAddr -> case v of KValue res -> (evals, applies, length res : ksizes, ssizes)
                                                     Bottom -> (evals, applies, ksizes, ssizes)
                        Step CEval{} -> case v of RValue vals -> (length vals : evals, applies, ksizes, ssizes)
                                                  Bottom -> (evals, applies, ksizes, ssizes)
                        Step CApply{} -> case v of RValue vals -> (evals, length vals : applies, ksizes, ssizes)
                                                   Bottom -> (evals, applies, ksizes, ssizes)
                        Step CContinue{} -> case v of RValue vals -> (length vals : evals, applies, ksizes, ssizes)
                                                      Bottom -> (evals, applies, ksizes, ssizes)
                        Step CHandleEffects{} -> case v of RValue vals -> (evals, length vals : applies, ksizes, ssizes)
                                                           Bottom -> (evals, applies, ksizes, ssizes)
                        Step CHandleLocal{} -> case v of RValue vals -> (evals, length vals : applies, ksizes, ssizes)
                                                         Bottom -> (evals, applies, ksizes, ssizes))
                        ([], [], [], []) cache
  let getValue addr addrsx =
        case M.lookup (VStore addr) cache of
          Just (SValue res) ->
            let !env = foldl (\acc addr ->
                            if S.member addr addrsx then
                              acc
                            else
                              let (v, map') = getValue addr (S.insert addr addrsx)
                              in M.insert addr v (M.union acc map')
                         ) M.empty (addrs res)
            in (res, env)
          Nothing -> error ("Couldn't find " ++ show addr ++ " in cache " ++ show (filter (\k -> case k of {VStore{} -> True; _ -> False}) (M.keys cache)))
  let (finalRes, finalEnv) = getValue EndVAddr S.empty

  let metrics = extractMetrics cache

  return (finalRes, finalEnv, cacheInfo, metrics)
evalMainK :: BuildContext
  -> TypeChecker -> Module -> Int
  -> IO Bool
evalMainK bc build mod m = do
  runQueryAtRange bc build mod m $ \ctx -> do
    c <- inject ctx
    -- trace (show (modCtx ctx)) $ return ()
    res <- doStep c
    case res of
      RV (RVAddr addr, _) -> do
        rebind addr EndVAddr
        return ()
      RV _ ->
        -- trace("Expected main to evaluate to an address" ++ show res)
        doBottom
    return ()

writeSimpleDependencyGraph :: forall e s . String ->  M.Map FixInput (FixOutput, Integer, [ContX e s FixInput FixOutput FixChange], [ContF e s FixInput FixOutput FixChange]) -> IO ()
writeSimpleDependencyGraph name cache = do
  let cache' = M.filterWithKey (\k v -> case k of {
      Step (CEval {}) -> True;
      Step (CApply {}) -> True;
      _ -> False}) cache
  -- trace ("cache': " ++ show (length cache') ++ " out of " ++ show (length cache)) $ return ()
  let values = M.foldl (\acc (v, toId, conts, fconts) -> acc ++ fmap (\(ContX _ from fromId) -> (v, from, fromId, toId)) conts) [] cache'
  let nodes = M.foldlWithKey (\acc k (v, toId, conts, fconts) -> (toId,k,v):acc) [] cache'
  let edges = S.toList $ S.fromList $ fmap (\(v, f, fi, ti) -> (fi, ti)) values
  let dot = "digraph G {\n"
            ++ intercalate "\n" (fmap (\(a, b) -> show a ++ " -> " ++ show b) edges) ++ "\n"
            ++ intercalate "\n" (fmap (\(fi, k, v) -> show fi ++ " [label=\"" ++ label k ++ "\n\n" ++ label v ++ "\"]") nodes)
            ++ "\n 0 [label=\"Start\"]\n"
            ++ "\n}"
  writeFile ("scratch/debug/graph_" ++ name ++ ".dot") dot
  return ()


showEscape :: Show a => a -> String
showEscape = escape . show

escape :: String -> String
escape (s:xs) = if s == '\"' then "\\" ++ s:escape xs else s : escape xs
escape [] = []

instance Label FixOutput where
  label o = escape $ show o

instance Label FixInput where
  label i = escape $ show i