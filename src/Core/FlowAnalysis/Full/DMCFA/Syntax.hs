{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant return" #-}
{-# HLINT ignore "Redundant if" #-}
module Core.FlowAnalysis.Full.DMCFA.Syntax where

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
import Core.FlowAnalysis.Full.DMCFA.DMCFA
import Core.FlowAnalysis.Full.DMCFA.AbstractValue
import Core.FlowAnalysis.Full.DMCFA.Monad
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


analyzeEach :: Show d => ExprContext -> (ExprContext -> FixAAMR a b c d) -> FixAAMR a b c d
analyzeEach = analyzeEachChild


runQueryAtRange :: HasCallStack => BuildContext
  -> TypeChecker
  -> Module -> Int -> Int
  -> (ExprContext -> FixAAMR FixChange () () ())
  -> IO Bool
runQueryAtRange bc build mod m d doQuery =
  do
    (_, s, ctxs) <- runFixFinish (emptyBasicEnv m d build False ()) (emptyBasicState bc ()) $
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
                result <- timeout 50000000 $ do
                  tstart <- getCurrentTime
                  trace (" Analyzing " ++ show name) $ return ()
                  (l, _, analysisResult) <- runFixFinishC (emptyBasicEnv m d build True ()) s' $ do
                                  runFixCont $ do
                                    (_,ctx) <- loadModule (modName mod)
                                    -- trace ("Context: " ++ show (contextId ctx)) $ return ()
                                    withEnv (\e -> e{currentModContext = ctx, currentContext = ctx}) $ doQuery mainCtx
                                  ress' <- getAbResult
                                  -- trace ("result': " ++ show ress') $ return ()
                                  return ress'
                  tend <- getCurrentTime
                  (_, _, expectedResult) <- runFixFinishC (emptyBasicEnv m d build True ()) s' $ do
                                  runFixCont $ do
                                    (_,ctx) <- loadModule (modName mod)
                                    -- trace ("Context: " ++ show (contextId ctx)) $ return ()
                                    withEnv (\e -> e{currentModContext = ctx, currentContext = ctx}) $ doQuery resCtx
                                  ress' <- getAbResult
                                  -- trace ("expected': " ++ show ress') $ return ()
                                  return ress'
                  let !result = (if compareResult analysisResult expectedResult S.empty then 1 else 0)
                  let (_, _, (evals, applies, kSizes, sSizes)) = analysisResult
                  -- writeSimpleDependencyGraph (moduleNameToPath (modName mod)) l
                  trace ("dmcfae," ++ nameModule (modName mod) ++ "/" ++ name ++ "," ++ show d ++ "," ++ show m ++ "," ++
                          show result ++ "," ++ show (length evals) ++ "," ++ show (length applies) ++ ","
                          ++ show (average evals) ++ "," ++ show (average applies) ++ ","
                          ++ show (average kSizes) ++ "," ++ show (average sSizes) ++ ","
                          ++ showFixed True (nominalDiffTimeToSeconds $ diffUTCTime tend tstart)) $ return ()
                  return result
                case result of
                  Nothing -> trace ("dmcfae," ++ nameModule (modName mod) ++ "/" ++ name ++ "," ++ show d ++ "," ++ show m ++ ",0,0,0,0,0,0,0,timeout") $ return ()
                  Just _ -> return ()
                (total, timeouts) <- recur rest
                case result of
                  Just res -> return (res + total, timeouts)
                  _ ->
                    return (total, timeouts + 1)
            
                
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

compareResult :: (AbValue, M.Map Addr AbValue, CacheInfo) -> (AbValue, M.Map Addr AbValue, CacheInfo) -> S.Set (AbValue, AbValue) -> Bool
compareResult (result, rMap, aci) (expected, eMap, bci) checked = do
  let objMatch :: (ExprContext, TName, [(Name, Addr)]) -> (ExprContext, TName, [(Name, Addr)]) -> Bool
      objMatch (_, name, args) (_, name2, args2) =
         let argsMatch = zipWith (\(n, a) (n2, a2) ->
                  let arg1 = fromJust $ M.lookup a rMap
                      arg2 = fromJust $ M.lookup a2 eMap in
                  n == n2 && compareResult (arg1, rMap, aci) (arg2, eMap, bci) (S.insert (result, expected) checked)) args args2
         in name == name2 && and argsMatch
      conMatch :: (ExprContext, [Name]) -> (ExprContext, [Name]) -> Bool
      conMatch (name, args) (name2, args2) = eConName name == eConName name2
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

getAbResult :: PostFixAAMR x s e (AbValue, M.Map Addr AbValue, CacheInfo)
getAbResult = do
  cache <- getCache
  let cacheInfo = M.foldlWithKey (\acc@(evals, applies, ksizes, ssizes) k v -> case k of
                        VStore (BindingAddr{}) -> case v of SValue res -> (evals, applies, ksizes, sizeOf res : ssizes)
                        VStore (BindImplicitAddr{}) -> case v of SValue res -> (evals, applies, ksizes, sizeOf res : ssizes)
                        VStore EndVAddr -> case v of SValue res -> (evals, applies, ksizes, sizeOf res : ssizes)
                        VStore (TopAddr{}) -> case v of SValue res -> (evals, applies, ksizes, sizeOf res : ssizes)
                        KStore (ImplicitAddr{}) -> case v of KValue res -> (evals, applies, length res : ksizes, ssizes)
                        KStore EndKAddr -> case v of KValue res -> (evals, applies, length res : ksizes, ssizes)
                        KStore (ImplicitLAddr{}) -> case v of KValue res -> (evals, applies, length res : ksizes, ssizes)
                        Step (CEval{}) -> case v of RValue vals -> (length vals : evals, applies, ksizes, ssizes)
                        Step (CContinue{}) -> case v of RValue vals -> (length vals : evals, applies, ksizes, ssizes)
                        Step (CApply{}) -> case v of RValue vals -> (evals, length vals : applies, ksizes, ssizes)
                                                     Bottom -> acc
                        _ -> acc) ([], [], [], []) cache
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
  return (finalRes, finalEnv, cacheInfo)
evalMain :: BuildContext
  -> TypeChecker -> Module -> Int -> Int
  -> IO Bool
evalMain bc build mod m d = do
  runQueryAtRange bc build mod m d $ \ctx -> do
    c <- inject ctx
    res <- doStep c
    case res of 
      RV (RVAddr addr) -> do
        rebind addr EndVAddr
        return ()
      RV _ -> 
        trace("Expected main to evaluate to an address" ++ show res)
        doBottom
    return ()

writeSimpleDependencyGraph :: forall e s . String ->  M.Map FixInput (FixOutput, Integer, [ContX e s FixInput FixOutput FixChange], [ContF e s FixInput FixOutput FixChange]) -> IO ()
writeSimpleDependencyGraph name cache = do
  let cache' = M.filterWithKey (\k v -> case k of {
      Step (CEval {}) -> True; 
      Step (CApply {}) -> True; 
      Step (CContinue {}) -> True;
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