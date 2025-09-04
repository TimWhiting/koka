{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
module Core.FlowAnalysis.Full.DMCFAR.Syntax where

import Data.List (intercalate, find, minimumBy)
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
import Core.FlowAnalysis.Full.DMCFAR.DMCFA
import Core.FlowAnalysis.Full.DMCFAR.AbstractValue
import Core.FlowAnalysis.Full.DMCFAR.Monad
import Common.Failure (HasCallStack)
import Common.NamePrim (nameMain)
import Common.Name (Name(..))
import Common.Range
import Debug.Trace (trace)
import Common.File (startsWith)
import Control.Monad (unless)
import Data.Time (getCurrentTime, diffUTCTime, nominalDiffTimeToSeconds)
import System.Timeout (timeout)
import Data.Fixed (showFixed)


analyzeEach :: Show d => ExprContext -> (ExprContext -> FixAAMR a b c d) -> FixAAMR a b c d
analyzeEach = analyzeEachChild

runQueryAtRange :: HasCallStack => BuildContext
  -> TypeChecker
  -> Module -> Int -> Int
  -> (ExprContext -> FixAAMR FixChange () () ())
  -> IO Bool
runQueryAtRange bc build mod m d doQuery = do
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
                  -- trace (" Analyzing " ++ show name) $ return ()
                  (_, _, analysisResult) <- runFixFinishC (emptyBasicEnv m d build True ()) s' $ do
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
                  let (_, _, (evals, confs, mkSizes, kSizes, sSizes)) = analysisResult
                  trace ("dmcfa," ++ nameModule (modName mod) ++ "/" ++ name ++ "," ++ show d ++ "," ++ show m ++ "," ++ 
                          show result ++ "," ++ show (length evals) ++ "," ++ show (length confs) ++ ","
                          ++ show (average evals) ++ "," ++ show (average confs) ++ ","
                          ++ show (average mkSizes) ++ "," ++ show (average kSizes) ++ "," ++ show (average sSizes) ++ ","
                          ++ showFixed True (nominalDiffTimeToSeconds $ diffUTCTime tend tstart)) $ return result
                case result of
                  Nothing -> trace ("dmcfa," ++ nameModule (modName mod) ++ "/" ++ name ++ "," ++ show d ++ "," ++ show m ++ ",0,0,0,0,0,0,0,0,timeout") $ return ()
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
    -- writeSimpleDependencyGraph (moduleNameToPath (modName mod)) l
    return $ not (null values)

truncate' :: Double -> Int -> Double
truncate' x n = fromIntegral (floor (x * t)) / t
    where t = 10^n

average :: [Int] -> Double
average xs = fromIntegral (sum xs) / fromIntegral (length xs)

type CacheInfo = ([Int], [Int], [Int], [Int], [Int])

compareResult :: (AbValue, M.Map Addr AbValue, CacheInfo) -> (AbValue, M.Map Addr AbValue, CacheInfo) -> S.Set (AbValue, AbValue) -> Bool
compareResult (result, rMap, aci) (expected, eMap, bci) checked = do
  let objMatch :: (ExprContext, TName, [(Name, Addr)]) -> (ExprContext, TName, [(Name, Addr)]) -> Bool
      objMatch (_, name, args) (_, name2, args2) =
         let argsMatch = zipWith (\(n, a) (n2, a2) ->
                  let arg1 = fromJust $ M.lookup a rMap
                      arg2 = fromJust $ M.lookup a2 eMap in
                  n == n2 && compareResult (arg1, rMap, aci) (arg2, eMap, bci) (S.insert (result, expected) checked)) args args2
         in name == name2 && all id argsMatch
      conMatch :: (ExprContext, [Name]) -> (ExprContext, [Name]) -> Bool
      conMatch (name, args) (name2, args2) = eConName name == eConName name2
  if S.member (result, expected) checked then 
    True
  else if alits result `litXEquiv` alits expected then
        -- Make sure that all the result values are in the expected, no more.
    let matches = all (\obj -> any id $ zipWith objMatch (repeat obj) (S.toList $ aobjs expected)) (S.toList $ aobjs result)
        matchesx = matches && all (\con -> any id $ zipWith conMatch (repeat con) (S.toList $ acons expected)) (S.toList $ acons result)
     in matchesx
      -- trace ("passed: " ++ show matchesx ++ "\n" ++ show result ++ "\n" ++ show expected) $ matchesx
  else
    -- trace (" FAILED:\nGot: " ++ show result ++ "\nExpected:\n" ++ show expected) 
    False

getAbResult :: PostFixAAMR x s e (AbValue, M.Map Addr AbValue, CacheInfo)
getAbResult = do
  cache <- getCache
  let cacheInfo = M.foldlWithKey (\acc@(evals, applies, mksizes, ksizes, ssizes) k v -> case k of
                        VStore (BindingAddr{}) -> case v of SValue res -> (evals, applies, mksizes, ksizes, sizeOf res : ssizes)
                        VStore (BindImplicitAddr{}) -> case v of SValue res -> (evals, applies, mksizes, ksizes, sizeOf res : ssizes)
                        VStore (ConImplicitAddr{}) -> case v of SValue res -> (evals, applies, mksizes, ksizes, sizeOf res : ssizes)
                        VStore EndVAddr -> case v of SValue res -> (evals, applies, mksizes, ksizes, sizeOf res : ssizes)
                        VStore (TopAddr{}) -> case v of SValue res -> (evals, applies, mksizes, ksizes, sizeOf res : ssizes)
                        KStore (ImplicitAddr{}) -> case v of KValue res -> (evals, applies, mksizes, length res : ksizes, ssizes)
                        KStore EndKAddr -> case v of KValue res -> (evals, applies, mksizes, length res : ksizes, ssizes)
                        KStore (ImplicitLAddr{}) -> case v of KValue res -> (evals, applies, mksizes, length res : ksizes, ssizes)
                        KStore (ImplicitLRAddr{}) -> case v of KValue res -> (evals, applies, mksizes, length res : ksizes, ssizes)
                        MKStore (ImplicitAddr{}) -> case v of MKValue res -> (evals, applies, length res : mksizes, ksizes, ssizes)
                        MKStore EndMKAddr -> case v of MKValue res -> (evals, applies, length res : mksizes, ksizes, ssizes)
                        Step (CEval{}) -> case v of Next confs -> (length confs : evals, applies, mksizes, ksizes, ssizes)
                        Step (CApply{}) -> case v of Next confs -> (length confs : evals, length confs : applies, mksizes, ksizes, ssizes)
                        _ -> acc) ([], [], [], [], []) cache
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
          Nothing -> error ("Couldn't find " ++ show addr ++ " in cache")
  let (finalRes, finalEnv) = getValue EndVAddr S.empty
  return (finalRes, finalEnv, cacheInfo)

evalMainR :: BuildContext
  -> TypeChecker -> Module -> Int -> Int
  -> IO Bool
evalMainR bc build mod m d = do
  runQueryAtRange bc build mod m d $ \ctx -> do
    c <- inject ctx
    doStep c
    return ()

-- writeSimpleDependencyGraph :: forall e s . String ->  M.Map FixInput (FixOutput FixChange, Integer, [ContX e s FixInput FixOutput FixChange], [ContF e s FixInput FixOutput FixChange]) -> IO ()
-- writeSimpleDependencyGraph name cache = do
--   let cache' = M.filterWithKey (\k v -> case k of {Eval {} -> True; Cont {} -> True}) cache
--   -- trace ("cache': " ++ show (length cache') ++ " out of " ++ show (length cache)) $ return ()
--   let values = M.foldl (\acc (v, toId, conts, fconts) -> acc ++ fmap (\(ContX _ from fromId) -> (v, from, fromId, toId)) conts) [] cache'
--   let nodes = M.foldlWithKey (\acc k (v, toId, conts, fconts) -> (toId,k,v):acc) [] cache'
--   let edges = S.toList $ S.fromList $ fmap (\(v, f, fi, ti) -> (fi, ti)) values
--   let dot = "digraph G {\n"
--             ++ intercalate "\n" (fmap (\(a, b) -> show a ++ " -> " ++ show b) edges) ++ "\n"
--             ++ intercalate "\n" (fmap (\(fi, k, v) -> show fi ++ " [label=\"" ++ label k ++ "\n\n" ++ label v ++ "\"]") nodes)
--             ++ "\n 0 [label=\"Start\"]\n"
--             ++ "\n}"
--   writeFile ("scratch/debug/graph_" ++ name ++ ".dot") dot
--   return ()

showEscape :: Show a => a -> String
showEscape = escape . show

escape :: String -> String
escape (s:xs) = if s == '\"' then "\\" ++ s:escape xs else s : escape xs
escape [] = []

instance Label (FixOutput m) where
  label o = escape $ show o

instance Label FixInput where
  label i = escape $ show i