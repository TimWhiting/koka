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
import Data.Time (getCurrentTime, diffUTCTime)


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
        recur :: [AProgram] -> IO Int
        recur l =
          case l of
            [] -> if nameModule (modName mod) `startsWith` "std/core" then
                return 0
              else
                -- trace ("No analysis context found in " ++ nameModule (modName mod)) $
                return 0
            (AProgram name mainCtx resCtx):rest ->
              do
                (_, _, analysisResult) <- runFixFinishC (emptyBasicEnv m d build True ()) s' $ do
                                runFixCont $ do
                                  (_,ctx) <- loadModule (modName mod)
                                  -- trace ("Context: " ++ show (contextId ctx)) $ return ()
                                  withEnv (\e -> e{currentModContext = ctx, currentContext = ctx}) $ doQuery mainCtx
                                ress' <- getAbResult
                                -- trace ("ress': " ++ show ress') $ return ()
                                return ress'
                (_, _, expectedResult) <- runFixFinishC (emptyBasicEnv m d build True ()) s' $ do
                                runFixCont $ do
                                  (_,ctx) <- loadModule (modName mod)
                                  -- trace ("Context: " ++ show (contextId ctx)) $ return ()
                                  withEnv (\e -> e{currentModContext = ctx, currentContext = ctx}) $ doQuery resCtx
                                ress' <- getAbResult
                                -- trace ("ress': " ++ show ress') $ return ()
                                return ress'
                let !result = (if compareResult analysisResult expectedResult then 1 else 0)
                total <- recur rest
                return $ result + total
    tstart <- getCurrentTime
    r <- recur values
    tend <- getCurrentTime
    let x :: Double
        x = fromIntegral r / fromIntegral (length values)
    unless (null values) $ do
      trace ("d=" ++ show d ++ ",m=" ++ show m) $ return ()
      trace ("Result " ++ show r ++ " / " ++ show (length values)) $ return ()
      trace ("Result " ++ show (truncate' (x * 100) 2) ++ "%, time: " ++ show (diffUTCTime tend tstart)) $ return ()
    -- trace ("l: " ++ show (length l)) $ return ()
    -- writeSimpleDependencyGraph (moduleNameToPath (modName mod)) l
    return $ not (null values)

truncate' :: Double -> Int -> Double
truncate' x n = fromIntegral (floor (x * t)) / t
    where t = 10^n

compareResult :: (AbValue, M.Map Addr AbValue) -> (AbValue, M.Map Addr AbValue) -> Bool
compareResult (result, rMap) (expected, eMap) = do
  let objMatch :: (TName, [(Name, Addr)]) -> (TName, [(Name, Addr)]) -> Bool
      objMatch (name, args) (name2, args2) = 
         let argsMatch = zipWith (\(n, a) (n2, a2) -> 
                  let arg1 = fromJust $ M.lookup a rMap
                      arg2 = fromJust $ M.lookup a2 rMap in
                  n == n2 && compareResult (arg1, rMap) (arg2, eMap)) args args2
         in name == name2 && all id argsMatch
  if alits result == alits expected then
    let matches = all (\obj -> any id $ zipWith objMatch (S.toList $ aobjs result) (repeat obj)) (S.toList $ aobjs expected)
    in
      trace ("passed\n" ++ show result ++ "\n" ++ show expected) 
      matches
  else
    -- trace (name ++ " FAILED:\nGot: " ++ show analysisResult ++ "\nExpected:\n" ++ show expectedResult) 
    False

getAbResult :: PostFixAAMR x s e (AbValue, M.Map Addr AbValue)
getAbResult = do
  cache <- getCache
  let getValue addr = 
        case M.lookup (VStore addr) cache of 
          Just (SValue res) -> 
            let env = foldl (\acc addr -> 
                            let (v, map') = getValue addr
                            in M.insert addr v (M.union acc map')
                         ) M.empty (addrs res)
            in (res, env)
  return $ getValue EndVAddr

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