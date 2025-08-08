{-# LANGUAGE RankNTypes #-}
module Core.FlowAnalysis.Full.DMCFA.Syntax where

import Data.List (intercalate, find, minimumBy, groupBy, sort, partition)
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


analyzeEach :: Show d => ExprContext -> (ExprContext -> FixAAMR a b c d) -> FixAAMR a b c d
analyzeEach = analyzeEachChild


runQueryAtRange :: HasCallStack => BuildContext
  -> TypeChecker
  -> Module -> Int -> Int
  -> (ExprContext -> FixAAMR FixChange () () ())
  -> IO ()
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
        recur l =
          case l of
            [] -> if nameModule (modName mod) `startsWith` "std/core" then
                return ()
              else
                trace ("No analysis context found in " ++ nameModule (modName mod)) $
                return ()
            (AProgram name mainCtx resCtx):rest ->
              do
                (_, _, analysisResult) <- runFixFinishC (emptyBasicEnv m d build True ()) s' $ do
                                runFixCont $ do
                                  (_,ctx) <- loadModule (modName mod)
                                  -- trace ("Context: " ++ show (contextId ctx)) $ return ()
                                  withEnv (\e -> e{currentModContext = ctx, currentContext = ctx}) $ doQuery mainCtx
                                res <- S.toList <$> getResults
                                -- let achanges = map (\(AC c) -> c) (filter (\c -> case c of {SValue ac -> True; _ -> False}) res)
                                --     (_, resM) = foldl (addChange . snd) (error "", emptyAbValue) achanges
                                ress' <- getAbResult
                                trace ("ress': " ++ show ress') $ return ()
                                return ress'
                (_, _, expectedResult) <- runFixFinishC (emptyBasicEnv m d build True ()) s' $ do
                                runFixCont $ do
                                  (_,ctx) <- loadModule (modName mod)
                                  -- trace ("Context: " ++ show (contextId ctx)) $ return ()
                                  withEnv (\e -> e{currentModContext = ctx, currentContext = ctx}) $ doQuery resCtx
                                res <- S.toList <$> getResults
                                -- let achanges = map (\(AC c) -> c) (filter (\c -> case c of {SValue ac -> True; _ -> False}) res)
                                --     (_, resM) = foldl (addChange . snd) (error "", emptyAbValue) achanges
                                ress' <- getAbResult
                                trace ("ress': " ++ show ress') $ return ()
                                return ress'
                compareResult name analysisResult expectedResult
                recur rest
    recur values
  -- trace ("l: " ++ show (length l)) $ return ()
  -- writeSimpleDependencyGraph (moduleNameToPath (modName mod)) l
  return ()

compareResult :: [Char] -> AbValue -> AbValue -> IO ()
compareResult name analysisResult expectedResult = do
  if alits analysisResult == alits expectedResult then
    trace (name ++ " passed") $ return ()
  else
    trace (name ++ " FAILED:\nGot: " ++ show analysisResult ++ "\nExpected:\n" ++ show expectedResult) $ return ()

getAbResult :: PostFixAAMR x s e AbValue
getAbResult = do
  cache <- getCache
  case M.lookup (VStore endVAddr) cache of
    Just (SValue res) -> return res


evalMain :: BuildContext
  -> TypeChecker -> Module -> Int -> Int
  -> IO ()
evalMain bc build mod m d = do
  runQueryAtRange bc build mod m d $ \ctx -> do
    doStep (inject ctx)
    return ()
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