{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
module Core.FlowAnalysis.Full.AAM.Syntax where

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
import Core.FlowAnalysis.Full.AAM.AAM
import Core.FlowAnalysis.Full.AbstractValue
import Core.FlowAnalysis.Full.AAM.Monad
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
        recur l =
          case l of
            [] -> if nameModule (modName mod) `startsWith` "std/core" then
                return 0
              else
                trace ("No analysis context found in " ++ nameModule (modName mod)) $
                return 0
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
                                -- let achanges = map (\(AC c) -> c) (filter (\c -> case c of {SValue ac -> True; _ -> False}) res)
                                --     (_, resM) = foldl (addChange . snd) (error "", emptyAbValue) achanges
                                ress' <- getAbResult
                                trace ("ress': " ++ show ress') $ return ()
                                return ress'
                
                let !result = (if compareResult name analysisResult expectedResult then 1 else 0)
                total <- recur rest
                return $ result + total
    r <- recur values
    let x :: Double
        x = fromIntegral r / fromIntegral (length values)
    trace ("Result " ++ show r ++ " / " ++ show (length values)) $ return ()
    trace ("Result " ++ show (truncate' (x * 100) 2) ++ "%") $ return ()
    -- trace ("l: " ++ show (length l)) $ return ()
    -- writeSimpleDependencyGraph (moduleNameToPath (modName mod)) l
    return $ not (null values)

truncate' :: Double -> Int -> Double
truncate' x n = fromIntegral (floor (x * t)) / t
    where t = 10^n

compareResult :: [Char] -> AbValue -> AbValue -> Bool
compareResult name analysisResult expectedResult = do
  if alits analysisResult == alits expectedResult then
    trace (name ++ " passed") True
  else
    trace (name ++ " FAILED:\nGot: " ++ show analysisResult ++ "\nExpected:\n" ++ show expectedResult) False

getAbResult :: PostFixAAMR x s e AbValue
getAbResult = do
  res <- S.toList <$> getResults
  return emptyAbValue

evalMain :: BuildContext
  -> TypeChecker -> Module -> Int -> Int
  -> IO Bool
evalMain bc build mod m d = do
  runQueryAtRange bc build mod m d $ \ctx -> do
    let mkont = KAddr (ctx, M.empty, KTime Nothing (KContour []))
    q <- doStep (Eval ctx M.empty M.empty (kstoreExtend mkont [EndProgram] M.empty) [EndProgram] mkont (KTime Nothing (KContour [])))
    addResult q

writeSimpleDependencyGraph :: forall e s . String ->  M.Map FixInput (FixOutput, Integer, [ContX e s FixInput FixOutput FixChange], [ContF e s FixInput FixOutput FixChange]) -> IO ()
writeSimpleDependencyGraph name cache = do
  let cache' = M.filterWithKey (\k v -> case k of {Eval {} -> True; Cont {} -> True}) cache
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

instance Label (FixOutput) where
  label (A a) = escape $ showSimpleAbValue a
  label Bottom = "Bottom"

showCont :: [Frame] -> [Doc]
showCont l =  map (text . show) (reverse l)-- (take 2 $ reverse l)

instance Label FixInput where
  label (Eval q env _ _ kont mkont time) = escape $ show (vcat (text "EVAL": showCont kont ++ [text (showSimpleContext q), text (showSimpleEnv env)]))
  label (Cont ch _ _ kont mkont time) = escape $ show (vcat $ text "CONT" :  showCont kont ++ [text $ show ch])