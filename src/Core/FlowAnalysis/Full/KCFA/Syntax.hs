{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE BangPatterns #-}
module Core.FlowAnalysis.Full.KCFA.Syntax where

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
import Compile.Options (Terminal, Flags (mSensitivity))
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
                let !result = (if compareResult name analysisResult expectedResult then 1 else 0)
                total <- recur rest
                return $ result + total
    tstart <- getCurrentTime
    r <- recur values
    tend <- getCurrentTime
    let x :: Double
        x = fromIntegral r / fromIntegral (length values)
    unless (null values) $ do
      trace ("k=" ++ show m) $ return ()
      trace ("Result " ++ show r ++ " / " ++ show (length values)) $ return ()
      trace ("Result " ++ show (truncate' (x * 100) 2) ++ "%, time: " ++ show (diffUTCTime tend tstart)) $ return ()
    -- trace ("l: " ++ show (length l)) $ return ()
    -- writeSimpleDependencyGraph (moduleNameToPath (modName mod)) l
    return $ not (null values)

truncate' :: Double -> Int -> Double
truncate' x n = fromIntegral (floor (x * t)) / t
    where t = 10^n

compareResult :: [Char] -> AbValue -> AbValue -> Bool
compareResult name analysisResult expectedResult = do
  if alits analysisResult == alits expectedResult then
    -- trace (name ++ " passed") 
    True
  else
    -- trace (name ++ " FAILED:\nGot: " ++ show analysisResult ++ "\nExpected:\n" ++ show expectedResult) 
    False

getAbResult :: PostFixAAMR x s e AbValue
getAbResult = do
  cache <- getCache
  case M.lookup (VStore EndVAddr) cache of
    Just (SValue res) -> return res

evalMainKCFA :: BuildContext
  -> TypeChecker -> Module -> Int -> Int
  -> IO Bool
evalMainKCFA bc build mod m d = do
  runQueryAtRange bc build mod m d $ \ctx -> do
    ctx' <- inject ctx
    doStep ctx'
    return ()

showEscape :: Show a => a -> String
showEscape = escape . show

escape :: String -> String
escape (s:xs) = if s == '\"' then "\\" ++ s:escape xs else s : escape xs
escape [] = []

instance Label (FixOutput m) where
  label o = escape $ show o

instance Label FixInput where
  label i = escape $ show i