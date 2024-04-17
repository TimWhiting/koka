{-# LANGUAGE RankNTypes #-}
module Core.Demand.ConstantProp where
import Core.Core
import Core.Demand.FixpointMonad
import Compile.Options (Terminal(..), Flags)
import GHC.IO (unsafePerformIO)
import Core.Demand.DemandMonad
import Compile.BuildMonad (BuildContext, Build)
import Core.Demand.DemandAnalysis
import Core.Demand.StaticContext
import Core.Demand.AbstractValue
import Debug.Trace (trace)
import qualified Data.Set as S
import Data.List (intercalate)
import qualified Data.Map.Strict as M
import Common.Error (Errors)

findAllVars :: ExprContext -> FixDemandR x s e ExprContext
findAllVars ctx =
  visitEachChild ctx $ do
      childCtx <- currentContext <$> getEnv
      case maybeExprOfCtx childCtx of
        Just Var{} -> each [return childCtx]
        _ -> findAllVars childCtx

propConstants :: TypeChecker -> State ExprContext () (M.Map ExprContext AChange) -> Core -> IO (State ExprContext () (M.Map ExprContext AChange))
propConstants build state core = do
  (l, s) <-
    runFix (emptyEnv 2 BasicEnvs build ()) state $ do
        (_, ctx) <- loadModule (coreProgName core)
        st <- getState
        let varsLeft = S.toList $ finalResults st
        case varsLeft of
          [] -> setResults S.empty
          v:rst -> do
            -- TODO: Set some gas limit
            res <- qeval (v, indeterminateStaticCtx 2 v)
            -- TODO: Check gas limit and assume the variable is not constant if gas ran out
            setResults $ S.fromList rst
            updateAdditionalState $ \s -> M.insert v res s
  return s

constantPropagation :: TypeChecker -> BuildContext -> Core -> IO ()
constantPropagation build bc core = do
  (lattice, state) <- runFix (emptyEnv 2 BasicEnvs build ()) (emptyState bc (-1) ()) $ do
    (_, ctx) <- loadModule (coreProgName core)
    var <- findAllVars ctx
    addResult var
  let vars = S.toList $ finalResults state
  -- TODO: Run an evaluation query on each var separately or in batches until some gas limit is hit
  propConstants build (transformState (\s -> M.empty) 2 state) core
  trace (intercalate "\n" $ map showSimpleContext vars) $ return ()
  return ()
