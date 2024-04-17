module Core.Demand.ConstantProp where
import Core.Core
import Core.Demand.FixpointMonad
import Compile.Options (Terminal(..), Flags)
import GHC.IO (unsafePerformIO)
import Core.Demand.DemandMonad
import Compile.BuildContext (BuildContext)
import Core.Demand.DemandAnalysis
import Core.Demand.StaticContext
import Core.Demand.AbstractValue
import Debug.Trace (trace)
import qualified Data.Set as S
import Data.List (intercalate)
import qualified Data.Map.Strict as M

findAllVars :: ExprContext -> FixDemandR x s e ExprContext
findAllVars ctx =
  visitEachChild ctx $ do
      case maybeExprOfCtx ctx of
        Just Var{} -> each [return ctx, findAllVars ctx]
        _ -> findAllVars ctx

propConstants :: Terminal -> Flags -> State ExprContext () (M.Map ExprContext AChange) -> Core -> IO (State ExprContext () (M.Map ExprContext AChange))
propConstants terminal flags state core = do
  (l, s, _) <-
    runFixFinishC (emptyEnv 2 BasicEnvs terminal flags ()) state $ do
      runFixCont $ do
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

constantPropagation :: Flags -> Terminal -> BuildContext -> Core -> IO ()
constantPropagation flags terminal bc core = do
  (lattice, state) <- runFix (emptyEnv 2 BasicEnvs terminal flags ()) (emptyState bc (-1) ()) $ do
    (_, ctx) <- loadModule (coreProgName core)
    vars <- findAllVars ctx
    addResult vars
  let vars = S.toList $ finalResults state
  -- TODO: Run an evaluation query on each var separately or in batches until some gas limit is hit
  propConstants terminal flags (transformState (\s -> M.empty) 2 state) core
  trace (intercalate "\n" $ map showSimpleContext vars) $ return ()
  return ()
