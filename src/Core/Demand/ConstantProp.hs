{-# LANGUAGE RankNTypes #-}
module Core.Demand.ConstantProp where
import Core.Core
import Common.NamePrim
import Type.Type
import Core.Demand.FixpointMonad
import Compile.Options (Terminal(..), Flags)
import GHC.IO (unsafePerformIO)
import Core.Demand.DemandMonad
import Compile.BuildMonad (BuildContext, Build)
import Core.Demand.DemandAnalysis
import Core.Demand.Primitives
import Core.Demand.StaticContext
import Core.Demand.AbstractValue
import Debug.Trace (trace)
import qualified Data.Set as S
import Data.List (intercalate)
import qualified Data.Map.Strict as M
import Common.Error (Errors)
import Data.Maybe (fromMaybe)

findAllVars :: ExprContext -> FixDemandR x s e ExprContext
findAllVars ctx =
  visitEachChild ctx $ do
      childCtx <- currentContext <$> getEnv
      case maybeExprOfCtx childCtx of
        Just (Var (TName n (TCon tc) _) _) | typeConName tc == nameTpInt -> each [return childCtx]
        _ -> findAllVars childCtx

propConstants :: TypeChecker -> State ExprContext () (M.Map ExprContext AbValue) -> Name -> IO (State ExprContext () (M.Map ExprContext AbValue))
propConstants build state name = do
  (l, s) <-
    runFix (emptyEnv 2 BasicEnvs build False ()) state $ do
      createPrimitives
      (_, ctx) <- loadModule name
      st <- getState
      let varsLeft = S.toList $ finalResults st
      case varsLeft of
        [] -> setResults S.empty
        v:rst -> do
          -- TODO: Set some gas limit
          res <- qeval (v, indeterminateStaticCtx 2 v)
          trace (showSimpleContext v ++ " " ++ show res) $ return ()
          -- TODO: Check gas limit and assume the variable is not constant if gas ran out
          setResults $ S.fromList rst
          updateAdditionalState $ \s -> 
            let old = fromMaybe emptyAbValue $ M.lookup v s
                new = addChange old res in
            M.insert v new s
  return s

constantPropagation :: TypeChecker -> BuildContext -> Core -> IO ()
constantPropagation build bc core = do
  (lattice, state) <- runFix (emptyEnv 2 BasicEnvs build False ()) (emptyState bc (-1) ()) $ do
    (_, ctx) <- loadModule (coreProgName core)
    var <- findAllVars ctx
    addResult var
  let vars = S.toList $ finalResults state
  -- TODO: Run an evaluation query on each var separately or in batches until some gas limit is hit
  propAllConstants build (transformState (\s -> M.empty) (\s -> s) (-1) state) (coreProgName core)
  -- trace (intercalate "\n" $ map showSimpleContext vars) $ return ()
  return ()

propAllConstants :: TypeChecker -> State ExprContext () (M.Map ExprContext AbValue) -> Name -> IO (M.Map ExprContext AbValue)
propAllConstants build state name = do
  s <- propConstants build state name
  let varsLeft = finalResults s
  let results = additionalState s
  if varsLeft == S.empty
    then return results
    else propAllConstants build (transformState id id (-1) s) name
