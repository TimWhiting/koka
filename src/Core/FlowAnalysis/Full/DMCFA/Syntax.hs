{-# LANGUAGE RankNTypes #-}
module Core.FlowAnalysis.Full.DMCFA.Syntax where

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
import Core.FlowAnalysis.Full.DMCFA.DMCFA
import Core.FlowAnalysis.Full.DMCFA.AbstractValue
import Core.FlowAnalysis.Full.DMCFA.Monad
import Common.Failure (HasCallStack)
import Common.NamePrim (nameMain)
import Common.Name (Name(..))
import Common.Range
import Debug.Trace (trace)


analyzeEach :: Show d => ExprContext -> (ExprContext -> FixAAMR a b c d) -> FixAAMR a b c d
analyzeEach = analyzeEachChild

findMainBody :: FixAR x s e i o c ExprContext
findMainBody = do
  ctx <- currentContext <$> getEnv
  case ctx of
    DefCNonRec{} -> do
      let name = unqualify $ getName $ defTName (defOfCtx ctx)
      if "analyze" == nameStem name then do focusDefBody ctx
      else doBottom
    _ -> doBottom

runQueryAtRange :: HasCallStack => BuildContext
  -> TypeChecker
  -> Module -> Int
  -> (ExprContext -> FixAAMR FixChange () () ())
  -> IO (M.Map FixInput (FixOutput FixChange), Maybe ([S.UserExpr], [S.UserDef], [S.External], [Syn.Lit], [(String, Maybe Range)], Set Type), BuildContext)
runQueryAtRange bc build mod m doQuery = do
  (l, s, (r, bc)) <- do
    (_, s, ctxs) <- runFixFinish (emptyBasicEnv m build False ()) (emptyBasicState bc ()) $
              do runFixCont $ do
                    (_,ctx) <- loadModule (modName mod)
                    withEnv (\e -> e{currentModContext = ctx, currentContext = ctx}) $ do
                      trace ("Context: " ++ show (contextId ctx)) $ return ()
                      res <- analyzeEach ctx (const findMainBody)
                      addResult res
                 getResults
    let s' = transformBasicState (const ()) (const S.empty) s
    case S.toList ctxs of
      [] ->
        trace "No main context found" $
        return (M.empty, s', (Nothing, bc))
      [mainCtx] ->
        do
          runFixFinishC (emptyBasicEnv m build True ()) s' $ do
                          runFixCont $ do
                            (_,ctx) <- loadModule (modName mod)
                            trace ("Context: " ++ show (contextId ctx)) $ return ()
                            withEnv (\e -> e{currentModContext = ctx, currentContext = ctx}) $ doQuery mainCtx
                          res <- S.toList <$> getResults
                          buildc' <- buildc <$> getStateR
                          -- let achanges = map (\(AC c) -> c) (filter (\c -> case c of {SValue ac -> True; _ -> False}) res)
                          --     (_, resM) = foldl (addChange . snd) (error "", emptyAbValue) achanges
                          ress' <- getAbResult
                          trace ("ress': " ++ show ress') $ return ()
                          return (Just ress', buildc')
  -- trace ("l: " ++ show (length l)) $ return ()
  writeDependencyGraph (moduleNameToPath (modName mod)) l
  -- writeSimpleDependencyGraph (moduleNameToPath (modName mod)) l
  return (M.map (\(x, _, _, _) -> x) l, r, bc)

evalMain :: BuildContext
  -> TypeChecker -> Module -> Int
  -> IO (Maybe ([S.UserExpr], [S.UserDef], [S.External], [S.Lit], [(String, Maybe Range)],
                                   Set Type), BuildContext)
evalMain bc build mod m = do
  (lattice, r, bc) <- runQueryAtRange bc build mod m $ \ctx -> do
    doStep (inject ctx) 
    return ()
  return (r, bc)

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


getAbResult :: PostFixAAMR x s e ([S.UserExpr], [S.UserDef], [S.External], [Syn.Lit], [(String, Maybe Range)], Set Type)
getAbResult = do
  cache <- getCache
  case M.lookup (VStore endVAddr) cache of 
    Nothing -> return ([], [], [], [], [], S.empty)
    Just (SValue res) -> do
      let vals = [res]
          lams = map fst $ concatMap (S.toList . aclos) vals
          i = intV res
          f = floatV res
          c = charV res
          s = stringV res
          topTypes = S.fromList $ topTypesOf (i, f, c, s)
          vs = syntaxLitsOf (i, f, c, s)
          cs = map fst $ concatMap (S.toList . acons) vals
      consts <- mapM toSynConstr cs
      source <- mapM findSourceExpr lams
      let sourceLambdas = map (\(SourceExpr e _) -> e) $ filter (\s -> case s of {SourceExpr _ _ -> True; _ -> False}) source
          sourceDefs = map (\(SourceDef e _) -> e) $ filter (\s -> case s of {SourceDef _ _ -> True; _ -> False}) source
          sourceExterns = map (\(SourceExtern e _) -> e) $ filter (\s -> case s of {SourceExtern _ _ -> True; _ -> False}) source
      return $ trace
        ("eval " ++
        "\nresult:\n----------------------\n" ++ showSimpleAbValue res ++ "\n----------------------\n")
        (sourceLambdas, sourceDefs, sourceExterns, vs, consts, topTypes)

showEscape :: Show a => a -> String
showEscape = escape . show

escape :: String -> String
escape (s:xs) = if s == '\"' then "\\" ++ s:escape xs else s : escape xs
escape [] = []

instance Label (FixOutput m) where
  label o = escape $ show o

instance Label FixInput where
  label i = escape $ show i