{-# LANGUAGE RankNTypes #-}
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

intV :: AbValue -> SLattice Integer
intV a = intVL (alits a)

floatV :: AbValue -> SLattice Double
floatV a = floatVL (alits a)

charV :: AbValue -> SLattice Char
charV a = charVL (alits a)

stringV :: AbValue -> SLattice String
stringV a = stringVL (alits a)

topTypesOf :: AbValue -> Set Type
topTypesOf ab =
  S.fromList $ catMaybes (
   [maybeTopI (intV ab)
   ,maybeTopD (floatV ab)
   ,maybeTopC (charV ab) 
   ,maybeTopS (stringV ab)]
  )

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
  -> IO (M.Map FixInput (FixOutput FixChange), Maybe ([S.UserExpr], [S.UserDef], [S.External], [Syn.Lit], [String], Set Type), BuildContext)
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
                          let achanges = map (\(AC c) -> c) (filter (\c -> case c of {AC ac -> True; _ -> False}) res)
                              resM = foldl addChange emptyAbValue achanges
                          ress' <- getAbResult resM
                          trace ("ress': " ++ show ress') $ return ()
                          return (Just ress', buildc')
  -- trace ("l: " ++ show (length l)) $ return ()
  writeDependencyGraph (moduleNameToPath (modName mod)) l
  writeSimpleDependencyGraph (moduleNameToPath (modName mod)) l
  return (M.map (\(x, _, _, _) -> x) l, r, bc)

evalMain :: BuildContext
  -> TypeChecker -> Module -> Int
  -> IO (Maybe ([S.UserExpr], [S.UserDef], [S.External], [S.Lit], [String],
                                   Set Type), BuildContext)
evalMain bc build mod m = do
  (lattice, r, bc) <- runQueryAtRange bc build mod m $ \ctx -> do
    q <- doStep (Eval ctx M.empty M.empty M.empty [EndProgram])
    addResult q
  return (r, bc)

writeSimpleDependencyGraph :: forall e s . String ->  M.Map FixInput (FixOutput FixChange, Integer, [ContX e s FixInput FixOutput FixChange], [ContF e s FixInput FixOutput FixChange]) -> IO ()
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

getAbResult :: AbValue -> PostFixAR x s e i o c ([S.UserExpr], [S.UserDef], [S.External], [Syn.Lit], [String], Set Type)
getAbResult res = do
  let vals = [res]
      lams = map fst $ concatMap (S.toList . aclos) vals
      i = map (toSynLit . intV) vals
      f = map (toSynLitD . floatV) vals
      c = map (toSynLitC . charV) vals
      s = map (toSynLitS . stringV) vals
      topTypes = S.unions $ map topTypesOf vals
      vs = catMaybes $ i ++ f ++ c ++ s
      cs = map fst $ concatMap (S.toList . acons) vals
  consts <- mapM toSynConstr cs
  source <- mapM findSourceExpr lams
  let sourceLambdas = map (\(SourceExpr e) -> e) $ filter (\s -> case s of {SourceExpr _ -> True; _ -> False}) source
      sourceDefs = map (\(SourceDef e) -> e) $ filter (\s -> case s of {SourceDef _ -> True; _ -> False}) source
      sourceExterns = map (\(SourceExtern e) -> e) $ filter (\s -> case s of {SourceExtern _ -> True; _ -> False}) source
  return $ trace
    ("eval " ++
     "\nresult:\n----------------------\n" ++ showSimpleAbValue res ++ "\n----------------------\n")
   (sourceLambdas, sourceDefs, sourceExterns, vs, catMaybes consts, topTypes)

showEscape :: Show a => a -> String
showEscape = escape . show

escape :: String -> String
escape (s:xs) = if s == '\"' then "\\" ++ s:escape xs else s : escape xs
escape [] = []

instance Label (FixOutput m) where
  label (A a) = escape $ showSimpleAbValue a
  label Bottom = "Bottom"

showCont :: [Frame] -> [Doc]
showCont l =  map (text . show) (reverse l)-- (take 2 $ reverse l)

instance Label FixInput where
  label (Eval q env _ _ kont) = escape $ show (vcat (text "EVAL": showCont kont ++ [text (showSimpleContext q), text (showSimpleEnv env)]))
  label (Cont ch env _ _ kont) = escape $ show (vcat $ text "CONT" :  showCont kont ++ [text $ show ch])