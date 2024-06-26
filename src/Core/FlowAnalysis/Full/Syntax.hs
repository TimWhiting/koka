{-# LANGUAGE RankNTypes #-}
module Core.FlowAnalysis.Full.Syntax where

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
import Core.FlowAnalysis.Full.AAC
import Core.FlowAnalysis.Full.AbstractValue
import Core.FlowAnalysis.Full.Monad
import Common.Failure (HasCallStack)
import Common.NamePrim (nameMain)
import Common.Name (Name(..))
import Common.Range
import Debug.Trace (trace)

intV :: AbValue -> M.Map VEnv (SLattice Integer)
intV a = fmap intVL (alits a)

floatV :: AbValue -> M.Map VEnv (SLattice Double)
floatV a = fmap floatVL (alits a)

charV :: AbValue -> M.Map VEnv (SLattice Char)
charV a = fmap charVL (alits a)

stringV :: AbValue -> M.Map VEnv (SLattice String)
stringV a = fmap stringVL (alits a)

topTypesOf :: AbValue -> Set Type
topTypesOf ab =
  S.fromList $ catMaybes (
    map maybeTopI (M.elems (intV ab)) ++
    map maybeTopD (M.elems (floatV ab)) ++
    map maybeTopC (M.elems (charV ab)) ++
    map maybeTopS (M.elems (stringV ab))
  )

analyzeEach :: Show d => ExprContext -> (ExprContext -> FixAACR a b c d) -> FixAACR a b c d
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
  -> (ExprContext -> FixAACR FixChange () () ())
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
  writeDependencyGraph (moduleNameToPath (modName mod)) l
  return (M.map (\(x, _, _) -> x) l, r, bc)

evalMain :: BuildContext
  -> TypeChecker -> Module -> Int
  -> IO (Maybe ([S.UserExpr], [S.UserDef], [S.External], [S.Lit], [String],
                                   Set Type), BuildContext)
evalMain bc build mod m = do
  (lattice, r, bc) <- runQueryAtRange bc build mod m $ \ctx -> do
    q <- doStep (Eval ctx M.empty M.empty M.empty [EndProgram] KEnd MEnd)
    addResult q
  return (r, bc)

getAbResult :: AbValue -> PostFixAR x s e i o c ([S.UserExpr], [S.UserDef], [S.External], [Syn.Lit], [String], Set Type)
getAbResult res = do
  let vals = [res]
      lams = map fst $ concatMap (S.toList . aclos) vals
      i = concatMap ((mapMaybe toSynLit . M.elems) . intV) vals
      f = concatMap ((mapMaybe toSynLitD . M.elems) . floatV) vals
      c = concatMap ((mapMaybe toSynLitC . M.elems) . charV) vals
      s = concatMap ((mapMaybe toSynLitS . M.elems) . stringV) vals
      topTypes = S.unions $ map topTypesOf vals
      vs = i ++ f ++ c ++ s
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
  label (K a) = escape $ show $ vcat [text "K" , hcat $ map (\(l, k) -> vcat $ showC (l, k)) (S.toList a)]
  label (C a) = escape $ show $ vcat [text "C" , hcat $ map (\(l, k, m) -> vcat $ showCont (l, k, m)) (S.toList a)]
  label (B a) = escape $ show $ vcat [text "B" , hcat $ map (text . show) (S.toList a)]
  label Bottom = "Bottom"

showCont :: (LocalKont, Kont, MetaKont) -> [Doc]
showCont (l, k, m) = [text $ show m, text $ show k, text "Local"] ++ map (text . show) l

showC :: (LocalKont, Kont) -> [Doc]
showC (l, k) = text (show k) : text "Local " : map (text . show) l

instance Label FixInput where
  label (Eval q env _ _ l k c) = escape $ show (vcat (text "EVAL": showCont (l, k, c) ++ [text (showSimpleContext q), text (showSimpleEnv env)]))
  label (Cont l k c ch _ _) = escape $ show (vcat $ text "CONT" :  showCont (l, k, c) ++ [text $ show ch])
  label (KStoreGet c) = escape $ show (vcat [text "KSTOREGET", text (show c)])
  label (CStoreGet c) = escape $ show (vcat [text "CSTOREGET", text (show c)])
  label (Pop l c) = escape $ show (vcat $ text "POP" :  showC (l, c))
  label (NoTop l c) = escape $ show (vcat $ text "NOTOP" : showC (l, c))
