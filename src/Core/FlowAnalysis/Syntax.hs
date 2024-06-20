{-# LANGUAGE RankNTypes #-}
module Core.FlowAnalysis.Syntax where
import Data.List (intercalate, find)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Maybe (catMaybes, mapMaybe, isJust)
import Data.Set(Set)
import Common.Range
import Compile.Module (Module(..))
import qualified Syntax.Syntax as Syn
import qualified Syntax.Syntax as S
import Syntax.Pretty
import Syntax.RangeMap (RangeInfo)
import qualified Core.Core as C
import Common.Name (Name(..))
import Core.Core
import Type.Type
import Lib.PPrint
import Compile.BuildMonad (BuildContext, Build)
import Compile.Options (Terminal, Flags)
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Monad
import Debug.Trace (trace)
import Core.Pretty (prettyExpr)
import Type.Pretty (defaultEnv)

findContext :: Range -> RangeInfo -> FixAR x s e i o c (ExprContext, Range)
findContext r ri = do
  ctx <- currentContext <$> getEnv
  case ctx of
    ExprCBasic _ _ (Var (TName _ _ (Just rng)) _) | r `rangesOverlap` rng ->
      trace ("found overlapping range " ++ showFullRange "" rng ++ " " ++ show ctx) $
        return (ctx, rng)
    ExprCBasic _ _ (Var (TName _ _ (Just rng)) _) -> -- trace ("var range doesn't overlap "++ show ctx ++ " " ++ showFullRange rng) $
      doBottom
    LetCDefNonRec{} -> fromNames ctx [defTName (defOfCtx ctx)]
    LetCDefRec{} -> fromNames ctx [defTName (defOfCtx ctx)]
    -- Hovering over a lambda parameter should query what values that parameter can evaluate to -- need to create an artificial Var expression
    LamCBody _ _ tnames _ -> fromNames ctx tnames
    CaseCBranch _ _ tnames _ _ -> fromNames ctx tnames
    _ -> doBottom
  where fromNames ctx tnames =
          case mapMaybe (\tn ->
                  case fmap (rangesOverlap r) (originalRange tn) of
                    Just True -> Just (tn, originalRange tn)
                    _ -> Nothing
                ) tnames of
              [(tn, Just rng)] -> do
                id <- newContextId
                return (ExprCBasic id ctx (Var tn InfoNone), rng)
              _ -> doBottom

toSynConstr :: ExprContext -> PostFixAR x s e i o c (Maybe String)
toSynConstr ctx =
  return $ Just (show (prettyExpr defaultEnv $ exprOfCtx ctx))

data SourceKind =
  SourceExpr Syn.UserExpr
  | SourceDef Syn.UserDef
  | SourceExtern Syn.External
  | SourceNotFound

findSourceExpr :: ExprContext -> PostFixAR x s e i o c SourceKind
findSourceExpr ctx =
  case ctx of
    DefCNonRec{} -> findDef (defOfCtx ctx)
    DefCRec{} -> findDef (defOfCtx ctx)
    LetCDefRec{} -> findDef (defOfCtx ctx)
    LetCDefNonRec{} -> findDef (defOfCtx ctx)
    AppCParam _ c _ _ -> findSourceExpr c
    AppCLambda _ c _ -> findSourceExpr c
    ExprCBasic _ c _ -> do
      res <- topBindExpr ctx (exprOfCtx ctx)
      case res of
        (Just def, _) -> findDef def
        (_, Just extern) -> findExtern extern
        _ -> findSourceExpr c
    _ ->
      case maybeExprOfCtx ctx of
        Just (Lam (n:_) _ _) -> findForName n
        Just (TypeLam _ (Lam (n:_) _ _)) -> findForName n
        Just (App _ _ rng) -> findForApp rng
        _ ->
          trace ("Unknown lambda type " ++ show ctx ++ ": " ++ show (maybeExprOfCtx ctx)) $ return SourceNotFound
  where
    findExtern e = do
      program <- modProgram <$> getModuleR (newModuleName $ nameModule $ C.externalName e)
      case (program, C.externalName e) of
        (Just prog, name) -> trace ("Finding location for " ++ show name ++ " " ++ show (S.programExternals prog)) $
          case find (\e -> case e of S.External{} -> nameStem (S.extName e) == nameStem name; _ -> False) (S.programExternals prog) of
            Just e -> return (SourceExtern e)
            Nothing -> return SourceNotFound
        _ -> trace ("No program or rng" ++ show e ++ " " ++ show (isJust program)) $ return SourceNotFound
    findDef d = do
      -- return $! Just $! Syn.Var (defName d) False (defNameRange d)
      program <- modProgram <$> getModuleR (moduleName $ contextId ctx)
      case (program, C.defNameRange d) of
        (Just prog, rng) -> -- trace ("Finding location for " ++ show rng ++ " " ++ show ctx ++ " in " ++ show (moduleName $ contextId ctx)) $ 
          case findDefFromRange prog rng (C.defName d) of Just e -> return (SourceDef e); _ -> return SourceNotFound
        _ -> trace ("No program or rng" ++ show d ++ " " ++ show (isJust program)) $ return SourceNotFound
      -- case (program, defNameRange d) of
      --   (Just prog, rng) -> trace ("Finding location for " ++ show rng ++ " " ++ show ctx ++ " in module " ++ show (moduleName $ contextId ctx)) $ return $! findLocation prog rng
      --   _ -> trace ("No program or rng" ++ show (defName d) ++ " " ++ show program) $ return Nothing
    findForName n = do
      program <- modProgram <$> getModuleR (moduleName $ contextId ctx)
      case (program, originalRange n) of
        (Just prog, Just rng) -> -- trace ("Finding location for " ++ show rng ++ " " ++ show ctx) $ 
          case findLambdaFromRange prog rng of Just e -> return (SourceExpr e); _ -> return SourceNotFound
        _ -> trace ("No program or rng" ++ show n ++ " " ++ show (isJust program)) $ return SourceNotFound
    findForApp rng = do
      program <- modProgram <$> getModuleR (moduleName $ contextId ctx)
      case (program, rng) of
        (Just prog, Just rng) -> trace ("Finding application location for " ++ show rng ++ " " ++ show ctx) $
          case findApplicationFromRange prog rng of Just e -> return (SourceExpr e); _ -> return SourceNotFound
        _ -> trace ("No program or rng" ++ show rng ++ " " ++ show (isJust program)) $ return SourceNotFound

-- Converting to user visible expressions
toSynLit :: SLattice Integer -> Maybe S.Lit
toSynLit (LSingle i) = Just $ S.LitInt i rangeNull
toSynLit _ = Nothing

toSynLitD :: SLattice Double -> Maybe S.Lit
toSynLitD (LSingle i) = Just $ S.LitFloat i rangeNull
toSynLitD _ = Nothing

toSynLitC :: SLattice Char -> Maybe S.Lit
toSynLitC (LSingle i) = Just $ S.LitChar i rangeNull
toSynLitC _ = Nothing

toSynLitS :: SLattice String -> Maybe S.Lit
toSynLitS (LSingle i) = Just $ S.LitString i rangeNull
toSynLitS _ = Nothing

maybeTopI :: SLattice Integer -> Maybe Type
maybeTopI LTop = Just typeInt
maybeTopI _ = Nothing

maybeTopD :: SLattice Double -> Maybe Type
maybeTopD LTop = Just typeFloat
maybeTopD _ = Nothing

maybeTopC :: SLattice Char -> Maybe Type
maybeTopC LTop = Just typeChar
maybeTopC _ = Nothing

maybeTopS :: SLattice String -> Maybe Type
maybeTopS LTop = Just typeString
maybeTopS _ = Nothing
