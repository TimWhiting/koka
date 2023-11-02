
module Core.StaticContext(
                          ExprContext(..),
                          ExprContextId(..),
                          ExpressionSet,
                          contextId,
                          contextOf,
                          exprOfCtx,
                          maybeExprOfCtx,
                          lamVar,
                          lamVarDef,
                          showExpr,
                          showDg,
                          showDef,
                          enclosingLambda,
                          branchContainsBinding,
                          branchVars,
                          findApplicationFromRange,
                          findLambdaFromRange,
                          basicExprOf,
                          defsOf,
                          lookupDefGroup,
                          lookupDefGroups,
                          lookupDef
                        ) where
import Core.Core as C
import Common.Name
import Compiler.Module
import Type.Type
import Data.Set hiding (map)
import Type.Pretty
import Syntax.Syntax as S
import Common.Range
import Data.Maybe (mapMaybe, catMaybes, fromMaybe)
import Core.CoreVar (bv)
import Core.Pretty
import Debug.Trace (trace)

-- Uniquely identifies expressions despite naming
data ExprContext =
  -- Current expression context
  ModuleC !ExprContextId !Module !Name -- Module context
  | DefCRec !ExprContextId !ExprContext ![TName] !Int !C.Def -- A recursive definition context, working on the index'th definition
  | DefCNonRec !ExprContextId !ExprContext ![TName] !C.Def -- In a non recursive definition context, working on Def
  | LamCBody !ExprContextId !ExprContext ![TName] !C.Expr -- Inside a lambda body expression
  | AppCLambda !ExprContextId !ExprContext !C.Expr -- Application context inside function context
  | AppCParam !ExprContextId !ExprContext !Int !C.Expr -- Application context inside param context
  -- TODO: This needs adjustment, currently it flatmaps over the defgroup and indexes over that
  | LetCDef !ExprContextId !ExprContext ![TName] !Int !C.DefGroup -- In a let definition context working on a particular defgroup
  | LetCBody !ExprContextId !ExprContext ![TName] !C.Expr -- In a let body expression
  | CaseCMatch !ExprContextId !ExprContext !C.Expr -- In a case match context working on the match expression (assumes only one)
  | CaseCBranch !ExprContextId !ExprContext ![TName] !Int !C.Branch -- Which branch currently inspecting, as well as the Case context
  | ExprCBasic !ExprContextId !ExprContext !C.Expr -- A basic expression context that has no sub expressions
  | ExprCTerm !ExprContextId !String -- Since analysis can fail or terminate early, keep track of the query that failed

data ExprContextId = ExprContextId{
  exprId:: !Int,
  moduleName:: !Name
} deriving (Ord, Eq)

instance Show ExprContextId where
  show id =
    nameId (moduleName id) ++ ":" ++ show (exprId id)

instance Eq ExprContext where
  ctx1 == ctx2 = contextId ctx1 == contextId ctx2

instance Ord ExprContext where
  compare ctx1 ctx2 = compare (contextId ctx1) (contextId ctx2)

instance Ord Type where
  compare tp1 tp2 = compare (show $ ppType defaultEnv tp1) (show $ ppType defaultEnv tp2)

instance Eq C.Def where
  def1 == def2 = C.defName def1 == C.defName def2 && C.defType def1 == C.defType def2

type ExpressionSet = Set ExprContextId

enclosingLambda :: ExprContext -> Maybe ExprContext
enclosingLambda ctx =
  case ctx of
    LamCBody{} -> Just ctx
    AppCLambda _ c _ -> enclosingLambda c
    AppCParam _ c _ _ -> enclosingLambda c
    DefCRec _ c _ _ _ -> enclosingLambda c
    DefCNonRec _ c _ _ -> enclosingLambda c
    LetCDef _ c _ _ _ -> enclosingLambda c
    LetCBody _ c _ _ -> enclosingLambda c
    CaseCMatch _ c _ -> enclosingLambda c
    CaseCBranch _ c _ _ _ -> enclosingLambda c
    ExprCBasic _ c _ -> enclosingLambda c
    ExprCTerm{} -> Nothing
    ModuleC{} -> Nothing


lamVar :: Int -> ExprContext -> C.Expr
lamVar index ctx =
  case maybeExprOfCtx ctx of
    Just (C.Lam names _ _) -> C.Var (names !! index) InfoNone
    Just (TypeLam e (C.Lam names _ _)) -> C.Var (names !! index) InfoNone
    _ -> trace ("DemandAnalysis.lamVar: not a lambda " ++ show ctx) error "Not a lambda"

lamVarDef :: C.Def -> C.Expr
lamVarDef def = C.Var (TName (C.defName def) (C.defType def) Nothing) InfoNone

showExpr :: C.Expr -> String
showExpr e = show $ prettyExpr defaultEnv{showRanges=True} e

showDg d = show $ prettyDefGroup defaultEnv d

showDef d = show $ prettyDef defaultEnv d

instance Show ExprContext where
  show e =
    case e of
      ModuleC _ _ nm -> "Module " ++ show nm
      DefCRec _ _ _ i df -> "DefRec " ++ showDef df
      DefCNonRec _ _ _ df -> "DefNonRec " ++ showDef df
      LamCBody _ _ tn e -> "LamBody " ++ show tn ++ " " ++ showExpr e
      AppCLambda _ _ f -> "AppLambda " ++ showExpr f
      AppCParam _ _ i p -> "AppParam " ++ show i ++ " " ++ showExpr p
      LetCDef _ _ _ i dg -> "LetDef " ++ showDg dg
      LetCBody _ _ _ e -> "LetBody " ++ showExpr e
      CaseCMatch _ _ e -> "CaseMatch " ++ showExpr e
      CaseCBranch _ _ _ i b -> "CaseBranch " ++ show i ++ " " ++ show b
      ExprCBasic _ _ e -> "ExprBasic " ++ showExpr e
      ExprCTerm _ s -> "Query: " ++ s

exprOfCtx :: ExprContext -> C.Expr
exprOfCtx ctx =
  case ctx of
    ModuleC {} -> error "ModuleC is a multi Expression Context"
    DefCRec _ _ _ _ d -> defExpr d
    DefCNonRec _ _ _ d -> defExpr d
    LamCBody _ _ _ e -> e
    AppCLambda _ _ f -> f
    AppCParam _ _ _ param -> param
    LetCDef _ _ _ i dg -> defExpr (defsOf dg !! i)
    LetCBody _ _ _ e -> e
    CaseCMatch _ _ e -> e
    CaseCBranch _ _ _ _ b -> C.guardExpr (head (C.branchGuards b))
    ExprCBasic _ _ e -> e
    ExprCTerm{} -> error "Query should never be queried for expression"

maybeExprOfCtx :: ExprContext -> Maybe C.Expr
maybeExprOfCtx ctx =
  case ctx of
    ModuleC {} -> Nothing
    DefCRec _ _ _ _ d -> Just $ defExpr d
    DefCNonRec _ _ _ d -> Just $ defExpr d
    LamCBody _ _ _ e -> Just e
    AppCLambda _ _ f -> Just f
    AppCParam _ _ _ param -> Just param
    LetCDef _ _ _ _ dg -> Nothing
    LetCBody _ _ _ e -> Just e
    CaseCMatch _ _ e -> Just e
    CaseCBranch _ _ _ _ b -> Just $ C.guardExpr (head (C.branchGuards b))
    ExprCBasic _ _ e -> Just e
    ExprCTerm{} -> error "Query should never be queried for expression"

contextId :: ExprContext -> ExprContextId
contextId ctx =
  case ctx of
    ModuleC c _ _ -> c
    DefCRec c _ _ _ _ -> c
    DefCNonRec c _ _ _ -> c
    LamCBody c _ _ _ -> c
    AppCLambda c _ _ -> c
    AppCParam c _ _ _ -> c
    LetCDef c _ _ _ _ -> c
    LetCBody c _ _ _ -> c
    CaseCMatch c _ _ -> c
    CaseCBranch c _ _ _ _ -> c
    ExprCBasic c _ _ -> c
    ExprCTerm c _ -> c

contextOf :: ExprContext -> Maybe ExprContext
contextOf ctx =
  case ctx of
    ModuleC{} -> Nothing
    DefCRec _ c _ _ _ -> Just c
    DefCNonRec _ c _ _ -> Just c
    LamCBody _ c _ _ -> Just c
    AppCLambda _ c _ -> Just c
    AppCParam _ c _ _ -> Just c
    LetCDef _ c _ _ _ -> Just c
    LetCBody _ c _ _ -> Just c
    CaseCMatch _ c _ -> Just c
    CaseCBranch _ c _ _ _ -> Just c
    ExprCBasic _ c _ -> Just c
    ExprCTerm{} -> error "Query should never be queried for context"

branchContainsBinding :: C.Branch -> TName -> Bool
branchContainsBinding (C.Branch pat guards) name =
  name `elem` bv pat

branchVars :: C.Branch -> [TName]
branchVars (C.Branch pat guards) = Data.Set.toList $ bv pat -- TODO: Is this deterministic? Assuming so since it is ordered

findApplicationFromRange :: UserProgram -> Range -> Maybe UserExpr
findApplicationFromRange prog rng =
  findInDefGs (programDefs prog)
  where
    findInDefGs :: S.DefGroups UserType -> Maybe UserExpr
    findInDefGs defgs = case mapMaybe findInDefG defgs of
      [l] -> Just l
      _ -> Nothing
    findInDefG def = -- trace ("Looking in defGroup " ++ show def) $
      case def of
        S.DefNonRec df -> findInDef df
        S.DefRec dfs -> case mapMaybe findInDef dfs of [l] -> Just l; _ -> Nothing
    findInDef :: UserDef -> Maybe UserExpr
    findInDef def =
      case def of
        S.Def vb rng0 _ _ _ _ -> -- trace ("Looking in def " ++ show def) $ 
          if rng `rangesOverlap` rng0 then Just $ fromMaybe (binderExpr vb) (findInBinder vb) else Nothing
    findInBinder :: ValueBinder () UserExpr -> Maybe UserExpr
    findInBinder vb =
      case vb of
        S.ValueBinder _ _ e _ _ -> -- trace ("Looking in binder " ++ show vb) $ 
          findInExpr e
    findInExpr :: UserExpr -> Maybe UserExpr
    findInExpr e =
      -- trace ("Looking in expr " ++ show e) $ 
      case e of
        S.Lam _ body rng0 -> findInExpr body
        S.App f args rng0 -> if rng `rangesOverlap` rng0 then case mapMaybe findInExpr (f:map snd args) of [x] -> Just x; _ -> Nothing else Nothing
        S.Let dg body _ ->
          case findInDefG dg of
            Just x -> Just x
            _ -> findInExpr body
        S.Bind d e _ ->
          case findInDef d of
            Just x -> Just x
            _ -> findInExpr e
        S.Case e bs _ ->
          case findInExpr e of
            Just x -> Just x
            _ -> case mapMaybe findInBranch bs of
              [x] -> Just x
              _ -> Nothing
        S.Parens e _ _ -> findInExpr e
        S.Inject _ e _ _ -> findInExpr e
        S.Var{} -> Nothing
        S.Lit _ -> Nothing
        S.Ann e _ _ -> findInExpr e
        S.Handler _ _ _ _ _ _ init ret fin bs _ _ ->
          let exprs = catMaybes [init, ret, fin]
              exprs' = mapMaybe findInExpr exprs
          in case exprs' of
            [x] -> Just x
            _ -> case mapMaybe findInHandlerBranch bs of
              [x] -> Just x
              _ -> Nothing
    findInHandlerBranch :: S.HandlerBranch UserType -> Maybe UserExpr
    findInHandlerBranch (S.HandlerBranch _ _ body _ _ _) = findInExpr body
    findInBranch :: S.Branch UserType -> Maybe UserExpr
    findInBranch (S.Branch pat guards) =
      case mapMaybe findInGuard guards of
          [x] -> Just x
          _ -> Nothing
    findInGuard :: S.Guard UserType -> Maybe UserExpr
    findInGuard (S.Guard e body) =
      case findInExpr e of
        Just x -> Just x
        _ -> findInExpr body

findLambdaFromRange :: UserProgram -> Range -> Maybe UserExpr
findLambdaFromRange prog rng =
  findInDefGs (programDefs prog)
  where
    findInDefGs :: S.DefGroups UserType -> Maybe UserExpr
    findInDefGs defgs = case mapMaybe findInDefG defgs of
      [l] -> Just l
      _ -> Nothing
    findInDefG def = -- trace ("Looking in defGroup " ++ show def) $
      case def of
        S.DefNonRec df -> findInDef df
        S.DefRec dfs -> case mapMaybe findInDef dfs of [l] -> Just l; _ -> Nothing
    findInDef :: UserDef -> Maybe UserExpr
    findInDef def =
      case def of
        S.Def vb rng0 _ _ _ _ -> -- trace ("Looking in def " ++ show def) $ 
          if rng `rangesOverlap` rng0 then Just $ fromMaybe (binderExpr vb) (findInBinder vb) else Nothing
    findInBinder :: ValueBinder () UserExpr -> Maybe UserExpr
    findInBinder vb =
      case vb of
        S.ValueBinder _ _ e _ _ -> -- trace ("Looking in binder " ++ show vb) $ 
          findInExpr e
    findInExpr :: UserExpr -> Maybe UserExpr
    findInExpr e =
      -- trace ("Looking in expr " ++ show e) $ 
      case e of
        S.Lam _ body rng0 -> if rng `rangesOverlap` rng0 then Just $ fromMaybe e (findInExpr body) else Nothing
        S.App f args _ ->
          case mapMaybe findInExpr (f:map snd args) of
            [x] -> Just x
            _ -> Nothing
        S.Let dg body _ ->
          case findInDefG dg of
            Just x -> Just x
            _ -> findInExpr body
        S.Bind d e _ ->
          case findInDef d of
            Just x -> Just x
            _ -> findInExpr e
        S.Case e bs _ ->
          case findInExpr e of
            Just x -> Just x
            _ -> case mapMaybe findInBranch bs of
              [x] -> Just x
              _ -> Nothing
        S.Parens e _ _ -> findInExpr e
        S.Inject _ e _ _ -> findInExpr e
        S.Var{} -> Nothing
        S.Lit _ -> Nothing
        S.Ann e _ _ -> findInExpr e
        S.Handler _ _ _ _ _ _ init ret fin bs _ _ ->
          let exprs = catMaybes [init, ret, fin]
              exprs' = mapMaybe findInExpr exprs
          in case exprs' of
            [x] -> Just x
            _ -> case mapMaybe findInHandlerBranch bs of
              [x] -> Just x
              _ -> Nothing
    findInHandlerBranch :: S.HandlerBranch UserType -> Maybe UserExpr
    findInHandlerBranch (S.HandlerBranch _ _ body _ _ _) = findInExpr body
    findInBranch :: S.Branch UserType -> Maybe UserExpr
    findInBranch (S.Branch pat guards) =
      case mapMaybe findInGuard guards of
          [x] -> Just x
          _ -> Nothing
    findInGuard :: S.Guard UserType -> Maybe UserExpr
    findInGuard (S.Guard e body) =
      case findInExpr e of
        Just x -> Just x
        _ -> findInExpr body

basicExprOf :: ExprContext -> Maybe C.Expr
basicExprOf ctx =
  case ctx of
    ExprCBasic _ ctx e -> Just e
    _ -> Nothing

defsOf :: C.DefGroup -> [C.Def]
defsOf (C.DefNonRec d) = [d]
defsOf (C.DefRec ds) = ds

lookupDefGroup :: C.DefGroup -> TName -> Bool
lookupDefGroup dg tname = tname `elem` defGroupTNames dg

lookupDefGroups :: C.DefGroups -> TName -> Bool
lookupDefGroups defGs tname = any (`lookupDefGroup` tname) defGs

lookupDef :: C.Def -> TName -> Bool
lookupDef def tname = C.defName def == C.getName tname && tnameType tname == C.defType def
