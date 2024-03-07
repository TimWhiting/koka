-----------------------------------------------------------------------------
-- Copyright 2024 Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
module Demand.StaticContext(
                          ExprContext(..),
                          ExprContextId(..),
                          ExpressionSet,
                          contextId,contextOf,exprOfCtx,modCtx,showContextPath,modCtxOf,
                          maybeExprOfCtx,
                          rangesOverlap,
                          lamVar,lamVarDef,lamNames,
                          showExpr,showDg,showDef,showCtxExpr,
                          enclosingLambda,
                          branchContainsBinding,
                          branchVars,
                          findApplicationFromRange,findLambdaFromRange,findDefFromRange,
                          basicExprOf,defsOf,defOfCtx,
                          lookupDefGroup,lookupDefGroups,lookupDef,
                          showSyntaxDef,showSyntax,showLit,
                          showSimpleContext,
                          isMain
                        ) where
import Core.Core as C
import Common.Name
import Compile.Module
import Type.Type
import Data.Set hiding (map)
import Type.Pretty
import Syntax.Syntax as S
import Common.Range
import Data.Maybe (mapMaybe, catMaybes, fromMaybe)
import Core.CoreVar (bv)
import Core.Pretty
import Debug.Trace (trace)
import Data.List (intercalate)
import Common.NamePrim (nameOpExpr, isNameTuple, nameTrue)
import qualified Data.Text as T

-- Uniquely identifies expressions despite naming
data ExprContext =
  -- Current expression context
  ModuleC !ExprContextId !Module !Name -- Module context
  | DefCRec !ExprContextId !ExprContext ![TName] !Int !C.DefGroup -- A recursive definition context, working on the index'th definition
  | DefCNonRec !ExprContextId !ExprContext ![TName] !C.DefGroup -- In a non recursive definition context, working on Def
  | LamCBody !ExprContextId !ExprContext ![TName] !C.Expr -- Inside a lambda body expression
  | AppCLambda !ExprContextId !ExprContext !C.Expr -- Application context inside function context
  | AppCParam !ExprContextId !ExprContext !Int !C.Expr -- Application context inside param context
  -- TODO: This needs adjustment, currently it flat-maps over the defgroup and indexes over that
  | LetCDef !ExprContextId !ExprContext ![TName] !Int !C.DefGroups -- In a let definition context working on a particular defgroup
  | LetCBody !ExprContextId !ExprContext ![TName] !C.Expr -- In a let body expression
  | CaseCMatch !ExprContextId !ExprContext !C.Expr -- In a case match context working on the match expression (assumes only one)
  | CaseCBranch !ExprContextId !ExprContext ![TName] !Int !C.Branch -- Which branch currently inspecting, as well as the Case context
  | ExprCBasic !ExprContextId !ExprContext !C.Expr -- A basic expression context that has no sub expressions
  | ExprCTerm !ExprContextId !String -- Since analysis can fail or terminate early, keep track of the query that failed

modCtxOf :: Module -> ExprContext
modCtxOf mod = ModuleC (ExprContextId (-1) (modName mod)) mod (modName mod)

isMain :: ExprContext -> Bool
isMain ctx = nameStem (C.defName (defOfCtx ctx)) == "main"

lamNames :: ExprContext -> [TName]
lamNames ctx =
  case maybeExprOfCtx ctx of
    Just (C.Lam names _ _) -> names
    Just (C.TypeLam _ (C.Lam names _ _)) -> names
    _ -> error ("Not a lambda: " ++ show ctx)

data ExprContextId = ExprContextId{
  exprId:: !Int,
  moduleName:: !Name
} deriving (Ord, Eq)

instance Show ExprContextId where
  show id =
    nameStem (moduleName id) ++ ":" ++ show (exprId id)

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

showContextPath :: ExprContext -> String
showContextPath ctx =
  case ctx of
    ModuleC _ _ n -> "Module " ++ show n
    DefCRec _ c _ _ _ -> showContextPath c ++ " -> DefRec " ++ show (defTName $ defOfCtx ctx)
    DefCNonRec _ c _ _ -> showContextPath c ++ " -> DefNonRec " ++ show (defTName $ defOfCtx ctx)
    LamCBody _ c tn _ -> showContextPath c ++ " -> LamBody(" ++ show tn ++ ")"
    AppCLambda _ c _ -> showContextPath c ++ " -> AppLambda"
    AppCParam _ c _ _ -> showContextPath c ++ " -> AppParam"
    LetCDef _ c _ _ _ -> showContextPath c ++ " -> LetDef " ++ show (defTName $ defOfCtx ctx)
    LetCBody _ c _ _ -> showContextPath c ++ " -> LetBody"
    CaseCMatch _ c _ -> showContextPath c ++ " -> CaseMatch"
    CaseCBranch _ c _ _ _ -> showContextPath c ++ " -> CaseBranch"
    ExprCBasic _ c _ -> showContextPath c ++ " -> " ++ show ctx
    ExprCTerm _ _ -> "Query Error"

lamVar :: Int -> ExprContext -> C.Expr
lamVar index ctx = 
  case maybeExprOfCtx ctx of
    Just x -> lamVarExpr index x
    Nothing -> trace ("DemandAnalysis.lamVar: not a lambda " ++ show ctx) error "Not a lambda"

lamVarExpr :: Int -> C.Expr -> C.Expr
lamVarExpr index e =
  case e of
    C.Lam names _ _ -> C.Var (names !! index) InfoNone
    TypeLam _ c -> lamVarExpr index c
    TypeApp c _ -> lamVarExpr index c
    _ -> error ("DemandAnalysis.lamVarExpr: not a lambda " ++ show e)
    
lamVarDef :: C.Def -> C.Expr
lamVarDef def = C.Var (TName (C.defName def) (C.defType def) Nothing) InfoNone

simpleEnv = defaultEnv{showKinds=False,fullNames=False,expandSynonyms=False,showFlavours=False,coreShowTypes=False}

showExpr :: C.Expr -> String
showExpr e = show $ prettyExpr simpleEnv e

showDg d = show $ prettyDefGroup simpleEnv d

showDef d = show $ prettyDef simpleEnv d

closestRange :: ExprContext -> Range
closestRange ctx =
  case ctx of
    ModuleC{} -> rangeNull
    DefCRec _ _ _ i d -> C.defNameRange (defOfCtx ctx)
    DefCNonRec _ _ _ d -> C.defNameRange (defOfCtx ctx)
    LamCBody _ c tn _ ->
      case tn of
        t:_ -> case C.originalRange t
          of Just r -> r
             Nothing -> closestRange c
        _ -> closestRange c
    AppCLambda _ c _ -> closestRange c
    AppCParam _ c _ _ -> closestRange c
    LetCDef _ _ _ i dg -> C.defNameRange (defOfCtx ctx)
    LetCBody _ c _ _ -> closestRange c
    CaseCMatch _ c _ -> closestRange c
    CaseCBranch _ c tn _ _ ->
      case tn of
        t:_ -> case C.originalRange t
          of Just r -> r
             Nothing -> closestRange c
        _ -> closestRange c
    ExprCBasic _ c _ -> closestRange c
    ExprCTerm _ _ -> rangeNull

showSimpleContext ctx =
  let r = show (closestRange ctx) in
  case ctx of
    ModuleC{} -> "Module " ++ r
    DefCRec _ _ _ i d -> "DefRec(" ++ showSimple (defTName (defOfCtx ctx)) ++ ")"
    DefCNonRec _ _ _ d -> "DefNonRec(" ++ showSimple (defTName (defOfCtx ctx)) ++ ")"
    LamCBody _ _ tn _-> "LamBody(" ++ showSimple tn ++ ")" 
    AppCLambda{} -> "AppLambda(" ++ showSimple (exprOfCtx ctx) ++ ")"
    AppCParam{} -> "AppParam(" ++ showSimple (exprOfCtx ctx) ++ ")"
    LetCDef _ _ _ i d -> "LetDef(" ++ showSimple (defTName (defOfCtx ctx)) ++ ")"
    LetCBody{} -> "LetBody(" ++ showSimple (exprOfCtx ctx) ++ ")"
    CaseCMatch{} -> "CaseMatch(" ++ showSimple (exprOfCtx ctx) ++ ")"
    CaseCBranch{} -> "CaseBranch(" ++ showSimple (exprOfCtx ctx) ++ ")"
    ExprCBasic{} -> "ExprBasic(" ++ showSimple (exprOfCtx ctx) ++ ")"
    ExprCTerm{} -> "Query Error"

rmNl :: String -> String
rmNl s = T.unpack $ T.replace "\n" "  " (T.pack s)

rangesOverlap :: Range -> Range -> Bool
rangesOverlap r1 r2 = rangeContains r1 (rangeStart r2) || rangeContains r2 (rangeStart r1)

rmNL :: (Show a) => a -> String
rmNL a = rmNl $ Prelude.take 500 $ show a

class SimpleShow a where
  showSimple :: a -> String

instance SimpleShow a => SimpleShow [a] where
  showSimple xs = "[" ++ intercalate "," (map showSimple xs) ++ "]"

instance SimpleShow C.TName where
  showSimple n = show $ prettyVar simpleEnv n

instance SimpleShow C.Expr where
  showSimple e = rmNL $ prettyExpr simpleEnv e

instance Show ExprContext where
  show e =
    case e of
      ModuleC _ _ nm -> "Module " ++ show nm
      DefCRec _ _ _ i df -> "DefRec " ++ showDef (defOfCtx e)
      DefCNonRec _ _ _ df -> "DefNonRec " ++ showDef (defOfCtx e)
      LamCBody _ _ tn e -> "LamBody " ++ show tn ++ " " ++ showExpr e
      AppCLambda _ _ f -> "AppLambda " ++ showExpr f
      AppCParam _ _ i p -> "AppParam " ++ show i ++ " " ++ showExpr p
      LetCDef _ _ _ i dg -> "LetDef " ++ showDef (defOfCtx e)
      LetCBody _ _ _ e -> "LetBody " ++ showExpr e
      CaseCMatch _ _ e -> "CaseMatch " ++ showExpr e
      CaseCBranch _ _ _ i b -> "CaseBranch " ++ show i ++ " " ++ show b
      ExprCBasic _ _ e -> "ExprBasic " ++ showExpr e
      ExprCTerm _ s -> "Query: " ++ s

defOfCtx :: ExprContext -> C.Def
defOfCtx ctx = 
  case ctx of
    DefCNonRec _ _ _ dg -> head $ defsOf dg
    DefCRec _ _ _ i dg -> defsOf dg !! i
    LetCDef _ _ _ i dg -> concatMap defsOf dg !! i
    _ -> error "Query should never be queried for definition"

exprOfCtx :: ExprContext -> C.Expr
exprOfCtx ctx =
  case ctx of
    ModuleC {} -> error "ModuleC is a multi Expression Context"
    DefCRec _ _ _ i d -> defExpr $ defOfCtx ctx
    DefCNonRec _ _ _ d -> defExpr $ defOfCtx ctx
    LamCBody _ _ _ e -> e
    AppCLambda _ _ f -> f
    AppCParam _ _ _ param -> param
    LetCDef _ _ _ i dg -> defExpr $ defOfCtx ctx
    LetCBody _ _ _ e -> e
    CaseCMatch _ _ e -> e
    CaseCBranch _ _ _ _ b -> C.guardExpr (head (C.branchGuards b))
    ExprCBasic _ _ e -> e
    ExprCTerm{} -> error "Query should never be queried for expression"

maybeExprOfCtx :: ExprContext -> Maybe C.Expr
maybeExprOfCtx ctx =
  case ctx of
    ModuleC {} -> Nothing
    DefCRec _ _ _ i d -> Just (defExpr $ defOfCtx ctx)
    DefCNonRec _ _ _ d -> Just (defExpr $ defOfCtx ctx)
    LamCBody _ _ _ e -> Just e
    AppCLambda _ _ f -> Just f
    AppCParam _ _ _ param -> Just param
    LetCDef _ _ _ i dg -> Just (defExpr $ defOfCtx ctx)
    LetCBody _ _ _ e -> Just e
    CaseCMatch _ _ e -> Just e
    CaseCBranch _ _ _ _ b -> Just $ C.guardExpr (head (C.branchGuards b))
    ExprCBasic _ _ e -> Just e
    ExprCTerm{} -> error "Query should never be queried for expression"

showCtxExpr :: ExprContext -> String
showCtxExpr ctx =
  case maybeExprOfCtx ctx of
    Just e -> showExpr e
    Nothing -> show ctx

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

modCtx :: ExprContext -> Maybe ExprContext
modCtx ctx =
  case ctx of
    ModuleC{} -> Just ctx
    ExprCTerm{} -> Nothing
    _ -> contextOf ctx >>= modCtx 

branchContainsBinding :: C.Branch -> TName -> Bool
branchContainsBinding (C.Branch pat guards) name =
  name `elem` bv pat

branchVars :: C.Branch -> [TName]
branchVars (C.Branch pat guards) = Data.Set.toList $ bv pat

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
        S.Parens e _ _ _ -> findInExpr e
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


findDefFromRange :: UserProgram -> Range -> Maybe UserDef
findDefFromRange prog rng =
  findInDefGs (programDefs prog)
  where
    findInDefGs :: S.DefGroups UserType -> Maybe UserDef
    findInDefGs defgs = case mapMaybe findInDefG defgs of
      [l] -> Just l
      _ -> Nothing
    findInDefG def = -- trace ("Looking in defGroup " ++ show def) $
      case def of
        S.DefNonRec df -> findInDef df
        S.DefRec dfs -> case mapMaybe findInDef dfs of [l] -> Just l; _ -> Nothing
    findInDef :: UserDef -> Maybe UserDef
    findInDef def =
      case def of
        S.Def vb rng0 _ _ _ _ -> -- trace ("Looking in def " ++ show def) $ 
          if rng `rangesOverlap` rng0 then Just $ fromMaybe def (findInBinder vb) else Nothing
    findInBinder :: ValueBinder () UserExpr -> Maybe UserDef
    findInBinder vb =
      case vb of
        S.ValueBinder _ _ e _ _ -> -- trace ("Looking in binder " ++ show vb) $ 
          findInExpr e
    findInExpr :: UserExpr -> Maybe UserDef
    findInExpr e =
      -- trace ("Looking in expr " ++ show e) $ 
      case e of
        S.Lam _ body rng0 -> if rng `rangesOverlap` rng0 then findInExpr body else Nothing
        S.App f args _ ->
          case mapMaybe findInExpr (f:map snd args) of
            [x] -> Just x
            _ -> Nothing
        S.Let dg body _ ->
          case findInDefG dg of
            Just x -> Just x
            _ -> findInExpr body
        S.Bind d e rng0 ->
          case findInDef d of
            Just x -> Just x
            _ -> findInExpr e
        S.Case e bs _ ->
          case findInExpr e of
            Just x -> Just x
            _ -> case mapMaybe findInBranch bs of
              [x] -> Just x
              _ -> Nothing
        S.Parens e _ _ _ -> findInExpr e
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
    findInHandlerBranch :: S.HandlerBranch UserType -> Maybe UserDef
    findInHandlerBranch (S.HandlerBranch _ _ body _ _ _) = findInExpr body
    findInBranch :: S.Branch UserType -> Maybe UserDef
    findInBranch (S.Branch pat guards) =
      case mapMaybe findInGuard guards of
          [x] -> Just x
          _ -> Nothing
    findInGuard :: S.Guard UserType -> Maybe UserDef
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
        S.Parens e _ _ _ -> findInExpr e
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


showSyntaxDef :: Int -> S.Def UserType -> String
showSyntaxDef indent (S.Def binder range vis sort inline doc)
  = concat (replicate indent " ") ++ "val " ++ show (nameStem $ binderName binder) ++ " = " ++ showSyntax indent (binderExpr binder)

showValBinder :: ValueBinder (Maybe UserType) (Maybe (S.Expr UserType)) -> String
showValBinder (ValueBinder name (Just tp) (Just expr) nameRange range)
  = show (nameStem name) ++ " = " ++ show expr
showValBinder (ValueBinder name Nothing (Just expr) nameRange range)
  = show (nameStem name) ++ " = " ++ show expr
showValBinder (ValueBinder name (Just tp) Nothing nameRange range)
  = show (nameStem name)
showValBinder (ValueBinder name Nothing Nothing nameRange range)
  = show (nameStem name)

showArg :: (Maybe (Name,Range),S.Expr UserType) -> String
showArg (Nothing,expr) = showSyntax 0 expr
showArg (Just (name,_),expr) = show (nameStem name) ++ "= " ++ showSyntax 0 expr

allDefs :: S.DefGroup UserType -> [S.Def UserType]
allDefs defs =
  case defs of
    S.DefNonRec d -> [d]
    S.DefRec ds   -> ds

showSyntax :: Int -> S.Expr UserType -> String
showSyntax indent (S.Lam pars expr range) =
  "fn(" ++ intercalate "," (map showValBinder pars) ++ ")\n" ++ concat (replicate (indent + 2) " ") ++
    showSyntax (indent + 2) expr
showSyntax indent (S.Let defs expr range) =
  intercalate ("\n" ++ concat (replicate indent " ")) (map (showSyntaxDef indent) (allDefs defs)) ++
  "\n" ++ concat (replicate indent " ") ++ showSyntax (indent + 2) expr
showSyntax indent (Bind def expr range) =
  showSyntaxDef indent def ++ "\n" ++ concat (replicate indent " ") ++ showSyntax (indent + 2) expr
showSyntax indent (S.App (S.Var name _ _) args range) | name == nameOpExpr =
  unwords (map showArg args)
showSyntax indent (S.App fun args range)  =
  showSyntax indent fun ++ "(" ++ intercalate "," (map showArg args) ++ ")"
showSyntax indent (S.Var name isop range) = nameStem name
showSyntax indent (S.Lit lit)             = showLit lit
showSyntax indent (Ann expr tp range)   = showSyntax indent expr
showSyntax indent (S.Case expr branches range) =
  "match " ++ showSyntax 0 expr ++ "\n" ++ concat (replicate (indent + 2) " ") ++
    intercalate ("\n" ++ concat (replicate (indent + 2) " ")) (map (showSyntaxBranch (indent + 2)) branches)
showSyntax indent (Parens expr name _ range) =
  "(" ++ showSyntax indent expr ++ ")"
showSyntax indent (Inject tp expr behind range) =
  "mask<" ++ show tp ++ ">{" ++ showSyntax 0 expr ++ "}"
showSyntax indent (Handler sort scope override allowmask eff pars reinit ret final branches drange range) =
  "handler " ++ show reinit ++ " " ++ show ret ++ " " ++ show final ++ " " ++ show branches
  -- TODO: Better show handlers

showSyntaxBranch :: Int -> S.Branch UserType -> String
showSyntaxBranch indent (S.Branch pat [S.Guard (S.Var n _ _) body]) | nameTrue == n
  = showSyntaxPattern pat ++ " ->\n" ++  concat (replicate (indent + 2) " ") ++ showSyntax indent body
showSyntaxBranch indent (S.Branch pat [guard])
  = showSyntaxPattern pat ++ " | " ++ showSyntaxGuard indent guard
showSyntaxBranch indent b = show b

showPatBinder :: ValueBinder (Maybe UserType) (S.Pattern UserType) -> String
showPatBinder (ValueBinder name _ (S.PatWild rng) nameRange range)
  = nameStem name
showPatBinder (ValueBinder name _ pat nameRange range)
  = nameStem name ++ " as " ++ showSyntaxPattern pat

showSyntaxPattern :: S.Pattern UserType -> String
showSyntaxPattern (S.PatWild range) = "_"
showSyntaxPattern (S.PatVar binder) = showPatBinder binder
showSyntaxPattern (PatAnn pat tp range) = showSyntaxPattern pat
showSyntaxPattern (S.PatCon name args nameRng range) =
  if isNameTuple name then "(" ++ intercalate ","  (map showPatternArg args) ++ ")"
  else nameStem name ++ "(" ++ intercalate "," (map showPatternArg args) ++ ")"
showSyntaxPattern (PatParens pat range) = "(" ++ showSyntaxPattern pat ++ ")"
showSyntaxPattern (S.PatLit lit) = showLit lit

showPatternArg :: (Maybe (Name,Range), S.Pattern UserType) -> String
showPatternArg (Nothing,pat) = showSyntaxPattern pat
showPatternArg (Just (name,_),S.PatWild rng) = nameStem name
showPatternArg (Just (name,_),pat) = nameStem name ++ "= " ++ showSyntaxPattern pat

showSyntaxGuard :: Int -> S.Guard UserType -> String
showSyntaxGuard indent (S.Guard guard body)
  = showSyntax indent guard ++ " -> " ++ "\n" ++ concat (replicate (indent + 2) " ") ++ showSyntax (indent + 2) body

showLit :: S.Lit -> String
showLit (S.LitInt i range) = show i
showLit (S.LitFloat f range) = show f
showLit (S.LitChar c range) = show c
showLit (S.LitString s range) = show s