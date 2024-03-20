-----------------------------------------------------------------------------
-- Copyright 2024 Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
module Core.Demand.StaticContext(
                          ExprContext(..),
                          ExprContextId(..),
                          ExpressionSet,
                          contextId,contextOf,exprOfCtx,modCtx,ppContextPath,modCtxOf,parentDefOfCtx,
                          maybeExprOfCtx,
                          rangesOverlap,
                          lamVar,lamVarDef,lamNames,
                          showDg,showDef,showCtxExpr,
                          enclosingLambda,
                          branchContainsBinding,
                          branchVars,
                          findApplicationFromRange,findLambdaFromRange,findDefFromRange,
                          basicExprOf,defsOf,defOfCtx,
                          lookupDefGroup,lookupDefGroups,lookupDef,
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
import Data.Maybe (mapMaybe, catMaybes, fromMaybe, maybeToList)
import Core.CoreVar (bv)
import Core.Pretty
import Debug.Trace (trace)
import Data.List (intercalate, intersperse, minimumBy)
import Common.NamePrim (nameOpExpr, isNameTuple, nameTrue)
import qualified Data.Text as T
import Lib.PPrint

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

ppContextPath :: ExprContext -> Doc
ppContextPath ctx =
  case ctx of
    ModuleC _ _ n -> text "Module " <+> text (show n)
    DefCRec _ c _ _ _ -> ppContextPath c <+> text "->" <+> text ("DefRec " ++ show (defTName $ defOfCtx ctx))
    DefCNonRec _ c _ _ -> ppContextPath c <+> text "->" <+> text ("DefNonRec " ++ show (defTName $ defOfCtx ctx))
    LamCBody _ c tn _ -> ppContextPath c <+> text "->" <+> text ("LamBody(" ++ show tn ++ ")")
    AppCLambda _ c _ -> ppContextPath c <+> text "->" <+> text "AppLambda"
    AppCParam _ c _ _ -> ppContextPath c <+> text "->" <+> text "AppParam"
    LetCDef _ c _ _ _ -> ppContextPath c <+> text "->" <+> text ("LetDef " ++ show (defTName $ defOfCtx ctx))
    LetCBody _ c _ _ -> ppContextPath c <+> text "->" <+> text "LetBody"
    CaseCMatch _ c _ -> ppContextPath c <+> text "->" <+> text "CaseMatch"
    CaseCBranch _ c _ _ _ -> ppContextPath c <+> text "->" <+> text "CaseBranch"
    ExprCBasic _ c _ -> ppContextPath c <+> text "->" <+> text (show ctx)
    ExprCTerm _ _ -> text "Query Error"

parentDefOfCtx :: ExprContext -> C.Def
parentDefOfCtx ctx =
  case ctx of
    DefCRec _ _ _ index dg -> defsOf dg !! index
    DefCNonRec _ _ _ dg -> head $ defsOf dg
    LetCDef _ c _ _ dg -> parentDefOfCtx c
    _ -> case contextOf ctx
      of Just c -> parentDefOfCtx c
         Nothing -> error "No parent def"

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
rmNL a = Prelude.take 500 $ show a

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
  findFromRange prog rng (const Nothing) $ \e -> case e of
    S.App f args rng0 -> if rng `rangesOverlap` rng0 then Just f else Nothing
    _ -> Nothing

findDefFromRange :: UserProgram -> Range -> Maybe UserDef
findDefFromRange prog rng =
  findFromRange prog rng (\d ->
      case d of
        S.Def vb rng0 _ _ _ _ -> if rng `rangesOverlap` rng0 then Just d else Nothing
    ) (const Nothing)

findLambdaFromRange :: UserProgram -> Range -> Maybe UserExpr
findLambdaFromRange prog rng =
  findFromRange prog rng (const Nothing) $ \e -> case e of
    S.Lam _ body rng0 -> if rng `rangesOverlap` rng0 then Just body else Nothing
    _ -> Nothing

findFromRange :: Ranged a => UserProgram -> Range -> (UserDef -> Maybe a) -> (UserExpr -> Maybe a) -> Maybe a
findFromRange prog rng extractDef extractExpr =
  findInDefGs (programDefs prog)
  where
    getBest ls =
      case ls of
        [] -> Nothing
        xs -> Just $ minimumBy (\l1 l2 -> compare (rangeLength (getRange l1)) (rangeLength (getRange l2))) xs
    findInDefGs defgs = getBest $ mapMaybe findInDefG defgs
    findInDefG def =
      case def of
        S.DefNonRec df -> findInDef df
        S.DefRec dfs -> getBest $ mapMaybe findInDef dfs
    findInDef def =
      case def of
        S.Def vb rng0 _ _ _ _ -> getBest (catMaybes [if rng `rangesOverlap` rng0 then extractDef def else Nothing, findInBinder vb])
    findInBinder vb =
      case vb of
        S.ValueBinder _ _ e _ _ -> findInExpr e
    findInExpr e =
      -- trace ("Looking in expr " ++ show e) $ 
      let bestChild =
            case e of
              S.Lam _ body rng0 -> findInExpr body
              S.App f args _ -> getBest $ catMaybes (findInExpr f : map (findInExpr . snd) args)
              S.Let dg body _ -> getBest $ catMaybes [findInDefG dg, findInExpr body]
              S.Bind d e _ -> getBest $ catMaybes [findInDef d, findInExpr e]
              S.Case e bs _ -> getBest $ catMaybes (findInExpr e: map findInBranch bs)
              S.Parens e _ _ _ -> findInExpr e
              S.Inject _ e _ _ -> findInExpr e
              S.Var{} -> Nothing
              S.Lit _ -> Nothing
              S.Ann e _ _ -> findInExpr e
              S.Handler _ _ _ _ _ _ init ret fin bs _ _ ->
                getBest (mapMaybe findInExpr (catMaybes [init, ret, fin]) ++ mapMaybe findInHandlerBranch bs)
        in if rng `rangesOverlap` getRange e then getBest (catMaybes [bestChild, extractExpr e]) else bestChild
    findInHandlerBranch (S.HandlerBranch _ _ body _ _ _) = findInExpr body
    findInBranch (S.Branch pat guards) = getBest $ mapMaybe findInGuard guards
    findInGuard (S.Guard e body) = getBest $ catMaybes [findInExpr e, findInExpr body]

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

