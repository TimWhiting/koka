-----------------------------------------------------------------------------
-- Copyright 2024 Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE BangPatterns #-}
module Core.FlowAnalysis.StaticContext(
                          ExprContext(..),
                          ExprContextId(..),
                          ExpressionSet,
                          contextId,contextOf,exprOfCtx,modCtx,ppContextPath,
                          enclosingDef,enclosingLambda,
                          maybeExprOfCtx,
                          rangesOverlap,
                          lamVar,lamVarName,lamNames,
                          showDg,showDef,showCtxExpr,
                          branchContainsBinding,
                          branchVars,
                          findApplicationFromRange,findLambdaFromRange,findDefFromRange,
                          basicExprOf,defOf,defsOf,defOfCtx,
                          lookupDefGroup,lookupDefGroups,lookupDef,
                          showSimpleContext,isLetDefBindingFinished,nextLetDefIndex,
                          letDefBinding,letDefsOf,
                          isMain,
                          letBindingName, nextFvs, eConName,
                          fvs, fvvs, dfsTNames, dgsTNames, dgTNames, localFv
                        ) where
import Core.Core as C
import Common.Name
import Compile.Module
import Type.Type
import Type.Pretty
import Syntax.Syntax as S
import qualified Data.Set as S
import Common.Range
import Data.Maybe (mapMaybe, catMaybes, fromMaybe, maybeToList, fromJust)
import Core.CoreVar (bv, fv)
import Core.Pretty
import Debug.Trace (trace)
import Data.List (intercalate, intersperse, minimumBy)
import Common.NamePrim (nameOpExpr, isNameTuple, nameTrue, nameLocalVar)
import qualified Data.Text as T
import Lib.PPrint
import Common.Failure (HasCallStack)

-- Uniquely identifies expressions despite naming
-- ExprC: [CaseCScrutinee + CaseCBranch* | AppCLambda + AppCParam*] (LetCBody, LamCBody, LetCDefGroup, ExprCBasic, and ExprPrim) 
data ExprContext =
  -- Current expression context
  -- Invariant DefRec / NonRec always has a DefGroup above it DefGroups have defs in the group as children, and the last def
  -- Children: [DefCGroup]
  ModuleC !ExprContextId !Module !Name -- Module context 
  -- Child: Bound ExprC
  | DefCRec !ExprContextId !ExprContext !Int ![TName]-- A recursive definition context, working on the index'th definition with tnames defined in the group
  -- Child: Bound ExprC
  | DefCNonRec !ExprContextId !ExprContext TName -- In a non recursive definition context, working on Def with tnames defined in the group
  -- Children: [DefCRec] | DefCNonRec
  | DefCGroup !ExprContextId !ExprContext ![TName] !C.DefGroup -- In a definition context working on a particular defgroup
  -- Child: Bound ExprC
  | LetCDefRec !ExprContextId !ExprContext !Int ![TName] -- In a let definition context working on a particular def with tnames defined in the group
  -- Child: Bound ExprC
  | LetCDefNonRec !ExprContextId !ExprContext TName -- In a let definition context working on a particular def with tnames defined in the group
  -- Children: (LetCBody | LetCDefGroup) + ([LetCDefRec] | LetCDefNonRec) 
  | LetCDefGroup !ExprContextId !ExprContext ![TName] Int !C.DefGroup -- In a let definition context working on a particular defgroup 
  -- Child: ExprC
  | LetCBody !ExprContextId !ExprContext ![TName] !C.Expr -- In a let body expression
  -- Child: ExprC
  | LamCBody !ExprContextId !ExprContext ![TName] !C.Expr -- Inside a lambda body expression
  -- Child: ExprC
  | AppCLambda !ExprContextId !ExprContext !C.Expr -- Application context inside function context
  -- Child: ExprC
  | AppCParam !ExprContextId !ExprContext !Int !C.Expr -- Application context inside param context
  -- Child: ExprC
  | CaseCScrutinee !ExprContextId !ExprContext !C.Expr -- In a case match context working on the match expression (assumes only one)
  -- Child: ExprC 
  | CaseCBranch !ExprContextId !ExprContext ![TName] !Int !C.Branch -- Which branch currently inspecting, as well as the Case context
  -- Children: None
  | ExprCBasic !ExprContextId !ExprContext !C.Expr -- A basic expression context that has no sub expressions
  -- Children: None
  | ExprPrim !ExprContextId !C.Expr -- A primitive expression that is not part of the program (part of primitive evaluation)

isMain :: ExprContext -> Bool
isMain ctx = nameStem (C.defName (defOfCtx ctx)) == "main"

letBindingName :: Int -> Int -> ExprContext -> TName
letBindingName groupIdx bindingIdx parent =
  let bind = letDefBinding groupIdx bindingIdx parent in
  defTName bind

parentLetExpr :: ExprContext -> ExprContext
parentLetExpr expr =
  case maybeExprOfCtx expr of
    Just (C.Let _ _) -> expr
    _ -> case contextOf expr of
      Just c -> parentLetExpr c
      Nothing -> error "No parent let expression"

nextFvs :: HasCallStack => ExprContext -> S.Set TName
nextFvs expr =
  let andParent fvs =
        let res = maybe S.empty nextFvs (contextOf expr)
        -- in trace ("nextFvs of " ++ showSimpleContext expr ++ " = " ++ show (S.toList fvs) ++ " with parent " ++ show (S.toList res)) $
           in S.union fvs res
      bound = bvs False (fromJust $ contextOf expr)
      parentExpr = exprOfCtx <$> contextOf expr
      parentLetExprFvs i =
         let letCtx = parentLetExpr expr
          in case maybeExprOfCtx letCtx of
                Just (C.Let dgs e) ->
                  let parentFvs = nextFvs letCtx in
                    let letFvs = S.unions $ fv e:map dgFvs (drop i dgs)
                      in -- trace ("LetExprFvs " ++ showSimpleContext letCtx ++ " i=" ++ show i ++
                        -- " parentFvs=" ++ show (S.toList parentFvs) ++
                        -- " letFvs=" ++ show (S.toList letFvs)) 
                        --  $
                         S.union parentFvs $ S.intersection bound letFvs
  in let result = case expr of
          ExprPrim _ e -> andParent (fvvs expr)
          ExprCBasic _ _ e -> andParent (fvvs expr)
          CaseCBranch{} -> andParent S.empty
          CaseCScrutinee{} -> andParent S.empty
          AppCParam _ _ param app -> andParent $ S.intersection bound $ S.unions (map fv $ drop param $ args (fromJust parentExpr))
          AppCLambda _ _ f -> andParent $ S.intersection bound $ S.unions (map fv $ args (fromJust parentExpr))
          LetCBody{} -> andParent S.empty
          LetCDefGroup _ _ _ i g -> parentLetExprFvs i
          LetCDefNonRec{} -> andParent S.empty
          LetCDefRec{} -> andParent S.empty
          _ -> S.empty
      in -- trace ("Ctx:\n" ++ show (ppContextPath expr) ++
            -- "\n" ++ maybe "" showSimpleExpr (maybeExprOfCtx expr) ++
            -- "\n" ++ show expr ++
            -- "\n" ++ show (S.toList bound) ++
            -- "\n" ++ show (S.toList (fvs expr)) ++
            -- "\n" ++ show (S.toList result)) $
       result

args expr =
  case expr of
    C.App _ ags _ -> ags
letDgs expr =
  case expr of
    C.Let defs _ -> defs
dgFvs (C.DefNonRec def) = fv def
dgFvs (C.DefRec dfs) = S.unions (map fv dfs)

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
    fileName (moduleName id) ++ ":" ++ show (exprId id)

fileName :: Name -> String
fileName name =
  let mod = nameModule name
  in T.unpack $ last $ T.split (== '/') (T.pack mod)

instance Eq ExprContext where
  ctx1 == ctx2 = contextId ctx1 == contextId ctx2

instance Ord ExprContext where
  compare ctx1 ctx2 = compare (contextId ctx1) (contextId ctx2)

instance Eq Type where
  tp1 == tp2 = show (ppType defaultEnv tp1) == show (ppType defaultEnv tp2)

instance Ord Type where
  compare tp1 tp2 = compare (show $ ppType defaultEnv tp1) (show $ ppType defaultEnv tp2)

instance Eq C.Def where
  def1 == def2 = C.defName def1 == C.defName def2 && C.defType def1 == C.defType def2

type ExpressionSet = S.Set ExprContextId

localFv :: C.Expr -> S.Set TName
localFv expr
  = S.fromList $ filter (not . isQualified . C.getName) (tnamesList (fv expr)) -- trick: only local names are not qualified

fvs :: HasCallStack => ExprContext -> S.Set TName
fvs ctx =
  case maybeExprOfCtx ctx of
    Just expr ->
      trace ("fvs of " ++ showSimpleExpr expr ++ " in " ++ show (ppContextPath ctx) ++ " = bvs " ++ show (bvs True ctx) ++ " fvs " ++ show (fv expr)) $
      S.intersection (bvs True ctx) (fv expr)
    Nothing -> S.empty

fvvs :: HasCallStack => ExprContext -> S.Set TName
fvvs ctx =
  case maybeExprOfCtx ctx of
    Just expr -> S.intersection (bvs False ctx) (fv expr)

bvs :: HasCallStack => Bool -> ExprContext -> S.Set TName
bvs includeVars ctx =
  -- trace (showSimpleContext ctx ++ " bvs includeVars=" ++ show includeVars) $
  let andParent bv = S.union bv $ maybe S.empty (bvs includeVars) (contextOf ctx)
      grandparentExpr = maybeExprOfCtx =<< (contextOf =<< contextOf ctx)
  in case ctx of
    ModuleC{} -> S.empty
    DefCRec{} -> S.empty
    DefCNonRec{} -> S.empty
    DefCGroup _ c _ dg -> S.empty
    LamCBody _ _ names _ ->
      if includeVars then andParent $ S.fromList names
      else case grandparentExpr of
        (Just (C.App (C.TypeApp (C.Var name _) _) _ _)) | nameLocalVar == C.getName name -> andParent S.empty
        _ -> andParent $ S.fromList names
    LetCBody _ _ names _ -> andParent $ S.fromList names
    LetCDefGroup _ _ names _ _ -> andParent $ S.fromList names
    LetCDefNonRec _ _ nm -> andParent $ S.singleton nm
    LetCDefRec _ _ _ names -> andParent $ S.fromList names
    AppCLambda{} -> andParent S.empty
    AppCParam{} -> andParent S.empty
    CaseCScrutinee{} -> andParent S.empty
    CaseCBranch _ _ vars _ _ -> andParent $ S.fromList vars
    ExprCBasic{} -> andParent S.empty
    ExprPrim{} -> S.empty

eConName :: ExprContext -> Maybe TName
eConName con =
  case maybeExprOfCtx con of
    Just (Con conName _ _) -> Just conName
    _ -> Nothing

enclosingLambda :: ExprContext -> Maybe ExprContext
enclosingLambda ctx =
  case ctx of
    LamCBody{} -> Just ctx
    _ -> enclosingLambda =<< contextOf ctx

ctxDefGroup :: ExprContext -> C.DefGroup
ctxDefGroup ctx =
  case ctx of
    DefCGroup _ _ _ dg -> dg
    LetCDefGroup _ _ _ _ dg -> dg
    _ -> error "No def group"

enclosingDef :: ExprContext -> C.Def
enclosingDef ctx =
  case ctx of
    DefCRec _ c index _ -> defOf (ctxDefGroup c) index
    DefCNonRec _ c _ -> defOf (ctxDefGroup c) 0
    LetCDefRec _ c index _ -> defOf (ctxDefGroup c) index
    LetCDefNonRec _ c _ -> defOf (ctxDefGroup c) 0
    _ -> case contextOf ctx
      of Just c -> enclosingDef c
         Nothing -> error "No parent def"

enclosingHandle :: ExprContext -> ExprContext
enclosingHandle ctx =
  case maybeHandleInLambda ctx of
    Just h -> h
    Nothing -> error "No enclosing handle"

maybeHandleInLambda :: ExprContext -> Maybe ExprContext
maybeHandleInLambda ctx =
  case maybeExprOfCtx ctx of
    Just (C.App (C.TypeApp (C.Var tn _) _) _ _ ) | isHandleName (C.getName tn) -> Just ctx
    _ -> case ctx of
      LamCBody{} -> Nothing
      _ -> maybeHandleInLambda =<< contextOf ctx

-- Gets the name and the type of the effect
maybeHandlerName :: ExprContext -> Maybe (Name,Type)
maybeHandlerName ctx =
  case exprOfCtx ctx of
    C.App (C.TypeApp (C.Con tn _ _) _) vars _ | isHandlerConName (C.getName tn) ->
      case splitFunScheme (C.typeOf tn) of
        Just (_, cfc:(cln, TApp _ (_:_:(TApp tc@(TCon{}) _):_)):_, _, _) ->
          trace ("maybeHandlerName: " ++ show (C.getName tn) ++ " " ++ show (pretty tc)) $
          Just (fromHandlerConName (C.getName tn), tc)
    e ->
      case contextOf ctx of
        Just c -> maybeHandlerName c

ppContextPath :: ExprContext -> Doc
ppContextPath ctx =
  case ctx of
    ModuleC _ _ n -> text "Module " <+> text (show n)
    DefCRec _ c _ _ -> ppContextPath c <+> text "->" <+> text ("DRec " ++ show (defTName $ defOfCtx ctx))
    DefCNonRec _ c _ -> ppContextPath c <+> text "->" <+> text ("DNonRec " ++ show (defTName $ defOfCtx ctx))
    DefCGroup _ c _ dg -> ppContextPath c
    LamCBody _ c tn _ -> ppContextPath c <+> text "->" <+> text ("LamB(" ++ show tn ++ ")")
    AppCLambda _ c _ -> ppContextPath c <+> text "->" <+> text "AppL"
    AppCParam _ c i _ -> ppContextPath c <+> text "->" <+> text ("AppP" ++ show i)
    LetCDefNonRec _ c _ -> ppContextPath c <+> text "->" <+> text ("LtD " ++ show (defTName $ defOfCtx ctx))
    LetCDefRec _ c _ _ -> ppContextPath c <+> text "->" <+> text ("LtDR " ++ show (defTName $ defOfCtx ctx))
    LetCBody _ c names _ -> ppContextPath c <+> text "->" <+> text ("LtB" ++ show names)
    LetCDefGroup _ c _ _ dg -> ppContextPath c
    CaseCScrutinee _ c _ -> ppContextPath c <+> text "->" <+> text "CaseM"
    CaseCBranch _ c _ _ _ -> ppContextPath c <+> text "->" <+> text "CaseB"
    ExprCBasic _ c _ -> ppContextPath c <+> text "->" <+> text (show ctx)
    ExprPrim{} -> text "Primitive"

lamVar :: Int -> ExprContext -> TName
lamVar index ctx =
  case maybeExprOfCtx ctx of
    Just x -> lamVarName index x
    Nothing ->
      trace ("DemandAnalysis.lamVar: not a lambda " ++ show ctx)
      error "Not a lambda"

lamVarName :: Int -> C.Expr -> TName
lamVarName index e =
  case e of
    C.Lam names _ _ -> names !! index
    TypeLam _ c -> lamVarName index c
    TypeApp c _ -> lamVarName index c
    _ -> error ("DemandAnalysis.lamVarName: not a lambda " ++ show e)

lamVarDef :: C.Def -> C.Expr
lamVarDef def = C.Var (TName (C.defName def) (C.defType def) Nothing) InfoNone

letDefsOf :: HasCallStack => ExprContext -> C.DefGroups
letDefsOf ctx =
  case exprOfCtx ctx of
    C.Let defs _ -> defs
    _ -> error "Not a let expression"

isLetDefBindingFinished :: Int -> Int -> ExprContext -> Bool
isLetDefBindingFinished defGroupIndex bindingIndex e = do
  case exprOfCtx e of
    C.Let defs _ ->
      length defs == defGroupIndex + 1 &&
        let dfs = defs !! defGroupIndex
        in length (defsOf dfs) == bindingIndex + 1

nextLetDefIndex :: Int -> Int -> ExprContext -> (Int,Int)
nextLetDefIndex !defGroupIndex !bindingIndex e = do
  case exprOfCtx e of
    C.Let defs _ ->
      let numDefGroups = length defs in
      let dfs = defs !! defGroupIndex in
      let numBindings = length (defsOf dfs) in
      if bindingIndex + 1 < numBindings then
        (defGroupIndex, bindingIndex + 1)
      else
        (defGroupIndex + 1, 0)

letDefBinding :: Int -> Int -> ExprContext -> C.Def
letDefBinding defGroupIndex bindingIndex e = do
  case exprOfCtx e of
    C.Let defs _ ->
      let dfs = defs !! defGroupIndex
      in defsOf dfs !! bindingIndex

dgsTNames :: C.DefGroups -> [TName]
dgsTNames = concatMap (\dg -> dfsTNames (defsOf dg))

dfsTNames :: [C.Def] -> [TName]
dfsTNames = map (\d -> TName (C.defName d) (C.defType d) Nothing)

dgTNames :: C.DefGroup -> [TName]
dgTNames (C.DefRec defs) = dfsTNames defs
dgTNames (C.DefNonRec df) = [TName (C.defName df) (C.defType df) Nothing]

simpleEnv = defaultEnv{showKinds=False,fullNames=False,noFullNames=True,expandSynonyms=False,showFlavours=False,coreShowTypes=False}

showExpr :: C.Expr -> String
showExpr e = show $ prettyExpr simpleEnv e

showDg d = show $ prettyDefGroup simpleEnv d

showDef d = show $ prettyDef simpleEnv d

closestRange :: ExprContext -> Range
closestRange ctx =
  case ctx of
    ModuleC{} -> rangeNull
    DefCRec{} -> C.defNameRange (defOfCtx ctx)
    DefCNonRec{} -> C.defNameRange (defOfCtx ctx)
    LamCBody _ c tn _ ->
      case tn of
        t:_ -> case C.originalRange t
          of Just r -> r
             Nothing -> closestRange c
        _ -> closestRange c
    AppCLambda _ c _ -> closestRange c
    AppCParam _ c _ _ -> closestRange c
    LetCDefNonRec{} -> C.defNameRange (defOfCtx ctx)
    LetCDefRec{} -> C.defNameRange (defOfCtx ctx)
    LetCBody _ c _ _ -> closestRange c
    CaseCScrutinee _ c _ -> closestRange c
    CaseCBranch _ c tn _ _ ->
      case tn of
        t:_ -> case C.originalRange t
          of Just r -> r
             Nothing -> closestRange c
        _ -> closestRange c
    ExprCBasic _ c _ -> closestRange c
    ExprPrim _ e -> rangeNull


simplePrettyExprN :: Env -> Int -> C.Expr -> Doc
simplePrettyExprN env n e =
  if n <= 0 then text "."
  else case e of
    C.Var n _ -> prettyVar env n
    C.App f args _ -> simplePrettyExprN env n f <.> argsdoc
      where argsdoc =
              if length args > 2 then
                tupled (map (simplePrettyExprN env (n - 1)) args ++ [text "."])
              else
                tupled (map (simplePrettyExprN env (n - 1)) args)
    C.Lam ns _ e -> text "(fn" <.> tupled (map (prettyVar env) ns) <+> indent 2 (simplePrettyExprN env (n - 1) e) <.> text ")"
    C.Let dgs e -> vcat (map (simplePrettyDefGroup env n) dgs ++ [simplePrettyExprN env (n - 1) e])
    C.Case e bs -> text "match" <+> simplePrettyExprN env (n - 1) (head e) <--> indent 2 (vcat (map (simplePrettyBranch env (n - 1)) bs))
    C.TypeLam ns e -> text "(tfn()" <.> simplePrettyExprN env n e <.> text ")"
    C.TypeApp e ts -> text "tapp(" <.> simplePrettyExprN env n e <.> text ")"
    C.Con n _ _ -> prettyVar env n
    C.Lit n -> case n of
      C.LitChar c -> text (show c)
      C.LitInt i -> text (show i)
      C.LitFloat f -> text (show f)
      C.LitString s -> text (show s)


simplePrettyBranch :: Env -> Int -> C.Branch -> Doc
simplePrettyBranch env n (C.Branch pat guards) =
  let (env', patDoc) = prettyPattern env (head pat) in
  patDoc <+> text "->" <--> indent 2 (simplePrettyExprN env' (n - 1) (C.guardExpr (head guards)))

simplePrettyDefGroup :: Env -> Int -> C.DefGroup -> Doc
simplePrettyDefGroup env n dg =
  case dg of
    C.DefNonRec d -> simplePrettyDef env n d
    C.DefRec ds -> vcat (map (simplePrettyDef env n) ds)

simplePrettyDef :: Env -> Int -> C.Def -> Doc
simplePrettyDef env n d =
  text "val" <+> pretty (C.defName d) <+> text "=" <--> indent 2 (simplePrettyExprN env n (C.defExpr d))

simplePrettyExpr :: Env -> C.Expr -> Doc
simplePrettyExpr env e = simplePrettyExprN env 4 e

showSimpleExpr :: C.Expr -> String
showSimpleExpr e = show $ simplePrettyExpr simpleEnv e


showSimpleContext :: HasCallStack => ExprContext -> [Char]
showSimpleContext ctx =
  let r = show (closestRange ctx) in
  -- show (contextId ctx) ++ " " ++ 
  case ctx of
    ModuleC _ _ n -> "Module " ++ show n
    DefCRec{} -> "DefRec(" ++ showSimple (defTName (defOfCtx ctx)) ++ ")"
    DefCNonRec{} -> "DefNonRec(" ++ showSimple (defTName (defOfCtx ctx)) ++ ")"
    DefCGroup _ _ tn _ -> "DefGroup(" ++ showSimple tn ++ ")"
    LamCBody _ _ tn _-> "LamBody(" ++ showSimple tn ++ ")"
    AppCLambda{} -> "AppLambda(" ++ showSimple (exprOfCtx ctx) ++ ")"
    AppCParam{} -> "AppParam(" ++ showSimple (exprOfCtx ctx) ++ ")"
    LetCDefNonRec{} -> "LetDef(" ++ showSimple (defTName (defOfCtx ctx)) ++ ")"
    LetCDefRec{} -> "LetDefR(" ++ showSimple (defTName (defOfCtx ctx)) ++ ")"
    LetCDefGroup _ _ tn _ _ -> "LetDefGroup(" ++ showSimple tn ++ ")"
    LetCBody{} -> "LetBody(" ++ showSimple (exprOfCtx ctx) ++ ")"
    CaseCScrutinee{} -> "CaseMatch(" ++ showSimple (exprOfCtx ctx) ++ ")"
    CaseCBranch{} -> "CaseBranch(" ++ showSimple (exprOfCtx ctx) ++ ")"
    ExprCBasic{} -> "ExprBasic(" ++ showSimple (exprOfCtx ctx) ++ ")"
    ExprPrim _ e -> "Primitive(" ++ showSimple e ++ ")"

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
      ModuleC id _ nm -> "Module " ++ show nm
      DefCRec id _ _ _ -> "DefRec "  ++ showDef (defOfCtx e)
      DefCNonRec id _ _ -> "DefNonRec " ++ showDef (defOfCtx e)
      DefCGroup id _ tn _ -> "DefGroup " ++ show tn
      LamCBody id _ tn e -> "LamBody " ++ show tn ++ " " ++ showExpr e
      AppCLambda id _ f -> "AppLambda " ++ showExpr f
      AppCParam id _ i p -> "AppParam " ++ show id ++ " " ++ show i ++ " " ++ showExpr p
      LetCDefNonRec id _ _ -> "LetDef " ++ showDef (defOfCtx e)
      LetCDefRec id _ _ _ -> "LetDefR " ++ showDef (defOfCtx e)
      LetCDefGroup id _ tn _ _ -> "LetDefGroup " ++ show tn
      LetCBody id _ _ e -> "LetBody " ++ showExpr e
      CaseCScrutinee id _ e -> "CaseMatch " ++ showExpr e
      CaseCBranch id _ _ i b -> "CaseBranch " ++ show i ++ " " ++ show b
      ExprCBasic id _ e -> "ExprBasic " ++ showExpr e
      ExprPrim _ e -> "Primitive " ++ show e

defOfCtx :: ExprContext -> C.Def
defOfCtx ctx =
  case ctx of
    DefCNonRec _ c _ -> defOf (ctxDefGroup c) 0
    DefCRec _ c i _ -> defOf (ctxDefGroup c) i
    LetCDefNonRec _ c _ -> defOf (ctxDefGroup c) 0
    LetCDefRec _ c i _ -> defOf (ctxDefGroup c) i
    _ -> error "Query should never be queried for definition"

exprOfCtx :: HasCallStack => ExprContext -> C.Expr
exprOfCtx ctx =
  case ctx of
    ModuleC {} -> error "ModuleC is a multi Expression Context"
    DefCRec{} -> defExpr $ defOfCtx ctx
    DefCNonRec{} -> defExpr $ defOfCtx ctx
    DefCGroup{} -> error "DefCGroup is a multi Expression Context"
    LamCBody _ _ _ e -> e
    AppCLambda _ _ f -> f
    AppCParam _ _ _ param -> param
    LetCDefNonRec {} -> defExpr $ defOfCtx ctx
    LetCDefRec{} -> defExpr $ defOfCtx ctx
    LetCDefGroup{} -> error "LetCDefGroup is a multi Expression Context"
    LetCBody _ _ _ e -> e
    CaseCScrutinee _ _ e -> e
    CaseCBranch _ _ _ _ b -> C.guardExpr (head (C.branchGuards b))
    ExprCBasic _ _ e -> e
    ExprPrim _ e -> e

maybeExprOfCtx :: ExprContext -> Maybe C.Expr
maybeExprOfCtx ctx =
  case ctx of
    DefCRec{} -> Just (defExpr $ defOfCtx ctx)
    DefCNonRec{} -> Just (defExpr $ defOfCtx ctx)
    LamCBody _ _ _ e -> Just e
    AppCLambda _ _ f -> Just f
    AppCParam _ _ _ param -> Just param
    LetCDefNonRec{} -> Just (defExpr $ defOfCtx ctx)
    LetCDefRec{} -> Just (defExpr $ defOfCtx ctx)
    LetCBody _ _ _ e -> Just e
    CaseCScrutinee _ _ e -> Just e
    CaseCBranch _ _ _ _ b -> Just $ C.guardExpr (head (C.branchGuards b))
    ExprCBasic _ _ e -> Just e
    ExprPrim _ e -> Just e
    ModuleC{} -> Nothing
    DefCGroup{} -> Nothing
    LetCDefGroup{} -> Nothing

showCtxExpr :: ExprContext -> String
showCtxExpr ctx =
  case maybeExprOfCtx ctx of
    Just e -> showExpr e
    Nothing -> show ctx

contextId :: HasCallStack => ExprContext -> ExprContextId
contextId ctx =
  case ctx of
    ModuleC c _ _ -> c
    DefCRec c _ _ _ -> c
    DefCNonRec c _ _ -> c
    DefCGroup c _ _ _ -> c
    LamCBody c _ _ _ -> c
    AppCLambda c _ _ -> c
    AppCParam c _ _ _ -> c
    LetCDefNonRec c _ _ -> c
    LetCDefRec c _ _ _ -> c
    LetCDefGroup c _ _ _ _ -> c
    LetCBody c _ _ _ -> c
    CaseCScrutinee c _ _ -> c
    CaseCBranch c _ _ _ _ -> c
    ExprCBasic c _ _ -> c
    ExprPrim c _ -> c

contextOf :: ExprContext -> Maybe ExprContext
contextOf ctx =
  case ctx of
    ModuleC{} -> Nothing
    DefCRec _ c _ _ -> Just c
    DefCNonRec _ c _ -> Just c
    DefCGroup _ c _ _ -> Just c
    LamCBody _ c _ _ -> Just c
    AppCLambda _ c _ -> Just c
    AppCParam _ c _ _ -> Just c
    LetCDefNonRec _ c _ -> Just c
    LetCDefRec _ c _ _ -> Just c
    LetCDefGroup _ c _ _ _ -> Just c
    LetCBody _ c _ _ -> Just c
    CaseCScrutinee _ c _ -> Just c
    CaseCBranch _ c _ _ _ -> Just c
    ExprCBasic _ c _ -> Just c
    ExprPrim _ _ -> Nothing

modCtx :: ExprContext -> ExprContext
modCtx ctx =
  case ctx of
    ModuleC{} -> ctx
    DefCRec _ c _ _ -> modCtx c
    DefCNonRec _ c _ -> modCtx c
    DefCGroup _ c _ _ -> modCtx c
    LamCBody _ c _ _ -> modCtx c
    AppCLambda _ c _ -> modCtx c
    AppCParam _ c _ _ -> modCtx c
    LetCDefNonRec _ c _ -> modCtx c
    LetCDefRec _ c _ _ -> modCtx c
    LetCDefGroup _ c _ _ _ -> modCtx c
    LetCBody _ c _ _ -> modCtx c
    CaseCScrutinee _ c _ -> modCtx c
    CaseCBranch _ c _ _ _ -> modCtx c
    ExprCBasic _ c _ -> modCtx c
    ExprPrim _ _ -> error "Primitive context has no module context"

branchContainsBinding :: C.Branch -> TName -> Bool
branchContainsBinding (C.Branch pat guards) name =
  name `elem` bv pat

branchVars :: C.Branch -> [TName]
branchVars (C.Branch pat guards) = S.toList $ bv pat

findApplicationFromRange :: UserProgram -> Range -> Maybe UserExpr
findApplicationFromRange prog rng =
  findFromRange prog rng (const Nothing) $ \e -> case e of
    S.App f args rng0 -> if rng `rangesOverlap` rng0 then Just e else Nothing
    _ -> Nothing

findDefFromRange :: UserProgram -> Range -> Name -> Maybe UserDef
findDefFromRange prog rng name =
  case findFromRange prog rng (\d ->
        case d of -- First try to find the def that is exactly the same range and def name
          S.Def vb rng0 _ _ _ _ -> if rng `rangesOverlap` rng0 && S.defName d == name then Just d else Nothing
      ) (const Nothing) of
    Just d -> Just d
    Nothing ->
      findFromRange prog rng (\d ->
          case d of -- Otherwise we lost the range or something, loosen the range / name check.
            S.Def vb rng0 _ _ _ _ -> if rng `rangesOverlap` rng0 || S.defName d == name then Just d else Nothing
        ) (const Nothing)

findLambdaFromRange :: UserProgram -> Range -> Maybe UserExpr
findLambdaFromRange prog rng =
  findFromRange prog rng (const Nothing) $ \e -> case e of
    S.Lam _ body topDef rng0 -> if rng `rangesOverlap` rng0 then Just e else Nothing
    _ -> Nothing

findFromRange :: Ranged a => UserProgram -> Range -> (UserDef -> Maybe a) -> (UserExpr -> Maybe a) -> Maybe a
findFromRange prog rng extractDef extractExpr =
  findInDefGs (programDefs prog)
  where
    getBest ls =
      case ls of
        [] -> Nothing
        [x] ->
          -- trace ("One result " ++ showCompactRange rng) $ 
          Just x
        x1:x2:xs -> -- trace ("getBest: goal: " ++ showCompactRange rng ++ " got: " ++ showCompactRange (getRange x1) ++ " and: " ++ showCompactRange (getRange x2)) $
                    if getRange x1 == rng then Just x1 else if getRange x2 == rng then Just x2 else
                    case compare (rangeLength (getRange x1)) (rangeLength (getRange x2)) of
                      LT -> getBest (x1:xs)
                      EQ -> getBest (x1:xs)
                      GT -> getBest (x2:xs)
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
              S.Lam _ body topLevel rng0 -> findInExpr body
              S.App f args _ -> getBest $ catMaybes (findInExpr f : map (findInExpr . snd) args)
              S.Let dg body _ -> getBest $ catMaybes [findInDefG dg, findInExpr body]
              S.Bind d e _ -> getBest $ catMaybes [findInDef d, findInExpr e]
              S.Case e bs _ _ -> getBest $ catMaybes (findInExpr e: map findInBranch bs)
              S.Parens e _ _ _ -> findInExpr e
              S.Inject _ e _ _ -> findInExpr e
              S.Var{} -> Nothing
              S.Lit _ -> Nothing
              S.Ann e _ _ -> findInExpr e
              S.Handler _ _ _ _ _ _ init ret fin bs _ _ ->
                getBest (mapMaybe findInExpr (catMaybes [init, ret, fin]) ++ mapMaybe findInHandlerBranch bs)
        in getBest (catMaybes [bestChild, extractExpr e])
    findInHandlerBranch (S.HandlerBranch _ _ body _ _ _) = findInExpr body
    findInBranch (S.Branch pat guards) = getBest $ mapMaybe findInGuard guards
    findInGuard (S.Guard e body) = getBest $ catMaybes [findInExpr e, findInExpr body]

basicExprOf :: ExprContext -> Maybe C.Expr
basicExprOf ctx =
  case ctx of
    ExprCBasic _ ctx e -> Just e
    _ -> Nothing

defOf :: C.DefGroup -> Int -> C.Def
defOf (C.DefNonRec d) 0 = d
defOf (C.DefRec ds) n = ds !! n

defsOf :: C.DefGroup -> [C.Def]
defsOf (C.DefNonRec d) = [d]
defsOf (C.DefRec ds) = ds

lookupDefGroup :: C.DefGroup -> TName -> Bool
lookupDefGroup dg tname = tname `elem` defGroupTNames dg

lookupDefGroups :: C.DefGroups -> TName -> Bool
lookupDefGroups defGs tname = any (`lookupDefGroup` tname) defGs

lookupDef :: C.Def -> TName -> Bool
lookupDef def tname = C.defName def == C.getName tname && tnameType tname == C.defType def

