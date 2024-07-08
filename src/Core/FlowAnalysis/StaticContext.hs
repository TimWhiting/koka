-----------------------------------------------------------------------------
-- Copyright 2024 Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
module Core.FlowAnalysis.StaticContext(
                          ExprContext(..),
                          ExprContextId(..),
                          ExpressionSet,
                          contextId,contextOf,exprOfCtx,modCtx,ppContextPath,
                          enclosingDef,maybeHandleInLambda,enclosingHandle,enclosingLambda,maybeHandlerName,
                          maybeExprOfCtx,
                          rangesOverlap,
                          lamVar,lamVarDef,lamArgNames,
                          showDg,showDef,showCtxExpr,fvs,localFv,
                          branchContainsBinding,
                          branchVars,
                          findApplicationFromRange,findLambdaFromRange,findDefFromRange,
                          basicExprOf,defsOf,defOfCtx,
                          lookupDefGroup,lookupDefGroups,lookupDef,
                          isLetDefBindingFinished,letDefBinding,letDefBindingIndex,
                          dgTNames,dgsTNames,dfsTNames,letDefsOf,
                          showSimpleContext,
                          isMain
                        ) where
import Core.Core as C
import Common.Name
import Compile.Module
import Type.Type
import Data.Set hiding (take, filter, map)
import Type.Pretty
import Syntax.Syntax as S
import Common.Range
import Data.Maybe (mapMaybe, catMaybes, fromMaybe, maybeToList)
import Core.CoreVar (bv, HasExpVar (..))
import Core.Pretty
import Debug.Trace (trace)
import Data.List (intercalate, intersperse, minimumBy)
import Common.NamePrim (nameOpExpr, isNameTuple, nameTrue)
import qualified Data.Text as T
import Lib.PPrint
import Common.Failure (HasCallStack)
import qualified Data.Set as S hiding (take)

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
  | LetCDefRec !ExprContextId !ExprContext ![TName] !Int !C.DefGroup -- In a let definition context working on a particular def
  | LetCDefNonRec !ExprContextId !ExprContext ![TName] !C.DefGroup -- In a let definition context working on a particular def
  | LetCBody !ExprContextId !ExprContext ![TName] !C.Expr -- In a let body expression
  | CaseCMatch !ExprContextId !ExprContext !C.Expr -- In a case match context working on the match expression (assumes only one)
  | CaseCBranch !ExprContextId !ExprContext ![TName] !Int !C.Branch -- Which branch currently inspecting, as well as the Case context
  | ExprCBasic !ExprContextId !ExprContext !C.Expr -- A basic expression context that has no sub expressions
  | ExprPrim !C.Expr -- A primitive expression that is not part of the program (part of primitive evaluation)
  | ExprCTerm !ExprContextId !String -- Since analysis can fail or terminate early, keep track of the query that failed

isMain :: ExprContext -> Bool
isMain ctx = nameStem (C.defName (defOfCtx ctx)) == "main"

lamArgNames :: HasCallStack => ExprContext -> [TName]
lamArgNames ctx =
  lamExprArgNames (exprOfCtx ctx)

lamExprArgNames :: HasCallStack => C.Expr -> [TName]
lamExprArgNames e =
  case e of
    C.Lam names _ _ -> names
    C.TypeLam _ expr -> lamExprArgNames expr
    C.TypeApp expr _ -> lamExprArgNames expr
    _ -> error ("Not a lambda: " ++ showSimpleExpr e)

data ExprContextId = ExprContextId{
  exprId:: !Int,
  moduleName:: !Name
} deriving (Ord, Eq)

instance Show ExprContextId where
  show id =
    showFullyExplicit (moduleName id) ++ ":" ++ show (exprId id)

instance Eq ExprContext where
  ctx1 == ctx2 = 
    case (ctx1, ctx2) of
      (ExprPrim e1, ExprPrim e2) -> e1 == e2
      _ -> contextId ctx1 == contextId ctx2

instance Ord ExprContext where
  compare ctx1 ctx2 = 
    case (ctx1, ctx2) of
      (ExprPrim e1, ExprPrim e2) -> compare e1 e2
      _ -> compare (contextId ctx1) (contextId ctx2)

instance Eq C.Expr where
  e1 == e2 = showSimpleExpr e1 == showSimpleExpr e2

instance Ord C.Expr where
  compare e1 e2 = compare (showSimpleExpr e1) (showSimpleExpr e2)

instance Ord Type where
  compare tp1 tp2 = compare (show $ ppType defaultEnv tp1) (show $ ppType defaultEnv tp2)

instance Eq C.Def where
  def1 == def2 = C.defName def1 == C.defName def2 && C.defType def1 == C.defType def2

type ExpressionSet = Set ExprContextId

localFv :: C.Expr -> Set TName
localFv expr
  = S.fromList $ filter (not . isQualified . C.getName) (tnamesList (fv expr)) -- trick: only local names are not qualified

fvs :: HasCallStack => ExprContext -> S.Set TName
fvs ctx =
  case maybeExprOfCtx ctx of
    Just expr -> localFv expr

enclosingLambda :: ExprContext -> Maybe ExprContext
enclosingLambda ctx =
  case ctx of
    LamCBody{} -> Just ctx
    _ -> enclosingLambda =<< contextOf ctx

enclosingDef :: ExprContext -> C.Def
enclosingDef ctx =
  case ctx of
    DefCRec _ _ _ index dg -> defsOf dg !! index
    DefCNonRec _ _ _ dg -> head $ defsOf dg
    LetCDefRec _ c _ _ _ -> enclosingDef c
    LetCDefNonRec _ c _ _ -> enclosingDef c
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
    C.App (C.TypeApp (C.Con tn _) _) vars _ | isHandlerConName (C.getName tn) ->
      case splitFunScheme (C.typeOf tn) of
        Just (_, _, cfc:(cln, TApp _ (_:_:(TApp tc@(TCon{}) _):_)):_, _, _) ->
          trace ("maybeHandlerName: " ++ show (C.getName tn) ++ " " ++ show (pretty tc)) $
          Just (fromHandlerConName (C.getName tn), tc)
    e ->
      case contextOf ctx of
        Just c -> maybeHandlerName c

ppContextPath :: ExprContext -> Doc
ppContextPath ctx =
  case ctx of
    ModuleC _ _ n -> text "Module " <+> text (show n)
    DefCRec _ c _ _ _ -> ppContextPath c <+> text "->" <+> text ("DRec " ++ show (defTName $ defOfCtx ctx))
    DefCNonRec _ c _ _ -> ppContextPath c <+> text "->" <+> text ("DNonRec " ++ show (defTName $ defOfCtx ctx))
    LamCBody _ c tn _ -> ppContextPath c <+> text "->" <+> text ("LamB(" ++ show tn ++ ")")
    AppCLambda _ c _ -> ppContextPath c <+> text "->" <+> text "AppL"
    AppCParam _ c i _ -> ppContextPath c <+> text "->" <+> text ("AppP" ++ show i)
    LetCDefNonRec _ c _ _ -> ppContextPath c <+> text "->" <+> text ("LtD " ++ show (defTName $ defOfCtx ctx))
    LetCDefRec _ c _ _ _ -> ppContextPath c <+> text "->" <+> text ("LtDR " ++ show (defTName $ defOfCtx ctx))
    LetCBody _ c names _ -> ppContextPath c <+> text "->" <+> text ("LtB" ++ show names)
    CaseCMatch _ c _ -> ppContextPath c <+> text "->" <+> text "CaseM"
    CaseCBranch _ c _ _ _ -> ppContextPath c <+> text "->" <+> text "CaseB"
    ExprCBasic _ c _ -> ppContextPath c <+> text "->" <+> text (show ctx)
    ExprCTerm _ _ -> text "Query Error"

lamVar :: HasCallStack => Int -> ExprContext -> C.Expr
lamVar index ctx =
  case maybeExprOfCtx ctx of
    Just x -> lamVarExpr index x
    Nothing -> trace ("DemandAnalysis.lamVar: not a lambda " ++ show ctx) error "Not a lambda"

lamVarExpr :: HasCallStack => Int -> C.Expr -> C.Expr
lamVarExpr index e =
  case e of
    C.Lam names _ _ -> C.Var (names !! index) InfoNone
    TypeLam _ c -> lamVarExpr index c
    TypeApp c _ -> lamVarExpr index c
    _ -> error ("DemandAnalysis.lamVarExpr: not a lambda " ++ show e)

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
      let dfs = defs !! defGroupIndex
      in length (defsOf dfs) == bindingIndex

letDefBinding :: Int -> Int -> ExprContext -> C.Def
letDefBinding defGroupIndex bindingIndex e = do
  case exprOfCtx e of
    C.Let defs _ ->
      let dfs = defs !! defGroupIndex
      in defsOf dfs !! bindingIndex

letDefBindingIndex :: Int -> Int -> ExprContext -> Int
letDefBindingIndex defGroupIndex bindingIndex e = do
  case exprOfCtx e of
    C.Let defs _ ->
      let dfs = sum $ map (length . defsOf) $ take defGroupIndex defs
      in dfs + bindingIndex
      
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
    CaseCMatch _ c _ -> closestRange c
    CaseCBranch _ c tn _ _ ->
      case tn of
        t:_ -> case C.originalRange t
          of Just r -> r
             Nothing -> closestRange c
        _ -> closestRange c
    ExprCBasic _ c _ -> closestRange c
    ExprCTerm _ _ -> rangeNull
    ExprPrim e -> rangeNull

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
    C.Con n _ -> prettyVar env n
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

showSimpleContext ctx =
  let r = show (closestRange ctx) in
  -- show (contextId ctx) ++ " " ++ 
  case maybeExprOfCtx ctx of
    Just e -> showSimpleExpr e
    Nothing ->
      case ctx of
        ModuleC _ _ n -> "Module " ++ show n
        DefCRec{} -> "DefRec(" ++ showSimple (defTName (defOfCtx ctx)) ++ ")"
        DefCNonRec{} -> "DefNonRec(" ++ showSimple (defTName (defOfCtx ctx)) ++ ")"
        LamCBody _ _ tn _-> "LamBody(" ++ showSimple tn ++ ")"
        AppCLambda{} -> "AppLambda(" ++ showSimple (exprOfCtx ctx) ++ ")"
        AppCParam{} -> "AppParam(" ++ showSimple (exprOfCtx ctx) ++ ")"
        LetCDefNonRec _ _ _ d -> "LetDef(" ++ showSimple (defTName (defOfCtx ctx)) ++ ")"
        LetCDefRec _ _ _ i d -> "LetDefR(" ++ showSimple (defTName (defOfCtx ctx)) ++ ")"
        LetCBody{} -> "LetBody(" ++ showSimple (exprOfCtx ctx) ++ ")"
        CaseCMatch{} -> "CaseMatch(" ++ showSimple (exprOfCtx ctx) ++ ")"
        CaseCBranch{} -> "CaseBranch(" ++ showSimple (exprOfCtx ctx) ++ ")"
        ExprCBasic{} -> "ExprBasic(" ++ showSimple (exprOfCtx ctx) ++ ")"
        ExprCTerm{} -> "Query Error"
        ExprPrim e -> "Primitive(" ++ showSimple e ++ ")"

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
      DefCRec{} -> "DefRec " ++ showDef (defOfCtx e)
      DefCNonRec{} -> "DefNonRec " ++ showDef (defOfCtx e)
      LamCBody _ _ tn e -> "LamBody " ++ show tn ++ " " ++ showExpr e
      AppCLambda _ _ f -> "AppLambda " ++ showExpr f
      AppCParam _ _ i p -> "AppParam " ++ show i ++ " " ++ showExpr p
      LetCDefNonRec{} -> "LetDef " ++ showDef (defOfCtx e)
      LetCDefRec{} -> "LetDef " ++ showDef (defOfCtx e)
      LetCBody _ _ _ e -> "LetBody " ++ showExpr e
      CaseCMatch _ _ e -> "CaseMatch " ++ showExpr e
      CaseCBranch _ _ _ i b -> "CaseBranch " ++ show i ++ " " ++ show b
      ExprCBasic _ _ e -> "ExprBasic " ++ showExpr e
      ExprCTerm _ s -> "Query: " ++ s
      ExprPrim e -> "Primitive " ++ showSimpleExpr e

defOfCtx :: ExprContext -> C.Def
defOfCtx ctx =
  case ctx of
    DefCNonRec _ _ _ dg -> head $ defsOf dg
    DefCRec _ _ _ i dg -> defsOf dg !! i
    LetCDefNonRec _ _ _ dg -> head $ defsOf dg
    LetCDefRec _ _ _ i dg -> defsOf dg !! i
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
    LetCDefNonRec _ _ _ dg -> defExpr $ defOfCtx ctx
    LetCDefRec _ _ _ i dg -> defExpr $ defOfCtx ctx
    LetCBody _ _ _ e -> e
    CaseCMatch _ _ e -> e
    CaseCBranch _ _ _ _ b -> C.guardExpr (head (C.branchGuards b))
    ExprCBasic _ _ e -> e
    ExprCTerm{} -> error "Query should never be queried for expression"
    ExprPrim e -> e

maybeExprOfCtx :: ExprContext -> Maybe C.Expr
maybeExprOfCtx ctx =
  case ctx of
    ModuleC {} -> Nothing
    DefCRec _ _ _ i d -> Just (defExpr $ defOfCtx ctx)
    DefCNonRec _ _ _ d -> Just (defExpr $ defOfCtx ctx)
    LamCBody _ _ _ e -> Just e
    AppCLambda _ _ f -> Just f
    AppCParam _ _ _ param -> Just param
    LetCDefNonRec _ _ _ dg -> Just (defExpr $ defOfCtx ctx)
    LetCDefRec _ _ _ i dg -> Just (defExpr $ defOfCtx ctx)
    LetCBody _ _ _ e -> Just e
    CaseCMatch _ _ e -> Just e
    CaseCBranch _ _ _ _ b -> Just $ C.guardExpr (head (C.branchGuards b))
    ExprCBasic _ _ e -> Just e
    ExprCTerm{} -> error "Query should never be queried for expression"
    ExprPrim e -> Just e

showCtxExpr :: ExprContext -> String
showCtxExpr ctx =
  case maybeExprOfCtx ctx of
    Just e -> showExpr e
    Nothing -> show ctx

contextId :: HasCallStack => ExprContext -> ExprContextId
contextId ctx =
  case ctx of
    ModuleC c _ _ -> c
    DefCRec c _ _ _ _ -> c
    DefCNonRec c _ _ _ -> c
    LamCBody c _ _ _ -> c
    AppCLambda c _ _ -> c
    AppCParam c _ _ _ -> c
    LetCDefNonRec c _ _ _ -> c
    LetCDefRec c _ _ _ _ -> c
    LetCBody c _ _ _ -> c
    CaseCMatch c _ _ -> c
    CaseCBranch c _ _ _ _ -> c
    ExprCBasic c _ _ -> c
    ExprCTerm c _ -> c
    ExprPrim _ -> ExprContextId (-10) (newName "primitive expression")

contextOf :: ExprContext -> Maybe ExprContext
contextOf ctx =
  case ctx of
    ModuleC{} -> Nothing
    DefCRec _ c _ _ _ -> Just c
    DefCNonRec _ c _ _ -> Just c
    LamCBody _ c _ _ -> Just c
    AppCLambda _ c _ -> Just c
    AppCParam _ c _ _ -> Just c
    LetCDefNonRec _ c _ _ -> Just c
    LetCDefRec _ c _ _ _ -> Just c
    LetCBody _ c _ _ -> Just c
    CaseCMatch _ c _ -> Just c
    CaseCBranch _ c _ _ _ -> Just c
    ExprCBasic _ c _ -> Just c
    ExprCTerm{} -> Nothing

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

findDefFromRange :: UserProgram -> Range -> Name -> Maybe UserDef
findDefFromRange prog rng name =
  findFromRange prog rng (\d ->
      case d of
        S.Def vb rng0 _ _ _ _ -> if rng `rangesOverlap` rng0 || S.defName d == name then Just d else Nothing
    ) (const Nothing)

findLambdaFromRange :: UserProgram -> Range -> Maybe UserExpr
findLambdaFromRange prog rng =
  findFromRange prog rng (const Nothing) $ \e -> case e of
    S.Lam _ body rng0 -> if rng `rangesOverlap` rng0 then Just e else Nothing
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

