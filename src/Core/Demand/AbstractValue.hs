-----------------------------------------------------------------------------
-- Copyright 2024, Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-# LANGUAGE InstanceSigs #-}
module Core.Demand.AbstractValue(
                          Ctx(..),
                          EnvCtx(..),
                          LiteralLattice(..),
                          LiteralChange(..),
                          AbValue(..),
                          AChange(..),
                          BindInfo(..),
                          PatBinding(..),
                          changes, changeIn, callOfClos, envOfClos, ctxOfClos,
                          addChange, injLit, litLattice,
                          showSimpleClosure, showSimpleCtx, showSimpleEnv, showSimpleAbValue, showSimpleAbValueCtx,
                          showNoEnvClosure, showNoEnvAbValue,
                          emptyAbValue,
                          joinAbValue,
                          subsumes,subsumesCtx,
                          bind,
                          indeterminateStaticCtx,maybeModOfEnv,maybeModOfCtx,
                          refineCtx,
                          limitm,limitmenv,
                          isFullyDetermined, ccDetermined,
                          envtail,envhead
                        ) where
import Data.Map.Strict as M hiding (map)
import Common.Name
import Type.Type
import Data.Set hiding (map, map)
import Data.Set as S hiding (map)
import Core.Core as C
import Syntax.Syntax as S
import Data.List (elemIndex, intercalate)
import Compile.Module
import Debug.Trace (trace)
import Common.Range
import Data.Maybe (fromMaybe, catMaybes, isJust, fromJust)
import GHC.Base (mplus)
import Common.Failure (assertion)
import Core.Demand.StaticContext
import Core.Demand.FixpointMonad (SimpleLattice(..), Lattice (..), Contains(..), SimpleChange (..), SLattice)
import qualified Core.Demand.FixpointMonad as FM
import Core.CoreVar (bv)
import Data.Foldable (find)

-- TODO: Top Closures (expr, env, but eval results to the top of their type)

data LiteralLattice =
    LiteralLattice{
      intVL :: SLattice Integer,
      floatVL :: SLattice Double,
      charVL :: SLattice Char,
      stringVL :: SLattice String
    } deriving (Eq, Ord)

data LiteralChange =
  LiteralChangeInt (SimpleChange Integer)
  | LiteralChangeFloat (SimpleChange Double)
  | LiteralChangeChar (SimpleChange Char)
  | LiteralChangeString (SimpleChange String)
 deriving (Eq)

instance Show LiteralChange where
  show (LiteralChangeInt LChangeTop) = "int -> top"
  show (LiteralChangeFloat LChangeTop) = "float -> top"
  show (LiteralChangeChar LChangeTop) = "char -> top"
  show (LiteralChangeString LChangeTop) = "string -> top"
  show (LiteralChangeInt (LChangeSingle l)) = "int -> " ++ show l
  show (LiteralChangeFloat (LChangeSingle l)) = "float -> " ++ show l
  show (LiteralChangeChar (LChangeSingle l)) = "char -> " ++ show l
  show (LiteralChangeString (LChangeSingle l)) = "string -> " ++ show l

instance Show LiteralLattice where
  show (LiteralLattice i f c s) = intercalate "," [show i, show f, show c, show s]

data AChange =
  AChangeClos ExprContext EnvCtx
  | AChangeClosApp ExprContext ExprContext EnvCtx -- This is a closure that has a different application for it's calling context abstraction
  | AChangeConstr ExprContext EnvCtx
  | AChangeLit LiteralChange EnvCtx
  deriving (Eq)

callOfClos :: AChange -> ExprContext
callOfClos res = 
  case res of
    AChangeClos c _ -> c
    AChangeClosApp _ c _ -> c

envOfClos :: AChange -> EnvCtx
envOfClos res =
  case res of
    AChangeClos _ e -> e
    AChangeClosApp _ _ e -> e

ctxOfClos :: AChange -> ExprContext
ctxOfClos res = 
  case res of
    AChangeClos c _ -> c
    AChangeClosApp c _ _ -> c

instance Show AChange where
  show (AChangeClos expr env) =
    "clos(" ++ showNoEnvClosure (expr, env) ++ ")"
  show (AChangeClosApp expr _ env) =
    "clos(" ++ showNoEnvClosure (expr, env) ++ ")"
  show (AChangeConstr expr env) =
    "con(" ++ showNoEnvClosure (expr, env) ++ ")"
  show (AChangeLit lit env) =
    show lit

data AbValue =
  AbValue{
    aclos:: !(Set (ExprContext, EnvCtx)),
    aclosapps:: !(Set (ExprContext, ExprContext, EnvCtx)),
    acons:: !(Set (ExprContext, EnvCtx)),
    alits:: !(Map EnvCtx LiteralLattice)
  } deriving (Eq, Ord)

changes :: AbValue -> [AChange]
changes (AbValue clos clsapp constrs lits) =
  closs ++ closapps ++ constrss ++ litss
  where
    closs = map (uncurry AChangeClos) $ S.toList clos
    closapps = map (\(a, b, c) -> AChangeClosApp a b c) $ S.toList clsapp
    constrss = map (uncurry AChangeConstr) $ S.toList constrs
    litss = concatMap (\(env,lat) -> changesLit lat env) $ M.toList lits

changesLit :: LiteralLattice -> EnvCtx -> [AChange]
changesLit (LiteralLattice ints floats chars strings) env =
  intChanges ++ floatChanges ++ charChanges ++ stringChanges
  where
    intChanges = map (\x -> AChangeLit (LiteralChangeInt x) env) $ FM.elems ints
    floatChanges = map (\x -> AChangeLit (LiteralChangeFloat x) env) $ FM.elems floats
    charChanges = map (\x -> AChangeLit (LiteralChangeChar x) env) $ FM.elems chars
    stringChanges = map (\x -> AChangeLit (LiteralChangeString x) env) $ FM.elems strings

changeIn :: AChange -> AbValue -> Bool
changeIn (AChangeClos ctx env) (AbValue clos _ _ _) = S.member (ctx,env) clos
changeIn (AChangeClosApp ctx app env) (AbValue _ closapps _ _) = S.member (ctx,app,env) closapps
changeIn (AChangeConstr ctx env) (AbValue _ _ constr _) = S.member (ctx,env) constr
changeIn (AChangeLit lit env) (AbValue _ _ _ lits) =
  case M.lookup env lits of
    Just (LiteralLattice ints floats chars strings) ->
      case lit of
        LiteralChangeInt i -> i `lte` ints
        LiteralChangeFloat f -> f `lte` floats
        LiteralChangeChar c -> c `lte` chars
        LiteralChangeString s -> s `lte` strings
    Nothing -> False

instance Semigroup AbValue where
  (<>) :: AbValue -> AbValue -> AbValue
  (<>) = joinAbValue

instance Monoid AbValue where
  mempty = emptyAbValue
  mappend = (<>)

instance Show AbValue where
  show (AbValue cls clsapp cntrs lit) =
    (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
    (if S.null cntrs then "" else " constrs: " ++ show (map show (S.toList cntrs))) ++
    (if M.null lit then "" else " lit: " ++ show (map show (M.toList lit)))

instance Contains AbValue where
  contains :: AbValue -> AbValue -> Bool
  contains (AbValue cls0 clsa0 cntrs0 lit0) (AbValue cls1 clsa1 cntrs1 lit1) =
    S.isSubsetOf cls1 cls0 && S.isSubsetOf clsa1 clsa0 && cntrs1 `S.isSubsetOf` cntrs0 && M.isSubmapOfBy (\lit0 lit1 -> lit0 < lit1) lit0 lit1

-- Basic creating of abstract values
showSimpleClosure :: (ExprContext, EnvCtx) -> String
showSimpleClosure (ctx, env) = showSimpleContext ctx ++ " in " ++ showSimpleEnv env

showNoEnvClosure :: (ExprContext, EnvCtx) -> String
showNoEnvClosure (ctx, env) = showSimpleContext ctx

showSimpleEnv :: EnvCtx -> String
showSimpleEnv c =
  "<<" ++ showSimpleEnv_ c ++ ">>"

showSimpleEnv_ :: EnvCtx -> String
showSimpleEnv_ (EnvCtx ctx tail) =
  showSimpleCtx ctx ++ ":::" ++ showSimpleEnv_ tail
showSimpleEnv_ (EnvTail ctx) = showSimpleCtx ctx

showSimpleAbValueCtx :: (EnvCtx, AbValue) -> String
showSimpleAbValueCtx (env, ab) =
  showSimpleEnv env ++ ": " ++ showSimpleAbValue ab ++ "\n"

showSimpleAbValue :: AbValue -> String
showSimpleAbValue (AbValue cls clsa cntrs lit) =
  (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
  (if S.null cntrs then "" else " constrs: [" ++ intercalate "," (map showSimpleClosure (S.toList cntrs)) ++ "]") ++
  (if M.null lit then "" else " lits: " ++ show (M.toList lit))

showNoEnvAbValue :: AbValue -> String
showNoEnvAbValue (AbValue cls clsa cntrs lit) =
  (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
  (if S.null cntrs then "" else " constrs: [" ++ intercalate "," (map showNoEnvClosure (S.toList cntrs)) ++ "]") ++
  (if M.null lit then "" else " lits: " ++ show (map snd (M.toList lit)))

emptyAbValue :: AbValue
emptyAbValue = AbValue S.empty S.empty S.empty M.empty

injLit :: C.Lit -> EnvCtx -> AChange
injLit x env =
  case x of
    C.LitInt i -> (AChangeLit $ LiteralChangeInt $ LChangeSingle i) env
    C.LitFloat f -> (AChangeLit $ LiteralChangeFloat $ LChangeSingle f) env
    C.LitChar c -> (AChangeLit $ LiteralChangeChar $ LChangeSingle c) env
    C.LitString s -> (AChangeLit $ LiteralChangeString $ LChangeSingle s) env


addChange :: AbValue -> AChange -> (AChange, AbValue)
addChange ab@(AbValue cls clsapp cs lit) change =
  case change of
    AChangeClos lam env -> (change, AbValue (S.insert (lam,env) cls) clsapp cs lit)
    AChangeClosApp lam app env -> (change, AbValue cls (S.insert (lam,app,env) clsapp) cs lit)
    AChangeConstr c env -> (change, AbValue cls clsapp (S.insert (c,env) cs) lit)
    AChangeLit l env -> 
      case M.lookup env lit of
        Just litLattice ->
          let (change, newLattice) = joinLit l litLattice
          in (AChangeLit change env, AbValue cls clsapp cs (M.insert env newLattice lit) )
        Nothing ->
          let newLit = M.insert env (litLattice l) lit
          in (change, AbValue cls clsapp cs newLit)

litLattice :: LiteralChange -> LiteralLattice
litLattice lit =
  case lit of
    LiteralChangeInt ch -> LiteralLattice (snd $ ch `FM.insert` LBottom) LBottom LBottom LBottom
    LiteralChangeFloat ch -> LiteralLattice LBottom (snd $ ch `FM.insert` LBottom) LBottom LBottom
    LiteralChangeChar ch -> LiteralLattice LBottom LBottom (snd $ ch `FM.insert` LBottom) LBottom
    LiteralChangeString ch -> LiteralLattice LBottom LBottom LBottom (snd $ ch `FM.insert` LBottom)

joinLit :: LiteralChange -> LiteralLattice -> (LiteralChange, LiteralLattice)
joinLit (LiteralChangeInt ch) (LiteralLattice i2 f2 c2 s2) = 
    let (change, i) = (ch `FM.insert` i2)
    in (LiteralChangeInt change, LiteralLattice i f2 c2 s2)
joinLit (LiteralChangeFloat ch) (LiteralLattice i2 f2 c2 s2) =
    let (change, f) = (ch `FM.insert` f2)
    in (LiteralChangeFloat change, LiteralLattice i2 f c2 s2)
joinLit (LiteralChangeChar ch) (LiteralLattice i2 f2 c2 s2) =
    let (change, c) = (ch `FM.insert` c2)
    in (LiteralChangeChar change, LiteralLattice i2 f2 c s2)
joinLit (LiteralChangeString ch) (LiteralLattice i2 f2 c2 s2) =
    let (change, s) = (ch `FM.insert` s2)
    in (LiteralChangeString change, LiteralLattice i2 f2 c2 s)

joinLitLattice :: LiteralLattice -> LiteralLattice -> LiteralLattice
joinLitLattice (LiteralLattice i0 f0 c0 s0) (LiteralLattice i1 f1 c1 s1) =
  LiteralLattice (i0 `FM.joinSimple` i1) (f0 `FM.joinSimple` f1) (c0 `FM.joinSimple` c1) (s0 `FM.joinSimple` s1)


joinAbValue :: AbValue -> AbValue -> AbValue
joinAbValue (AbValue cls0 clsa0 cs0 lit0) (AbValue cls1 clsa1 cs1 lit1) = AbValue (S.union cls0 cls1) (S.union clsa0 clsa1) (S.union cs0 cs1) (M.unionWith joinLitLattice lit0 lit1)

-- Other static information

data PatBinding =
  BoundPatVar C.Pattern -- This is the PatVar variable it is bound to
  -- The variable is bound in the subpattern at the given index with the given constructor
  | BoundConIndex TName Int PatBinding
  | BoundPatIndex Int PatBinding deriving (Show)

data BindInfo =
  BoundLam ExprContext EnvCtx Int
  | BoundDef ExprContext EnvCtx Int -- Bound from the let binding, focused on the parent (descend to child i to evaluate)
  | BoundLetDef ExprContext EnvCtx Int -- Bound from the let binding, focused on the parent (descend to child i to evaluate) (already offset i + 1)
  | BoundCase ExprContext EnvCtx Int {- which match branch -} PatBinding
  | BoundModule ExprContext EnvCtx
  | BoundGlobal TName VarInfo
  | BoundError ExprContext deriving (Show)

-- BIND: The resulting context is not only a nested context focused on a lambda body It is also
-- can be focused on a Let Body or Recursive Let binding It can also be focused on a Recursive Top
-- Level Definition Body It can be bound to a different top level definition It can also be focused on a
-- branch of a match statement BIND requires searching the imported modules for both the name
-- and definition. As such a module import graph should be used. The value of the parameter in the
-- case of unknown definitions is simply the top of the type lattice for the type of the parameter in
-- question. - Additional note: Since Koka uses interface modules to avoid re-parsing user code, we
-- need to determine an appropriate tradeoff in precision and compilation. In particular, a full core
-- file might be an appropriate file to output in addition to the core interface. We only load the core
-- file with the full definitions on demand when we detect that it would increase precision?
bind :: ExprContext -> C.Expr -> EnvCtx -> BindInfo
bind ctx var@(C.Var tname vInfo) env =
  -- trace ("Variable binding " ++ show tname ++ ": " ++ showSimpleContext ctx) $ 
  case ctx of
    ModuleC _ mod _ ->
      if lookupDefGroups (coreProgDefs $ fromJust $ modCoreUnopt mod) tname then BoundModule ctx env
      else 
        -- trace ("External variable binding " ++ show tname ++ ": " ++ show vInfo) $
        BoundGlobal tname vInfo
    DefCRec _ ctx' i tn -> lookupName BoundDef tn ctx' ctx'
    DefCNonRec _ ctx' tn -> lookupName BoundDef [tn] ctx' ctx'
    DefCGroup _ ctx' tn _ -> lookupName BoundDef tn ctx' ctx -- Already the parent
    LamCBody _ ctx' names _  -> lookupNameNewCtx BoundLam names ctx'
    AppCLambda _ ctx' _ -> bind ctx' var env
    AppCParam _ ctx' _ _ -> bind ctx' var env
    LetCDefRec _ ctx' i tn -> lookupName1 BoundLetDef tn ctx' ctx'
    LetCDefNonRec _ ctx' tn -> lookupName1 BoundLetDef [tn] ctx' ctx'
    LetCDefGroup _ ctx' tn _ -> lookupName1 BoundLetDef tn ctx' ctx -- Already the parent
    LetCBody _ ctx' tn _ -> bind ctx' var env
    CaseCScrutinee _ ctx' _ -> bind ctx' var env
    CaseCBranch _ ctx' names i b -> caseBinding ctx' names i b
    ExprCBasic _ ctx' _ -> bind ctx' var env
  where
    caseBinding ctx' names i b =
      case find (\(p, i) -> tname `elem` bv p) (zip (branchPatterns b) [0..]) of
        Just (pat, index) -> BoundCase ctx env i (BoundPatIndex index (findPatBinding pat))
        Nothing -> bind ctx' var env
    findPatBinding :: C.Pattern -> PatBinding
    findPatBinding pat =
      case pat of
        C.PatVar tn sub -> if tn == tname then BoundPatVar pat else findPatBinding sub
        C.PatCon con fields _ _ _ _ _ _ ->
          case find (\(p, i) -> tname `elem` bv p) (zip fields [0..]) of
            Just (subPat, i) -> BoundConIndex con i (findPatBinding subPat)
        C.PatLit _ -> error "PatLit should not occur"
        C.PatWild -> error "PatWild should not occur"
    lookupNameNewCtx mk names ctx' =
      case elemIndex tname names
        of Just x -> mk ctx env x
           -- lambdas introduce a new binding context that relates to calls. Other binding expressions do not
           _ -> bind ctx' var (envtail env)
    lookupName mk names ctx' ctx =
      case elemIndex tname names
        of Just x -> mk ctx env x
           _ -> bind ctx' var env
    lookupName1 mk names ctx' ctx =
      case elemIndex tname names
        of Just x -> mk ctx env (x + 1)
           _ -> bind ctx' var env

data EnvCtx = EnvCtx Ctx EnvCtx
            | EnvTail Ctx
  deriving (Eq, Ord)

instance Show EnvCtx where
  show c = "<<" ++ showEnvCtx c ++ ">>"

showEnvCtx :: EnvCtx -> String
showEnvCtx (EnvCtx ctx tail) = show ctx ++ ":::" ++ showEnvCtx tail
showEnvCtx (EnvTail ctx) = show ctx

---------------- Environment Based Ctx -------------------
data Ctx =
  IndetCtx [TName]
  | BCallCtx !ExprContext !Ctx
  | TopCtx
  | CtxEnd
  deriving (Eq, Ord)

instance Show Ctx where
  show ctx =
    case ctx of
      IndetCtx tn -> "?(" ++ show tn ++ ")"
      BCallCtx ctx cc -> "call{" ++ showSimpleContext ctx ++ "," ++ show cc ++ "}"
      TopCtx -> "Top"
      CtxEnd -> "."

showSimpleCtx :: Ctx -> String
showSimpleCtx ctx =
  case ctx of
    IndetCtx tn -> show tn
    BCallCtx ctx cc -> "call{" ++ showSimpleContext ctx ++ ", " ++ showSimpleCtx cc ++ "}"
    TopCtx -> "Top"
    CtxEnd -> "."

indeterminateStaticCtx :: Int -> ExprContext -> EnvCtx
indeterminateStaticCtx m ctx =
  case ctx of
    ModuleC _ mod _ -> EnvTail TopCtx
    DefCRec _ ctx' _ _ -> EnvTail TopCtx
    DefCNonRec _ ctx' _ -> EnvTail TopCtx
    DefCGroup _ ctx' tn _ -> EnvTail TopCtx
    LamCBody _ ctx' tn _ ->
      let parent = indeterminateStaticCtx m ctx'
      in if m == 0 then EnvCtx CtxEnd parent else EnvCtx (IndetCtx tn) parent
    AppCLambda _ ctx' _ -> indeterminateStaticCtx m ctx'
    AppCParam _ ctx' _ _ -> indeterminateStaticCtx m ctx'
    LetCDefRec _ ctx' _ _ -> indeterminateStaticCtx m ctx'
    LetCDefNonRec _ ctx' _ -> indeterminateStaticCtx m ctx'
    LetCDefGroup _ ctx' _ _ -> indeterminateStaticCtx m ctx'
    LetCBody _ ctx' _ _ -> indeterminateStaticCtx m ctx'
    CaseCScrutinee _ ctx' _ -> indeterminateStaticCtx m ctx'
    CaseCBranch _ ctx' _ _ _ -> indeterminateStaticCtx m ctx'
    ExprCBasic _ ctx' _ -> indeterminateStaticCtx m ctx'

maybeModOfEnv :: EnvCtx -> Maybe ExprContext
maybeModOfEnv env = maybeModOfCtx $ envhead env

maybeModOfCtx :: Ctx -> Maybe ExprContext
maybeModOfCtx ctx =
  case ctx of
    BCallCtx ctx cc -> maybeModOfCtx cc -- Could also potentially use indeterminate contexts
    _ -> Nothing

envtail :: EnvCtx -> EnvCtx
envtail (EnvCtx cc tail) = tail
envtail (EnvTail x) = error "envtail on EnvTail"

envhead :: EnvCtx -> Ctx
envhead (EnvCtx cc tail) = cc
envhead (EnvTail cc) = cc

limitmenv :: EnvCtx -> Int -> EnvCtx
limitmenv (EnvCtx e tail) m =
  EnvCtx (limitm e m) (limitmenv tail m)
limitmenv (EnvTail e) m = EnvTail (limitm e m)

limitm :: Ctx -> Int -> Ctx
limitm ctx m =
  if m == 0 then
    case ctx of
      BCallCtx{} -> CtxEnd
      TopCtx -> TopCtx
      IndetCtx{} -> CtxEnd
      CtxEnd -> CtxEnd
  else
    case ctx of
      BCallCtx c e -> BCallCtx c (limitm e (m - 1))
      _ -> ctx

-- Environment Subsumption
-- If the first subsumes the second, then the first is more general than the second, and thus any value in the second should also be in the first
subsumes :: EnvCtx -> EnvCtx -> Bool
subsumes p1 p2 =
  case (p1, p2) of
    (EnvCtx ctx1 tail1, EnvCtx ctx2 tail2) -> ctx1 `subsumesCtx` ctx2 && tail1 `subsumes` tail2
    (EnvTail ctx1, EnvTail ctx2) -> ctx1 `subsumesCtx` ctx2
    _ -> False

subsumesCtx :: Ctx -> Ctx -> Bool
subsumesCtx c1 c2 =
  case (c1, c2) of
    (TopCtx, TopCtx) -> True
    (CtxEnd, CtxEnd) -> True
    (IndetCtx tn1, IndetCtx tn2) -> tn1 == tn2
    (BCallCtx id1 env1, BCallCtx id2 env2) -> id1 == id2 && env1 `subsumesCtx` env2
    (IndetCtx{}, BCallCtx{}) -> True
    (IndetCtx{}, TopCtx{}) -> True
    (CtxEnd, TopCtx{}) -> True
    (CtxEnd, BCallCtx{}) -> True
    (CtxEnd, IndetCtx{}) -> True
    _ -> False

refineCtx :: (EnvCtx, EnvCtx) -> EnvCtx -> EnvCtx
refineCtx (c1, c0) c =
  if c == c0 then c1 else
    case c of
      EnvCtx ctx tail -> EnvCtx ctx (refineCtx (c1, c0) tail)
      EnvTail ctx -> EnvTail ctx

isFullyDetermined :: EnvCtx -> Bool
isFullyDetermined env =
  case env of
    EnvCtx cc tail -> ccDetermined cc && isFullyDetermined tail
    EnvTail cc -> ccDetermined cc

ccDetermined :: Ctx -> Bool
ccDetermined ctx =
  case ctx of
    CtxEnd -> True
    IndetCtx{} -> False
    TopCtx -> True
    BCallCtx c rst -> ccDetermined rst