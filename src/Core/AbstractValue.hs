-----------------------------------------------------------------------------
-- Copyright 2012-2023, Microsoft Research, Daan Leijen. Brigham Young University, Tim Whiting.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
module Core.AbstractValue(
                          Ctx(..),
                          EnvCtx(..),
                          ConstrContext(..),
                          AbValue(..),
                          AbstractLattice(..),
                          SimpleLattice(..),
                          EnvCtxLattice(..),
                          Joinable(..),
                          showSimpleClosure, showSimpleCtx, showSimpleEnv,
                          emptyAbValue,
                          injClosure,injErr,injLit,injCon,injClosures,
                          joinAbValue,joinL,joinML,
                          addJoin,
                          subsumes,subsumesCtx,
                          toSynLit,toSynLitD,toSynLitC,toSynLitS,
                          topTypesOf,
                          bind,
                          indeterminateStaticCtx,
                          refine,
                          succm,succmenv,
                          calibratemenv,calibratemctx,
                          envtail,
                        ) where
import Data.Map.Strict as M hiding (map)
import Core.StaticContext
import Common.Name
import Type.Type
import Data.Set hiding (map, map)
import Data.Set as S hiding (map)
import Core.Core as C
import Syntax.Syntax as S
import Data.List (elemIndex, intercalate)
import Compiler.Module
import Debug.Trace (trace)
import Common.Range
import Data.Maybe (fromMaybe, catMaybes)
import GHC.Base (mplus)
import Common.Failure (assertion)

data AbstractLattice =
  AbBottom | AbTop

newtype EnvCtxLattice t = EnvCtxLattice (M.Map EnvCtx (Int, t))

newtype EnvCtx = EnvCtx [Ctx] deriving (Eq, Ord)

instance Show EnvCtx where
  show (EnvCtx ctxs) = show ctxs

data Ctx =
  IndetCtx [TName] ExprContext
  | DegenCtx
  | CallCtx !ExprContext !EnvCtx
  | TopCtx
  deriving (Eq, Ord)

instance Show Ctx where
  show ctx =
    case ctx of
      IndetCtx tn c -> "?(" ++ show tn ++ ")"
      DegenCtx -> "[]"
      CallCtx ctx env -> "call(" ++ showExpr (exprOfCtx ctx) ++ "," ++ show env ++ ")"
      TopCtx -> "()"

data ConstrContext =
  ConstrContext{
    constrName:: !TName,
    constrType:: !Name,
    constrParams:: ![ExprContext]
  } deriving (Eq, Ord, Show)

data SimpleLattice x =
  SimpleAbBottom
  | Simple !x
  | SimpleAbTop
  deriving (Eq, Ord, Show)

data AbValue =
  AbValue{
    closures:: !(Set (ExprContext, EnvCtx)),
    constrs:: M.Map EnvCtx (Set ConstrContext),
    intV:: M.Map EnvCtx (SimpleLattice Integer),
    floatV:: M.Map EnvCtx (SimpleLattice Double),
    charV:: M.Map EnvCtx (SimpleLattice Char),
    stringV:: M.Map EnvCtx (SimpleLattice String),
    err:: Maybe String
  } deriving (Eq, Ord)


class Joinable t where
  join :: t -> t -> t
  bottom :: t

instance Joinable AbValue where
  join = joinAbValue
  bottom = emptyAbValue

instance Ord a => Joinable [a] where
  join l1 l2 = S.toList $ S.union (S.fromList l1) (S.fromList l2) 
  bottom = []

instance Show AbValue where
  show (AbValue cls cntrs i f c s e) =
    (if S.null cls then "" else "closures: " ++ show (map showSimpleClosure (S.toList cls))) ++
    (if M.null cntrs then "" else " constrs: " ++ show (M.toList cntrs)) ++
    (if M.null i then "" else " ints: " ++ show (M.toList i)) ++
    (if M.null f then "" else " floats: " ++ show (M.toList f)) ++
    (if M.null c then "" else " chars: " ++ show (M.toList c)) ++
    (if M.null s then "" else " strings: " ++ show (M.toList s)) ++
    maybe "" (" err: " ++) e

-- Basic creating of abstract values
showSimpleClosure :: (ExprContext, EnvCtx) -> String
showSimpleClosure (ctx, env) = showSimpleContext ctx ++ " in " ++ showSimpleEnv env

showSimpleEnv :: EnvCtx -> String
showSimpleEnv (EnvCtx ctxs) = 
  "<" ++ intercalate "," (map showSimpleCtx ctxs) ++ ">"

showSimpleCtx :: Ctx -> String
showSimpleCtx ctx =
  case ctx of
    IndetCtx tn c -> show tn
    DegenCtx -> "-"
    CallCtx ctx env -> "call(" ++ showSimpleContext ctx ++ ", " ++ showSimpleEnv env ++ ")"
    TopCtx -> "()"

emptyAbValue :: AbValue
emptyAbValue = AbValue S.empty M.empty M.empty M.empty M.empty M.empty Nothing
injClosure ctx env = emptyAbValue{closures= S.singleton (ctx, env)}
injClosures cls = emptyAbValue{closures= S.fromList cls}
injErr err = emptyAbValue{err= Just err}

injLit :: C.Lit -> EnvCtx -> AbValue
injLit x env =
  case x of
    C.LitInt i -> emptyAbValue{intV= M.singleton env $ Simple i}
    C.LitFloat f -> emptyAbValue{floatV= M.singleton env $ Simple f}
    C.LitChar c -> emptyAbValue{charV= M.singleton env $ Simple c}
    C.LitString s -> emptyAbValue{stringV= M.singleton env $ Simple s}

injCon :: TName -> Name -> [ExprContext] -> EnvCtx -> AbValue
injCon nm tp args env =
  emptyAbValue{constrs=M.singleton env $ S.singleton $ ConstrContext nm tp args}

--- JOINING
joinL :: Eq x => SimpleLattice x -> SimpleLattice x -> SimpleLattice x
joinL SimpleAbBottom x = x
joinL x SimpleAbBottom = x
joinL SimpleAbTop _ = SimpleAbTop
joinL _ SimpleAbTop = SimpleAbTop
joinL (Simple x) (Simple y) = if x == y then Simple x else SimpleAbTop

joinML :: Eq x => M.Map EnvCtx (SimpleLattice x) -> M.Map EnvCtx (SimpleLattice x) -> M.Map EnvCtx (SimpleLattice x)
joinML = M.unionWith joinL

joinMC :: Map EnvCtx (Set ConstrContext) -> Map EnvCtx (Set ConstrContext) -> Map EnvCtx (Set ConstrContext)
joinMC = M.unionWith S.union

joinAbValue :: AbValue -> AbValue -> AbValue
joinAbValue (AbValue cls0 cs0 i0 f0 c0 s0 e0) (AbValue cls1 cs1 i1 f1 c1 s1 e1) = AbValue (S.union cls0 cls1) (cs0 `joinMC` cs1) (i0 `joinML` i1) (f0 `joinML` f1) (c0 `joinML` c1) (s0 `joinML` s1) (e0 `mplus` e1)

addJoin :: Eq a => Joinable a => EnvCtxLattice a -> Int -> EnvCtx -> a -> (Bool, S.Set EnvCtx, EnvCtxLattice a)
addJoin (EnvCtxLattice m) version env ab =
  let ((changed, newAb, s), newMap) = M.mapAccumWithKey (\(changed, newAb, s) k (v, ab') ->
        if k `subsumes` env then -- i.e. env refines k -- add to the more general value
          -- TODO: Problem -- updating the version doesn't actually guarantee that the query is rerun for this more general context
          -- Adding something to a more specific context, so we need to update the more general context (assuming it exists)
          if ab' `join` ab == ab' then
            ((changed, newAb, s), (v, ab' `join` ab))
          else
            ((ab' /= ab || changed, newAb, S.insert k s), (version, ab' `join` ab))
        else if env `subsumes` k then -- i.e. k refines env -- include it in our new value
          let newV = newAb `join` ab' in
          -- Adding to a more general context, so we need to keep track of any more specific contexts that should be incorporated into the general value
          -- But not changing the more specific context
          ((newAb /= newV || changed, newV, s), (v, ab'))
        else ((changed, newAb, s), (v, ab'))) (False, ab, S.empty) m in
  let oldV = snd (fromMaybe (version, bottom) (M.lookup env m)) in
  if oldV `join` newAb == oldV then
    (changed || oldV /= newAb, s, EnvCtxLattice newMap)
  else
    (changed || oldV /= newAb, s, EnvCtxLattice $ M.insert env (version, oldV `join` newAb) newMap)

-- Environment Subsumption
-- If the first subsumes the second, then the first is more general than the second, and thus any value in the second should also be in the first
subsumes :: EnvCtx -> EnvCtx -> Bool
subsumes (EnvCtx ctxs1) (EnvCtx ctxs2) =
  and $ zipWith subsumesCtx ctxs1 ctxs2

subsumesCtx :: Ctx -> Ctx -> Bool
subsumesCtx c1 c2 =
  case (c1, c2) of
    (DegenCtx, DegenCtx) -> True
    (TopCtx, TopCtx) -> True
    (IndetCtx tn1 c1, IndetCtx tn2 c2) -> tn1 == tn2 && c1 == c2
    (CallCtx id1 env1, CallCtx id2 env2) -> id1 == id2 && env1 `subsumes` env2
    (IndetCtx{}, CallCtx{}) -> True
    _ -> False

-- Converting to user visible expressions
toSynLit :: SimpleLattice Integer -> Maybe S.Lit
toSynLit (Simple i) = Just $ S.LitInt i rangeNull
toSynLit _ = Nothing

toSynLitD :: SimpleLattice Double -> Maybe S.Lit
toSynLitD (Simple i) = Just $ S.LitFloat i rangeNull
toSynLitD _ = Nothing

toSynLitC :: SimpleLattice Char -> Maybe S.Lit
toSynLitC (Simple i) = Just $ S.LitChar i rangeNull
toSynLitC _ = Nothing

toSynLitS :: SimpleLattice String -> Maybe S.Lit
toSynLitS (Simple i) = Just $ S.LitString i rangeNull
toSynLitS _ = Nothing

maybeTopI :: SimpleLattice Integer -> Maybe Type
maybeTopI SimpleAbTop = Just typeInt
maybeTopI _ = Nothing

maybeTopD :: SimpleLattice Double -> Maybe Type
maybeTopD SimpleAbTop = Just typeFloat
maybeTopD _ = Nothing

maybeTopC :: SimpleLattice Char -> Maybe Type
maybeTopC SimpleAbTop = Just typeChar
maybeTopC _ = Nothing

maybeTopS :: SimpleLattice String -> Maybe Type
maybeTopS SimpleAbTop = Just typeString
maybeTopS _ = Nothing

topTypesOf :: AbValue -> Set Type
topTypesOf ab =
  S.fromList $ catMaybes (map maybeTopI (M.elems (intV ab)) ++ map maybeTopD (M.elems (floatV ab)) ++ map maybeTopC (M.elems (charV ab)) ++ map maybeTopS (M.elems (stringV ab)))


-- Other static information

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
bind :: ExprContext -> C.Expr -> EnvCtx -> Maybe ((ExprContext, EnvCtx), Maybe Int)
bind ctx var@(C.Var tname vInfo) env =
  case ctx of
    ModuleC _ mod _ -> if lookupDefGroups (coreProgDefs $ modCoreNoOpt mod) tname then Just ((ctx, env), Nothing) else trace ("External variable binding " ++ show tname ++ ": " ++ show vInfo) Nothing
    DefCRec _ ctx' names i d -> lookupName names ctx'
    DefCNonRec _ ctx' names d -> lookupName names ctx'
    LamCBody _ ctx' names _  -> lookupNameNewCtx names ctx'
    AppCLambda _ ctx _ -> bind ctx var env
    AppCParam _ ctx _ _ -> bind ctx var env
    LetCDef _ ctx' names i _ -> lookupName names ctx'
    LetCBody _ ctx' names _ -> lookupName names ctx'
    CaseCMatch _ ctx _ -> bind ctx var env
    CaseCBranch _ ctx' names _ b -> lookupName names ctx'
    ExprCBasic _ ctx _ -> bind ctx var env
    ExprCTerm{} -> Nothing
  where
    lookupNameNewCtx names ctx' =
      case elemIndex tname names
        of Just x -> Just ((ctx, env), Just x)
           _ -> bind ctx' var (envtail env) -- lambdas introduce a new binding context that relates to calls. Other binding expressions do not
    lookupName names ctx' =
      case elemIndex tname names
        of Just x -> Just ((ctx, env), Just x)
           _ -> bind ctx' var env

indeterminateStaticCtx :: ExprContext -> EnvCtx
indeterminateStaticCtx ctx =
  case ctx of
    ModuleC _ mod _ -> EnvCtx [TopCtx]
    DefCRec _ ctx' _ _ _ -> indeterminateStaticCtx ctx'
    DefCNonRec _ ctx' _ _ -> indeterminateStaticCtx ctx'
    LamCBody _ ctx' tn _ ->
      let (EnvCtx parent) = indeterminateStaticCtx ctx'
      in EnvCtx (IndetCtx tn ctx:parent)
    AppCLambda _ ctx _ -> indeterminateStaticCtx ctx
    AppCParam _ ctx _ _ -> indeterminateStaticCtx ctx
    LetCDef _ ctx' _ _ _ -> indeterminateStaticCtx ctx'
    LetCBody _ ctx' _ _ -> indeterminateStaticCtx ctx'
    CaseCMatch _ ctx _ -> indeterminateStaticCtx ctx
    CaseCBranch _ ctx' _ _ _ -> indeterminateStaticCtx ctx'
    ExprCBasic _ ctx _ -> indeterminateStaticCtx ctx
    ExprCTerm{} -> error "Never should occur"

refine :: (Ctx, Ctx) -> EnvCtx -> EnvCtx
refine (c1, c0) env@(EnvCtx p)  =
  EnvCtx (map (refineCtx (c1, c0)) p)

refineCtx ::(Ctx, Ctx) -> Ctx -> Ctx
refineCtx (c1, c0) c =
  if c == c0 then c1 else
    case c of
      CallCtx c' e -> CallCtx c' (refine (c1, c0) e)
      _ -> c

succm :: Ctx -> Int -> Ctx
succm envctx m =
  if m == 0 then if envctx == TopCtx then TopCtx else DegenCtx
  else
    case envctx of
      CallCtx c e -> CallCtx c (succmenv e (m - 1))
      _ -> envctx

succmenv :: EnvCtx -> Int -> EnvCtx
succmenv (EnvCtx e) m =
  EnvCtx (map (\x -> succm x m) e)

calibratemenv :: Int -> EnvCtx -> EnvCtx
calibratemenv mlimit (EnvCtx ps) = do
  EnvCtx $! map (calibratemctx mlimit) ps

envtail :: EnvCtx -> EnvCtx
envtail (EnvCtx (c:p)) = EnvCtx p
envtail (EnvCtx []) = EnvCtx []

calibratemctx :: Int -> Ctx -> Ctx
calibratemctx mlimit p =
  if mlimit == 0 then DegenCtx
  else case p of
    IndetCtx tn c -> IndetCtx tn c
    DegenCtx -> let id = (ExprContextId (-1) (newName "_err")) in IndetCtx [] (ExprCTerm id "Err") -- TODO: Fix this?
    CallCtx c p' -> CallCtx c (calibratemenv (mlimit - 1) p')
    TopCtx -> TopCtx
