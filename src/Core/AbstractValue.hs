
module Core.AbstractValue(
                          Ctx(..),
                          EnvCtx(..),
                          ConstrContext(..),
                          AbValue(..),
                          AbstractLattice(..),
                          SimpleLattice(..),
                          EnvCtxLattice(..),
                          emptyAbValue,
                          injClosure,
                          injErr,
                          injLit,
                          joinAbValue,
                          joinL,
                          joinML,
                          addAbValue,
                          addLamSet,
                          subsumes,
                          subsumesCtx,
                          toSynLit,
                          toSynLitD,
                          toSynLitC,
                          toSynLitS,
                          bind,
                          indeterminateStaticCtx,
                          refine,
                          succm,
                          succmenv,
                          calibratemenv,
                          calibratemctx,
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
import Data.List (elemIndex)
import Compiler.Module
import Debug.Trace (trace)
import Common.Range
import Data.Maybe (fromMaybe)
import GHC.Base (mplus)

data AbstractLattice =
  AbBottom | AbTop

newtype EnvCtxLattice t = EnvCtxLattice (M.Map EnvCtx (Int, t))

newtype EnvCtx = EnvCtx [Ctx] deriving (Eq, Ord)

instance Show EnvCtx where
  show (EnvCtx ctxs) = show ctxs

data Ctx =
  IndetCtx
  | DegenCtx
  | CallCtx !ExprContext !EnvCtx
  | TopCtx
  deriving (Eq, Ord)

instance Show Ctx where
  show ctx =
    case ctx of
      IndetCtx -> "?"
      DegenCtx -> "[]"
      CallCtx id env -> "call(" ++ show id ++ "," ++ show env ++ ")"
      TopCtx -> "()"

data ConstrContext =
  ConstrContext{
    constrName:: !Name,
    constrType:: !Type,
    constrParams:: !AbValue
  } deriving (Eq, Ord, Show)

data SimpleLattice x =
  SimpleAbBottom
  | Simple !x
  | SimpleAbTop
  deriving (Eq, Ord, Show)

data AbValue =
  AbValue{
    closures:: !(Set (ExprContext, EnvCtx)),
    constrs:: !(Set ConstrContext),
    intV:: M.Map EnvCtx (SimpleLattice Integer),
    floatV:: M.Map EnvCtx (SimpleLattice Double),
    charV:: M.Map EnvCtx (SimpleLattice Char),
    stringV:: M.Map EnvCtx (SimpleLattice String),
    err:: Maybe String
  } deriving (Eq, Ord)

instance Show AbValue where
  show (AbValue cls cntrs i f c s e) =
    (if S.null cls then "" else "closures: " ++ show (S.toList cls)) ++
    (if S.null cntrs then "" else " constrs: " ++ show (S.toList cntrs)) ++
    (if M.null i then "" else " ints: " ++ show (M.toList i)) ++
    (if M.null f then "" else " floats: " ++ show (M.toList f)) ++
    (if M.null c then "" else " chars: " ++ show (M.toList c)) ++
    (if M.null s then "" else " strings: " ++ show (M.toList s)) ++
    maybe "" (" err: " ++) e

-- Basic creating of abstract values

emptyAbValue :: AbValue
emptyAbValue = AbValue S.empty S.empty M.empty M.empty M.empty M.empty Nothing
injClosure ctx env = emptyAbValue{closures= S.singleton (ctx, env)}
injErr err = emptyAbValue{err= Just err}

injLit :: C.Lit -> EnvCtx -> AbValue
injLit x env =
  case x of
    C.LitInt i -> emptyAbValue{intV= M.singleton env $ Simple i}
    C.LitFloat f -> emptyAbValue{floatV= M.singleton env $ Simple f}
    C.LitChar c -> emptyAbValue{charV= M.singleton env $ Simple c}
    C.LitString s -> emptyAbValue{stringV= M.singleton env $ Simple s}

--- JOINING
joinL :: Eq x => SimpleLattice x -> SimpleLattice x -> SimpleLattice x
joinL SimpleAbBottom x = x
joinL x SimpleAbBottom = x
joinL SimpleAbTop _ = SimpleAbTop
joinL _ SimpleAbTop = SimpleAbTop
joinL (Simple x) (Simple y) = if x == y then Simple x else SimpleAbTop

joinML :: Eq x => M.Map EnvCtx (SimpleLattice x) -> M.Map EnvCtx (SimpleLattice x) -> M.Map EnvCtx (SimpleLattice x)
joinML = M.unionWith joinL

joinAbValue :: AbValue -> AbValue -> AbValue
joinAbValue (AbValue cls0 cs0 i0 f0 c0 s0 e0) (AbValue cls1 cs1 i1 f1 c1 s1 e1) = AbValue (S.union cls0 cls1) (S.union cs0 cs1) (i0 `joinML` i1) (f0 `joinML` f1) (c0 `joinML` c1) (s0 `joinML` s1) (e0 `mplus` e1)

addAbValue :: EnvCtxLattice AbValue -> Int -> EnvCtx -> AbValue -> (Bool, EnvCtxLattice AbValue)
addAbValue (EnvCtxLattice m) version env ab =
  let (changed, newMap) = M.mapAccumWithKey (\acc k (v, ab') -> if k `subsumes` env then (ab' /= ab || acc, (version, ab' `joinAbValue` ab)) else (acc, (v, ab'))) False m in
  let oldV = snd (fromMaybe (version, emptyAbValue) (M.lookup env m)) in
  (changed || oldV /= ab, EnvCtxLattice $ M.insert env (version, oldV `joinAbValue` ab) newMap)

addLamSet :: EnvCtxLattice (Set (ExprContext, EnvCtx)) -> Int -> EnvCtx -> Set (ExprContext, EnvCtx) -> (Bool, EnvCtxLattice (Set (ExprContext, EnvCtx)))
addLamSet (EnvCtxLattice m) version env ab =
  let (changed, newMap) = M.mapAccumWithKey (\acc k (v, ab') -> if k `subsumes` env then (ab' /= ab || acc, (version, ab' `S.union` ab)) else (acc, (v, ab'))) False m in
  let oldV = snd (fromMaybe (version, S.empty) (M.lookup env m)) in
  (changed || oldV /= ab, EnvCtxLattice $ M.insert env (version, oldV `S.union` ab) newMap)

-- Environment Subsumption
-- If the first subsumes the second, then the first is more general than the second, and thus any value in the second should also be in the first
subsumes :: EnvCtx -> EnvCtx -> Bool
subsumes (EnvCtx ctxs1) (EnvCtx ctxs2) =
  and $ zipWith subsumesCtx ctxs1 ctxs2

subsumesCtx :: Ctx -> Ctx -> Bool
subsumesCtx c1 c2 =
  case (c1, c2) of
    (IndetCtx, IndetCtx) -> True
    (DegenCtx, DegenCtx) -> True
    (CallCtx id1 env1, CallCtx id2 env2) -> id1 == id2 && env1 `subsumes` env2
    (TopCtx, TopCtx) -> True
    (IndetCtx, CallCtx id env2) -> True
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
    LamCBody _ ctx' _ _ ->
      let (EnvCtx parent) = indeterminateStaticCtx ctx'
      in EnvCtx (IndetCtx:parent)
    AppCLambda _ ctx _ -> indeterminateStaticCtx ctx
    AppCParam _ ctx _ _ -> indeterminateStaticCtx ctx
    LetCDef _ ctx' _ _ _ -> indeterminateStaticCtx ctx'
    LetCBody _ ctx' _ _ -> indeterminateStaticCtx ctx'
    CaseCMatch _ ctx _ -> indeterminateStaticCtx ctx
    CaseCBranch _ ctx' _ _ _ -> indeterminateStaticCtx ctx'
    ExprCBasic _ ctx _ -> indeterminateStaticCtx ctx
    ExprCTerm{} -> error "Never should occur"

refine :: EnvCtx -> ([Ctx], [Ctx]) -> EnvCtx
refine env@(EnvCtx p) (c1, c0) =
  if p == c0 then EnvCtx c1 else env

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
    IndetCtx -> IndetCtx
    DegenCtx -> IndetCtx
    CallCtx c p' -> CallCtx c (calibratemenv (mlimit - 1) p')
    TopCtx -> TopCtx
