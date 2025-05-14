{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use newtype instead of data" #-}

module Core.FirstOrder.Core ( -- Data structures
) where
import Core.Core
import Common.Name
import Common.Range
import Common.Syntax
import Type.Type
import qualified Type.Pretty as Pretty
import Lib.PPrint
import Common.Unique
import Control.Monad (ap)
import Lib.Trace (trace)
import Common.Failure (failure)
import Common.NamePrim
import Syntax.Parse (visibility)
import Core.CoreVar (HasExpVar, fv)


-- An effectful function is compiled using the following template:
-- 0. The function is split into a list of labeled expressions denoting the join points (monadic calls)
-- 1. The function takes in arguments, + the resumption + the context
-- 2. On function entry, the resumption is checked
--    * If null resumption, we fall through to normal evaluation (fast path)
--    * Less likely: resumption is not null -> jump to jump table at the end of the function
-- 3. Jump table at the end restores (free) variables to local variables, then jumps to the appropriate label 
-- The resumption closure record needs to have dummy values for arguments that are not used in the function.
-- The ctx or res needs a field to store the value the resumption is called with.
-- Also resumptions are specially called by using the first n arguments in the closure record (where $n$ is the number of original arguments in that stack frame)

-- Example: (Assume f and g are monadic)
-- fun g (a, b) = 
--   val x = f(a, b)
--   val y = g(x + a)
--   y + x
--
-- Assumes all local variables have unique names (throughout the function), also assumes all inner functions are lifted to the top level (FunLift)
-- After an ANF transformation -- all arguments to calls & returns are in local variables, local variables are lifted to the top of the function
-- fun g (a, b) = 
--   var x
--   var tmp
--   x = f(a, b)
--   tmp = x + a
--   val y = g(tmp) -- variables after the last monadic binding do not need to be lifted to local variables
--   val res = y + x
--   res
-- 
-- Becomes (after this transformation & dup/drop insertion):
-- fun g(a, b, res, ctx) = 
--  var x = int/null
--  var y = int/null -- ideally uninitialized, but right now we are using DefVal
--  if kk_likely(res == null) then
--    x = f(a, b, res, ctx)
--    label f':
--    if returning() then
--      drop(b)
--      dup(x)
--      tmp = x + a
--      drops(x,a) (in addition function - inlined)
--      y = g(tmp, res, ctx)
--      label g':
--      if returning() then
--        drop(tmp)
--        val res = y + x
--        drops(x,y) (in addition function - inlined)
--        return res
--      else
--        ctx->res = g_G(&g, 2, int/null, int/null, x, tmp, ctx->res) // y is the resumption, int/null is a dummy version of a/b (no allocation, will never be used)
--        return int/null
--    else
--      ctx->res = g_F(&g, 2, a, b, ctx->res) // x is the resumption
--      return int/null
--  else
--    case res of
--      g_F(target, _, a', b', res') ->
--        x = target(a, b, res', ctx) -- No closure needed.
--        goto f'
--      g_G(target, _, _, _, x', tmp', res') ->
--        x = x'
--        y = target(tmp', res', ctx)
--        goto g'
-- 
-- With some analysis and optimization (recognizing that a & b are not used in g_G, and x & tmp could be stored in them - if the appropriate size)
-- Becomes:
-- fun g(a, b, res, ctx) = 
--  ...
--        return g_G(&g, 2, x, tmp, y) // y is the resumption, tmp
--  ...
--      g_G(_, _, tmp', _, res') ->
--        tmp = tmp'
--  ...
-- also we might be able to optimize f - since there is nothing before it in the function?
-- Also monadic tail calls are just directly returned (we don't need to do anything else in this function)
-- Actually we would need to adjust the parameters :( - unless they have the same number of parameters of the same size

-- In Javascript / direct WASM the control flow structure becomes:
-- Becomes (after this transformation & codegen):
-- fun g(a, b, res, ctx) = 
--  let x = null; -- ideally uninitialized, but right now we are using DefVal
--  let y = null; 
--  g': { // labels are all at the beginning of the function and delimit various scopes which we can jump to (forwards using break)
--    f': { start': { 
--      if (res == null) {
--        break start'; // f and start are the same in this case, but start' might be needed.
--      } else if (res.variant == 'f') {
--        x = res.func(...res.args, res.res, ctx);
--        break f';
--      } else if (res.variant == 'g') {
--        x = res.x;
--        y = res.func(...res.args, res.res, ctx);
--        break g';
--      } 
--    } // end start' 
--    x = f(a, b, res, ctx);
--    } // end f' 
--    if (returning()) then {
--      tmp = x + a;
--    } else {
--      ctx.res = {variant: 'f', func: g, args: [a, b], res: ctx.res}; // x is the resumption
--      return null;
--    }
--    y = g(tmp, res, ctx);
--  } // end g'
--  if (returning()) then {
--    val res = y + x;
--    return res;
--  } else {
--    ctx.res = {variant: 'g', func: g, x: x, args: [tmp], res: ctx.res}; // y is the resumption, int/null is a dummy version of a/b (no allocation, will never be used)
--    return null;
--  } 
-- This is a bit more complicated than C, also, it might pose problems with nested ifs - requiring multiple jumps.
-- If we have nested ifs we cannot jump inside the if. 
-- So if we have a case statement, we need to split the function at the call to the monadic function, and return the result of the subpiece.
-- This way we can just capture what's left to do in that function, and ignore the rest of this function.
-- This might pose problems with tail call optimization (into while loops) -- does that happen for JS anyways?
-- Also, it might be good to keep a copy for running functions under no control effects - and switch to the slow path at the introduction of a handler with a control effect. (Unfortunately exn is prevalent).
-- Knowing if we are under no control effects also might be tricky with named handlers?

-- Notes: 
-- The return value  with dummy value returned?
-- Parameters have to be boxed? (Otherwise how to we start calling the resumption?)
-- Still need to figure out where to pass the value given to the resumption

-- Struct information
-- Sizes: &g == intptr_t, size == int8_t, res == kk_box_t, args = function args
-- Additional free variables: (prior to monadic call) - including lifting parameters to variables prior to call
-- * Free variables can be stored in missing function arguments (if they are the same size and the function args are not in the free variables)
-- Ideally names of variants & corresponding labels use source locations of the join points.


-- Every value type should have a null/value (corresponding to a zero-initialized value), pointer types can reuse 0

-- We will want to optimize case expressions as much as we can


-- If the function is not effectful, we omit the resumption parameter, and the jump tables.

-- TODO: Optimize functions with no free variables


monTransform :: Pretty.Env -> CorePhase b ()
monTransform penv
  = liftCorePhaseUniq $ \uniq defs -> runMon penv uniq (monDefGroups defs)

{--------------------------------------------------------------------------
  transform definition groups
--------------------------------------------------------------------------}
monDefGroups :: DefGroups -> Mon DefGroups
monDefGroups monDefGroups
  = do defGroups <- mapM monDefGroup monDefGroups
       return (defGroups)

monDefGroup (DefRec defs)
  = do defs <- mapM monDef defs
       return (DefRec defs)

monDefGroup (DefNonRec def)
  = do def <- monDef def
       return (DefNonRec def)

{--------------------------------------------------------------------------
  transform a definition
--------------------------------------------------------------------------}
monDef :: Def -> Mon Def
monDef def
  = if not (isMonDef def)
     then return def
     else withCurrentDef def $
          do [expr] <- monExpr (defExpr def)
             return $ def{ defExpr = expr } -- TODO: Jump table

monExpr :: Expr -> Mon [Expr]
monExpr expr = 
  case expr of
    TypeApp e targs -> 
      do e':rst <- monExpr e
         return (TypeApp e' targs:rst)
    TypeLam tbars body -> 
      do e':rst <- monExpr body
         return $ TypeLam tbars e':rst
    Lam pars eff body -> 
      do bodyExprs <- monExpr body
         names <- mapM (\_ -> uniqueName "tgt") [0..length bodyExprs-1]
         expr <- makeCoreExpr names bodyExprs
         return [Lam pars eff (expr exprTrue)]
    Let defs body ->
      do defs' <- mapM monDefGroup defs
         bodyExpr:rst <- monExpr body
         return $ Let defs' bodyExpr : rst -- If the body of a def is complex (an application then we might need to re-arrange lets)
    -- Let, Case, and App
    _ -> return [expr] -- Lit, Lam, TypeLam, Var, Con

tnames :: TNames -> [(Name,Type)]
tnames tns
  = [(name,tp) | (TName name tp) <- tnamesList tns]

localFv :: HasExpVar a => a -> [(Name, Type)]
localFv expr
  = filter (not . isQualified . fst) (tnames (fv expr)) -- trick: only local names are not qualified

makeRepr :: [(Name, Type)] -> Mon ConRepr
makeRepr fvs = error "makeRepr: not implemented" -- TODO: implement

makeVariants :: [Expr] -> Mon DataInfo
makeVariants variants = error "makeVariants: not implemented"

makeHeader :: Expr -> Mon Expr
makeHeader expr = return expr -- Create ifn 0 goto jumptbl

makeCoreExpr :: [Name] -> [Expr] -> Mon (Expr -> Expr)
makeCoreExpr names exprs
  = case (names, exprs) of
      ([], []) -> return $ \e -> Label (newName "jumptbl") e
      (name:names , expr:exprs) -> do
        newName <- uniqueNameFrom name
        expr' <- makeCoreExpr names exprs
        return $ \e -> Label name (Let [DefNonRec (makeDef name expr)] (expr' e))
  where makeDef name expr =
           Def{defName = name, defType = typeOf expr, defExpr = expr, defVis = Public,
               defSort = DefVal, defInline = InlineAuto, defNameRange = rangeNull, defDoc = ""}

{--------------------------------------------------------------------------
  Check if expressions need monadic translation
--------------------------------------------------------------------------}

-- Some expressions always need mon translation
isAlwaysMon :: Expr -> Bool
isAlwaysMon expr
  = case expr of
      TypeApp e _ -> isAlwaysMon e
      Var v _     -> -- getName v == nameYieldOp ||
                     getName v == nameUnsafeTotal -- TODO: remove these special cases?
                     -- getName v == namePerform 0
      _ -> False

-- Some expressions never need mon translation
isNeverMon :: Expr -> Bool
isNeverMon expr
  = case expr of
      App eopen@(TypeApp (Var open _) [effFrom,effTo,tpFrom,tpTo]) [f] | getName open == nameEffectOpen
        -> isTypeTotal effFrom  -- TODO: more cases? generally handler free
      TypeApp e _ -> isNeverMon e
      Var v _     -> getName v == nameDeref -- canonicalName 1 nameDeref --TODO: remove special case?
      _ -> isTotal expr


-- Does this definition need any mon translation (sometimes deeper inside)
isMonDef :: Def -> Bool
isMonDef def
  = isMonType (defType def) || isMonExpr (defExpr def)

isMonExpr :: Expr -> Bool
isMonExpr expr
  = case expr of
      App (TypeApp (Var open _) [_, effTo]) [f] | getName open == nameEffectOpen
        -> isMonEffect effTo || isMonExpr f
      App f args
        -> any isMonExpr (f:args)
      Lam pars eff body
        -> or [isMonEffect eff, isMonExpr body]

      TypeApp (TypeLam tpars body) targs
        -> (any isMonType targs) || (isMonExpr body)
      TypeApp (Var tname info) targs
        -> any isMonType targs || isMonType (typeOf expr)

      TypeApp body targs
        -> any isMonType targs || isMonExpr body
      TypeLam tpars body
        -> isMonExpr body
      Let defs body
        -> any isMonDefGroup defs || isMonExpr body
      Case exprs bs
        -> any isMonExpr exprs || any isMonBranch bs
      _ -> isMonType (typeOf expr)

isMonDefGroup defGroup
  = case defGroup of
      DefRec defs -> any isMonDef defs
      DefNonRec def -> isMonDef def

isMonBranch (Branch pat guards)
  = any isMonGuard  guards

isMonGuard (Guard g e)
  = any isMonExpr [g,e]


{--------------------------------------------------------------------------
  Mon monad
--------------------------------------------------------------------------}
newtype Mon a = Mon (Env -> State -> Result a)

data Env = Env{ currentDef :: [Def],
                prettyEnv :: Pretty.Env }

data State = State{ uniq :: Int }

data Result a = Ok a State

instance MonadFail Mon where
  fail msg = error msg

runMon :: Pretty.Env -> Int -> Mon a -> (a,Int)
runMon penv u (Mon c)
  = case c (Env [] penv) (State u) of
      Ok x (State u') -> (x,u')

instance Functor Mon where
  fmap f (Mon c)  = Mon (\env st -> case c env st of
                                      Ok x st' -> Ok (f x) st')

instance Applicative Mon where
  pure x = Mon (\env st -> Ok x st)
  (<*>)  = ap

instance Monad Mon where
  -- return = pure
  (Mon c) >>= f = Mon (\env st -> case c env st of
                                    Ok x st' -> case f x of
                                                   Mon d -> d env st' )

instance HasUnique Mon where
  updateUnique f = Mon (\env st -> Ok (uniq st) st{ uniq = (f (uniq st)) })
  setUnique  i   = Mon (\env st -> Ok () st{ uniq = i} )

withEnv :: (Env -> Env) -> Mon a -> Mon a
withEnv f (Mon c)
  = Mon (\env st -> c (f env) st)

getEnv :: Mon Env
getEnv
  = Mon (\env st -> Ok env st)

updateSt :: (State -> State) -> Mon State
updateSt f
  = Mon (\env st -> Ok st (f st))

withCurrentDef :: Def -> Mon a -> Mon a
withCurrentDef def action
  = -- trace ("mon def: " ++ show (defName def)) $
    withEnv (\env -> env{currentDef = def:currentDef env}) $
    action

monTraceDoc :: (Pretty.Env -> Doc) -> Mon ()
monTraceDoc f
  = do env <- getEnv
       monTrace (show (f (prettyEnv env)))

monTrace :: String -> Mon ()
monTrace msg
  = do env <- getEnv
       trace ("mon: " ++ show (map defName (currentDef env)) ++ ": " ++ msg) $ return ()
