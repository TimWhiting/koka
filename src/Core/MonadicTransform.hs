-----------------------------------------------------------------------------
-- Copyright 2016-2025 Microsoft Research, Daan Leijen
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- Transform user-defined effects into monadic bindings.
-----------------------------------------------------------------------------
{-# LANGUAGE FlexibleInstances #-}

module Core.MonadicTransform
  ( monTransform
  ) where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Identity

import Lib.PPrint
import Common.Failure
import Common.Name
import Common.Range
import Common.Unique 
import Common.NamePrim( nameEffectOpen,
                        nameReturn, nameDeref, nameByref,
                        nameTrue, nameFalse, nameTpBool, nameUnsafeTotal,
                        nameBind
                      )
import Common.Error
import Common.Syntax

import Kind.Kind( kindStar, isKindEffect, kindFun, kindEffect,   kindHandled )
import Type.Type
import Type.Kind
import Type.TypeVar
import Type.Pretty hiding (Env)
import qualified Type.Pretty as Pretty
import Type.Assumption
import Type.Operations( freshTVar )
import Core.Core
import qualified Core.Core as Core
import Core.Pretty
import Core.CoreVar
import Debug.Trace (trace)

-- Entry point
monTransform :: Pretty.Env -> CorePhase b ()
monTransform penv =
  liftCorePhaseUniq $ \uniq defs -> runMon penv uniq (monDefGroups defs)

-- Environment and State
data Env = Env
  { currentDef :: [Def]
  , prettyEnv  :: Pretty.Env
  }

data St = St
  { uniq :: Int
  }

type Mon = ReaderT Env (State St)

instance HasUnique Mon where
  updateUnique f = do
    s <- get
    let u' = f (uniq s)
    put s { uniq = u' }
    return (uniq s)
  setUnique i = modify (\s -> s { uniq = i })

runMon :: Pretty.Env -> Int -> Mon a -> (a, Int)
runMon penv u m =
  let env = Env [] penv
      st  = St u
      (a, st') = runState (runReaderT m env) st
  in (a, uniq st')

withCurrentDef :: Def -> Mon a -> Mon a
withCurrentDef def = local (\env -> env { currentDef = def : currentDef env })

getPrettyEnv :: Mon Pretty.Env
getPrettyEnv = asks prettyEnv

monTraceDoc :: (Pretty.Env -> Doc) -> Mon ()
monTraceDoc f
  = do env <- getPrettyEnv
       monTrace (show (f env))

monTrace :: String -> Mon ()
monTrace msg
  = do env <- ask
       trace ("mon: " ++ show (map defName (currentDef env)) ++ ": " ++ msg) $ return ()


-- Example: refactored monDefGroups and monDefGroup
monDefGroups :: DefGroups -> Mon DefGroups
monDefGroups = mapM monDefGroup

monDefGroup :: DefGroup -> Mon DefGroup
monDefGroup (DefRec defs)    = DefRec <$> mapM (monDef True) defs
monDefGroup (DefNonRec def)  = DefNonRec <$> monDef False def

{--------------------------------------------------------------------------
  transform a definition
--------------------------------------------------------------------------}
monDef :: Bool -> Def -> Mon Def
monDef recursive def =
  if not (isMonDef def)
    then return def
    else withCurrentDef def $ do
      expr' <- monExpr' True (defExpr def)
      return def { defExpr = expr' id }

type Trans a = TransX a a
type TransX a b = (a -> b) -> b

monExpr :: Expr -> Mon (Trans Expr)
monExpr expr = monExpr' False expr

-- Refactored monExpr'
monExpr' :: Bool -> Expr -> Mon (Trans Expr)
monExpr' topLevel expr = case expr of
  -- optimized open binding
  -- note: we cannot just check for `isMonEffect effFrom` as the effFrom
  -- might be total but inside we may still need a monadic translation if `f`
  -- contains handlers itself for example.
  App (App eopen@(TypeApp (Var open _) [effFrom, effTo, _, _]) [f]) args
    | getName open == nameEffectOpen && not (isMonExpr f) -> do
        args' <- mapM monExpr args
        return $ \k -> applies args' (\argss -> k (App (App eopen [f]) argss))
  App (TypeApp (App eopen@(TypeApp (Var open _) [effFrom, effTo, _, _]) [f]) targs) args
    | getName open == nameEffectOpen && not (isMonExpr f) -> do
        args' <- mapM monExpr args
        return $ \k -> applies args' (\argss -> k (App (TypeApp (App eopen [f]) targs) argss))
  --  lift _open_ applications
  App eopen@(TypeApp (Var open _) [effFrom, effTo, _, _]) [f]
    | getName open == nameEffectOpen -> do
        f' <- monExpr f
        return $ \k -> f' (\ff -> k (App eopen [ff]))
  -- regular cases
  Lam args eff body -> do 
    -- monTraceDoc $ \env -> text "not effectful lambda:" <+> niceType env eff
    body' <- monExpr body
    return $ \k -> k (Lam args eff (body' id))
  App f args -> do
    f' <- monExpr f
    args' <- mapM monExpr args
    let ftp = typeOf f
    let (tvs, preds, rho) = splitPredType ftp
    feff <- case splitFunType rho of
                 Just (_, feff', _) -> return feff'
                 _ -> do
                    monTraceDoc $ \env -> text "Core.Monadic.App: illegal application:" <+> ppType env ftp
                    failure ("Core.Monadic.App: illegal application: " ++ show (ppType defaultEnv ftp))
    if (not (isMonType ftp || isAlwaysMon f)) || isNeverMon f
      then do monTraceDoc $ \env -> text "app non-mon: eff:" <+> pretty feff <+> text ", expr:" <+> prettyExpr env expr
              return $ \k -> f' (\ff -> applies args' (\argss -> k (App ff argss)))
      else do
        monTraceDoc $ \env -> text "app mon:" <+> prettyExpr env expr
        nameY <- uniqueName "y"
        let resTp = typeOf expr
            tnameY = TName nameY resTp
        return $ \k ->
          let contBody = k (Var tnameY InfoNone)
              cont = case contBody of
                      -- optimize (fun(y) { let x = y in .. })
                      Let [DefNonRec def@(Def{ defExpr = Var v _ })] body
                        | getName v == nameY
                        -> Lam [TName (defName def) (defType def)] feff body
                      -- TODO: optimize (fun (y) { lift(expr) } )?
                      body -> Lam [tnameY] feff body
          in f' (\ff -> applies args' (\argss -> appBind resTp feff (typeOf contBody) ff argss cont))
  Let defgs body -> monLetGroups defgs body
  Case exprs bs -> do
    exprs' <- monTrans monExpr exprs
    bs' <- mapM monBranch bs
    if not (any isMonBranch bs)
      then return $ \k -> exprs' (\xxs -> k (Case xxs bs'))
      else do
        nameC <- uniqueName "c"
        let resTp = typeOf expr
            tnameC = TName nameC resTp
        return $ \k ->
          let effTp = typeTotal
              contBody = k (Var tnameC InfoNone)
              cont = Lam [tnameC] effTp contBody
          in exprs' (\xss -> applyBind resTp effTp (typeOf contBody) (Case xss bs') cont)
  Var (TName name tp) info -> return (\k -> k (Var (TName name tp) info))
  -- type application and abstraction
  TypeLam tvars body -> do
    body' <- monExpr' topLevel body
    return $ \k -> body' (\xx -> k (TypeLam tvars xx))
  TypeApp body tps -> do
    body' <- monExpr' topLevel body
    return $ \k -> body' (\xx -> k (TypeApp xx tps))
  _ -> return (\k -> k expr) -- leave unchanged

-- Refactored monBranch and monGuard
monBranch :: Branch -> Mon Branch
monBranch (Branch pat guards) = do
  guards' <- mapM monGuard guards
  return $ Branch pat guards'

monGuard :: Guard -> Mon Guard
monGuard (Guard guard body) = do
  -- guard' <- monExpr guard  -- guards are total!
  body' <- monExpr body
  return $ Guard guard (body' id)
-- Refactored monLetGroups and monLetGroup
monLetGroups :: DefGroups -> Expr -> Mon (TransX Expr Expr)
monLetGroups [] body = monExpr body
monLetGroups (dg:dgs) body = do
  dg' <- monLetGroup dg
  expr' <- monLetGroups dgs body
  return $ \k -> dg' (\xdg -> Let xdg (expr' k))

monLetGroup :: DefGroup -> Mon (TransX [DefGroup] Expr)
monLetGroup (DefRec defs) = do
  ldefs <- monTrans (monLetDef True) defs
  return $ \k -> ldefs (\xss -> k (concat [[DefRec xds] | xds <- xss]))
monLetGroup (DefNonRec d) = do
  ldef <- monLetDef False d
  return $ \k -> ldef (\xds -> k (map DefNonRec xds))

monLetDef :: Bool -> Def -> Mon (TransX [Def] Expr)
monLetDef _ def = withCurrentDef def $ do
  expr' <- monExpr' True (defExpr def) -- don't increase depth
  return $ \k -> expr' (\xx -> k [def { defExpr = xx }])


monTrans :: (a -> Mon (TransX b c)) -> [a] -> Mon (TransX [b] c)
monTrans _ [] = return $ \k -> k []
monTrans f (x:xs) = do
  x' <- f x
  xs' <- monTrans f xs
  return $ \k -> x' (\y -> xs' (\ys -> k (y:ys)))

applies :: [Trans a] -> ([a] -> a) -> a
applies [] f = f []
applies (t:ts) f = t (\c -> applies ts (\cs -> f (c:cs)))

appBind :: Type -> Effect -> Type -> Expr -> [Expr] -> Expr -> Expr
appBind tpArg tpEff tpRes fun args cont =
  applyBind tpArg tpEff tpRes (App fun args) cont

applyBind :: Type -> Effect -> Type -> Expr -> Expr -> Expr
applyBind tpArg tpEff tpRes expr cont =
  case cont of
    Lam [aname] eff (Var v _) | getName v == getName aname -> expr
    _ -> monMakeBind tpArg tpEff tpRes expr cont

monMakeBind :: Type -> Effect -> Type -> Expr -> Expr -> Expr
monMakeBind tpArg tpEff tpRes arg next =
  App (TypeApp (Var (TName nameBind typeBind) info) [tpArg, tpRes, tpEff]) [arg, next]
  where
    info = Core.InfoArity 2 3

typeBind :: Type
typeBind =
  TForall [tvarA, tvarB, tvarE] []
    (TFun [(nameNil, typeYld (TVar tvarA)),
           (nameNil, TFun [(nameNil, TVar tvarA)] (TVar tvarE) (typeYld (TVar tvarB)))]
          (TVar tvarE) (typeYld (TVar tvarB)))

typeYld :: Type -> Type -- Yld<a> == a
typeYld tp = tp

tvarA, tvarB :: TypeVar
tvarA = TypeVar 0 kindStar Bound
tvarB = TypeVar 1 kindStar Bound
tvarE :: TypeVar
tvarE = TypeVar 2 kindEffect Bound

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
isMonDef def = isMonType (defType def) || isMonExpr (defExpr def)

isMonExpr :: Expr -> Bool
isMonExpr expr =
  case expr of
    App (TypeApp (Var open _) [_, effTo]) [f] | getName open == nameEffectOpen
      -> isMonEffect effTo || isMonExpr f
    App f args
      -> any isMonExpr (f:args)
    Lam _ eff body
      -> isMonEffect eff || isMonExpr body
    TypeApp (TypeLam _ body) targs
      -> any isMonType targs || isMonExpr body
    TypeApp (Var _ _) targs
      -> any isMonType targs || isMonType (typeOf expr)
    TypeApp body targs
      -> any isMonType targs || isMonExpr body
    TypeLam _ body
      -> isMonExpr body
    Let defs body
      -> any isMonDefGroup defs || isMonExpr body
    Case exprs bs
      -> any isMonExpr exprs || any isMonBranch bs
    _ -> isMonType (typeOf expr)

isMonDefGroup :: DefGroup -> Bool
isMonDefGroup (DefRec defs) = any isMonDef defs
isMonDefGroup (DefNonRec def) = isMonDef def

isMonBranch :: Branch -> Bool
isMonBranch (Branch _ guards) = any isMonGuard guards

isMonGuard :: Guard -> Bool
isMonGuard (Guard g e) = any isMonExpr [g, e]
