-----------------------------------------------------------------------------
-- Copyright 2012-2024, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-
    The update `x := e` of a local variable moves the value of `x` into `e`, so `e` may not read
    or write `x`. `e` can use the other local variables of the scope of `x` directly, and call
    functions that use them, but not call a function that may use `x`.

    A function that uses the local variables of a block is created in that block (the variables
    cannot escape it), so which of them a value may reach is found by a fixpoint over the Core of
    the block, with its binders made unique first so that each name is one binder: a lambda reaches what its free variables reach, a call returns what its function
    and arguments reach, a variable holds what is assigned to it anywhere in the block, and a
    parameter of a lambda in the block whose type mentions the heap of the block may reach any
    of its variables. Any call evaluated by `e` that may use `x` has its function or one of its
    arguments reach `x`, and its effect contains the local effect of the block.
-}
-----------------------------------------------------------------------------

module Type.UpdateReach ( UpdateSite(..), checkBlockUpdates ) where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Control.Monad( when, filterM )
import Control.Monad.State.Strict

import Lib.PPrint
import Common.Name
import Common.Range
import Common.NamePrim( nameLocalVar, nameLocalGet, nameLocalSet, nameLocalUpdate, nameByref, nameEffectOpen, nameRunLocal, nameTpLocal )
import Type.Type
import Type.TypeVar
import Core.Core
import Core.CoreVar( freeLocals )
import Core.Uniquefy( uniquefyExpr )

-- | An update `x := e`: the variable `x`, the range of the assignment, and its Core.
data UpdateSite = UpdateSite{ usVar :: Name, usRange :: Range, usCore :: Expr }

-- | Check the updates of a block, given the Core of the block (the argument of `local-scope`).
-- The types must be substituted. An update is found in the block by the evidence of its
-- `max-effects` constraint, whose name is unique.
checkBlockUpdates :: Expr -> [UpdateSite] -> [(Range,Doc)]
checkBlockUpdates block0 sites
  = case blockHeap of
      Nothing   -> []
      Just heap -> let env = Env heap (S.fromList (map fst own)) (S.fromList (cellsOf block))
                       r   = fixpoint env block
                   in concat [ evalState (checkUpdate env site upd) r
                             | site <- sites, Just ev <- [evidenceOf (usVar site) (usCore site)]
                             , Just upd <- [findUpdate ev block] ]
  where
    block     = uniquefyExpr block0
    own       = blockCells block
    blockHeap = case own of
                  ((_,tp):_) -> localVarHeap tp
                  []         -> Nothing


{--------------------------------------------------------------------------
  The variables of a block
--------------------------------------------------------------------------}

-- The heap of the block, its variables, and the variables of the block and the blocks nested in it.
data Env = Env{ envHeap :: Type, envAll :: S.Set Name, envCells :: S.Set Name }

children :: Expr -> [Expr]
children expr
  = case expr of
      Lam _ _ body  -> [body]
      TypeLam _ e   -> [e]
      TypeApp e _   -> [e]
      App f args    -> f : args
      Let dgs body  -> map defExpr (flattenDefGroups dgs) ++ [body]
      Case es bs    -> es ++ [e | b <- bs, Guard t g <- branchGuards b, e <- [t,g]]
      _             -> []

-- The parameter of a `local-var` function, with its initial value and scope.
localVar :: Expr -> Maybe (Name, Type, Expr, Expr)
localVar expr
  = case expr of
      App f [init, Lam [TName c tp] _ body] | primName f == Just nameLocalVar -> Just (c,tp,init,body)
      _ -> Nothing

-- The variables declared directly in the block (not in a nested block).
blockCells :: Expr -> [(Name,Type)]
blockCells expr
  = case localVar expr of
      Just (c,tp,init,body) -> (c,tp) : blockCells init ++ blockCells body
      Nothing -> case expr of
                   App f _ | primName f == Just nameRunLocal -> []
                   _ -> concatMap blockCells (children expr)

-- All variables declared in the block, including those of nested blocks.
cellsOf :: Expr -> [Name]
cellsOf expr
  = [c | Just (c,_,_,_) <- [localVar expr]] ++ concatMap cellsOf (children expr)

localVarHeap :: Type -> Maybe Type
localVarHeap tp
  = case expandSyn tp of
      TApp _ [h,_] -> Just h
      _            -> Nothing

mentionsHeap :: Env -> Type -> Bool
mentionsHeap env tp
  = case expandSyn (envHeap env) of
      TVar tv -> tvsMember tv (ftv tp)
      _       -> False

-- The name of a (primitive) function, through type applications and opens.
primName :: Expr -> Maybe Name
primName expr
  = case expr of
      Var tn _      -> Just (getName tn)
      TypeApp e _   -> primName e
      App (TypeApp (Var open _) _) [e] | getName open == nameEffectOpen -> primName e
      _             -> Nothing

-- A variable argument of a primitive, through `@byref`.
cellArg :: Expr -> Maybe Name
cellArg expr
  = case expr of
      Var tn _                   -> Just (getName tn)
      App f [e] | primName f == Just nameByref -> cellArg e
      TypeApp e _                -> cellArg e
      _                          -> Nothing

-- An update of a variable: the variable, the parameter of the update function, its body, and the
-- other arguments (the evidence).
localUpdate :: Expr -> Maybe (Name, Name, Expr, [Expr])
localUpdate expr
  = case expr of
      App f (cell : Lam [TName p _] _ body : rest) | primName f == Just nameLocalUpdate, Just c <- cellArg cell
        -> Just (c,p,body,rest)
      _ -> Nothing

-- The evidence name of the update of `x` in the Core of an assignment.
evidenceOf :: Name -> Expr -> Maybe Name
evidenceOf x expr
  = case localUpdate expr of
      Just (c,_,_,rest) | c == x, (ev:_) <- [getName tn | Var tn _ <- rest] -> Just ev
      _ -> firstJust (map (evidenceOf x) (children expr))

-- The update with the given evidence in the block.
findUpdate :: Name -> Expr -> Maybe (Name, Name, Expr)
findUpdate ev expr
  = case localUpdate expr of
      Just (c,p,body,rest) | ev `elem` [getName tn | Var tn _ <- rest] -> Just (c,p,body)
      _ -> firstJust (map (findUpdate ev) (children expr))

firstJust :: [Maybe a] -> Maybe a
firstJust xs = case [y | Just y <- xs] of
                 (y:_) -> Just y
                 []    -> Nothing


{--------------------------------------------------------------------------
  Fixpoint: the variables of the block a value may reach
--------------------------------------------------------------------------}

-- | For each binder (and, for a variable, its value), the variables of the block it may reach.
data Reach = Reach{ reachVal :: M.Map Name (S.Set Name), reachContent :: M.Map Name (S.Set Name) }
  deriving Eq

type R a = State Reach a

fixpoint :: Env -> Expr -> Reach
fixpoint env block
  = loop (Reach M.empty M.empty)
  where
    loop r = let r' = execState (reach env block) r
             in if r' == r then r else loop r'

joinVal :: Name -> S.Set Name -> R ()
joinVal name s
  = if S.null s then return ()
     else modify (\r -> r{ reachVal = M.insertWith S.union name s (reachVal r) })

joinContent :: Name -> S.Set Name -> R ()
joinContent name s
  = if S.null s then return ()
     else modify (\r -> r{ reachContent = M.insertWith S.union name s (reachContent r) })

contentOf :: Name -> R (S.Set Name)
contentOf name = gets (M.findWithDefault S.empty name . reachContent)

varReach :: Env -> Name -> R (S.Set Name)
varReach env name
  | name `S.member` envCells env = S.insert name <$> contentOf name
  | otherwise                    = gets (M.findWithDefault S.empty name . reachVal)

-- The variables an expression may reach, recording what it assigns. A value whose type does not
-- mention the heap of the block cannot hold one of its variables, or a function that uses them.
reach :: Env -> Expr -> R (S.Set Name)
reach env expr
  = do r <- reachExpr env expr
       return (if mentionsHeap env (typeOf expr) then r else S.empty)

reachExpr :: Env -> Expr -> R (S.Set Name)
reachExpr env expr
  | Just (c,_,init,body) <- localVar expr
    = do reach env init >>= joinContent c
         reach env body
  | Just (c,p,body,rest) <- localUpdate expr
    = do contentOf c >>= joinVal p
         reach env body >>= joinContent c
         mapM_ (reach env) rest
         return S.empty
  | otherwise
    = case expr of
      Var tn _      -> varReach env (getName tn)
      Con _ _       -> return S.empty
      Lit _         -> return S.empty
      TypeLam _ e   -> reach env e
      TypeApp e _   -> reach env e
      Lam pars _ body
        -> do mapM_ (\(TName p tp) -> when (mentionsHeap env tp) $ joinVal p (envAll env)) pars
              _ <- reach env body
              captured env expr
      Let dgs body
        -> do mapM_ (\def -> reach env (defExpr def) >>= joinVal (defName def)) (flattenDefGroups dgs)
              reach env body
      Case es bs
        -> do rs <- S.unions <$> mapM (reach env) es
              results <- mapM (\b -> do mapM_ (\v -> joinVal v rs) (concatMap patVars (branchPatterns b))
                                        S.unions <$> mapM (\(Guard t g) -> reach env t >> reach env g) (branchGuards b)) bs
              return (S.unions results)
      App f args
        -> case (primName f, args) of
             (Just name, (cell : _)) | name == nameLocalGet, Just c <- cellArg cell
               -> do mapM_ (reach env) (tail args)
                     contentOf c
             (Just name, [cell, val]) | name == nameLocalSet, Just c <- cellArg cell
               -> do reach env val >>= joinContent c
                     return S.empty
             _ -> do rf  <- reach env f
                     ras <- mapM (reach env) args
                     -- a call may store any argument in a mutable argument that can hold it
                     let rall = S.unions (rf:ras)
                     mapM_ (\a -> case a of
                                    Var (TName v tp) _ | mentionsHeap env tp && not (v `S.member` envCells env) -> joinVal v rall
                                    _ -> return ()) args
                     return rall
  where
    patVars pat
      = case pat of
          PatVar (TName v _) p -> v : patVars p
          PatCon{}             -> concatMap patVars (patConPatterns pat)
          _                    -> []

-- What a function value may reach: what its free variables reach.
captured :: Env -> Expr -> R (S.Set Name)
captured env lam
  = S.unions <$> mapM (\(TName v _) -> varReach env v) (tnamesList (freeLocals lam))


{--------------------------------------------------------------------------
  Check an update
--------------------------------------------------------------------------}

-- The calls evaluated by the right-hand side of the update of `c` (not the bodies of the lambdas in
-- it) that have the local effect of the block must not have a function or argument that reaches `c`.
checkUpdate :: Env -> UpdateSite -> (Name, Name, Expr) -> R [(Range,Doc)]
checkUpdate env site (c,p,body)
  = take 1 <$> calls body
  where
    calls expr
      = case expr of
          App f args   -> do errs <- callError f args
                             rest <- concat <$> mapM calls (f:args)
                             return (errs ++ rest)
          Lam{}        -> return []
          _            -> concat <$> mapM calls (children expr)

    callError f args
      | Just name <- primName f, name `elem` [nameLocalGet, nameLocalSet, nameByref]
        = return []  -- they use their variable directly and call nothing
      | not (usesLocal (typeOf f))
        = return []
      | otherwise
        = do let args' = case primName f of
                           Just name | name == nameLocalUpdate -> drop 1 args  -- the variable itself
                           _ -> args
             culprits <- filterM (\e -> (c `S.member`) <$> reach env e) (f:args')
             case culprits of
               []    -> return []
               (e:_) -> return [(usRange site, err e)]

    usesLocal tp
      = case splitFunType (stripForall tp) of
          Just (_,eff,_) -> any isLocalOfBlock (fst (extractOrderedEffect eff))
          Nothing        -> True

    isLocalOfBlock l
      = case expandSyn l of
          TApp (TCon tc) [h] -> typeConName tc == nameTpLocal && matchType h (envHeap env)
          _                  -> False

    stripForall tp
      = case expandSyn tp of
          TForall _ t -> t
          t           -> t

    xs = writtenName (usVar site)
    err e
      = let what = case peel e of
                     Var tn _ | getName tn == p -> text "the value of" <+> text xs <+> text "may hold a function that uses" <+> text xs
                     Var tn _ -> text (writtenName (getName tn)) <+> text "may be or hold a function that uses" <+> text xs
                     App f (cell:_) | primName f == Just nameLocalGet, Just v <- cellArg cell
                              -> text "the value of" <+> text (writtenName v) <+> text "may be or hold a function that uses" <+> text xs
                     e'       -> fun e'
            fun e' = case e' of
                       Lam{} -> text "this function may call a function that uses" <+> text xs
                       _     -> text "this call may call a function that uses" <+> text xs
            -- through type applications and opens
            peel e' = case e' of
                        TypeApp e2 _ -> peel e2
                        App (TypeApp (Var open _) _) [e2] | getName open == nameEffectOpen -> peel e2
                        _ -> e'
        in text "the right-hand side of" <+> text xs <+> text ":= ... may read or write" <+> text xs <+> text "while it is updated"
           <-> text " because:" <+> what
           <-> text " hint   :" <+> text ("use `" ++ xs ++ " ::= ...` to assign it")

-- The name as written, without the suffix that makes it unique in the block.
writtenName :: Name -> String
writtenName name
  = let s = show (unqualify name)
    in case break (=='@') (reverse s) of
         (ds,'@':rest) | not (null ds), all (`elem` ['0'..'9']) ds, not (null rest) -> reverse rest
         _ -> s
