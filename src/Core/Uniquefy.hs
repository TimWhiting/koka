-----------------------------------------------------------------------------
-- Copyright 2012-2021, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-    Make local variables unique
-}
-----------------------------------------------------------------------------

module Core.Uniquefy ( uniquefy
                     , uniquefyDefGroup {- used for divergence analysis -}
                     , uniquefyExpr, uniquefyExprWith, uniquefyExprU
                     , uniquefyDefGroups {- used in inline -}
                     ) where

import Control.Monad
import Control.Applicative
import Common.Name
import qualified Common.NameSet as S
import qualified Common.NameMap as M
import Core.Core
import Core.CoreVar( freeLocals )
import Common.Failure
import Common.Unique

type Locals = S.NameSet
type Renaming = M.NameMap Name

data Un a  = Un (State -> (a,State))
data State = St{ locals :: Locals, renaming :: Renaming, uniq :: Int }

instance Functor Un where
  fmap f (Un u)  = Un (\st -> case u st of
                                (x,st1) -> (f x,st1))

instance Applicative Un where
  pure x  = Un (\st -> (x,st))
  (<*>) = ap

instance Monad Un where
  -- return = pure
  (Un u) >>= f  = Un (\st0 -> case u st0 of (x,st1) -> case f x of Un u1 -> u1 st1)

instance HasUnique Un where
  updateUnique f
    = do st' <- updateSt (\st -> st{ uniq = f (uniq st)})
         return (uniq st')


updateSt f
  = Un (\st -> (st,f st))

getSt = updateSt id
setSt st  = updateSt (const st)

fullLocalized u
  = do locals <- getLocals
       x <- localized u
       setLocals locals
       return x

localized u
  = do ren <- getRenaming
       x <- u
       setRenaming ren
       return x

getLocals = fmap locals getSt
getRenaming = fmap renaming getSt
setLocals l = updateSt (\st -> st{ locals = l })
setRenaming r = updateSt (\st -> st{ renaming = r })

makeFullUnique
  = do st <- getSt
       return (uniq st /= 0)

runUn uniq (Un u)
  = fst (u (St S.empty M.empty uniq))

uniquefyExpr :: Expr -> Expr
uniquefyExpr expr
  = uniquefyExprWith tnamesEmpty expr

uniquefyExprWith :: TNames -> Expr -> Expr
uniquefyExprWith free expr
  = let locals = S.map getName (free `tnamesUnion` (freeLocals expr))
    in runUn 0 $
       do setLocals locals
          uniquefyExprX expr

uniquefyExprU :: HasUnique m => Expr -> m Expr
uniquefyExprU expr
  = withUnique $ \uniq0 ->
    runUn uniq0 $
    do expr' <- uniquefyExprX expr
       uniq1 <- unique
       return (expr',uniq1)


uniquefy :: Core -> Core
uniquefy core
  = core{coreProgDefs = uniquefyDefGroups (coreProgDefs core) }

uniquefyDefGroups :: [DefGroup] -> [DefGroup]
uniquefyDefGroups dgs
  = runUn 0 $
    do locals <- getLocals
       let toplevelDefs = filter (not . nameIsNil) (map defName (flattenDefGroups dgs))
       setLocals (foldr (\name locs -> S.insert (unqualify name) locs) locals toplevelDefs)
       mapM (fullLocalized . uniquefyDG) dgs
  where
    uniquefyDG (DefNonRec def)
      = fmap DefNonRec $
        do expr <- uniquefyExprX (defExpr def)
           return def{ defExpr = expr }
    uniquefyDG (DefRec defs)
      = fmap DefRec $
        do exprs <- mapM (uniquefyExprX . defExpr) defs
           return [def{ defExpr = expr } | (def,expr) <- zip defs exprs]


uniquefyDefGroup :: DefGroup -> DefGroup
uniquefyDefGroup defgroup
  = runUn 0 $
    case defgroup of
      DefNonRec def
        -> fmap DefNonRec $ uniquefyDef def
      DefRec defs
        -> fmap DefRec $
           do locals <- getLocals
              setLocals (foldr (\name locs -> S.insert name locs) locals (filter (not . nameIsNil) (map defName defs)))
              exprs <- localized $ mapM (uniquefyExprX . defExpr) defs
              return [def{ defExpr = expr } | (def,expr) <- zip defs exprs]



uniquefyInnerDefGroup :: DefGroup -> Un DefGroup
uniquefyInnerDefGroup dg
  = case dg of
      DefNonRec def
        -> fmap DefNonRec $ uniquefyDef def
      DefRec defs
        -> fmap DefRec $ uniquefyRecDefs defs

uniquefyRecDefs :: [Def] -> Un [Def]
uniquefyRecDefs defs
  = do names <- mapM (uniquefyName . defName) defs
       exprs <- localized $ mapM (uniquefyExprX . defExpr) defs
       return [def{ defExpr = expr, defName = name } | (def,(name,expr)) <- zip defs (zip names exprs)]

uniquefyDef :: Def -> Un Def
uniquefyDef def
  = do expr1 <- localized $ uniquefyExprX (defExpr def)
       name1 <- uniquefyName (defName def)  -- works because we can't have overloaded recursive identifiers in an inner scope
       return (def{ defName = name1, defExpr = expr1 })

uniquefyExprX :: Expr -> Un Expr
uniquefyExprX expr
  = case expr of
      Lam tnames eff expr-> localized $
                            do tnames1 <- mapM uniquefyTName tnames
                               expr1   <- uniquefyExprX expr
                               return (Lam tnames1 eff expr1)
      Var tname info    -> do renaming <- getRenaming
                              case M.lookup (getName tname) renaming of
                                Just name -> return $ Var (TName name (typeOf tname) (originalRange tname)) info
                                Nothing   -> return expr
      App f args rng       -> do  f1 <- uniquefyExprX f
                                  args1 <- mapM uniquefyExprX args
                                  return (App f1 args1 rng)
      TypeLam tvs expr  -> do expr1 <- uniquefyExprX expr
                              return (TypeLam tvs expr1)
      TypeApp expr tps  -> do expr1 <- uniquefyExprX expr
                              return (TypeApp expr1 tps)
      Con tname repr    -> return expr
      Lit lit           -> return expr
      Let defGroups expr  -> do defGroups1 <- mapM uniquefyInnerDefGroup defGroups
                                expr1 <- uniquefyExprX expr
                                return (Let defGroups1 expr1)
      Case exprs branches
        -> do exprs1 <- mapM uniquefyExprX exprs
              branches1 <- localized $ mapM (localized . uniquefyBranch (map typeOf exprs)) branches
              return (Case exprs1 branches1 )


uniquefyBranch patTps (Branch patterns guardExprs)
  = do patterns1   <- mapM uniquefyPattern (zip patterns patTps)
       guardExprs1 <- mapM uniquefyGuard guardExprs
       return (Branch patterns1 guardExprs1)

uniquefyGuard (Guard test expr)
  = do t <- uniquefyExprX test
       e <- uniquefyExprX expr
       return (Guard t e)

uniquefyPattern (pattern, patTp)
  = case pattern of
      PatVar tname pat -> do tname' <- uniquefyTName tname
                             pat'   <- uniquefyPatternX pat patTp
                             return (PatVar tname' pat')
      _ -> do -- insert PatVar
              name <- uniquefyName (newHiddenName "pat")
              pat  <- uniquefyPatternX pattern patTp
              return (PatVar (TName name patTp Nothing) pat)


uniquefyPatternX pattern patTp
  = case pattern of
     PatWild  -> return pattern
     PatLit _ -> return pattern
     PatCon { patConPatterns = patterns, patTypeArgs = patTps }
        -> do patterns1 <- mapM uniquefyPattern (zip patterns patTps)
              return pattern{ patConPatterns = patterns1 }
     PatVar tname pat
        -> do tname' <- uniquefyTName tname
              pat' <- uniquefyPatternX pat patTp
              return (PatVar tname' pat')
     -- _  -> failure "Core.Uniquefy.UniquefyPatternX: unexpected case"

uniquefyTName :: TName -> Un TName
uniquefyTName tname
  = do name1 <- uniquefyName (getName tname)
       return (TName name1 (typeOf tname) Nothing)

uniquefyName :: Name -> Un Name
uniquefyName name | nameIsNil name
  = return name
uniquefyName name
  = do locals <- getLocals
       full <- makeFullUnique
       if (full || S.member name locals)
        then do renaming <- getRenaming
                name1 <- if full
                           then uniqueNameFrom name
                           else return (findUniqueName 0 name locals)
                let locals1 = S.insert name1 locals
                    renaming1 = M.insert name name1 renaming
                setLocals locals1
                setRenaming renaming1
                return name1
        else do setLocals (S.insert name locals)
                return name

findUniqueName i name locals
  = let name1 = toUniqueName i name -- qualify (qualifier name) (newName (nameId name ++ show i))
    in if (S.member name1 locals)
        then findUniqueName (i+1) name locals
        else name1
