module Core.MatchMerge(matchMergeDefs) where

import qualified Lib.Trace
import Control.Monad
import Control.Monad.Identity
import Control.Applicative
import Data.Maybe( catMaybes )
import Lib.PPrint
import Common.Failure
import Common.NamePrim ( nameEffectOpen )
import Common.Name
import Common.Range
import Common.Unique
import Common.Error
import Common.Syntax

import Kind.Kind
import Type.Type
import Type.Kind
import Type.TypeVar
import Type.Pretty hiding (Env)
import qualified Type.Pretty as Pretty
import Type.Assumption
import Core.Core
import qualified Core.Core as Core
import Core.Pretty
import Core.CoreVar
import Core.Uniquefy
import Data.Tree.Lens (branches)

trace s x =
  Lib.Trace.trace s
    x

matchMergeDefs :: CorePhase ()
matchMergeDefs
  = liftCorePhaseUniq $ \uniq defs ->
    runUnique uniq $ matchMergeDefGroups defs

{--------------------------------------------------------------------------
  transform definition groups
--------------------------------------------------------------------------}
matchMergeDefGroups :: DefGroups -> Unique DefGroups
matchMergeDefGroups
  = mapM matchMergeDefGroup

matchMergeDefGroup :: DefGroup -> Unique DefGroup
matchMergeDefGroup (DefRec dgs)
  = do ndgs <- mapM matchMergeRecDef dgs
       return $ DefRec ndgs 
matchMergeDefGroup (DefNonRec def)
 = do ndef <- matchMergeRecDef def
      return $ DefNonRec ndef 

matchMergeRecDef :: Def -> Unique Def
matchMergeRecDef def
  = do e <- rewriteBottomUpM matchMergeExpr $ defExpr def
       trace ("matchMergeRecDef: " ++ show (defName def) ++ "\n" ++ show (defExpr def) ++ "\n rewrote to: \n" ++ show e) $
        return def{defExpr=e}

matchMergeExpr :: Expr -> Unique Expr
matchMergeExpr body
  = case body of
      Case exprs branches -> 
        do
          branches' <- mergeBranches branches
          return $ Case exprs branches'
      _ -> return body

mergeBranches :: [Branch] -> Unique [Branch]
mergeBranches [] = return []
mergeBranches branches@(b@(Branch [pat@PatCon{patConPatterns=ps}] _): rst)
  = case splitBranchConstructors b rst of
      ([b], []) -> return [b]
      ([b], rst) -> 
        do
          rest <- mergeBranches rst 
          return $ b:rest
      (bs, rst) -> 
        do
          names <- mapM (\x -> uniqueId "case" >>= (\id -> return $ newHiddenName ("case" ++ show id))) [0..length ps-1]
          let
            patterns = zipWith (\i p -> if isPatLit p then p else PatVar (TName (names !! i) (patTypeArgs pat !! i)) PatWild) [0..length ps-1] ps
            vars = zipWith (\i p -> Var (TName (names !! i) (patTypeArgs pat !! i)) InfoNone) [0..length ps-1] ps
            varsMatch = concat (zipWith (\i p -> if isPatLit p then [] else [Var (TName (names !! i) (patTypeArgs pat !! i)) InfoNone]) [0..length ps-1] ps)
          rest <- mergeBranches rst
          return $ Branch [pat{patConPatterns = patterns}]
            [Guard exprTrue (Case varsMatch $ map (stripOuterConstructors vars pat) bs)] : rest
mergeBranches (b:bs) = mergeBranches bs >>= (\bs' -> return $ b:bs')

splitBranchConstructors :: Branch -> [Branch] -> ([Branch], [Branch])
splitBranchConstructors b@(Branch [p] _) branches =
  case branches of
    [] -> ([b], [])
    b'@(Branch [p'] _):bs ->
      let (bs', bs2') = splitBranchConstructors b bs in
        if patternsMatch p p' then (b':bs', bs2') else (bs', b':bs2')

patternsMatch :: Pattern -> Pattern -> Bool
patternsMatch p p'
  = case (p, p') of
    (PatLit l1, PatLit l2) -> l1 == l2
    (PatVar _ v1, PatVar _ v2) -> patternsMatch v1 v2
    (PatWild, PatWild) -> True
    (PatCon name1 patterns1 _ targs1 exists1 res1 _ _, PatCon name2 patterns2 _ targs2 exists2 res2 _ _) ->
      name1 == name2 &&
      any (\(p1,p2) -> patternsMatch p1 p2) (zip patterns1 patterns2) &&
      targs1 == targs2 &&
      exists1 == exists2 &&
      res1 == res2
    (_, _) -> False

isPatLit :: Pattern -> Bool
isPatLit (PatLit _) = True
isPatLit _ = False

stripOuterConstructors :: [Expr] -> Pattern -> Branch -> Branch
stripOuterConstructors vars pat (Branch [PatCon{patConPatterns=ps}] exprs)
  = Branch (map replaceInPattern ps) $ map replaceInGuard exprs
  where
    replaceInPattern p
      = case p of
          PatVar name _ -> case lookup name replaceMap of
            Just (Var name info) -> PatVar name PatWild
            _ -> p
          PatCon{patConPatterns = ps'} -> p{patConPatterns = map replaceInPattern ps'}
          _ -> p
    replaceInGuard (Guard tst expr)
      = Guard (rewriteTopDown replaceInExpr tst) (rewriteTopDown replaceInExpr expr)
    replaceInExpr :: Expr -> Expr
    replaceInExpr e
      = case e of
          Var name _ -> case lookup name replaceMap of
            Just (Var name info) -> Var name info
            _ -> e
          e' -> e'
    replaceMap = zip (map (\p -> case p of {PatVar n _ -> n; _ -> TName (newName "__NOT_FOR_REPLACING__ ") typeAny}) ps) vars
