module Core.MatchMerge(matchMergeDefs) where

import qualified Lib.Trace
import Control.Monad
import Control.Monad.Identity
import Control.Applicative
import Data.Maybe( catMaybes, isJust, maybeToList, isNothing, fromJust, fromMaybe )
import Lib.PPrint
import Common.Failure
import Common.NamePrim ( nameEffectOpen, namePatternMatchError )
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
import Data.List (intercalate)

trace s x =
  Lib.Trace.trace s
    x

matchMergeDefs :: CorePhase b ()
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
       return def{defExpr=e}

matchMergeExpr :: Expr -> Unique Expr
matchMergeExpr body
  = case body of
      Case exprs branches ->
        do
          (branches', changed) <- mergeBranches branches
          -- if changed then 
          --   trace ("matchMergeExpr:\n" ++ show (vcat (map (text . show) branches)) ++ "\nrewrote to: \n" ++ show (vcat (map (text . show) branches')) ++ "\n") (return ()) 
          -- else return ()
          return $ Case exprs branches'
      _ -> return body

isTrueGuard :: Guard -> Bool
isTrueGuard guard = isExprTrue (guardTest guard)

-- Takes a set of branches, and transforms them by merging branches that have some shared superstructure.
-- Returns the new branch structure and whether any changes were made
mergeBranches :: [Branch] -> Unique ([Branch], Bool)
-- No branches, no changes
mergeBranches [] = return ([], False)
-- Skip branches with complex guards (in the future we can optimize to merge guards)
mergeBranches (b@(Branch [pat@PatCon{patConPatterns=ps}] guard):bs) | not (all isTrueGuard guard) =
  mergeBranches bs >>= (\(bs', v) -> return (b:bs', v))
-- Branch with constructor pattern, try to merge it with the rest
mergeBranches branches@(b@(Branch [pat@PatCon{patConPatterns=ps}] _): rst) = 
  -- trace ("mergeBranches:\n" ++ show b ++ "\n\n" ++ show rst ++ "\n\n\n") $
  do
    splitted <- splitBranchConstructors b rst
    case splitted of
      -- Single branch, return itself unchanged
      ([b], [], err, any, tns, pat') -> return ([b], False)
      -- Single branch shares structure, rest do not, merge the rest and append
      ([b], rst, err, any, tns, pat') ->
        do
          (rest, v) <- mergeBranches rst
          return (b : rest, v)
      -- Multiple branches share structure
      (bs, rst, err, any, distinguishingVars, pat') ->
        do
          -- trace ("mergeBranches:\n" ++ " has error? " ++ show err ++ "\n" ++ intercalate "\n" (map (show . branchPatterns) bs) ++ "\n with common superstructure:\n" ++ show pat' ++ "\n\n") $ return ()
          let
            varsMatch = [Var tn InfoNone | tn <- distinguishingVars] -- Create expressions for those vars
          -- Get rid of the common superstructure from the branches that share superstructure
          -- Also add the implicit error branch if it exists
            subBranches = map (stripOuterConstructors distinguishingVars pat') bs ++ maybeToList any ++ maybeToList err
          (newSubBranches, innerV) <- mergeBranches subBranches 
          (rest, v) <- mergeBranches rst -- Merge the branches that do not share structure with the current set
          -- Replace the set of common branches, with a single branch that matches on the shared superstructure, and delegates
          -- to another case expression to distinguish between the different substructures
          return (Branch pat' [Guard exprTrue (Case varsMatch newSubBranches)] : rest, True)
-- Default (non-constructor patterns), just merge the rest, and add the first branch back
mergeBranches (b:bs) = mergeBranches bs >>= (\(bs', v) -> return (b:bs', v))
-- TODO: Add support for branches with multiple patterns

splitBranchConstructors :: Branch -> [Branch] -> Unique ([Branch], [Branch], Maybe Branch, Maybe Branch, [TName], [Pattern])
splitBranchConstructors b branches = do
  res <- splitBranchConstructors' b branches 
  case res of -- Add branch back to the front of the list
    (bs, no, err, any, tns, pat) -> return (b:bs, no, err, any, tns, pat)

-- Split branches into 
-- - a list of those that match
-- - those that are left
-- - a possible (implicit error) branch found 
-- - and the pattern that unifies the matched branches
-- Greedily in order processing, The first branch is the branch under consideration and the others are the next parameter
splitBranchConstructors' :: Branch -> [Branch] -> Unique ([Branch], [Branch], Maybe Branch, Maybe Branch, [TName], [Pattern])
splitBranchConstructors' b@(Branch ps _) branches =
  -- trace ("splitBranchConstructors:\n" ++ show b ++ "\n\n" ++ show (vcat (map (text . show) branches)) ++ "\n\n") $
  case branches of
    -- Only one branch, it matches it's own pattern
    [] -> return ([], [], if isErrorBranch b then Just b else Nothing, Nothing, [], ps) 
    b'@(Branch ps' _):bs ->
      do
        -- First do the rest other than b'
        (bs', bs2', err, matchAny, restTns, accP) <- splitBranchConstructors' b bs
        -- keep track of error branch to propagate into sub branches
        let newError = case (err, b') of
              (Just e, _) -> Just e -- implicit error is in the rest of the branches
              (_, b') | isErrorBranch b' -> Just b' -- b' is the error branch
              _ -> Nothing -- no error branch
        let newAny = case (matchAny, b') of
              (Just e, _) -> Just e
              (_, b') | isMatchAnyBranch b' -> Just b'
              _ -> Nothing -- no error branch
        -- Acumulated pattern and p'
        patNew <- zipWithM (\acc p -> patternsMatch restTns acc p) accP ps' 
        let (newVars, patNews) = unzip patNew
        if not $ isSimpleMatches patNews then
          -- Restrict the pattern to the smallest that matches multiple branches
          -- Add the new branch to the list of branches that match partially
          -- trace ("splitConstructors:\n" ++ show accP ++ "\nand\n" ++ show ps' ++ "\n have common superstructure:\n" ++ show patNew ++ "\nwith discriminating variables: " ++ show newVars ++ "\n") $
            return (b':bs', bs2', newError, newAny, concat newVars, patNews)
          -- Didn't match the current branch, keep the old pattern
          -- Add the new branch to the list of branches that don't match any subpattern
        else return (bs', b':bs2', newError, newAny, restTns, accP)

isPatWild :: Pattern -> Bool
isPatWild PatWild = True
isPatWild _ = False

isSimpleMatches :: [Pattern] -> Bool
isSimpleMatches = all isSimpleMatch

isSimpleMatch :: Pattern -> Bool
isSimpleMatch p =
  case p of
    PatVar _ p -> isSimpleMatch p
    PatWild -> True
    _ -> False

-- Checks to see if the branch is an error branch
isErrorBranch:: Branch -> Bool
isErrorBranch (Branch _ [Guard _ e]) = isErrorExpr e
isErrorBranch _ = False

isMatchAnyBranch:: Branch -> Bool
isMatchAnyBranch (Branch [pat] _) = isSimpleMatch pat
isMatchAnyBranch _ = False

isErrorExpr :: Expr -> Bool
isErrorExpr (TypeApp (Var name _) _) = 
  let nm = getName name in
  nm == namePatternMatchError 
isErrorExpr (App (App (TypeApp (Var name _) _) [e]) args) = 
  getName name == nameEffectOpen && isErrorExpr e  
isErrorExpr (App e args) = isErrorExpr e
isErrorExpr (TypeApp e args) = isErrorExpr e
isErrorExpr e =
  False

generalErrorBranch:: Branch -> Branch
generalErrorBranch b@(Branch p g) | isErrorBranch b = Branch [PatWild] g
generalErrorBranch b = b

-- Returns largest common pattern superstructure, with variables added where needed, and the distinguishing variables returned
patternsMatch :: [TName] -> Pattern -> Pattern -> Unique ([TName], Pattern)
patternsMatch distinguishingVars p p' = 
  let recur = patternsMatch distinguishingVars in
    -- trace ("Common superstructure of " ++ (show $ vcat [text $ show p, text $ show p'])) $
    case (p, p') of
    (PatLit l1, PatLit l2) -> 
      if l1 == l2 then return ([], p) -- Literals that match, just match the literal
      else do -- Match a variable of the literal's type
        name <- newVarName 
        let tn = TName name (typeOf l1)
        return ([tn], PatVar tn PatWild)
    (PatVar tn1 v1, PatVar tn2 v2) | tn1 == tn2 -> do 
      -- Same pattern variable, can't reuse the variable name - because it could be a name representing another location in another pattern
      name <- newVarName 
      (tns, sub) <- recur v1 v2
      let tn' = TName name (typeOf tn1)
      let distinguished = tn1 `elem` distinguishingVars
      return (tns ++ if distinguished then [tn'] else [], PatVar tn' sub)
    (PatVar tn1 v1, PatVar tn2 v2) -> do
      -- Variables that don't match name, but (should match types because of type checking)
      -- Create a common name to match for
      name <- newVarName 
      (tns, sub) <- recur v1 v2
      let distinguished = tn1 `elem` distinguishingVars
      let tn' = TName name (typeOf tn1)
      return (tns ++ if distinguished then [tn'] else [], PatVar tn' sub)
    (PatWild, PatWild) -> return ([], PatWild) -- Wilds match trivially
    (PatCon name1 patterns1 cr targs1 exists1 res1 ci sk, PatCon name2 patterns2 _ targs2 exists2 res2 _ _) -> 
      if -- Same constructor (name, and types) -- types should match due to type checking, but names could differ
        name1 == name2 &&
        targs1 == targs2 &&
        exists1 == exists2 &&
        res1 == res2
      then do 
        -- Same constructor, match substructure
        res <- zipWithM recur patterns1 patterns2
        let (subs, pats) = unzip res
        return (concat subs, PatCon name1 pats cr targs1 exists1 res1 ci sk)
      else do
        name <- newVarName
        let tn = TName name res1
        return ([tn], PatVar tn PatWild) -- Different constructors, no match
    (PatVar tn PatWild, PatWild) -> do
      return ([], PatVar tn PatWild)
    (PatWild, PatVar tn PatWild) -> do
      return ([], PatVar tn PatWild)
    (PatVar tn PatWild, _) -> do
      return ([tn], PatVar tn PatWild)
    (_, PatVar tn PatWild) -> do
      return ([tn], PatVar tn PatWild)
    (PatVar tn pat, _) -> do
      (tns, sub) <- recur pat p'
      return (tns, PatVar tn sub)
    (_, PatVar tn pat) -> do
      (tns, sub) <- recur p pat
      return (tns, PatVar tn sub)
    -- Double sided wilds already handled so we can safely request the type, as well as one sided vars
    (_, PatWild) -> do
      name <- newVarName
      let tn = TName name (patternType p)
      return ([tn], PatVar tn PatWild)
    (PatWild, _) -> do
      name <- newVarName
      let tn = TName name (patternType p')
      return ([tn], PatVar tn PatWild)
    (_, _) -> failure $ "patternsMatch: " ++ show p ++ " " ++ show p' ++ " "
    where newVarName = uniqueId "case" >>= (\id -> return $ newHiddenName ("case" ++ show id))

patternType :: Pattern -> Type
patternType p = case p of
  PatLit l -> typeOf l
  PatVar tn _ -> typeOf tn
  PatCon tn _ _ targs _ resTp _ _ -> resTp

-- Strip the outer constructors and propagate variable substitution into branch expressions
stripOuterConstructors :: [TName] -> [Pattern] -> Branch -> Branch
stripOuterConstructors discriminatingVars templates (Branch pts exprs) = 
  -- trace ("Using template\n" ++ show templates ++"\n" ++ show pts ++ "\ngot:\n" ++ show discriminatingVars ++ "\n" ++ show patNew ++ "\n\n" ++ show (vcat (map (text . show) (zip discriminatingVars patNew))) ++ "\nWith variable name mapping:\n" ++ show replaceMap ++ "\n") $ 
    assertion "Invalid subpattern match " (length patNew == length discriminatingVars) $
    Branch patNew $ map replaceInGuard exprs
  where
    replaceInGuard (Guard tst expr)
      = Guard (rewriteBottomUp replaceInExpr tst) (rewriteBottomUp replaceInExpr expr)
    replaceInExpr :: Expr -> Expr
    replaceInExpr e
      = case e of
          Var name _ -> case lookup name replaceMap of
            Just (Var name info) -> Var name info
            _ -> e
          e' -> e'
    (patsNew, replaceMaps) = unzip $ zipWith (getReplaceMap discriminatingVars) templates pts
    patNew = concat patsNew
    replaceMap = concat replaceMaps

getReplaceMap :: [TName] -> Pattern -> Pattern -> ([Pattern], [(TName, Expr)])
getReplaceMap discriminatingVars template p' = 
  case getReplaceMap' discriminatingVars template p' of
    (Just pats, replacers) -> (pats, replacers)
    (Nothing, replacers) -> error "Should never happen"

-- Get the new pattern that differs from the old pattern and the subsitution map
getReplaceMap' :: [TName] -> Pattern -> Pattern -> (Maybe [Pattern], [(TName, Expr)])
getReplaceMap' discriminatingVars template p'
  = let recur = getReplaceMap' discriminatingVars in
    case (template, p') of
    (PatLit l1, PatLit l2) -> (Nothing, [])
    (PatVar tn1 v1, PatVar tn2 v2) | tn1 == tn2 -> 
      let (pat', rp) = recur v1 v2 
      in case pat' of
        Nothing -> if tn1 `notElem` discriminatingVars then (Nothing, rp) else (Just [PatWild], rp)
        Just _ -> (pat', rp)
    (PatVar tn1 v1, PatVar tn2 v2) -> 
      let (pat', rp) = recur v1 v2
          -- introduce a new variable using the template's name, and map the other name to the template
          rp' = (tn2, Var tn1 InfoNone):rp in
      -- trace (show pat' ++ show (tn1 `elem` discriminatingVars) ++ show tn1) $
      case pat' of 
        Nothing -> -- 
          -- Differs but doesn't discriminate
          if tn1 `notElem` discriminatingVars then (Nothing, rp') 
          else (Just [PatWild], rp') 
        Just _ -> -- Use the new pattern
          (pat', rp')
    (PatWild, PatWild) -> (Nothing, [])
    (PatCon name1 patterns1 cr targs1 exists1 res1 ci _, PatCon name2 patterns2 _ targs2 exists2 res2 _ sk) -> 
      let res = zipWith recur patterns1 patterns2 
          (patterns', replaceMaps) = unzip res
          replaceMap = concat replaceMaps in 
      -- trace ("Subpats " ++ show (vcat (map (text . show) patterns')) ++ " " ++ show (length (concatMap (fromMaybe []) patterns'))) $
      (Just (concatMap (fromMaybe []) patterns'), replaceMap)
    (PatVar tn PatWild, PatWild) -> 
      (if tn `notElem` discriminatingVars then Nothing else Just [PatWild], [])
    (PatVar tn PatWild, pat2) -> 
      -- trace ("Here " ++ show discriminatingVars) $
       (if tn `notElem` discriminatingVars then Nothing else Just [pat2], [])
    (PatVar tn pat, pat2) -> recur pat pat2
    (PatWild, pat2) -> (Just [pat2], [])
    -- (PatCon _ _ _ _ _ _ _ _, PatWild) -> (Just [template], [])
    _ -> failure $ "\ngetReplaceMap:\n" ++ show template ++ "\n:" ++ show p' ++ "\n" 
