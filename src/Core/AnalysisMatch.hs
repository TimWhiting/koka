-----------------------------------------------------------------------------
-- Copyright 2020-2021, Microsoft Research, Daan Leijen
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
{-    Analyze partiality of core match statements
-}
-----------------------------------------------------------------------------

module Core.AnalysisMatch( analyzeBranches ) where


import Lib.Trace
import Lib.PPrint
import Data.List (nub)
import Common.Name
import Common.Range
import Kind.Newtypes
import Type.Type
import Type.Pretty
import Type.TypeVar
import Type.Unify( runUnifyEx, unify )
import Core.Core
import Core.Pretty
import Data.Maybe (listToMaybe, isNothing, isJust)
import Control.Applicative ((<|>))

analyzeBranches :: Newtypes -> Name -> Range -> [Branch] -> [Type] -> [DataInfo] -> Bool -> (Bool,[(Range,Doc)],[Branch])
analyzeBranches = analyzeBranches'

-- ---------------------------------------------------------------------------
-- Coverage analysis
-- ---------------------------------------------------------------------------
--
-- Builds a decision tree to detect exhaustive and redundant pattern matches.
-- Each level inspects exactly one constructor position; the alphabet at each
-- level is the constructor set of the type at that position.  Unlike a trie,
-- the alphabet changes at every level.
--
-- The tree is purely internal: the flat [Branch] list is returned to the
-- caller unchanged, except that PatCon nodes have their 'skip' flag set when
-- all sibling constructors are already fully covered before this branch.
--
-- Key invariant — complement node (Maybe WildId on CovBranch):
--   A wildcard over a closed type does NOT expand eagerly into one ConBranch
--   per constructor.  Instead, the CovBranch carries a WildId complement,
--   meaning "every constructor NOT in the explicit ConBranch list is covered
--   with implicit sub-coverage CovDone."  Constructors are pulled out of the
--   complement lazily in unionCoverage, only when a later explicit PatCon
--   forces it.  This avoids O(N) blowup for types with many constructors.

-- | Source range of the original wildcard pattern that established a complement.
type WildId = Range

-- | Coverage of a sequence of pattern positions (fields).
data Coverage
  = CovDone                                        -- ^ End of field sequence; fully covered.
  | CovBranch [ConInfo] [ConBranch] (Maybe WildId) -- ^ Constructor choice at the current field.
                                                   --   [ConInfo] = ALL known constructors.
                                                   --   [ConBranch] = explicitly-matched constructors.
                                                   --   Maybe WildId = complement: every constructor
                                                   --   NOT in [ConBranch] is covered by this wildcard,
                                                   --   with implicit sub-coverage CovDone.  Lazy: we
                                                   --   only pull a constructor out of the complement
                                                   --   when a later explicit PatCon forces it.
  | CovOpen (Maybe WildId) Coverage               -- ^ Open/primitive type: no constructor check;
                                                   --   continue with the next field.
  | CovNone                                        -- ^ Nothing covered (identity for unionCoverage).
  deriving (Show)

-- | One arm of a constructor branch in the coverage decision tree.
data ConBranch = ConBranch
  { cbCon    :: ConInfo  -- ^ The constructor matched at this level.
  , cbParams :: Coverage -- ^ Coverage of cbCon's own sub-fields (not sibling fields).
  } deriving (Show)

-- | Is a Coverage fully exhaustive?
isCovComplete :: Coverage -> Bool
isCovComplete CovDone                          = True
isCovComplete (CovOpen _ cov)                  = isCovComplete cov
-- With a complement, all constructors not in [ConBranch] are implicitly CovDone;
-- only the explicit ones need to be individually complete.
isCovComplete (CovBranch _ childs (Just _))    = all (isCovComplete . cbParams) childs
isCovComplete (CovBranch infos childs Nothing)
  = length infos == length childs && all (isCovComplete . cbParams) childs
isCovComplete _                                = False

instance Pretty Coverage where
  pretty cov = case cov of
    CovNone                -> text "none"
    CovDone                -> text "done"
    CovOpen mw next        -> text "open" <+> maybe empty (const (text "(+wild)")) mw <+> pretty next
    CovBranch infos cbs mw ->
      text "branch" <+> list (map (pretty . conInfoName) infos)
        <+> maybe empty (const (text "(+wild)")) mw <->
      indent 2 (vcat [ pretty (conInfoName (cbCon cb)) <.> colon <+> pretty (cbParams cb)
                     | cb <- cbs ])

type Warnings = [(Range,Doc)]

dataInfoGetConInfos :: Bool -> DataInfo -> [ConInfo]
dataInfoGetConInfos isLazyMatch info
  = -- trace ("data info for: " ++ show (dataInfoName info) ++ ": " ++ show info)$
    if (dataInfoIsOpen info || dataInfoIsLiteral info)
     then []
    else if (not isLazyMatch) && dataInfoIsLazy info
     then filter (not . conInfoIsLazy) (dataInfoConstrs info)  -- only consider whnf constructors (as it is forced)
     else dataInfoConstrs info



analyzeGuards :: Range -> [Guard] -> Warnings
analyzeGuards range (Guard test expr : guards)  | isExprTrue test && not (null guards)
  = [(range, text "Some guards in the branches will never be reached")]
analyzeGuards range (Guard test expr : guards)  | isExprFalse test
  = [(range, text "Some guard condition in the branches is never true")] ++ analyzeGuards range guards
analyzeGuards range (g:gs) = analyzeGuards range gs
analyzeGuards range []     = []

lookupDataInfo :: Newtypes -> Name -> Maybe DataInfo
lookupDataInfo newtypes tpname
  = newtypesLookupAny tpname newtypes

lookupConInfos :: Newtypes -> Type -> [ConInfo]
lookupConInfos newtypes tp
  = case expandSyn tp of
      TCon tcon -> case lookupDataInfo newtypes (typeconName tcon) of
                     Just di -> dataInfoGetConInfos False di    -- [] for open or literals
                     Nothing -> [] -- trace ("Core.AnalysisMatch.lookupConInfos: not found: " ++ show (typeconName tcon)) $ []
      TApp t targs -> lookupConInfos newtypes t -- list<a>
      _         -> [] -- trace ("Core.AnalysisMatch.lookupConInfos: not a tcon: " ++ show (pretty t)) $ []

-- ---------------------------------------------------------------------------
-- Entry point and branch processing
-- ---------------------------------------------------------------------------

-- | Top-level entry point.
-- Asserts exactly one scrutinee, then processes branches in source order,
-- accumulating coverage and emitting warnings for redundant branches.
analyzeBranches' :: Newtypes -> Name -> Range -> [Branch] -> [Type] -> [DataInfo] -> Bool -> (Bool,[(Range,Doc)],[Branch])
analyzeBranches' newtypes defName range branches types dataInfos isLazyMatch
  = case types of
      [tp] ->
        let initCov = case dataInfos of
                        [info] | not (dataInfoIsLiteral info || dataInfoIsOpen info)
                               -> CovBranch (dataInfoGetConInfos isLazyMatch info) [] Nothing
                        (_:_:_) -> error ("Internal error: multiple data infos for match analysis on " ++ show defName)
                        _       -> CovNone
            (finalCov, branches', warnings) =
              foldl (\(acc,bs,ws) branch ->
                       let (branch', rowCov, warnings1) = matchRowBranch newtypes defName range acc [tp] branch
                       in (unionCoverage acc rowCov, branch':bs, warnings1 ++ ws))
                    (initCov, [], [])
                    branches
            exhaustive = isCovComplete finalCov
            -- TODO: append makeDefaultErrorBranch when not exhaustive
        in (exhaustive, reverse warnings, reverse branches')
      _ -> error ("Internal error: AnalysisMatch.analyzeBranches' called with " ++
                  show (length types) ++ " scrutinees for " ++ show defName ++
                  " — only a single scrutinee is supported at this stage of compilation.")

-- | Process one branch, threading the accumulated coverage.
-- Returns (rewritten branch, this row's Coverage contribution, warnings).
matchRowBranch :: Newtypes -> Name -> Range -> Coverage -> [Type] -> Branch
               -> (Branch, Coverage, Warnings)
matchRowBranch newtypes defName range accCov types branch@(Branch patterns guards)
  | not (any (isExprTrue . guardTest) guards) = (branch, CovNone, [])
  | otherwise =
      let (patterns', rowCov, isRedundant) = matchRowPats newtypes defName range accCov types patterns
          warnings1 = [ (range, text "Some branches in the match will never be reached:"
                                <+> text (show (prettyBranch defaultEnv branch)))
                      | isRedundant ]
          warnings2 = analyzeGuards range guards
      in (Branch patterns' guards, rowCov, warnings1 ++ warnings2)

-- | Process one row of patterns against the accumulated coverage.
-- Returns (rewritten patterns, this row's Coverage contribution, was-redundant).
--
-- The accumulator 'accCov' represents everything covered by branches BEFORE
-- this row; it is used for redundancy detection and for complement expansion
-- of wildcards.
--
-- PatWild  → closed type: record a complement node (Maybe WildId) on the
--              CovBranch rather than expanding eagerly.  Exception: if exactly
--              one constructor is uncovered and no complement exists, replace
--              with an explicit PatCon (FIP/PARC opt — see tryWildOpt).
--            open/primitive type: emit a CovOpen node and recurse.
-- PatVar   → transparent; recurse with the wrapped pattern.
-- PatLit   → contributes CovNone (literals are not coverage-tracked).
-- PatCon   → emit one ConBranch for this constructor; recurse into sub-fields.
matchRowPats :: Newtypes -> Name -> Range -> Coverage -> [Type] -> [Pattern]
             -> ([Pattern], Coverage, Bool)
-- Base case: no more fields → this combination is newly covered.
-- Redundant if already complete.
matchRowPats _ _ _ accCov [] []
  = ([], CovDone, isCovComplete accCov)

matchRowPats newtypes defName range accCov (tp:tps) (pat:pats) = case pat of

  -- PatVar: transparent wrapper — recurse with the inner pattern.
  PatVar tname inner ->
    let (pats', rowCov, red) = matchRowPats newtypes defName range accCov (typeOf tname : tps) (inner : pats)
    in case pats' of
         (p':rest) -> (PatVar tname p' : rest, rowCov, red)
         _         -> error "Internal error: matchRowPats PatVar"

  -- PatLit: literals are not tracked in coverage (too many possible values).
  PatLit lit -> (pat : pats, CovNone, False)

  -- PatWild: mark as wildcard complement for closed types; CovOpen for open/primitive.
  -- We do NOT eagerly expand to individual ConBranches — instead we record a complement
  -- node (Maybe WildId) on the CovBranch.  Individual constructors are only pulled out
  -- of the complement lazily during unionCoverage when an explicit PatCon forces it.
  --
  -- Exception: if exactly ONE constructor is uncovered and there is no existing complement,
  -- we replace the wildcard with an explicit PatCon for that constructor (FIP/PARC
  -- optimization — lets the memory reuse analysis see the concrete constructor).
  PatWild ->
    let wildId    = range
        conInfos  = lookupConInfos newtypes tp
    in if null conInfos
       then -- Open or primitive type: no constructors, so just thread through.
            let subAcc = case accCov of { CovOpen _ c -> c; CovDone -> CovDone; _ -> CovNone }
                (pats', restCov, red) = matchRowPats newtypes defName range subAcc tps pats
                cov = if isCovComplete restCov then CovDone else CovOpen (Just wildId) restCov
            in (pat : pats', cov, isCovComplete accCov || red)
       else if isCovComplete accCov
       then (pat : pats, CovNone, True)  -- everything already covered: redundant
       else
         let existingCbs   = case accCov of { CovBranch _ cbs _ -> cbs; _ -> [] }
             hasComplement  = case accCov of { CovBranch _ _ (Just _) -> True; _ -> False }
             uncovered      = filter (\ci -> not (maybe False (isCovComplete . cbParams)
                                                      (findCb (conInfoName ci) existingCbs))) conInfos
             -- FIP/PARC optimization: if exactly one constructor is uncovered and there is no
             -- existing complement, replace PatWild with an explicit PatCon so the memory
             -- reuse analysis can see the concrete constructor and avoid deallocation.
             tryWildOpt = case uncovered of
               [con] | not hasComplement
                     , null (conInfoExists con)
                     -> case lookupDataInfo newtypes (conInfoTypeName con) of
                          Just di | not (dataInfoIsLazy di)
                            -> case instantiatePatCon tp (conInfoParams con) (conInfoType con) of
                                 Just (targs, tres) ->
                                   let wildArgs = [PatWild | _ <- conInfoParams con]
                                       cname    = TName (conInfoName con) (conInfoType con)
                                       repr     = getConRepr di con
                                   in Just (matchRowPats newtypes defName range accCov (tp:tps)
                                              (PatCon cname wildArgs repr targs [] tres con False : pats))
                                 Nothing -> Nothing
                          _ -> Nothing
               _ -> Nothing
         in case tryWildOpt of
              Just result -> result
              Nothing ->
                -- Mark the complement.  For constructors already explicitly listed but not
                -- yet complete (partials), upgrade their sub-coverage to CovDone so that
                -- unionCoverage sees them as complete after merging.
                let partialCbs   = [ cb { cbParams = CovDone }
                                   | cb <- existingCbs, not (isCovComplete (cbParams cb)) ]
                    coveredNames = map (conInfoName . cbCon) existingCbs
                    hasUncovered = any (\ci -> conInfoName ci `notElem` coveredNames) conInfos
                    mWild        = if hasUncovered then Just wildId else Nothing
                in (pat : pats, CovBranch conInfos partialCbs mWild, False)

  -- PatCon: explicit constructor match.
  PatCon cname args repr targs exists res cinfo _ ->
    let -- If accCov has a complement that covers this constructor, the branch is redundant.
        inComplement = case accCov of
                         CovBranch _ cbs (Just _) -> isNothing (findCb (conInfoName cinfo) cbs)
                         _                        -> False
        -- Sub-coverage accumulated for this constructor before this branch.
        -- If it's in the complement, the prior sub-coverage is implicitly CovDone.
        conSubAcc = case accCov of
                      CovBranch _ cbs _ | inComplement -> CovDone
                      CovBranch _ cbs _                -> maybe CovNone cbParams (findCb (conInfoName cinfo) cbs)
                      CovDone                          -> CovDone
                      _                                -> CovNone
        -- Recurse into constructor's fields, then remaining patterns.
        (newPats, subCov, red) = matchRowPats newtypes defName range conSubAcc (targs ++ tps) (args ++ pats)
        (args', pats')         = splitAt (length args) newPats
        skip                   = covOthersComplete newtypes tp cinfo accCov
        allCons                = lookupConInfos newtypes tp
        newCb  = ConBranch { cbCon = cinfo, cbParams = subCov }
        rowCov = CovBranch allCons [newCb] Nothing
        pat'   = PatCon cname args' repr targs exists res cinfo skip
    in (pat' : pats', rowCov, isCovComplete accCov || red)

matchRowPats _ _ _ _ tps pats
  = error ("AnalysisMatch: mismatch in patterns/types: types=" ++ show (length tps)
           ++ ", patterns=" ++ show (length pats))

-- | Check whether all constructors OTHER than 'cinfo' are already fully
-- covered in the accumulated coverage.  Used to set the skip flag on the
-- output PatCon (telling backends they can omit the runtime constructor tag
-- check).  A complement node covers all constructors not explicitly listed,
-- so any "other" constructor absent from the explicit list is trivially complete.
covOthersComplete :: Newtypes -> Type -> ConInfo -> Coverage -> Bool
covOthersComplete newtypes tp cinfo accCov
  = case accCov of
      CovBranch infos cbs mw ->
        let others = filter (\ci -> conInfoName ci /= conInfoName cinfo) infos
        in all (\ci -> case (findCb (conInfoName ci) cbs, mw) of
                         (Just cb, _)      -> isCovComplete (cbParams cb)
                         (Nothing, Just _) -> True   -- covered by complement
                         (Nothing, Nothing)-> False) others
      CovDone -> True
      CovNone ->
        -- First branch ever: skip only for a singleton type (no other constructors).
        let allInfos = lookupConInfos newtypes tp
            others   = filter (\ci -> conInfoName ci /= conInfoName cinfo) allInfos
        in null others && not (null allInfos)
      _ -> False

-- | Find the ConBranch for a given constructor name, if present.
findCb :: Name -> [ConBranch] -> Maybe ConBranch
findCb n = listToMaybe . filter (\cb -> conInfoName (cbCon cb) == n)

-- | Union of two coverage trees (least upper bound).
-- Both arguments must represent the same field position.
unionCoverage :: Coverage -> Coverage -> Coverage
unionCoverage CovDone _       = CovDone
unionCoverage _ CovDone       = CovDone
unionCoverage CovNone c       = c
unionCoverage c CovNone       = c
unionCoverage (CovOpen w1 c1) (CovOpen w2 c2)
  = let c = unionCoverage c1 c2
    in if isCovComplete c then CovDone else CovOpen (w1 <|> w2) c
unionCoverage (CovBranch infos cbs1 mw1) (CovBranch _ cbs2 mw2)
  = let -- Lazy complement expansion: when a constructor is explicit on one side
        -- but only covered by the complement on the other, its implicit
        -- sub-coverage is CovDone.
        fromComplement sub mw = case mw of { Just _ -> CovDone; Nothing -> sub }
        allNames = nub (map (conInfoName . cbCon) cbs1 ++ map (conInfoName . cbCon) cbs2)
        merged   = [ case (findCb n cbs1, findCb n cbs2) of
                       (Just cb1, Just cb2) -> cb1 { cbParams = unionCoverage (cbParams cb1) (cbParams cb2) }
                       (Just cb,  Nothing)  -> cb  { cbParams = fromComplement (cbParams cb) mw2 }
                       (Nothing,  Just cb)  -> cb  { cbParams = fromComplement (cbParams cb) mw1 }
                       _                    -> error "impossible"
                   | n <- allNames ]
        mw          = mw1 <|> mw2
        -- Complete if complement covers remaining constructors, and all explicit are done.
        allPresent  = isJust mw || length merged == length infos
        allComplete = all (isCovComplete . cbParams) merged
    in if allPresent && allComplete then CovDone
       else CovBranch infos merged mw
unionCoverage _ _
  = error "Internal error: unionCoverage called with mismatched Coverage shapes"

-- | Generate the catch-all error branch added when coverage is incomplete.
-- Mirrors the logic currently in Type/Infer.hs (~line 1700).
-- The branch matches a wildcard and raises a pattern-match failure at 'range'.
makeDefaultErrorBranch :: Name -> Range -> Type -> Branch
makeDefaultErrorBranch defName range resultTp = undefined -- TODO

-- | Instantiate a constructor type, unifying the result type with 'tpRes'.
-- Returns the field types and instantiated result type, or Nothing on failure.
instantiatePatCon :: Type -> [(Name,Type)] -> Scheme -> Maybe ([Type],Type)
instantiatePatCon tpRes [] conTp
  = Just ([],tpRes)
instantiatePatCon tpRes conParams conTp
  = case splitFunScheme conTp of
      Nothing -> Nothing
      Just (tforall,tpars,eff,tres)
        -> case runUnifyEx 0 (unify tpRes tres) of
             (Right _, sub, _) -> Just ([sub |-> tpar | (_,tpar) <- tpars], sub |-> tres)
             _ -> Nothing
