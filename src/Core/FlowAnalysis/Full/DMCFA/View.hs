-----------------------------------------------------------------------------
-- A readable report of the results of the full HMCFA analysis:
-- what every expression evaluates to and what every variable is bound to,
-- at each timestamp, shown in terms of the source program.
-- See analysis/hmcfa-viewer.md for the roadmap.
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}
module Core.FlowAnalysis.Full.DMCFA.View( hmcfaReport, hmcfaJson ) where

import Data.List (intercalate, sortOn, nub)
import Data.Char (isSpace)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe, mapMaybe)
import Compile.Module (Module(..))
import qualified Core.Core as C
import Core.Core (TName(..))
import Compile.BuildMonad (BuildContext)
import Core.FlowAnalysis.StaticContext
import Core.FlowAnalysis.FixpointMonad
import Core.FlowAnalysis.Literals
import Core.FlowAnalysis.Monad
import Core.FlowAnalysis.Full.DMCFA.DMCFA
import Core.FlowAnalysis.Full.DMCFA.AbstractValue
import Core.FlowAnalysis.Full.DMCFA.Monad
import Core.FlowAnalysis.Full.DMCFA.Syntax ()   -- Label instances for the fixpoint cache
import Common.Name
import Common.Range
import Common.File (startsWith)
import System.Timeout (timeout)
import qualified Data.Aeson as J
import Data.Aeson ((.=))

type Cache  = M.Map FixInput FixOutput
type States = M.Map ExprContextId ExprContext

-- | Run HMCFA on each entry point of a module and describe the results as markdown.
-- An entry point is a top-level function named `analyze-...` or, failing that, `main`.
-- `m` bounds the call-site component of a timestamp and `d` the handler (meta-stack) component.
-- Entries for compiler-generated code are left out unless `showGenerated` is set.
hmcfaReport :: BuildContext -> TypeChecker -> Module -> Int -> Int -> Bool -> IO String
hmcfaReport bc build mod m d showGenerated
  = do sections <- analyzeEntries bc build mod m d
       return $ unlines $
         [ "# HMCFA results for `" ++ show (modName mod) ++ "`"
         , ""
         , "Timestamps keep the innermost " ++ show m ++ " call site(s) and " ++ show d ++ " handler level(s)."
         , "" ] ++
         (if null sections then ["No entry point found: add a `main` function or a function named `analyze-...`."]
                           else concatMap (renderSection showGenerated) sections)

-- | The same results as structured data, for the editor's interactive view.
hmcfaJson :: BuildContext -> TypeChecker -> Module -> Int -> Int -> IO J.Value
hmcfaJson bc build mod m d
  = do sections <- analyzeEntries bc build mod m d
       return $ J.object [ "module" .= show (modName mod), "file" .= modSourcePath mod, "m" .= m, "d" .= d
                         , "entryPoints" .= map sectionJson sections ]

data Section = Section { secName :: String, secSize :: Int, secEntries :: Maybe [Entry] }  -- Nothing: timed out

analyzeEntries :: BuildContext -> TypeChecker -> Module -> Int -> Int -> IO [Section]
analyzeEntries bc build mod m d
  = do (_, s, found) <- runFixFinish (emptyBasicEnv m d build False ()) (emptyBasicState bc ()) $
                          do runFixCont $ do
                               (_,ctx) <- loadModule (modName mod)
                               withEnv (\e -> e{currentModContext = ctx, currentContext = ctx}) $ do
                                 res <- analyzeEachChild ctx (const findEntry)
                                 addResult res
                             getResults
       let s'      = transformBasicState (const ()) (const S.empty) s
           all     = S.toList found
           chosen  = case filter (\(n,_) -> n /= "main") all of
                       [] -> all
                       xs -> xs
       mapM (entrySection s') chosen
  where
    file = modSourcePath mod

    entrySection s' (name, entry)
      = do res <- timeout 60000000 $
                    do (_, sEnd, cache) <- runFixFinishC (emptyBasicEnv m d build True ()) s' $ do
                                              runFixCont $ do
                                                (_,ctx) <- loadModule (modName mod)
                                                withEnv (\e -> e{currentModContext = ctx, currentContext = ctx}) $ do
                                                  c   <- inject entry
                                                  res <- doStep c
                                                  case res of
                                                    RV (RVAddr addr) -> do rebind addr EndVAddr
                                                                           return ()
                                                    _ -> doBottom
                                                  return ()
                                              getCache
                       return $! M.size cache `seq` (cache, states sEnd)
           return $ case res of
             Nothing           -> Section name 0 Nothing
             Just (cache, sts) -> Section name (M.size cache) (Just (cacheEntries file sts cache))

-- | Find the body of an entry point at the current context.
findEntry :: FixAAMR (String, ExprContext) () () (String, ExprContext)
findEntry = do
  ctx <- currentContext <$> getEnv
  case ctx of
    DefCNonRec{} -> do
      let name = nameStem (unqualify (getName (C.defTName (defOfCtx ctx))))
      if name `startsWith` "analyze-" || name == "main"
        then do body <- focusDefBody ctx
                return (name, body)
        else doBottom
    _ -> doBottom


{---------------------------------------------------------------
  The report as data
---------------------------------------------------------------}

-- | What one expression evaluates to, or what one variable is bound to, at each timestamp.
data Entry = Entry { eKind      :: String        -- "expression" or "binding"
                   , eId        :: String        -- the core expression (or variable) this entry is about
                   , eRange     :: Range
                   , eText      :: String        -- as written in the source
                   , eCore      :: String        -- the core expression, to tell apart entries with the same source text
                   , eGenerated :: Bool          -- compiler-generated code
                   , eResults   :: [(Time, [Val], [String])]   -- timestamp, values, operations performed
                   }

-- | A timestamp. Reading outwards from the current point:
--   * `tCalls`: the call sites entered since the innermost delimiter (innermost first);
--   * `tHandlers`: the delimiters we are inside (innermost first). A delimiter is either the installation
--     of a handler or the resumption of a continuation. Each remembers `hCalls`, the call sites that
--     were on the stack when it was crossed, i.e. the calling context outside (below) that delimiter.
data Time   = Time { tKey :: String, tCalls :: Calls, tHandlers :: [HandlerLevel] }
data Calls  = Calls { cInHandler :: Bool, cSites :: [Site] }
data HandlerLevel = HandlerLevel { hEffect :: String
                                 , hKind   :: String       -- "handle": a handler was installed; "resume": a continuation was resumed
                                 , hAt     :: Maybe Site   -- the `with` handler, or the call to `resume`
                                 , hOthers :: Int          -- other handlers for this effect it could also be (only for "handle")
                                 , hCalls  :: Calls }
data Site   = Site { sText :: String, sRange :: Maybe Range }
data Val    = Val { vKind :: String, vText :: String } deriving (Eq)

cacheEntries :: FilePath -> States -> Cache -> [Entry]
cacheEntries file sts cache
  = let evals  = [ (ctx, time, rvs) | (Step (CEval ctx _ time), RValue rvs) <- M.toList cache, hasOwnRange ctx, inFile (ctxRange ctx) ]
        exprs  = M.toList $ M.fromListWith (\(c,a) (_,b) -> (c, M.unionWith S.union a b))
                   [ ((sortKey ctx, contextId ctx), (ctx, M.singleton time rvs)) | (ctx, time, rvs) <- evals ]
        binds  = [ (tn, r, time, ab) | (VStore (BindingAddr time tn _), SValue ab) <- M.toList cache
                                     , Just r <- [C.originalRange tn], inFile r ]
        vars   = M.toList $ M.fromListWith (\(r,a) (_,b) -> (r, M.unionWith joinVal a b))
                   [ ((pos r, showName (getName tn)), (r, M.singleton time ab)) | (tn, r, time, ab) <- binds ]
        -- source positions + text that more than one core expression maps back to (desugared code)
        shared = M.keysSet $ M.filter (> (1::Int)) $ M.fromListWith (+) [ (k, 1) | ((k, _), _) <- exprs ]
    in [ Entry "expression" (show cid) (ctxRange ctx) label (oneLine 80 (showSimpleContext ctx))
               (rangeIsHidden (ctxRange ctx) || key `S.member` shared)
               [ (mkTime sts handleSites time, results (S.toList rvs), ops (S.toList rvs)) | (time, rvs) <- M.toList byTime ]
       | ((key@(_, label), cid), (ctx, byTime)) <- exprs ] ++
       [ Entry "binding" (name ++ "@" ++ show p) r name name
               (rangeIsHidden r || name `startsWith` "@")
               [ (mkTime sts handleSites time, showVals ab, []) | (time, ab) <- M.toList byTime ]
       | ((p, name), (r, byTime)) <- vars ]
  where
    inFile r      = not (rangeIsNull r) && sourceName (rangeSource r) == file
    pos r         = (posLine (rangeStart r), posColumn (rangeStart r))
    sortKey ctx   = (pos (ctxRange ctx), ctxLabel ctx)
    joinVal a b   = foldl (\v ch -> snd (addChange v ch)) a (changes b)
    results rvs   = case [ ab | RVAddr addr <- rvs, Just (SValue ab) <- [M.lookup (VStore addr) cache] ] of
                      []   -> []
                      vals -> showVals (foldl1 joinVal vals)
    ops rvs       = nub [ nameStem (dOpName dval) | ROp dval _ _ _ _ <- rvs ]
    -- effect name -> where handlers for it are installed in this file: applications of `<effect>/@handle`
    handleSites   = M.map (nub . sortOn pos) $ M.fromListWith (++)
                      [ (eff, [r]) | ctx <- M.elems sts, Just e <- [maybeExprOfCtx ctx], Just (eff, r) <- [handleRef e], inFile r ]
    -- a reference to `<effect>/@handle`, with the range of the handler it was generated for
    handleRef e
      = case e of
          C.App f _ (Just r) | Just eff <- handledEffect f -> Just (eff, r)
          C.Var tn _ | Just eff <- handledEffect e, Just r <- C.originalRange tn -> Just (eff, r)
          _ -> Nothing
    handledEffect f
      = case f of
          C.TypeApp g _ -> handledEffect g
          C.Var tn _    -> let full = show (getName tn)
                               suffix = "/@handle"
                           in if length full > length suffix && drop (length full - length suffix) full == suffix
                                then Just (dropWhile (== '#') (reverse (takeWhile (/= '/') (drop (length suffix) (reverse full)))))   -- local qualifiers print as `#effect`
                                else Nothing
          _ -> Nothing

mkTime :: States -> M.Map String [Range] -> CombinedCtx -> Time
mkTime sts handleSites time@(CombinedCtx static dyn)
  = Time (show time) (mkCalls static) [ mkLevel c (showName nm) (mkCalls st) | ((c, nm), st) <- dyn ]
  where
    -- A handler is installed by generated code (a call to `@hhandle` inside the effect's `@handle` function),
    -- so we point at the `with` handler(s) for that effect in the source instead.
    mkLevel c eff calls
      = case (c, mkSite c) of
          (CallApp _, site@(Site _ (Just _))) -> HandlerLevel eff "resume" (Just site) 0 calls
          _ -> case M.findWithDefault [] eff handleSites of
                 (r:rs) -> HandlerLevel eff "handle" (Just (Site "with handler" (Just r))) (length rs) calls
                 []     -> HandlerLevel eff "handle" Nothing 0 calls
    mkCalls (TKTop calls)   = Calls False (map mkSite calls)
    mkCalls (TKDelim calls) = Calls True  (map mkSite calls)
    mkSite call
      = case call of
          CallTop          -> Site "top" Nothing
          CallDelim        -> Site "handler" Nothing
          CallApp cid      -> fromId cid
          CtxId (Left cid) -> fromId cid
          CtxId (Right nm) -> Site (showName nm) Nothing
    fromId cid
      = case M.lookup cid sts of
          Just ctx -> let r = ctxRange ctx
                      in if rangeIsNull r || rangeIsHidden r || not (hasOwnRange ctx)
                           then Site ("generated: " ++ oneLine 40 (showSimpleContext ctx)) Nothing   -- a call the compiler or library made
                           else Site (ctxLabel ctx) (Just r)
          Nothing  -> Site (show cid) Nothing

showVals :: AbValue -> [Val]
showVals ab
  = nub $ [ Val "function" (ctxLabel ctx) | (ctx, _) <- S.toList (aclos ab) ] ++
          [ Val "constructor" (showName nm) | (nm, _) <- S.toList (acons ab) ] ++
          [ Val "constructor" (showName nm ++ "(..)") | (nm, _) <- S.toList (aobjs ab) ] ++
          [ Val "function" (showName nm) | nm <- S.toList (aprims ab) ] ++
          [ Val "continuation" "a continuation" | _ <- take 1 (S.toList (akonts ab)) ] ++
          showLits (alits ab)

showLits :: LiteralLatticeX -> [Val]
showLits (LiteralLatticeX i f c s)
  = one "int" i ++ one "float64" f ++ one "char" c ++ one "string" s
  where
    one :: Show a => String -> SLattice (ExprContextId, a) -> [Val]
    one tp l = case lat l of
                 LSingle x -> [Val "literal" (show x)]
                 LTop      -> [Val "any" ("any " ++ tp)]
                 LBottom   -> []


{---------------------------------------------------------------
  As JSON
---------------------------------------------------------------}

sectionJson :: Section -> J.Value
sectionJson (Section name size mbEntries)
  = J.object [ "name" .= name, "cacheSize" .= size, "timedOut" .= (case mbEntries of { Nothing -> True; _ -> False })
             , "entries" .= map entryJson (fromMaybe [] mbEntries) ]

entryJson :: Entry -> J.Value
entryJson e
  = J.object [ "kind" .= eKind e, "id" .= eId e, "range" .= rangeJson (eRange e), "text" .= eText e, "core" .= eCore e
             , "generated" .= eGenerated e
             , "results" .= [ J.object [ "time" .= timeJson t, "values" .= map valJson vs, "performs" .= ops ] | (t, vs, ops) <- eResults e ] ]

timeJson :: Time -> J.Value
timeJson (Time key calls handlers)
  = J.object [ "key" .= key, "calls" .= callsJson calls
             , "handlers" .= [ J.object [ "effect" .= eff, "kind" .= kind, "at" .= fmap siteJson at, "others" .= others, "calls" .= callsJson cs ]
                             | HandlerLevel eff kind at others cs <- handlers ] ]

callsJson :: Calls -> J.Value
callsJson (Calls inHandler sites) = J.object [ "inHandler" .= inHandler, "sites" .= map siteJson sites ]

siteJson :: Site -> J.Value
siteJson (Site text mbRange) = J.object [ "text" .= text, "range" .= fmap rangeJson mbRange ]

valJson :: Val -> J.Value
valJson (Val kind text) = J.object [ "kind" .= kind, "text" .= text ]

-- | 1-based lines and columns; the end is inclusive, as in the compiler.
rangeJson :: Range -> J.Value
rangeJson r
  = J.object [ "line" .= posLine (rangeStart r), "column" .= posColumn (rangeStart r)
             , "endLine" .= posLine (rangeEnd r), "endColumn" .= posColumn (rangeEnd r) ]


{---------------------------------------------------------------
  As markdown
---------------------------------------------------------------}

renderSection :: Bool -> Section -> [String]
renderSection showGenerated (Section name size mbEntries)
  = [ "## `" ++ name ++ "`", "" ] ++
    case mbEntries of
      Nothing -> [ "The analysis did not finish within 60 seconds.", "" ]
      Just es ->
        let visible = filter (\e -> showGenerated || not (eGenerated e)) es
            part k  = case filter ((== k) . eKind) visible of
                        [] -> [ "(none)", "" ]
                        xs -> concatMap renderEntry xs
        in [ "### Expressions", "" ] ++ part "expression" ++
           [ "### Bindings", "" ] ++ part "binding" ++
           [ "_" ++ show size ++ " entries in the analysis cache; " ++ show (size - sum (map (length . eResults) visible)) ++
             " not shown (library code, " ++ (if showGenerated then "" else "compiler-generated code, ") ++
             "continuations, and internal steps)._", "" ]

renderEntry :: Entry -> [String]
renderEntry e
  = [ "- **" ++ show (posLine (rangeStart (eRange e))) ++ ":" ++ show (posColumn (rangeStart (eRange e))) ++ "** `" ++ eText e ++ "`" ++
      (if eGenerated e && eKind e == "expression" then " — core: `" ++ eCore e ++ "`" else "") ] ++
    [ "  - at " ++ renderTime t ++ " → " ++ renderResult vs ops | (t, vs, ops) <- eResults e ] ++ [ "" ]
  where
    renderResult vs ops
      = case (if null vs then [] else [ "{" ++ intercalate ", " (map renderVal vs) ++ "}" ]) ++
             [ "performs `" ++ op ++ "` (not handled inside this expression)" | op <- ops ] of
          [] -> "nothing"
          xs -> intercalate " **or** " xs
    renderVal (Val kind text) = if kind `elem` ["function", "constructor"] then "`" ++ text ++ "`" else text

-- | Outermost first: the calls outside each delimiter, the delimiter, and finally the calls since the innermost one.
renderTime :: Time -> String
renderTime (Time _ calls handlers)
  = "`" ++ unwords (concatMap level (reverse handlers) ++ [renderCalls calls]) ++ "`"
  where
    level (HandlerLevel eff kind at _ cs)
      = [ renderCalls cs, "⟦" ++ kind ++ " " ++ eff ++ maybe "" (\st -> " " ++ renderSite st) at ++ "⟧" ]
    renderCalls (Calls _ sites)    = "[" ++ intercalate " > " (map renderSite (reverse sites)) ++ "]"
    renderSite (Site text mbRange) = text ++ maybe "" (\r -> "@" ++ show (posLine (rangeStart r))) mbRange


{---------------------------------------------------------------
  Source labels
---------------------------------------------------------------}

-- | The source range of an expression, or the closest enclosing binding if it has none.
ctxRange :: ExprContext -> Range
ctxRange ctx
  = case maybeExprOfCtx ctx of
      Just (C.App _ _ (Just r))       -> r
      Just (C.Var tn _) | Just r <- C.originalRange tn -> r
      Just (C.Con _ _ (Just r))       -> r
      _                               -> closestRange ctx

hasOwnRange :: ExprContext -> Bool
hasOwnRange ctx
  = case maybeExprOfCtx ctx of
      Just (C.App _ _ (Just _)) -> True
      Just (C.Var tn _)         -> C.originalRange tn /= Nothing
      Just (C.Con _ _ (Just _)) -> True
      _                         -> False

-- | An expression as the user wrote it, when we know its range; otherwise a short description.
ctxLabel :: ExprContext -> String
ctxLabel ctx
  = if hasOwnRange ctx then snippet (ctxRange ctx)
    else case ctx of
      LamCBody _ _ tns _ -> "body of " ++ showLam tns
      DefCRec{}          -> showName (getName (C.defTName (defOfCtx ctx)))
      DefCNonRec{}       -> showName (getName (C.defTName (defOfCtx ctx)))
      LetCDefRec{}       -> showName (getName (C.defTName (defOfCtx ctx)))
      LetCDefNonRec{}    -> showName (getName (C.defTName (defOfCtx ctx)))
      _ -> case fmap stripTypes (maybeExprOfCtx ctx) of
             Just (C.Lam tns _ _) -> showLam tns
             _                    -> oneLine 60 (showSimpleContext ctx)
  where
    stripTypes e = case e of
                     C.TypeLam _ b -> stripTypes b
                     C.TypeApp b _ -> stripTypes b
                     _             -> e

showLam :: [TName] -> String
showLam tns = "fn(" ++ intercalate "," (map (showName . getName) tns) ++ ")"

-- | Names without their module path.
showName :: Name -> String
showName = nameStem

snippet :: Range -> String
snippet r = oneLine 60 (sourceFromRange r)

oneLine :: Int -> String -> String
oneLine n s
  = let flat = unwords (words (map (\c -> if c == '`' then '\'' else c) s))
    in if length flat > n then take (n - 1) flat ++ "…" else flat

