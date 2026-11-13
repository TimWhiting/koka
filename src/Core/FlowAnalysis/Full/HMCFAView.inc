-- The body of the HMCFA results viewer, shared by both variants of the analysis:
-- Core.FlowAnalysis.Full.DMCFA.View and Core.FlowAnalysis.Full.DMCFAR.View include it after importing their variant,
-- whose types and functions have the same names. Not a module of its own (so not a .hs file).
import Data.List (intercalate, sortOn, nub, dropWhileEnd)
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
import Common.Name
import Common.Range
import Common.File (startsWith)
import System.Timeout (timeout)
import qualified System.Environment as Env
import Data.Time.Clock (getCurrentTime, diffUTCTime)
import qualified Data.Aeson as J
import Data.Aeson ((.=))
import qualified Data.Aeson.Types as JT

type Cache  = M.Map FixInput FixOutput
type States = M.Map ExprContextId ExprContext

-- | Run HMCFA on the chosen entry point of a module (or the default ones) and describe the results as markdown.
-- Any top-level function without parameters can be an entry point; by default the analysis runs each function
-- named `analyze-...`, or `main` when there are none.
-- `m` bounds the call-site component of a timestamp and `h` the handler (meta-stack) component.
-- Entries for compiler-generated code are left out unless `showGenerated` is set.
hmcfaReport :: BuildContext -> TypeChecker -> Module -> Int -> Int -> Bool -> Maybe String -> IO String
hmcfaReport bc build mod m d showGenerated selected
  = do (candidates, sections) <- analyzeEntries bc build mod m d selected
       return $ unlines $
         [ "# HMCFA results for `" ++ show (modName mod) ++ "`"
         , ""
         , "Timestamps keep the innermost " ++ show m ++ " call site(s) and " ++ show d ++ " handler level(s)."
         , ""
         , "Entry points: " ++ intercalate ", " [ "`" ++ c ++ "`" | c <- candidates ] ++ " (choose one with `--hmcfa-entry`)."
         , "" ] ++
         (if null sections then ["No entry point found: add a `main` function or a function named `analyze-...`."]
                           else concatMap (renderSection showGenerated) sections)

-- | The same results as structured data, for the editor's interactive view.
hmcfaJson :: BuildContext -> TypeChecker -> Module -> Int -> Int -> Maybe String -> IO J.Value
hmcfaJson bc build mod m d selected
  = do (candidates, sections) <- analyzeEntries bc build mod m d selected
       return $ J.object [ "module" .= show (modName mod), "file" .= modSourcePath mod, "m" .= m, "h" .= d
                         , "candidates" .= candidates, "selected" .= selected
                         , "entryPoints" .= map sectionJson sections ]

data Section = Section { secName :: String, secSize :: Int, secSeconds :: Double, secEntries :: Maybe ([Entry], [(Time, [String])]) }  -- Nothing: timed out

-- | The names of all entry points the module offers, and the sections for the ones analyzed: the selected one,
-- or by default each `analyze-...` function (or `main` when there are none).
analyzeEntries :: BuildContext -> TypeChecker -> Module -> Int -> Int -> Maybe String -> IO ([String], [Section])
analyzeEntries bc build mod m d selected
  = do (_, s, found) <- runFixFinish (emptyBasicEnv m d build False ()) (emptyBasicState bc ()) $
                          do runFixCont $ do
                               (_,ctx) <- loadModule (modName mod)
                               withEnv (\e -> e{currentModContext = ctx, currentContext = ctx}) $ do
                                 res <- analyzeEachChild ctx (const findEntry)
                                 addResult res
                             getResults
       let s'      = transformBasicState (const ()) (const S.empty) s
           all     = S.toList found
           byDefault = case filter (\(n,_) -> n `startsWith` "analyze-") all of
                         [] -> filter (\(n,_) -> n == "main") all
                         xs -> xs
           chosen  = case selected of
                       Just n | any ((== n) . fst) all -> filter ((== n) . fst) all
                       _ -> byDefault
       sections <- mapM (entrySection s') chosen
       return (nub (map fst all), sections)
  where
    file = modSourcePath mod

    entrySection s' (name, entry)
      = do start <- getCurrentTime
           -- the time limit per entry point: 60 seconds, or KOKA_HMCFA_TIMEOUT seconds
           limit <- maybe 60 id . (>>= \v -> case reads v of { [(n, "")] -> Just n; _ -> Nothing }) <$> Env.lookupEnv "KOKA_HMCFA_TIMEOUT"
           res <- timeout (limit * 1000000) $
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
           end <- getCurrentTime
           let seconds = realToFrac (diffUTCTime end start)   -- the fixpoint only, not building the entries
           return $ case res of
             Nothing           -> Section name 0 seconds Nothing
             Just (cache, sts) -> Section name (M.size cache) seconds (Just (cacheEntries file sts cache, cacheContexts file sts cache))

-- | Where a variable is declared. A binding address carries the variable as it was looked up (at a use, so with the
-- range of that use) and the context that binds it; the binder with the same name in that context has the declaration's range.
binderRange :: States -> ExprContextId -> TName -> Maybe Range
binderRange sts bid tn
  = case [ r | b <- maybe [] binders (M.lookup bid sts), b == tn, Just r <- [C.originalRange b], not (rangeIsNull r) ] of
      (r:_) -> Just r
      []    -> C.originalRange tn
  where
    binders ctx
      = (case ctx of
           DefCRec _ _ _ ns         -> ns
           DefCNonRec _ _ n         -> [n]
           DefCGroup _ _ ns _       -> ns
           LetCDefRec _ _ _ ns      -> ns
           LetCDefNonRec _ _ n      -> [n]
           LetCDefGroup _ _ ns _ _  -> ns
           LetCBody _ _ ns _        -> ns
           LamCBody _ _ ns _        -> ns
           CaseCBranch _ _ ns _ b   -> ns ++ branchVars b
           CaseCGuard _ _ ns _ b _  -> ns ++ branchVars b
           CaseCBody _ _ ns _ b _   -> ns ++ branchVars b
           _                        -> [])
        ++ maybe [] exprBinders (maybeExprOfCtx ctx)
    exprBinders e
      = case e of
          C.Lam ns _ body   -> ns ++ exprBinders body
          C.TypeLam _ body  -> exprBinders body
          C.TypeApp body _  -> exprBinders body
          C.App f args _    -> exprBinders f ++ concatMap exprBinders args
          C.Let dgs body    -> concat [ C.defTName d : exprBinders (C.defExpr d) | dg <- dgs, d <- defsOf dg ] ++ exprBinders body
          C.Case es bs      -> concatMap exprBinders es ++
                               concat [ branchVars b ++ concat [ exprBinders t ++ exprBinders g | C.Guard t g <- gs ] | b@(C.Branch _ gs) <- bs ]
          _                 -> []

-- | Find the body of an entry point at the current context: a top-level function without parameters.
findEntry :: FixAAMR (String, ExprContext) () () (String, ExprContext)
findEntry = do
  ctx <- currentContext <$> getEnv
  case ctx of
    DefCNonRec{} -> do
      let name = nameStem (unqualify (getName (C.defTName (defOfCtx ctx))))
      if name `startsWith` "analyze-" || name == "main" || noParams (C.defExpr (defOfCtx ctx))
        then do body <- focusDefBody ctx
                return (name, body)
        else doBottom
    _ -> doBottom
  where
    noParams e = case e of
                   C.TypeLam _ b -> noParams b
                   C.Lam [] _ _  -> True
                   _             -> False


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
                   , eReference :: Bool          -- just a variable (its value is the value of the binding)
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
data Site   = Site { sText :: String, sRange :: Maybe Range, sId :: Maybe String }   -- id: the call's expression context, if any
-- | A value. `vExtra` carries more about some kinds: whether a function is defined at the top level,
-- and the frames of a continuation.
data Val    = Val { vKind :: String, vText :: String, vExtra :: [JT.Pair] } deriving (Eq)

-- | Every timestamp something was evaluated at, in any module, with the expressions evaluated there (by context id).
-- The editor uses these to connect the call stacks of the entries, whose calls may go through library code.
cacheContexts :: FilePath -> States -> Cache -> [(Time, [String])]
cacheContexts file sts cache
  = [ (mkTime file sts M.empty time, S.toList ids)
    | (time, ids) <- M.toList $ M.fromListWith S.union
                       [ (time, S.singleton (show (contextId ctx))) | (Step conf, RValue _) <- M.toList cache, Just (ctx, time) <- [evalStep conf] ] ]

-- | Whether a range is in the analyzed file.
inFile :: FilePath -> Range -> Bool
inFile file r = not (rangeIsNull r) && sourceName (rangeSource r) == file

-- | The module a range is in, for labels: the file name without directories and extension.
moduleOf :: Range -> String
moduleOf r = let name = reverse (takeWhile (/= '/') (reverse (sourceName (rangeSource r))))
             in reverse (drop 1 (dropWhile (/= '.') (reverse name)))

cacheEntries :: FilePath -> States -> Cache -> [Entry]
cacheEntries file sts cache
  = let evals  = [ (ctx, time, rvs) | (Step conf, RValue rvs) <- M.toList cache, Just (ctx, time) <- [evalStep conf], hasOwnRange ctx, inFile (ctxRange ctx) ] ++
                 -- a value handed to an application frame is the value of its function or of one of its arguments; after a
                 -- resumption this is the only place the value of such a subexpression (say an operation call) shows up
                 [ (child, time, S.singleton (RVAddr addr))
                 | (Step (CContinue (RVAddr addr) (FApp _ _ res eApp _) time), _) <- M.toList cache
                 , Just child <- [M.lookup (contextId eApp, length res) appChildren], hasOwnRange child, inFile (ctxRange child) ] ++
                 -- likewise a value handed to a val frame is the value of that binding's right-hand side
                 [ (rhs, time, S.singleton (RVAddr addr))
                 | (Step (CContinue (RVAddr addr) (FLet _ _ _ _ name _ _ _) time), _) <- M.toList cache
                 , Just rhs <- [M.lookup name letRhs], hasOwnRange rhs, inFile (ctxRange rhs) ] ++
                 -- and a value handed to a match frame is the value of the scrutinee (`if yield(x) then ...`)
                 [ (scrut, time, S.singleton (RVAddr addr))
                 | (Step (CContinue (RVAddr addr) FScrut{ parent = p } time), _) <- M.toList cache
                 , Just scrut <- [M.lookup (contextId p) scrutinees], hasOwnRange scrut, inFile (ctxRange scrut) ]
        -- the right-hand side of each local definition, by the name it defines
        letRhs = M.fromList $ concat [ case c of
                                         LetCDefNonRec _ _ tn  -> [(tn, c)]
                                         LetCDefRec _ _ i tns  -> [(tns !! i, c)]
                                         _                     -> []
                                     | c <- M.elems sts ]
        -- the scrutinee of each match, by the match's context
        scrutinees = M.fromList [ (contextId p, c) | c@(CaseCScrutinee _ p _) <- M.elems sts ]
        -- the function (0) and arguments (1, 2, ...) of each application, by the application's context
        appChildren = M.fromList $ concat [ case c of
                                              AppCLambda _ p _  -> [((contextId p, 0), c)]
                                              AppCParam _ p i _ -> [((contextId p, i + 1), c)]
                                              _                 -> []
                                          | c <- M.elems sts ]
        exprs  = M.toList $ M.fromListWith (\(c,a) (_,b) -> (c, M.unionWith S.union a b))
                   [ ((sortKey ctx, contextId ctx), (ctx, M.singleton time rvs)) | (ctx, time, rvs) <- evals ]
        binds  = [ (tn, r, time, ab) | (VStore (BindingAddr time tn bid), SValue ab) <- M.toList cache
                                     , Just r <- [binderRange sts bid tn], inFile r ]
        vars   = M.toList $ M.fromListWith (\(r,a) (_,b) -> (r, M.unionWith joinVal a b))
                   [ ((pos r, showName (getName tn)), (r, M.singleton time ab)) | (tn, r, time, ab) <- binds ]
        -- source positions + text that more than one core expression maps back to (desugared code)
        shared = M.keysSet $ M.filter (> (1::Int)) $ M.fromListWith (+) [ (k, 1) | ((k, _), _) <- exprs ]
    in [ Entry "expression" (show cid) (ctxRange ctx) label (oneLine 80 (showSimpleContext ctx))
               (rangeIsHidden (ctxRange ctx) || key `S.member` shared) (isReference ctx)
               [ (mkTime file sts handleSites time, results (S.toList rvs), ops (S.toList rvs)) | (time, rvs) <- M.toList byTime ]
       | ((key@(_, label), cid), (ctx, byTime)) <- exprs ] ++
       [ Entry "binding" (name ++ "@" ++ show p) r name name
               ((rangeIsHidden r || name `startsWith` "@") && not (isResume byTime)) False
               [ (mkTime file sts handleSites time, showVals file sts cache ab, []) | (time, ab) <- M.toList byTime ]
       | ((p, name), (r, byTime)) <- vars ]
  where
    inFile r      = not (rangeIsNull r) && sourceName (rangeSource r) == file
    isReference ctx = case maybeExprOfCtx ctx of { Just (C.Var _ _) -> True; Just (C.TypeApp (C.Var _ _) _) -> True; _ -> False }
    pos r         = (posLine (rangeStart r), posColumn (rangeStart r))
    sortKey ctx   = (pos (ctxRange ctx), ctxLabel ctx)
    -- the implicit `resume` of an operation clause: its range is generated, but it holds the continuation the clause got
    isResume byTime = any (not . S.null . akonts) (M.elems byTime)
    joinVal a b   = foldl (\v ch -> snd (addChange v ch)) a (changes b)
    results rvs   = case [ ab | RVAddr addr <- rvs, Just (SValue ab) <- [M.lookup (VStore addr) cache] ] of
                      []   -> []
                      vals -> showVals file sts cache (foldl1 joinVal vals)
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

mkTime :: FilePath -> States -> M.Map String [Range] -> CombinedCtx -> Time
mkTime file sts handleSites time@(CombinedCtx static dyn)
  = Time (show time) (mkCalls static) [ if isQualified nm then mkLevel c (showName nm) (mkCalls st) else localLevel (showName nm) (mkCalls st)
                                       | ((c, nm), st) <- dyn ]
  where
    -- Effect labels are qualified by their module.
    -- A handler is installed by generated code (a call to `@hhandle` inside the effect's `@handle` function),
    -- so we point at the `with` handler(s) for that effect in the source instead.
    -- a local variable (`var x`) is a handler too, labeled by the variable's (unqualified) name; installing it and
    -- assigning to it both cross its delimiter, so they are one kind of level
    localLevel x calls = HandlerLevel x "local" Nothing 0 calls
    mkLevel c eff calls
      = case (c, mkSite c) of
          (CallApp _, site@(Site _ (Just _) _)) -> HandlerLevel eff "resume" (Just site) 0 calls
          _ -> case M.findWithDefault [] eff handleSites of
                 (r:rs) -> HandlerLevel eff "handle" (Just (Site "with handler" (Just r) Nothing)) (length rs) calls
                 []     -> HandlerLevel eff "handle" Nothing 0 calls
    mkCalls = staticCalls file sts
    mkSite  = callSite file sts

staticCalls :: FilePath -> States -> StaticCtx -> Calls
staticCalls file sts (TKTop calls)   = Calls False (map (callSite file sts) calls)
staticCalls file sts (TKDelim calls) = Calls True  (map (callSite file sts) calls)

callSite :: FilePath -> States -> Call -> Site
callSite file sts call
      = case call of
          CallTop          -> Site "top" Nothing Nothing
          CallDelim        -> Site "handler" Nothing Nothing
          CallApp cid      -> fromId cid
          CtxId (Left cid) -> fromId cid
          CtxId (Right nm) -> Site (showName nm) Nothing Nothing
  where
    fromId cid
      = let ident = Just (show cid) in
        case M.lookup cid sts of
          Just ctx -> let r = ctxRange ctx
                      in if rangeIsNull r || rangeIsHidden r || not (hasOwnRange ctx)
                           then Site ("generated: " ++ oneLine 40 (showSimpleContext ctx)) Nothing ident   -- a call the compiler made
                           else if not (inFile file r)
                           then Site (ctxLabel ctx ++ " (in " ++ moduleOf r ++ ")") Nothing ident          -- a call in a library
                           else Site (ctxLabel ctx) (Just r) ident
          Nothing  -> Site (show cid) Nothing ident

showVals :: FilePath -> States -> Cache -> AbValue -> [Val]
showVals file sts cache ab
  = nub $ [ Val "function" (ctxLabel ctx) [ "top" .= isTopLevel ctx ] | (ctx, _) <- S.toList (aclos ab) ] ++
          [ Val "constructor" (showName nm) [] | (nm, _) <- S.toList (acons ab) ] ++
          [ Val "constructor" (showName nm ++ "(..)") [] | (nm, _) <- S.toList (aobjs ab) ] ++
          [ Val "function" (showName nm) [ "top" .= True ] | nm <- S.toList (aprims ab) ] ++
          [ kontVal file sts cache k h | (k, _, h) <- S.toList (akonts ab) ] ++
          showLits (alits ab)
  where
    -- a function defined at the top level of a module (the closure of a definition, not of a lambda in an expression)
    isTopLevel ctx = case ctx of { DefCRec{} -> True; DefCNonRec{} -> True; _ -> False }

-- | A continuation captured by a handler, in its finite (abstract) form: the frames waiting for the result of the
-- operation, from the outermost (next to the handler) inwards, each with the static context it runs in.
-- Frames come from the continuation store, where a frame may continue with several frames (and loop, for recursion),
-- so the result is a graph: `start` is the outermost frame and `next` gives each frame's possible inner frames;
-- the innermost frame is the operation call itself.
kontVal :: FilePath -> States -> Cache -> Addr -> Handler -> Val
kontVal file sts cache start h
  = Val "continuation" text [ "kont" .= J.object [ "effect" .= showName (hLabel h), "op" .= op, "opAt" .= fmap siteJson opSite
                                                , "start" .= idOf first, "frames" .= map frameJson nodes
                                                , "acts" .= map actJson acts ] ]
  where
    -- the operation is performed by a generated function: point at the newest call in the source that led to it
    (op, opSite) = case start of
                     KAddr _ _ _ dval -> (nameStem (dOpName dval),
                                          case exprSite (dExpr dval) of
                                            st@(Site _ (Just _) _) -> Just st
                                            st -> case newestSource (staticCalls file sts (static (dCtx dval))) of
                                                    Just src -> Just src
                                                    Nothing  -> Just (Site (nameStem (dOpName dval) ++ "(…)") Nothing Nothing))
                     _                -> ("", Nothing)
    newestSource (Calls _ sites) = case [ st | st@(Site _ (Just _) _) <- sites ] of { (st:_) -> Just st; [] -> Nothing }
    text = "continuation of " ++ (if null op then showName (hLabel h) else op) ++ maybe "" (\st -> " at " ++ sText st) opSite
    -- the frames reachable from the start, breadth first, at most 200
    nodes = take 200 (go [first] S.empty)
    -- a continuation captured where the operation is performed starts with that frame: start after it
    first = case skipDone start of { [a] -> a; _ -> start }
    go [] _ = []
    go (a:rest) seen
      | a `S.member` seen = go rest seen
      | otherwise         = a : go (rest ++ succs a) (S.insert a seen)
    succs a = concatMap skipDone (stored a)
    stored a = case M.lookup (KStore a) cache of
                 Just (KValue ks) -> S.toList ks
                 _                -> []
    -- the frame pushed where the operation is performed (inside the generated operation function): the value passed
    -- to resume returns through it to the caller, which is exactly what the op frame says, so show its successors instead
    skipDone b = case b of
                   KAddr FrameDone{} _ _ _ -> stored b
                   _                       -> [b]
    ids = M.fromList (zip nodes [0 :: Int ..])
    idOf a = M.findWithDefault (-1) a ids
    -- Each frame's hole: the source of the subexpression it waits for, and the function activation it belongs to,
    -- so the view can show a continuation as source with a hole, one block per call.
    holes = M.fromList [ (a, h) | a@(KAddr frame _ _ _) <- nodes, Just h <- [frameHole file frame] ]
    acts = nub [ l | (_, _, l) <- M.elems holes ]
    actIds = M.fromList (zip acts [0 :: Int ..])
    actJson l = activationJson file l
    holeJson a = case M.lookup a holes of
                   Just (r, region, l) -> [ "hole" .= rangeJson r, "region" .= rangeJson region, "act" .= M.lookup l actIds ]
                   Nothing     -> []
    frameJson a
      = J.object $ [ "id" .= idOf a, "next" .= [ idOf b | b <- succs a, M.member b ids ] ] ++ holeJson a ++
          case a of
            KAddr frame sctx _ _ -> let calls = staticCalls file sts sctx
                                        (kind, text, site) = case (describeFrame file sts frame, newestSource calls) of
                                                               (("done", _, _), Just call) -> ("return", "return from " ++ sText call, Just call)
                                                               (d, _) -> d
                                    in [ "kind" .= kind, "text" .= text, "at" .= fmap siteJson site, "calls" .= callsJson calls ]
            _                    -> [ "kind" .= ("op" :: String), "text" .= (maybe op sText opSite ++ " returns the value passed to resume"), "at" .= fmap siteJson opSite ]
    exprSite ctx = let r = ctxRange ctx
                   in if rangeIsNull r || rangeIsHidden r || not (inFile file r) then Site (oneLine 40 (showSimpleContext ctx)) Nothing Nothing else Site (ctxLabel ctx) (Just r) Nothing

-- | The hole of a frame: the source range of the subexpression whose value the frame waits for, and the body of the
-- function it is in (a `LamCBody` context), and the extent of the expression the frame belongs to (what is left of it
-- is the local continuation). Nothing for frames without a source hole (delimiters, generated code).
frameHole :: FilePath -> Frame -> Maybe (Range, Range, ExprContext)
frameHole file frame
  = do (p, hole) <- case frame of
                      FApp{ parent = p, resolvedArgs = done } ->
                        case maybeExprOfCtx p of
                          Just (C.App f args _) -> let i = length done in Just (p, if i == 0 then f else args !! (i - 1))
                          _ -> Nothing
                      FLet{ groupIdx = g, bindingIdx = b, parent = p } ->
                        case maybeExprOfCtx p of
                          Just (C.Let dgs _) | g < length dgs -> case dgs !! g of
                                                                   C.DefRec ds | b < length ds -> Just (p, C.defExpr (ds !! b))
                                                                   C.DefNonRec d | b == 0      -> Just (p, C.defExpr d)
                                                                   _ -> Nothing
                          _ -> Nothing
                      FScrut{ parent = p } ->
                        case maybeExprOfCtx p of
                          Just (C.Case [e] _) -> Just (p, e)
                          _ -> Nothing
                      _ -> Nothing
       r <- case exprSpan file hole of
              Just r  -> Just r
              Nothing -> case frame of
                           FLet{ name = n } -> C.originalRange n >>= afterEquals file
                           _                -> Nothing
       l <- enclosingLambda p
       let span = fromMaybe r (maybeExprOfCtx p >>= exprSpan file)
           -- where the remaining source starts: a binding from its line's start (`val x = □`), a desugared `if` or a
           -- `match` from its keyword, anything else from the expression itself
           region = case frame of
                      FLet{ name = n } -> case C.originalRange n of
                                            Just nr | not (rangeIsNull nr || rangeIsHidden nr) && inFile file nr
                                                    -> withKeyword ["val", "var"] (makeRange (rangeStart nr) (rangeEnd span))
                                            _ -> makeRange (rangeStart span){ posColumn = 1, posOfs = -1 } (rangeEnd span)
                      FScrut{} -> withKeyword ["if", "match"] span
                      _        -> span
       return (r, region, l)

-- | The source extent of an expression: from the first to the last source range inside it (ranges in this file only).
exprSpan :: FilePath -> C.Expr -> Maybe Range
exprSpan file e
  = case [ r | r <- go e, not (rangeIsNull r || rangeIsHidden r), inFile file r ] of
      [] -> Nothing
      rs -> Just (foldr1 combineRange rs)
  where
    go ex = case ex of
              C.Lam _ _ b        -> go b
              C.Var _ _          -> []   -- a variable's range is where it is defined, not where it is used
              C.App f as mr      -> case mr of
                                      Just r  -> r : go f ++ concatMap go as
                                      Nothing -> go f ++ concatMap go as
              C.TypeLam _ b      -> go b
              C.TypeApp b _      -> go b
              C.Con _ _ mr       -> maybe [] (: []) mr
              C.Lit _            -> []
              C.Let dgs b        -> concatMap (go . C.defExpr) (C.flattenDefGroups dgs) ++ go b
              C.Case es bs       -> concatMap go es ++ concat [ go (C.guardTest g) ++ go (C.guardExpr g) | br <- bs, g <- C.branchGuards br ]

-- | A range extended back over one of the keywords (`if`, `val`, ...) right before it on the same line.
withKeyword :: [String] -> Range -> Range
withKeyword keywords r
  = let ls     = lines (sourceText (posSource (rangeStart r)))
        ln     = posLine (rangeStart r)
        before = reverse (take (posColumn (rangeStart r) - 1) (if ln <= length ls then ls !! (ln - 1) else ""))
        spaces = length (takeWhile isSpace before)
        word   = reverse (takeWhile (not . isSpace) (drop spaces before))
    in if word `elem` keywords
         then makeRange (rangeStart r){ posColumn = posColumn (rangeStart r) - spaces - length word, posOfs = -1 } (rangeEnd r)
         else r

-- | The rest of the line after the `=` that follows a binder: the bound expression, when core has no range for it.
afterEquals :: FilePath -> Range -> Maybe Range
afterEquals file r
  | rangeIsNull r || rangeIsHidden r || not (inFile file r) = Nothing
  | otherwise
  = let ls   = lines (sourceText (posSource (rangeStart r)))
        ln   = posLine (rangeEnd r)
        line = if ln <= length ls then ls !! (ln - 1) else ""
        rest = drop (posColumn (rangeEnd r)) line
    in case break (== '=') rest of
         (_, '=' : expr) | not (all isSpace expr) ->
           let lead  = length (takeWhile isSpace expr)
               start = posColumn (rangeEnd r) + length rest - length expr + lead + 1
               end   = length (dropWhileEnd isSpace line)
               pos c = (rangeEnd r){ posColumn = c, posOfs = -1 }
           in Just (makeRange (pos start) (pos end))
         _ -> Nothing

-- | A function activation: its name, where it is defined, and its body's source lines (for the holes to go in).
activationJson :: FilePath -> ExprContext -> J.Value
activationJson file lam
  = J.object [ "name" .= name, "at" .= fmap rangeJson at, "first" .= first, "lines" .= body ]
  where
    (params, bodyExpr, parent) = case lam of
                                   LamCBody _ p tns b -> (tns, Just b, Just p)
                                   _                  -> ([], Nothing, Nothing)
    args = "(" ++ intercalate ", " (map (showName . getName) params) ++ ")"
    named = case parent of
              Just p@DefCRec{}       -> Just (C.defName (defOfCtx p), C.defNameRange (defOfCtx p))
              Just p@DefCNonRec{}    -> Just (C.defName (defOfCtx p), C.defNameRange (defOfCtx p))
              Just p@LetCDefRec{}    -> Just (C.defName (defOfCtx p), C.defNameRange (defOfCtx p))
              Just p@LetCDefNonRec{} -> Just (C.defName (defOfCtx p), C.defNameRange (defOfCtx p))
              _                      -> Nothing
    -- an anonymous function is named after the definition it is in (a block is a function without parameters)
    owner = showName (C.defName (enclosingDef lam))
    name = case named of
             Just (n, _) -> showName n ++ args
             Nothing | null params -> "block in " ++ owner
                     | otherwise   -> "fn" ++ args ++ " in " ++ owner
    at = case named of
           Just (_, r) | not (rangeIsNull r || rangeIsHidden r) && inFile file r -> Just r
           _ -> Nothing
    span = bodyExpr >>= exprSpan file
    first = maybe 0 (posLine . rangeStart) span
    body = case span of
             Just r -> take (posLine (rangeEnd r) - posLine (rangeStart r) + 1) $ drop (posLine (rangeStart r) - 1) $
                         lines (sourceText (posSource (rangeStart r)))
             Nothing -> []

-- | What a continuation frame waits for, in source terms: a kind, a description, and where it is (if in the source).
describeFrame :: FilePath -> States -> Frame -> (String, String, Maybe Site)
describeFrame file sts frame
  = case frame of
      FLet{ name = n, parent = p }
        | isStatement n            -> ("let", "□, then the next statement", fmap statementSite (binder n p))
        | otherwise                -> ("let", "val " ++ showName (getName n) ++ " = □", binder n p)
      FApp{ parent = p }           -> ("app", "□ in " ++ label p, site p)
      FScrut{ parent = p }         -> case scrutinee p of
                                        -- a desugared match (an `if`) has no range of its own: name what it branches on
                                        Just r | not (hasOwnRange p) -> let t = snippet r in ("match", "branch on the result of " ++ t, Just (Site t (Just r) Nothing))
                                        _ -> ("match", "match □ in " ++ label p, site p)
      FDollar{ ctx = c }           -> ("return", "the handler's return clause", byId c)
      FResume{ rCtx = c }          -> ("resume", "resume(…)", byId c)
      FRestoreDelim (DFrame _ _ h) -> ("handle", "handle " ++ showName (hLabel h), Nothing)
      FRestoreDelim (DFrameLocal _ _ (_, tn) _) -> ("handle", "local var " ++ showName (getName tn), Nothing)
      FRestoreDelim _              -> ("handle", "a delimiter", Nothing)
      FMask{}                      -> ("mask", "mask", Nothing)
      FrameDone{}                  -> ("done", "done", Nothing)
      FCount                       -> ("done", "done", Nothing)
  where
    statementSite (Site t mr i) = case mr of { Just r -> Site ("the statement on line " ++ show (posLine (rangeStart r))) mr i; Nothing -> Site t mr i }
    isStatement n = showName (getName n) `elem` ["_", "_.", ""] || take 1 (showName (getName n)) == "_"
    own ctx = let r = ctxRange ctx in not (rangeIsNull r || rangeIsHidden r) && inFile file r
    label ctx = if own ctx then ctxLabel ctx else "generated code: " ++ oneLine 40 (showSimpleContext ctx)
    site ctx = if own ctx then Just (Site (ctxLabel ctx) (Just (ctxRange ctx)) Nothing) else Nothing
    scrutinee ctx = case maybeExprOfCtx ctx of
                      Just (C.Case [C.App _ _ (Just r)] _) | not (rangeIsNull r || rangeIsHidden r) && inFile file r -> Just r
                      _ -> Nothing
    byId c = M.lookup c sts >>= site
    binder n p = case C.originalRange n of
                   Just r | not (rangeIsNull r || rangeIsHidden r) && inFile file r -> Just (Site (showName (getName n)) (Just r) Nothing)
                   _ -> site p

showLits :: LiteralLatticeX -> [Val]
showLits (LiteralLatticeX i f c s)
  = one "int" i ++ one "float64" f ++ one "char" c ++ one "string" s
  where
    one :: Show a => String -> SLattice (ExprContextId, a) -> [Val]
    one tp l = case lat l of
                 LSingle x -> [Val "literal" (show x) []]
                 LTop      -> [Val "any" ("any " ++ tp) []]
                 LBottom   -> []


{---------------------------------------------------------------
  As JSON
---------------------------------------------------------------}

sectionJson :: Section -> J.Value
sectionJson (Section name size seconds mbEntries)
  = J.object [ "name" .= name, "cacheSize" .= size, "seconds" .= seconds, "timedOut" .= (case mbEntries of { Nothing -> True; _ -> False })
             , "entries" .= map entryJson (maybe [] fst mbEntries)
             , "contexts" .= [ J.object [ "time" .= timeJson t, "evals" .= ids ] | (t, ids) <- maybe [] snd mbEntries ] ]

entryJson :: Entry -> J.Value
entryJson e
  = J.object [ "kind" .= eKind e, "id" .= eId e, "range" .= rangeJson (eRange e), "text" .= eText e, "core" .= eCore e
             , "generated" .= eGenerated e, "reference" .= eReference e
             , "results" .= [ J.object [ "time" .= timeJson t, "values" .= map valJson vs, "performs" .= ops ] | (t, vs, ops) <- eResults e ] ]

timeJson :: Time -> J.Value
timeJson (Time key calls handlers)
  = J.object [ "key" .= key, "calls" .= callsJson calls
             , "handlers" .= [ J.object [ "effect" .= eff, "kind" .= kind, "at" .= fmap siteJson at, "others" .= others, "calls" .= callsJson cs ]
                             | HandlerLevel eff kind at others cs <- handlers ] ]

callsJson :: Calls -> J.Value
callsJson (Calls inHandler sites) = J.object [ "inHandler" .= inHandler, "sites" .= map siteJson sites ]

siteJson :: Site -> J.Value
siteJson (Site text mbRange ident) = J.object [ "text" .= text, "range" .= fmap rangeJson mbRange, "id" .= ident ]

valJson :: Val -> J.Value
valJson (Val kind text extra) = J.object ([ "kind" .= kind, "text" .= text ] ++ extra)

-- | 1-based lines and columns; the end is inclusive, as in the compiler.
rangeJson :: Range -> J.Value
rangeJson r
  = J.object [ "line" .= posLine (rangeStart r), "column" .= posColumn (rangeStart r)
             , "endLine" .= posLine (rangeEnd r), "endColumn" .= posColumn (rangeEnd r) ]


{---------------------------------------------------------------
  As markdown
---------------------------------------------------------------}

renderSection :: Bool -> Section -> [String]
renderSection showGenerated (Section name size seconds mbEntries)
  = [ "## `" ++ name ++ "`", "", "Analyzed in " ++ showSeconds seconds ++ ".", "" ] ++
    case mbEntries of
      Nothing -> [ "The analysis did not finish within 60 seconds.", "" ]
      Just (es, _) ->
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
    renderVal (Val kind text _) = if kind `elem` ["function", "constructor"] then "`" ++ text ++ "`" else text

-- | Outermost first: the calls outside each delimiter, the delimiter, and finally the calls since the innermost one.
showSeconds :: Double -> String
showSeconds t
  = if t < 1 then show (round (t * 1000) :: Int) ++ " ms"
             else show (fromIntegral (round (t * 100) :: Int) / 100 :: Double) ++ " s"

renderTime :: Time -> String
renderTime (Time _ calls handlers)
  = "`" ++ unwords (concatMap level (reverse handlers) ++ [renderCalls calls]) ++ "`"
  where
    level (HandlerLevel eff kind at _ cs)
      = [ renderCalls cs, "⟦" ++ kind ++ " " ++ eff ++ maybe "" (\st -> " " ++ renderSite st) at ++ "⟧" ]
    renderCalls (Calls _ sites)    = "[" ++ intercalate " > " (map renderSite (reverse sites)) ++ "]"
    renderSite (Site text mbRange _) = text ++ maybe "" (\r -> "@" ++ show (posLine (rangeStart r))) mbRange


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

