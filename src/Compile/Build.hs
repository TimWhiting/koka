-----------------------------------------------------------------------------
-- Copyright 2012-2024, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
module Compile.Build( Build
                      , modulesFullBuild
                      , modulesBuild
                      , modulesTypeCheck

                      , modulesResolveDependencies
                      , modulesReValidate
                      , moduleFromSource, moduleFromModuleName
                      , modulesFlushErrors
                      , virtualMount
                      , searchSourceFile
                      ) where

import Debug.Trace
import Data.Char
import Data.Maybe
import Data.List
import Data.Either
import Data.IORef
import Control.Exception
import Control.Applicative
import Control.Monad          ( ap, when, foldM )
import qualified Control.Monad.Fail as F
import Control.Concurrent.QSem
import Control.Concurrent.Async (mapConcurrently)
import Control.Concurrent.Chan
import Control.Concurrent
import System.Directory ( doesFileExist )

import Lib.Scc( scc )
import Lib.PPrint
import Platform.Config        ( version, exeExtension, dllExtension, libPrefix, libExtension, pathSep, sourceExtension )
import Common.Syntax          ( Target(..), isPublic, Visibility(..))
import Common.Error
import Common.Failure         ( assertion, HasCallStack, failure )
import Common.File   hiding (getFileTime)
import qualified Common.File as F
import qualified Common.NameMap as M
import Common.ColorScheme
import Common.Range
import Common.NamePrim        (isPrimitiveModule)
import Syntax.Lexeme          (LexImport(..), lexImportNub)
import Syntax.Syntax
import Syntax.Layout          (lexSource)
import Syntax.Parse           (parseProgramFromLexemes, parseDependencies)
import Type.Type
import qualified Type.Pretty as TP
import Type.Assumption        ( Gamma, gammaLookupQ, NameInfo(..) )
import qualified Core.Core as Core
import Core.Parse
import Compile.Options
import Compile.Module
import Compile.TypeCheck      ( typeCheck )
import Compile.Optimize       ( coreOptimize )
import Compile.CodeGen        ( codeGen, Link, LinkResult(..), noLink )
import Compile.BuildMonad
import Core.Core (Core(coreProgDefs))
import GHC.IORef (atomicSwapIORef)
import Core.FlowAnalysis.Demand.ConstantProp (constantPropagation)
import Core.FlowAnalysis.Full.Syntax (evalMain)


{---------------------------------------------------------------
  Concurrently compile a list of root modules.
  All phases are cached and rebuilds from previous modules should
  be efficient.
---------------------------------------------------------------}

-- Builds given a list of root modules (and possibly dependencies)
-- Returns all required modules as compiled in build order.
-- Internally composed of `modulesReValidate` and `modulesBuild`.
modulesFullBuild :: Bool -> [ModuleName] -> [Name] -> [Module] -> [Module] -> Build [Module]
modulesFullBuild rebuild forced mainEntries cachedImports roots
  = do modules <- modulesReValidate rebuild forced cachedImports roots
       modulesBuild mainEntries modules


-- Given a complete list of modules in build order (and main entry points), build them all.
modulesBuild :: [Name] -> [Module] -> Build [Module]
modulesBuild mainEntries modules
  = -- phaseTimed 2 "build" (\_ -> Lib.PPrint.empty) $ -- (list (map (pretty . modName) modules))
    do parsedMap   <- modmapCreate modules
       tcheckedMap <- modmapCreate modules
       optimizedMap<- modmapCreate modules
       codegenMap  <- modmapCreate modules
       linkedMap   <- modmapCreate modules
       let buildOrder = map modName modules
       compiled    <- seqList buildOrder $
                      withTotalWork (workNeeded PhaseLinked modules) $
                      mapConcurrentModules
                       (moduleCompile mainEntries parsedMap tcheckedMap optimizedMap codegenMap linkedMap buildOrder)
                       modules
       -- mapM_ modmapClear [tcheckedMap,optimizedMap,codegenMap,linkedMap]
       return compiled -- modulesFlushErrors compiled

-- Given a complete list of modules in build order, type check them all.
modulesTypeCheck :: [Module] -> Build [Module]
modulesTypeCheck modules
  = phaseTimed 3 "checking" (const Lib.PPrint.empty) $
    do parsedMap   <- modmapCreate modules
       tcheckedMap <- modmapCreate modules
       tchecked    <- withTotalWork (workNeeded PhaseTyped modules) $
                      mapConcurrentModules (moduleTypeCheck parsedMap tcheckedMap) modules
       -- modmapClear tcheckedMap
       return tchecked -- modulesFlushErrors tchecked


-- Given a list of cached modules (`cachedImports`), and a set of root modules (`roots`), return a list of
-- required modules to build the roots in build order, and validated against the
-- file system (so updated sources get rebuild).
-- Can force to rebuild everything (`rebuild`), or give list of specicfic modules that need to be rebuild (`forced`).
--
-- after revalidate, typecheck and build are valid operations.
modulesReValidate :: Bool -> [ModuleName] -> [Module] -> [Module] -> Build [Module]
modulesReValidate rebuild forced cachedImports roots
  = phaseTimed 4 "resolving" (const Lib.PPrint.empty) $
    do -- rootsv    <- modulesValidate roots
       resolved  <- modulesResolveDependencies rebuild forced cachedImports roots
       return resolved -- modulesFlushErrors resolved

{---------------------------------------------------------------
  Module map
  We build concurrently using `mapConcurrentModules`

  Each module has 5 compilation phases that can be done concurrently with others. The 5 module maps
  (tcheckedMap, optimizedMap, codegenMap, and linkedMap) synchronize between these phases through mvar's.

  - resolve     : Parse each module, or load it from a previously compiled interface file.
                  This can be completely concurrent, but each load leads to more imports that are resolved
                  concurrently in a fixpoint.
                  This produces the user program (`modProgram`), the lexemes (`modLexemes`) and
                  a rangemap (`modRangeMap`).

  - type check  : As soon as the user+pub imports are type checked, a module can be checked as well.
                  This produces the initial core (`modCore`) and the "definitions" (`modDefinitions`)
                  that contain the gamma, kind gamma, etc.

  - optimize    : As soon as the user+pub imports, and the imports due to inline definitions are optimized,
                  the initial core be optimized as well (and use exported inline definitions)
                  This gives final core (updated `modCore`) and exported inline definitions (`modInlines`).
                  Note: optimization cannot be skipped as it also includes essential transformations
                  (like monadic lifting for effectful code).

  - codegen     : As soon as all imports are optimized, (no need to wait for the imports to be codegen'd!)
                  the optimized core can be translated to the backend (.c, .js, etc)

  - link        : As soon as all imports are codegen'd, the generated backend files can
                  be compiled/linked into object files (as they depend on the other's header files, etc).
                  An exe needs to wait until all imports are _linked_ though.
                  This produces an interface file (.kki) and backend object and executable files.
---------------------------------------------------------------}

type ModuleMap = M.NameMap (MVar Module)

-- signal a module is done with a compilation phase and unblock all pending reads.
modmapPut :: ModuleMap -> Module -> Build ()
modmapPut modmap mod
  = seq mod $ liftIO $ putMVar ((M.!) modmap (modName mod)) mod

-- signal a module is done with a compilation phase and unblock all pending reads.
-- only the first call succeeds but subsequent ones will not block (useful for exception handling)
modmapTryPut :: ModuleMap -> Module -> Build Bool
modmapTryPut modmap mod
  = seq mod $ liftIO $ tryPutMVar ((M.!) modmap (modName mod)) mod

-- blocks until a `modmapTryPut` happens (at which point it returns the module definition at that phase).
-- (all further reads are non-blocking)
modmapRead :: ModuleMap -> ModuleName -> Build Module
modmapRead modmap modname
  = liftIO $ readMVar ((M.!) modmap modname)

-- create an initial module map
modmapCreate :: [Module] -> Build ModuleMap
modmapCreate modules
   = M.fromList <$> mapM (\mod -> do v <- liftIO $ newEmptyMVar
                                     return (modName mod, v)) modules


-- ensure a phase always sets its mvar to guarantee progress
moduleGuard :: ModulePhase -> ModulePhase -> ModuleMap -> (a -> Module) -> (Module -> b)
                -> (Module -> Build a) -> ((Module -> Build b) -> a -> Build b) -> (Module -> Build b)
moduleGuard expectPhase targetPhase modmap fromRes toRes initial action mod0
  = do res <- onBuildException (edone mod0) (initial mod0)
       let mod = fromRes res
       seq mod $ buildFinally (edone mod) $
        if (modPhase mod < expectPhase || modPhase mod >= targetPhase)
          then done mod
          else action done res
  where
    edone mod = seq mod $
                do phaseCompleted targetPhase
                   modmapTryPut modmap mod  -- fails if it was already set
                   return ()

    done mod  = seq mod $
                do modmapPut modmap mod
                   return $! (toRes mod)


modmapClear :: ModuleMap -> Build ()
modmapClear modmap
  = liftIO $ mapM_ (\(_,mvar) -> tryPutMVar mvar moduleZero) (M.toList modmap)

moduleZero = moduleNull nameNil

{---------------------------------------------------------------
  Compile a module (type check, core compile, codegen, and link)
---------------------------------------------------------------}

moduleCompile :: HasCallStack => [Name] -> ModuleMap -> ModuleMap -> ModuleMap -> ModuleMap -> ModuleMap -> [ModuleName] -> Module -> Build Module
moduleCompile mainEntries parsedMap tcheckedMap optimizedMap codegenMap linkedMap buildOrder
  = moduleGuard PhaseCodeGen PhaseLinked linkedMap (\(_,_,mod) -> mod) id
                (moduleCodeGen mainEntries parsedMap tcheckedMap optimizedMap codegenMap)
    $ \done (fullLink,link,mod) ->
     do -- wait for all required imports to be codegen'd
        -- However, for a final exe we need to wait for the imports to be _linked_ as well (so we use linkedMap instead of codegenMap).
        imports0 <- moduleWaitForImports {-fullLink-} True -- with parallel builds in optimized mode we sometimes get permission errors
                                                           -- during C compilation; it seems sometime header file writes are delayed causing
                                                           -- concurrent read errors from a C compile. A fix is to wait for all required
                                                           -- modules recursively to be linked/codegen'd
                                         (if fullLink then linkedMap else codegenMap) [] (modImportNames mod)
        let imports = orderByBuildOrder buildOrder imports0  -- we order for a full link to link object files correctly
        if any (\m -> modPhase m < (if fullLink then PhaseLinked else PhaseCodeGen)) imports
          then done mod  -- dependencies had errors
          else do phaseVerbose (if fullLink then 1 else 2) (if fullLink then "linking" else "link") $
                                \penv -> TP.ppName penv (modName mod) -- <+> text ", imports:" <+> list (map (TP.ppName penv . modName) imports)
                  mbEntry <- pooledIO $ link imports  -- link it! (specifics were returned by codegen)
                  ftIface <- getFileTime (modIfacePath mod)
                  let mod' = mod{ modPhase = PhaseLinked
                                , modIfaceTime = ftIface
                                , modCore  = case modCore mod of
                                               Just core -> Just $! coreReset core  -- no need anymore for the definitions
                                               Nothing   -> Nothing
                                , modEntry = case mbEntry of
                                              LinkDone -> Nothing
                                              LinkExe exe run -> Just $! seqqTuple2 $ (exe,run) }
                  done mod'


orderByBuildOrder :: HasCallStack => [ModuleName] -> [Module] -> [Module]
orderByBuildOrder buildOrder mods
  = let ordered = -- nubBy (\m1 m2 -> modName m1 == modName m2) $
                  catMaybes (map (\mname -> find (\m -> modName m == mname) mods) buildOrder)
    in -- note: can happen with explicit duplicate imports, like `std/core/types` and `std/core` -- see `std/toc.kk`.
       -- should we fix this?
       -- assertion "Compile.Build.orderByBuildOrder: wrong modules?" (length ordered == length mods)  $
       seqqList $ ordered

{---------------------------------------------------------------
  Code generation (.c,.js)
---------------------------------------------------------------}

moduleCodeGen :: [Name] -> ModuleMap -> ModuleMap -> ModuleMap -> ModuleMap -> Module -> Build (Bool, Link, Module)
moduleCodeGen mainEntries parsedMap tcheckedMap optimizedMap codegenMap
  = moduleGuard PhaseOptimized PhaseCodeGen codegenMap (\mod -> mod) (\mod -> (False,noLink,mod))
                (moduleOptimize parsedMap tcheckedMap optimizedMap) $ \done mod ->
    do -- wait for all required imports to be optimized (no need to wait for codegen!)
       imports <- moduleWaitForImports False optimizedMap [] (modImportNames mod)
       if any (\m -> modPhase m < PhaseOptimized) imports
         then done mod
         else do  phaseVerbose 2 "codegen" $ \penv -> TP.ppName penv (modName mod) -- <.> text ": imported:" <+> list (map (pretty . modName) imports)
                  flags <- getFlags
                  term  <- getTerminal
                  let defs    = defsFromModules (mod:imports)  -- todo: optimize by reusing the defs from the compile?
                      inlines = inlinesFromModules imports
                  mbEntry <- getMainEntry (defsGamma defs) mainEntries mod
                  seqIO   <- sequentialIO
                  link    <- pooledIO $ codeGen term flags seqIO
                                                (defsNewtypes defs) (defsBorrowed defs) (defsKGamma defs) (defsGamma defs)
                                                mbEntry imports mod
                  let mod' = mod{ modPhase = PhaseCodeGen }
                  phaseVerbose 3 "codegen done" $ \penv -> TP.ppName penv (modName mod)
                  done mod'
                  return $! seq mod' $ seqMaybe mbEntry $ (isJust mbEntry,link,mod')


getMainEntry :: Gamma -> [Name] -> Module -> Build (Maybe (Name,Type))
getMainEntry gamma mainEntries mod
  = case find (\name -> qualifier name == modName mod) mainEntries of
      Nothing   -> return Nothing
      Just main -> -- trace ("getMainEntry: " ++ show mainEntries ++ " in " ++ show (modName mod)) $
                   case gammaLookupQ main gamma of
                    [InfoFun{infoType=tp}]
                           -> do return $ Just (main,tp)
                    []     -> do addErrorMessageKind ErrBuild (\penv -> text "unable to find main function:" <+> TP.ppName penv main)
                                 return Nothing
                    [info] -> do addErrorMessageKind ErrBuild (\penv -> text "main function" <+> TP.ppName penv (infoCName info) <+> text "must be a function")
                                 return Nothing
                    _      -> do addErrorMessageKind ErrBuild (\penv -> text "ambiguous main function:" <+> TP.ppName penv main)
                                 return Nothing


-- Import also modules required for checking inlined definitions from direct imports.
moduleWaitForImports :: Bool -> ModuleMap -> [ModuleName] -> [ModuleName] -> Build [Module]
moduleWaitForImports recurse modmap alreadyDone0 [] = return []
moduleWaitForImports recurse modmap alreadyDone0 importNames
  = do -- wait for imported modules to be compiled
       imports <- mapM (modmapRead modmap) importNames
       if not recurse
         then return imports
         else do let alreadyDone = alreadyDone0 ++ importNames
                     extras = nub $ [Core.importName imp | mod <- imports,
                                                           imp <- modCoreImports mod,
                                                           not (Core.importName imp `elem` alreadyDone)]
                 extraImports <- moduleWaitForImports recurse modmap alreadyDone extras
                 return (extraImports ++ imports)


{---------------------------------------------------------------
  Core optimize a module
  (not just optimization, some transformations are essential
  like perceus ref counting etc.)
---------------------------------------------------------------}

moduleOptimize :: ModuleMap -> ModuleMap -> ModuleMap -> Module -> Build Module
moduleOptimize parsedMap tcheckedMap optimizedMap
  = moduleGuard PhaseTyped PhaseOptimized optimizedMap id id (moduleTypeCheck parsedMap tcheckedMap) $ \done mod ->
     do -- wait for imports to be optimized (and include imports needed for inline definitions)
        imports <- moduleWaitForInlineImports optimizedMap (modImportNames mod)
        if any (\m -> modPhase m < PhaseOptimized) imports
          then done mod  -- dependencies had errors (todo: we could keep going if the import has (previously computed) core?)
          else if modPhase mod == PhaseIfaceLoaded
            then -- an interface has inline definitions that we can now parse
              do  phaseVerbose 3 "inlines" $ \penv -> TP.ppName penv (modName mod) -- <.> text ": imported:" <+> list (map (pretty . modName) imports)
                  case modInlines mod of
                    Right _ -> -- already done
                               done mod{ modPhase = PhaseLinked }
                    Left parse
                      -> do let defs = defsFromModules (mod:imports)  -- todo: optimize by reusing the defs from the type check?
                            case checkError (parse (defsGamma defs)) of
                              Left errs
                                -> done mod{ modPhase = PhaseLinked
                                           , modErrors = mergeErrors errs (modErrors mod)
                                           , modInlines = Right []
                                           }
                              Right (inlines,warns)
                                -> done mod{ modPhase = PhaseLinked
                                           , modErrors = mergeErrors warns (modErrors mod)
                                           , modInlines = Right inlines
                                           }
            else -- core compile
              do  phaseVerbose 2 "optimize" $ \penv -> TP.ppName penv (modName mod) -- <.> text ": imported:" <+> list (map (pretty . modName) imports)
                  flags <- getFlags
                  term <- getTerminal
                  let defs    = defsFromModules (mod:imports)  -- todo: optimize by reusing the defs from the type check?
                      inlines = inlinesFromModules imports
                  (core,inlineDefs) <- liftError $ coreOptimize flags (defsNewtypes defs) (defsGamma defs) inlines (fromJust (modCore mod))
                  let h = flagsHash flags
                      bc = seqString h $ BuildContext [modName mod] (mod:imports) h
                  liftIO $ evalMain bc (\_ -> error "Should not require loading") mod 0
                  -- liftIO $ constantPropagation (\bc m -> -- error "Should not require loading"
                  --     runBuild term flags $ buildcTypeCheck [m] bc
                  --    ) bc core
                  let mod' = mod{ modPhase   = PhaseOptimized
                                , modCore    = Just $! core
                                , modDefinitions = if showHiddenTypeSigs flags
                                                     then Just $! defsFromCore False core -- update defs so we can see generated ones as well
                                                     else modDefinitions mod
                                , modInlines = Right $! seqqList $ inlineDefs
                                }
                  phaseVerbose 3 "optimize done" $ \penv -> TP.ppName penv (modName mod)
                  done mod'


-- Import also modules required for checking inlined definitions from direct imports.
moduleWaitForInlineImports :: ModuleMap -> [ModuleName] -> Build [Module]
moduleWaitForInlineImports modmap importNames
  = do -- wait for imported modules to be compiled
       imports <- mapM (modmapRead modmap) importNames
       let extras = nub $ [Core.importName imp | mod <- imports, hasInlines (modInlines mod),
                                                  -- consider all of its imports too to ensure we can check its inline definitions
                                                  imp <- modCoreImports mod,
                                                  not (Core.importName imp `elem` importNames)]
       extraImports <- mapM (modmapRead modmap) extras
       return $! seqqList $ (extraImports ++ imports)
  where
    hasInlines (Right []) = False
    hasInlines _          = True


{---------------------------------------------------------------
  Type check a module
---------------------------------------------------------------}

moduleTypeCheck :: ModuleMap -> ModuleMap -> Module -> Build Module
moduleTypeCheck parsedMap tcheckedMap
  = moduleGuard PhaseParsed PhaseTyped tcheckedMap id id (moduleParse parsedMap) $ \done mod ->
     do -- wait for direct imports to be type checked
        let openDeps = [(lexImportIsOpen imp,lexImportName imp) | imp <- modDeps mod]
        imports <- moduleWaitForPubImports tcheckedMap [] openDeps
        if any (\m -> modPhase m < PhaseTyped) imports
          then done mod  -- dependencies had errors (todo: we could keep going if the import has (previously computed) core?)
          else -- type check
               do flags <- getFlags
                  phase "check" $ \penv -> TP.ppName penv (modName mod) -- <.> text ": imports:" <+> list (map (pretty . modName) imports)
                  let defs     = defsFromModules imports
                      cimports = coreImportsFromModules (modDeps mod) imports
                      program  = fromJust (modProgram mod)
                  case checkError (typeCheck flags defs cimports program) of
                    Left errs
                      -> done mod{ modPhase  = PhaseTypedError
                                 , modErrors = mergeErrors errs (modErrors mod)
                                 }
                    Right ((simple,core,mbRangeMap),warns)
                      -> do let mod' = mod{ modPhase       = PhaseTyped
                                          , modCore        = Just $! core
                                          , modCoreUnopt   = Just $! simple
                                          , modErrors      = mergeErrors warns (modErrors mod)
                                          , modRangeMap    = seqqMaybe mbRangeMap
                                          , modDefinitions = Just $! defsFromCore False core
                                          }
                            phaseVerbose 3 "check done" $ \penv -> TP.ppName penv (modName mod')
                            done mod'


-- Recursively load public imports from imported modules in a fixpoint
moduleWaitForPubImports :: ModuleMap -> [ModuleName] -> [(Bool,ModuleName)] -> Build [Module]
moduleWaitForPubImports tcheckedMap alreadyDone0 importDeps
  = do -- wait for imported modules to be type checked
       let (importOpen,importNames) = unzip importDeps
       imports0 <- mapM (modmapRead tcheckedMap) importNames
       let imports = zipWith (\isOpen mod -> mod{ modShouldOpen = isOpen }) importOpen imports0
           alreadyDone = alreadyDone0 ++ importNames
           extras = nub $ [(modShouldOpen mod,Core.importName imp)
                          | mod <- imports, imp <- modCoreImports mod,
                            isPublic (Core.importVis imp), not (Core.isCompilerImport imp),
                            not (Core.importName imp `elem` alreadyDone)]
       if null extras
         then return imports
         else do extraImports <- moduleWaitForPubImports tcheckedMap alreadyDone extras
                 return (extraImports ++ imports)

-- Return all (user and pub) core imports for a list of user imported modules.
-- (needs the original lexical user imports as well to determine provenance and visibility)
coreImportsFromModules :: [LexImport] -> [Module] -> [Core.Import]
coreImportsFromModules lexImports modules
  = [Core.Import (modName mod) ""
      (getProvenance (modName mod))
      (getVisibility (modName mod))
      (case modCore mod of                   -- careful: need to be strict enough or we hang on to the entire "modCore mod" !
        Just core -> Core.coreProgDoc core
        Nothing -> "")
    | mod <- modules ]
  where
    getVisibility modname
      = case find (\imp -> lexImportName imp == modname) lexImports of
          Just imp -> lexImportVis imp
          _        -> Private

    getProvenance modname
      = case find (\imp -> lexImportName imp == modname) lexImports of
          Just imp -> Core.ImportUser
          _        -> Core.ImportPub



{---------------------------------------------------------------
  Parse a module
---------------------------------------------------------------}

moduleParse :: ModuleMap -> Module -> Build Module
moduleParse tparsedMap
  = moduleGuard PhaseLexed PhaseParsed tparsedMap id id return $ \done mod ->
    do  flags <- getFlags
        phase "parse" $ \penv -> text (if verbose flags > 1 || isAbsolute (modSourceRelativePath mod)
                                        then modSourcePath mod
                                        else ".../" ++ modSourceRelativePath mod)
        case checkError (parseProgramFromLexemes (modSource mod) (modLexemes mod)) of
          Left errs
            -> done mod{ modPhase  = PhaseParsedError
                       , modErrors = mergeErrors errs (modErrors mod)
                       }
          Right (prog,warns)
            -> do penv <- getPrettyEnv
                  let err = if not (reverse (show (programName prog)) `isPrefixOf` reverse (show (modName mod)))
                             then errorsSingle $ errorMessageKind ErrStatic (programNameRange prog) $
                                                 text "the module name" <+> TP.ppName penv (programName prog) <+>
                                                 text "is not a suffix of the expected name" <+> TP.ppName penv (modName mod)
                             else errorsNil
                  done mod{ modPhase   = PhaseParsed
                          , modErrors  = mergeErrors warns (mergeErrors err (modErrors mod))
                          , modProgram = Just $! prog{ programName = modName mod }  -- todo: test suffix!
                          }


-- Add roots to a build context
buildcAddRootSources :: [FilePath] -> BuildContext -> Build (BuildContext,[ModuleName])
buildcAddRootSources fpaths buildc
  = do mods <- mapM moduleFromSource fpaths
       let rootNames = map modName mods
           roots   = nub (map modName mods ++ buildcRoots buildc)
           modules = mergeModulesLeftBias (buildcModules buildc) mods
           buildc' = buildc{ buildcRoots = seqqList roots, buildcModules = seqqList modules }
       seqList rootNames $ seq buildc' $
        return (buildc', rootNames)

-- Reset a build context from the roots (for example, when the flags have changed)
buildcFreshFromRoots :: BuildContext -> Build BuildContext
buildcFreshFromRoots buildc
  = do let (roots,imports) = buildcSplitRoots buildc
           rootSources = map modSourcePath roots
       flags <- getFlags
       (buildc1,_) <- buildcAddRootSources rootSources (buildc{ buildcRoots = [], buildcModules=[], buildcHash = flagsHash flags })
       let (roots1,_) = buildcSplitRoots buildc1
       mods  <- modulesReValidate False [] [] roots1
       return $! buildc1{ buildcModules = seqqList mods }

-- Validate a build context to the current state of the file system and flags,
-- and resolve any required modules to build the root set. Also discards
-- any cached modules that are no longer needed.
-- Can pass a boolean to force everything to be rebuild (on a next build)
-- or a list of specific modules to be recompiled.
buildcValidate :: Bool -> [ModuleName] -> BuildContext -> Build BuildContext
buildcValidate rebuild forced buildc
  = do flags <- getFlags
       let hash = flagsHash flags
       if (hash /= buildcHash buildc)
         then buildcFreshFromRoots buildc
         else do let (roots,imports) = buildcSplitRoots buildc
                 mods <- modulesReValidate rebuild forced imports roots
                 return $! buildc{ buildcModules = seqqList mods }

-- Return the root modules and their (currently cached) dependencies.
buildcSplitRoots :: BuildContext -> ([Module],[Module])
buildcSplitRoots buildc
  = let (xs,ys) = partition (\m -> modName m `elem` buildcRoots buildc) (buildcModules buildc)
    in seqList xs $ seqList ys $ (xs,ys)


-- Type check the current build context (also validates and resolves)
buildcTypeCheck :: [ModuleName] -> BuildContext -> Build BuildContext
buildcTypeCheck force buildc0
  = do buildc <- buildcValidate False force buildc0
       mods   <- modulesTypeCheck (buildcModules buildc)
       return $! buildc{ buildcModules = seqqList $ mods }

{---------------------------------------------------------------
  Given a set of modules,
  return all required modules in build order
---------------------------------------------------------------}

-- given a root set of modules, and a list of previously loaded modules (for reuse),
-- load- or parse all required modules to compile the root set.
-- needs also `rebuild` and `forced` to know whether re-parse or load from an interface file
-- to determine dependencies
modulesResolveDependencies :: Bool -> [ModuleName] -> [Module] -> [Module] -> Build [Module]
modulesResolveDependencies rebuild forced cached roots
  = do ordered <- -- phaseTimed "resolving" (list (map (pretty . modName) roots)) $
                  modulesResolveDeps rebuild forced cached roots []
       return ordered

modulesResolveDeps :: Bool -> [ModuleName] -> [Module] -> [Module] -> [Module] -> Build [Module]
modulesResolveDeps rebuild forced cached roots acc
  = do lroots     <- mapConcurrentModules (moduleLoad rebuild forced) roots    -- we can concurrently load (and lex) modules
       let loaded = lroots ++ acc
       newimports <- nubBy (\m1 m2 -> modName m1 == modName m2) <$> concat <$>
                     mapM (addImports loaded) lroots
       if (null newimports)
         then do ordered <- toBuildOrder loaded    -- all modules in build order
                 validateDependencies ordered      -- now bottom-up reload also modules whose dependencies have updated
                                                   -- so, we have have optimistically loaded an (previously compiled) interface
                                                   -- for its dependencies, but then discover one of its dependencies has changed,
                                                   -- in which case we need to load from source anyways. (This is still good as any
                                                   -- definitions from the interface etc. will stay even if there are compilation
                                                   -- errors which helps for the IDE.)
         else do -- phaseVerbose 2 "resolve" $ \penv -> list (map (TP.ppName penv . modName) newimports)
                 modulesResolveDeps rebuild forced cached newimports loaded  -- keep resolving until all have been loaded
  where
    addImports loaded mod
      = catMaybes <$> mapM (addImport . lexImportName) (modDeps mod)
      where
        addImport :: ModuleName -> Build (Maybe Module)
        addImport impName
          = if any (\m -> modName m == impName) loaded  -- already done?
              then return Nothing
              else case find (\m -> modName m == impName) cached of   -- do we already have this module cached?
                     Just mod  -> do return (Just mod)
                     _         -> do let relativeDir = dirname (modSourcePath mod)
                                     m <- moduleFromModuleName relativeDir impName
                                     return (Just m)

-- order the loaded modules in build order (by using scc)
toBuildOrder :: [Module] -> Build [Module]
toBuildOrder modules
  = -- todo: might be faster to check if the modules are already in build order before doing a full `scc` ?
    let deps    = [(modName mod, map lexImportName (modDeps mod)) | mod <- modules]
        ordered = scc deps
        ungroup [mname]  | Just mod <- find (\m -> modName m == mname) modules  = return [mod]
        ungroup grp      = do throwErrorKind ErrBuild (\penv -> text "recursive imports:" <+> list (map (TP.ppName penv) grp))
                              return []
    in do phaseVerbose 3 "build order" $ \penv -> list (map (\grp -> hsep (map (TP.ppName penv) grp)) ordered)
          concat <$> mapM ungroup ordered

-- validate that dependencies of a module are not out-of-date
-- modules must be in build order
validateDependencies :: [Module] -> Build [Module]
validateDependencies modules
  = do mods <- foldM validateDependency [] modules
       return (reverse mods)
  where
    validateDependency :: [Module] -> Module -> Build [Module]
    validateDependency visited mod
      = if (modPhase mod < PhaseLexed || null (modDeps mod))
          then return (mod:visited)
          else let imports = map lexImportName (modDeps mod)
                   phases  = map (\iname -> case find (\m -> modName m == iname) visited of
                                              Just m -> modPhase m
                                              _      -> PhaseInit) imports
               in if (minimum phases < modPhase mod)
                    then -- trace ("invalidated: " ++ show (modName mod)) $
                         do mod' <- moduleLoad True [] mod
                            return (mod' : visited)
                    else return (mod : visited)

-- Flush all stored errors to the build monad (and reset stored errors per module)
modulesFlushErrors :: [Module] -> Build [Module]
modulesFlushErrors modules
  = mapM moduleFlushErrors modules

moduleFlushErrors :: Module -> Build Module
moduleFlushErrors mod
  = -- trace ("flush errors: " ++ show (modPhase mod, modName mod) ++ ", " ++ show (modErrors mod)) $
    do addErrors (modErrors mod)
       return mod -- keep errors for the IDE diagnostict  -- mod{ modErrors = errorsNil }


{---------------------------------------------------------------
  Parse modules from source, or load from an interface file
  After this, `modDeps` should be valid
---------------------------------------------------------------}

moduleLoad :: Bool -> [ModuleName] -> Module -> Build Module
moduleLoad rebuild forced mod0
  = do mod <- moduleValidate mod0  -- check file times
       let force = (rebuild || modName mod `elem` forced || isErrorPhase (modPhase mod))
       if (modPhase mod >= PhaseLexed) && not force
          then return mod
          else -- trace ("reloading " ++ show (modName mod) ++ ", forced: " ++ show forced) $
               do (mod',errs) <- checkedDefault mod $ -- on error, return the original module
                                 if not (null (modLibIfacePath mod)) && (modIfaceTime mod < modLibIfaceTime mod) && not force
                                   then moduleLoadLibIface mod
                                   else if (modSourceTime mod < modIfaceTime mod) && not force
                                     then moduleLoadIface mod
                                     else moduleLex mod
                  return mod'{ modErrors = mergeErrors errs (modErrors mod') }




moduleLex :: HasCallStack => Module -> Build Module
moduleLex mod
  = do flags <- getFlags
       phaseVerbose 2 "scan" $ \penv -> text (if verbose flags > 1 || isAbsolute (modSourceRelativePath mod)
                                                  then modSourcePath mod
                                                  else ".../" ++ modSourceRelativePath mod)
       let allowAt = True -- isPrimitiveModule (modName mod) || modSourcePath mod `endsWith` "/@main.kk"
       input <- getFileContents (modSourcePath mod)
       let source  = Source (modSourcePath mod) input
           lexemes = lexSource allowAt (semiInsert flags) id 1 source
       case checkError (parseDependencies source lexemes) of
         Left errs
            -> return mod{ modPhase  = PhaseInit
                         , modErrors = errs
                         , modSource = source
                         }
         Right (imports,warns)
            -> return mod{ modPhase   = PhaseLexed
                         , modStatus = LoadedSource
                         , modErrors  = warns
                         , modSource  = source
                         , modLexemes = lexemes
                         , modDeps    = seqqList $ lexImportNub $
                                        [LexImport (importFullName imp) (importName imp) (importVis imp) (importOpen imp) | imp <- imports]
                         }


moduleLoadIface :: Module -> Build Module
moduleLoadIface mod
  = do phase "load" $ \penv -> TP.ppName penv (modName mod)
       (core,parseInlines) <- liftIOError $ parseCore (modIfacePath mod) (modSourcePath mod)
       return (modFromIface core parseInlines mod)

moduleLoadLibIface :: Module -> Build Module
moduleLoadLibIface mod
  = do cscheme <- getColorScheme
       phase "load" $ \penv -> TP.ppName penv (modName mod) <+> color (colorInterpreter cscheme) (text "from:") <+> text (modLibIfacePath mod)
       (core,parseInlines) <- liftIOError $ parseCore (modLibIfacePath mod) (modSourcePath mod)
       flags   <- getFlags
       pooledIO $ copyLibIfaceToOutput flags (modLibIfacePath mod) (modIfacePath mod) core
       ftIface <- getFileTime (modIfacePath mod) -- update interface time or we load from that next time around
       return (modFromIface core parseInlines mod){ modLibIfaceTime = ftIface }

modFromIface :: Core.Core -> Maybe (Gamma -> Error () [Core.InlineDef]) -> Module -> Module
modFromIface core parseInlines mod
  =  mod{ modPhase       = case parseInlines of
                             Nothing -> PhaseLinked
                             Just f  -> PhaseIfaceLoaded
        , modErrors      = errorsNil
        , modSource      = sourceNull
        , modDeps        = seqqList $ [LexImport (Core.importName imp) nameNil (Core.importVis imp) False {- @open -}
                                       | imp <- Core.coreProgImports core, not (Core.isCompilerImport imp) ]
        , modStatus      = LoadedIface
        , modCore        = Just $! core
        , modDefinitions = Just $! defsFromCore False core
        , modInlines     = case parseInlines of
                             Nothing -> Right []
                             Just f  -> Left f
        }

copyLibIfaceToOutput :: Flags -> FilePath -> FilePath -> Core.Core -> IO ()
copyLibIfaceToOutput flags libIfacePath ifacePath core  {- core is needed to know imported clibs etc. -}
  = do let withext fname ext = notext fname ++ ext
           force = rebuild flags
       copyTextIfNewer force libIfacePath ifacePath
       case target flags of
        CS    -> do copyBinaryIfNewer force (withext libIfacePath dllExtension) (withext ifacePath dllExtension)
        JS _  -> do copyTextIfNewer force (withext libIfacePath ".mjs") (withext ifacePath ".mjs")
        C _   -> do copyTextIfNewer force (withext libIfacePath ".c") (withext ifacePath ".c")
                    copyTextIfNewer force (withext libIfacePath ".h") (withext ifacePath ".h")
                    let cc = ccomp flags
                    copyBinaryIfNewer force (ccObjFile cc (notext libIfacePath)) (ccObjFile cc (notext ifacePath))
                    mapM_ (\clib -> do let libFile = ccLibFile cc clib
                                       -- todo: only copy if it exists?
                                       copyBinaryIfNewer force (joinPath (dirname libIfacePath) libFile)
                                                               (joinPath (dirname ifacePath) libFile)
                          ) (clibsFromCore flags core)


clibsFromCore :: Flags -> Core -> [String]
clibsFromCore flags core
  = externalImportKeyFromCore (target flags) (buildType flags) core "library"

csyslibsFromCore :: Flags -> Core -> [String]
csyslibsFromCore flags core
  = externalImportKeyFromCore (target flags) (buildType flags) core "syslib"


externalImportKeyFromCore :: Target -> BuildType -> Core.Core -> String -> [String]
externalImportKeyFromCore target buildType core key
  = catMaybes [Core.eimportLookup buildType key keyvals  | keyvals <- externalImportsFromCore target core]

externalImportsFromCore :: Target -> Core.Core -> [[(String,String)]]
externalImportsFromCore target core
  = [keyvals  | Core.ExternalImport imports _ <- Core.coreProgExternals core, (target,keyvals) <- imports]


{---------------------------------------------------------------
  Create initial empty modules
  from a source path (from IDE) or module name (from an import)
---------------------------------------------------------------}

moduleFromSource :: FilePath -> Build Module
moduleFromSource fpath0
  = do let fpath = normalize fpath0
       mbpath <- searchSourceFile "" fpath
       case mbpath of
         Nothing          -> throwFileNotFound fpath
         Just (root,stem) -> do let stemParts  = splitPath (noexts stem)
                                    sourcePath = if null root then stem   -- on wsl2: ("","/@virtual///wsl.localhost/...")
                                                              else joinPath root stem
                                modName <- if isAbsolute stem || any (not . isValidId) stemParts
                                            then case reverse stemParts of
                                                    (base:_)  | isValidId base
                                                      -> return (newModuleName base)  -- module may not be found if imported
                                                    _ -> throwErrorKind ErrBuild (\penv -> text ("file path cannot be mapped to a valid module name: " ++ sourcePath))
                                            else return (newModuleName (noexts stem))
                                ifacePath <- outputName (moduleNameToPath modName ++ ifaceExtension)
                                -- trace ("moduleFromSource: " ++ show (root,stem,sourcePath,ifacePath)) $
                                moduleValidate $ (moduleCreateInitial modName sourcePath ifacePath ""){ modSourceRelativePath = stem }
  where
    isValidId :: String -> Bool  -- todo: make it better
    isValidId ""      = False
    isValidId (c:cs)  = (isLower c || c=='@') && all (\c -> isAlphaNum c || c `elem` "_-@") cs


moduleFromModuleName :: FilePath -> Name -> Build Module
moduleFromModuleName relativeDir modName
  = -- trace ("moduleFromModuleName: " ++ show modName ++ ", relative dir: " ++ relativeDir) $
    do mbSourceName <- searchSourceFile relativeDir (nameToPath modName ++ sourceExtension)
       ifacePath    <- outputName (moduleNameToPath modName ++ ifaceExtension)
       libIfacePath <- searchLibIfaceFile (moduleNameToPath modName ++ ifaceExtension)
       case mbSourceName of
         Just (root,stem)
            -> moduleValidate $ (moduleCreateInitial modName (joinPath root stem) ifacePath libIfacePath){ modSourceRelativePath = stem }
         Nothing
            -> do ifaceExist <- buildDoesFileExistAndNotEmpty ifacePath
                  if ifaceExist
                    then do cs <- getColorScheme
                            addWarningMessage (warningMessageKind ErrBuild rangeNull (text "interface" <+> color (colorModule cs) (pretty modName) <+> text "found but no corresponding source module"))
                            moduleValidate $ moduleCreateInitial modName "" ifacePath libIfacePath
                    else throwModuleNotFound rangeNull modName

-- Find a source file and resolve it
-- with a `(root,stem)` where `stem` is the minimal module path relative to the include roots.
-- The root is either in the include paths or the full directory for absolute paths.
-- (and absolute file paths outside the include roots always have a single module name corresponding to the file)
-- relativeDir is set when importing from a module so a module name is first resolved relative to the current module
searchSourceFile :: FilePath -> FilePath -> Build (Maybe (FilePath,FilePath))
searchSourceFile relativeDir fname
  = do -- trace ("search source: " ++ fname ++ " from " ++ concat (intersperse ", " (relativeDir:includePath flags))) $ return ()
       flags <- getFlags
       mb <- lookupVFS fname
       case mb of  -- must match exactly; we may improve this later on and search relative files as well?
         Just _ -> if fname `startsWith` (virtualMount ++ "///") -- just for wsl paths :-( TODO: fix this in general
                     then let (root,stem) = getMaximalPrefixPath (virtualMount : includePath flags) fname
                          in return $! Just $! if root == virtualMount
                               then ("",fname)     -- maintain wsl2 paths: ("","/@virtual///wsl.localhost/...")
                               else (root,stem)
                     else return $! Just $! (getMaximalPrefixPath (virtualMount : includePath flags) fname)
         _      -> -- trace ("searchSourceFile: relativeDir: " ++ relativeDir) $
                   liftIO $ searchPathsCanonical relativeDir (includePath flags) [sourceExtension,sourceExtension++".md"] [] fname

virtualStrip path
  = if path `startsWith` (virtualMount ++ "/") then drop (length virtualMount + 1) path else path

virtualMount
  = "/@virtual"


-- find a pre-compiled libary interface
-- in the future we can support packages as well
searchLibIfaceFile :: FilePath -> Build FilePath  -- can be empty
searchLibIfaceFile fname
  = do flags <- getFlags
       let libIfacePath = joinPaths [localLibDir flags, buildLibVariant flags, fname]  -- lib variant is without a hash
       exist <- buildDoesFileExist libIfacePath
       return (if exist then libIfacePath else "")


{---------------------------------------------------------------
  Validate if modules are still valid
---------------------------------------------------------------}
{-
modulesValidate :: [Module] -> Build [Module]
modulesValidate modules
  = mapM moduleValidate modules
-}

moduleValidate :: Module -> Build Module
moduleValidate mod
  = do ftSource   <- getFileTime (modSourcePath mod)
       ftIface    <- getFileTime (modIfacePath mod)
       ftLibIface <- getFileTime (modLibIfacePath mod)
       let stale = (ftSource > modSourceTime mod ||
                    ftIface > modIfaceTime mod ||
                    ftLibIface > modLibIfaceTime mod)
           mod'  = mod{ modSourceTime = ftSource
                      , modIfaceTime  = ftIface
                      , modLibIfaceTime = ftLibIface
                      }
       phaseVerbose 3 "validate" (\penv -> TP.ppName penv (modName mod') <.> text (": times: " ++ show (stale,ftSource,modSourceTime mod)))
       if stale
         then return $ moduleReset mod'
         else return mod'

moduleReset :: Module -> Module
moduleReset mod
  = mod{ modPhase = PhaseInit,
         modErrors = errorsNil,
         -- reset fields that are not used by an IDE to reduce memory pressure
         -- leave lexemes, rangeMap, and definitions. todo: maybe don't cache definitions at all?
         modSource = sourceNull,
         modProgram = Nothing,
         modCore    = case modCore mod of
                        Just core -> Just $! coreReset core
                        Nothing   -> Nothing,
         modInlines = Right [],
         modEntry   = Nothing
      }

coreReset :: Core -> Core
coreReset core
  = core{ coreProgDefs = seqqList [defGroupReset dg  | dg <- coreProgDefs core] }
  where
    defGroupReset dg
      = case dg of
          Core.DefRec defs    -> Core.DefRec (seqqList (map defReset defs))
          Core.DefNonRec def  -> Core.DefNonRec (defReset def)
    defReset def
      = def{ Core.defExpr = Core.exprUnit }


{---------------------------------------------------------------
  Helpers
---------------------------------------------------------------}

throwModuleNotFound :: Range -> Name -> Build a
throwModuleNotFound range name
  = do flags <- getFlags
       throwError (\penv -> errorMessageKind ErrBuild range (errorNotFound flags colorModule "module" (pretty name)))

throwFileNotFound :: FilePath -> Build a
throwFileNotFound name
  = do flags <- getFlags
       throwError (\penv -> errorMessageKind ErrBuild rangeNull (errorNotFound flags colorSource "" (text name)))

errorNotFound flags clr kind namedoc
  = text ("could not find" ++ (if null kind then "" else (" " ++ kind)) ++ ":") <+> color (clr cscheme) namedoc <->
    text "search path:" <+> prettyIncludePath flags
  where
    cscheme = colorSchemeFromFlags flags

-- name to path preserves '/' while moduleNameToPath uses '_' for '/'
nameToPath :: Name -> FilePath
nameToPath name
  = show name

outputName :: FilePath -> Build FilePath
outputName fpath
  = do flags <- getFlags
       return $ outName flags fpath

ifaceExtension :: FilePath
ifaceExtension
  = sourceExtension ++ "i"
