-----------------------------------------------------------------------------
-- Copyright 2012-2024, Microsoft Research, Daan Leijen.
--
-- This is free software; you can redistribute it and/or modify it under the
-- terms of the Apache License, Version 2.0. A copy of the License can be
-- found in the LICENSE file at the root of this distribution.
-----------------------------------------------------------------------------
module Compile.BuildMonad( 
  BuildContext(..), buildcLookupModule,
  Build, VFS(..), noVFS, lookupVFS,
  runBuildMaybe, runBuildIO, runBuild
    , phase, phaseVerbose, phaseTimed
    , throwError, throwErrorKind
    , throwOnError, hasBuildError, throwNil
    , liftIO, liftError, liftIOError, checkedDefault, addErrors
    , getFlags, getPrettyEnv, getTerminal, getColorScheme
    , addErrorMessageKind, addWarningMessage
    , withVFS
    , withTotalWork, workNeeded, onBuildException, buildFinally
    , phaseCompleted
    , sequentialIO, pooledIO
    , getFileContents, getFileTime, buildDoesFileExist, buildDoesFileExistAndNotEmpty
    , mapConcurrentModules
  ) where

import Compile.Module
import Common.Name
import Compile.Options
import Control.Concurrent (Chan, QSem)
import Control.Concurrent.MVar (MVar)
import Common.Error (Errors (..), Error, ErrorMessage (..), ErrorKind (..), errorMessageKind, errorsSingle, ErrorSeverity (..), errorsNil, mergeErrors, checkError)
import Control.Exception (ErrorCall, catch)
import Control.Exception.Base (IOException, SomeException)
import qualified Control.Monad.Fail as F
import qualified Type.Pretty as TP
import Lib.PPrint
import Common.Range (BString, Range (..), Pos (..), Ranged (getRange), rangeNull, makeSourceRange, bstringIsEmpty)
import Common.File (FileTime, getCurrentTime, showTimeDiff, normalize, endsWith, doesFileExistAndNotEmpty, fileTime0, seqqMaybe)
import Common.ColorScheme (ColorScheme (..))
import Common.Failure (HasCallStack, failure)
import Data.IORef (IORef)
import Control.Exception (throw)
import Data.Maybe (isJust)
import Data.List (find)
import GHC.IORef (readIORef, atomicSwapIORef)
import Control.Concurrent
import Data.IORef
import Control.Exception (finally)
import Control.Monad (when, ap)
import Data.Either (rights, lefts)
import Control.Concurrent.Async (mapConcurrently)
import Control.Exception (onException)
import Data.Char
import System.Directory (doesFileExist)
import qualified Common.File as F
import Syntax.Lexer (readInput)

{---------------------------------------------------------------
  Compilation monad
  carries flags and terminal and catches errors
---------------------------------------------------------------}
data VFS = VFS { vfsFind :: FilePath -> Maybe (BString,FileTime) }

noVFS :: VFS
noVFS = VFS (\fpath -> Nothing)

composeVFS :: VFS -> VFS -> VFS
composeVFS (VFS find1) (VFS find2)
  = VFS (\fpath -> case find2 fpath of
                     Just res -> Just res
                     Nothing  -> find1 fpath)


-- Return a module by name
buildcLookupModule :: HasCallStack => ModuleName -> BuildContext -> Maybe Module
buildcLookupModule modname buildc
  = seqqMaybe $ find (\mod -> modName mod == modname) (buildcModules buildc)

-- An abstract build context contains all information to build
-- from a set of root modules (open files in an IDE, compilation files on a command line)
-- It checks it validity against the flags it was created from.
data BuildContext = BuildContext {
                      buildcRoots   :: ![ModuleName],
                      buildcModules :: ![Module],
                      buildcHash    :: !String
                    }


data Build a = Build (Env -> IO a)

data Env = Env { envTerminal :: !Terminal,
                 envFlags    :: !Flags,
                 envVFS      :: !VFS,
                 envModName  :: !ModuleName,     -- for better error reporting
                 envErrors   :: !(IORef Errors), -- we use fresh IORef's if mapping concurrently
                 envWork     :: !Int,            -- total amount of work units to do (usually a phase is 1 unit)
                 envWorkDone :: !(IORef Int),    -- current total of work completed
                 envSemPooled     :: !QSem,      -- limit I/O concurrency
                 envSemSequential :: !QSem       -- limit some I/O to be atomic
               }

-- Execute an action assuming a certain amount of work to be done
withTotalWork :: Int -> Build a -> Build a
withTotalWork total build
  = seq total $ withEnv (\env -> env{ envWork = total }) $
    do env <- getEnv
       old <- liftIO $ atomicSwapIORef (envWorkDone env) 0
       x   <- build
       liftIO $ atomicModifyIORef' (envWorkDone env) (\i -> (i + old,()))
       return x


-- work units needed to complete a compilation
workNeeded :: ModulePhase -> [Module] -> Int
workNeeded maxPhase modules
  = phaseTotalWork maxPhase * length modules

-- total work units to reach a target phase
phaseTotalWork :: ModulePhase -> Int
phaseTotalWork maxPhase
  = case dropWhile (\(phase,_) -> maxPhase > phase) workAmounts of
      ((phase,n):_) -> n
      _             -> failure "Compile.Build.phaseWork: invalid max phase"
  where
    workAmounts
      = accumulate 0 [PhaseParsed,PhaseTyped,PhaseOptimized,PhaseCodeGen,PhaseLinked]

    accumulate n [] = []
    accumulate n (phase:phases)
      = let m = n + phaseWorkUnit phase
        in (phase,m) : accumulate m phases

-- work for a single step to a target phase
phaseWorkUnit :: ModulePhase -> Int
phaseWorkUnit phase
  = case phase of
      PhaseTyped          -> 2
      PhaseLinked         -> 3
      _                   -> 1

-- Finishes a target phase unit of work and reports it via the termProgress printer
phaseCompleted :: ModulePhase -> Build ()
phaseCompleted targetPhase = do
  env <- getEnv
  liftIO $ atomicModifyIORef' (envWorkDone env) (\i -> (i + phaseWorkUnit targetPhase, ()))
  progress <- getWorkProgress
  liftIO $ termProgress (envTerminal env) (progress, Just (text (phaseProgress targetPhase)))

-- Gets the work done as a percentage
getWorkProgress :: Build Double
getWorkProgress = do
  env <- getEnv
  workDone <- liftIO $ readIORef (envWorkDone env)
  return ((fromIntegral workDone) / (fromIntegral (envWork env)))

runBuildMaybe :: Terminal -> Flags -> Build (Maybe a) -> IO (Maybe a)
runBuildMaybe term flags action
  = do (mbRes,_) <- runBuildIO term flags False action
       case mbRes of
         Just res -> return res
         Nothing  -> return Nothing

runBuildIO :: Terminal -> Flags -> Bool -> Build a -> IO (Maybe a,Maybe Range)
runBuildIO term flags showM build
  = do res <- runBuild term flags build
       let getErrRange errs  = case reverse (errors errs) of
                                 (err:_) -> Just (getRange err)
                                 _       -> Nothing
       case res of
         Right (x,errs) -> do let erng = getErrRange errs
                              when showM $ showMarker term flags erng
                              mapM_ (termError term) (take (maxErrors flags) (errors errs))
                              return (Just x, getErrRange errs)
         Left errs      -> do let erng = getErrRange errs
                              when showM $ showMarker term flags erng
                              mapM_ (termError term) (take (maxErrors flags) (errors errs))
                              return (Nothing, getErrRange errs)
  where
    -- Show a marker in the interpreter
    showMarker :: Terminal -> Flags -> Maybe Range -> IO ()
    showMarker term flags Nothing = return ()
    showMarker term flags (Just rng)
      = do let c1 = posColumn (rangeStart rng)
               c2 = if (posLine (rangeStart rng) == posLine (rangeStart rng))
                     then posColumn (rangeEnd rng)
                     else c1
           let cscheme = colorSchemeFromFlags flags
           let doc     = color (colorMarker cscheme) (text (replicate (c1 - 1) ' ' ++ replicate 1 {- (c2 - c1 + 1) -} '^'))
           termInfo term doc


runBuild :: Terminal -> Flags -> Build a -> IO (Either Errors (a,Errors))
runBuild term flags cmp
  = do errs <- newIORef errorsNil
       semPooled     <- newQSem (min 64 (max 1 (maxConcurrency flags)))
       semSequential <- newQSem 1
       termProxyDone <- newEmptyMVar
       (termProxy,stop) <- forkTerminal term termProxyDone
       workDone      <- newIORef 0
       finally (runBuildEnv (Env termProxy flags noVFS nameNil errs 0 workDone semPooled semSequential) cmp)
               (do stop
                   readMVar termProxyDone)


-- Fork off a thread to handle output from other threads so it is properly interleaved
forkTerminal :: Terminal -> MVar () -> IO (Terminal, IO ())
forkTerminal term termProxyDone
  = do ch <- newChan
       forkIO (handleOutput ch `finally` putMVar termProxyDone ())
       let termProxy = Terminal (writeChan ch . Just . termError term)
                                (writeChan ch . Just . termTrace term)
                                (writeChan ch . Just . termProgress term)
                                (writeChan ch . Just . termPhase term)
                                (writeChan ch . Just . termInfo term)
       return (termProxy, writeChan ch Nothing)
  where
    handleOutput :: Chan (Maybe (IO ())) -> IO ()
    handleOutput ch
      = do mbf <- readChan ch
           case mbf of
             Nothing -> do return ()
             Just io -> do io `catchAny` \err -> termError term (errorMessageKind ErrGeneral rangeNull (text (show err)))
                           handleOutput ch




runBuildEnv :: Env -> Build a -> IO (Either Errors (a,Errors))
runBuildEnv env action
  = case checked action of
      Build cmp -> cmp env


checked :: Build a -> Build (Either Errors (a,Errors))
checked (Build cmp)
  = Build   (\env0 ->do errsRef <- newIORef errorsNil
                        let env = env0{ envErrors = errsRef }
                        res <- do{ x <- cmp env; return (Right x) }
                               `catch` (\errs -> return (Left errs)) -- ErrorMessage's
                               `catchError` (\err -> makeErr env ErrInternal (show err))  -- error(...)
                               `catchIO` (\exn -> makeErr env ErrBuild (show exn))  -- IO errors
                        errsw <- readIORef errsRef
                        writeIORef errsRef errorsNil
                        case res of
                          Right x    -> return (Right (x,errsw))
                          Left errs  -> return (Left (mergeErrors errsw errs))
            )
  where
    makeErr env errKind msg
      = do let rng = makeSourceRange (show (envModName env)) 1 1 1 1
           return (Left (errorsSingle (errorMessageKind errKind rng (text msg))))

checkedDefault :: a -> Build a -> Build (a,Errors)
checkedDefault def action
  = do res <- checked action
       case res of
         Left errs      -> return (def,errs)
         Right (x,errs) -> return (x,errs)


catchError :: IO a -> (ErrorCall -> IO a) -> IO a
catchError io f
  = io `catch` f


catchIO :: IO a -> (IOException -> IO a) -> IO a
catchIO io f
  = io `catch` f


catchAny :: IO a -> (SomeException -> IO a) -> IO a
catchAny io f
  = io `catch` f

liftIO :: IO a -> Build a
liftIO io = Build (\env -> io)

liftIOError :: IO (Error () a) -> Build a
liftIOError io
  = do res <- liftIO io
       liftError res

liftError :: Error () a -> Build a
liftError res
  = case checkError res of
      Left errs       -> throw errs
      Right (x,warns) -> do addErrors warns
                            return x

-- map concurrently and merge (and rethrow) all errors
mapConcurrent :: (a -> Build b) -> [a] -> Build [b]
mapConcurrent f xs
  = do env <- getEnv
       flags <- getFlags
       ys  <- if (maxConcurrency flags <= 1)
                then liftIO $ mapM (\x -> runBuildEnv env (f x)) xs
                else liftIO $ mapConcurrently (\x -> runBuildEnv env (f x)) xs
       let errs = lefts ys
       if null errs
         then do let (zs,warns) = unzip (rights ys)
                 mapM_ addErrors warns
                 return zs
         else throw (foldr mergeErrors errorsNil errs)

-- pooled is used for I/O operations that need to be limited in total concurrency
pooledIO :: IO a -> Build a
pooledIO io
  = do env <- getEnv
       liftIO $ withSem (envSemPooled env) io

sequentialIO :: Build (IO a -> IO a)
sequentialIO
  = do env <- getEnv
       return (withSem (envSemSequential env))

withSem :: QSem -> IO a -> IO a
withSem sem io
  = do waitQSem sem
       io `finally` signalQSem sem


-- map concurrently and keep errors in the processed module
mapConcurrentModules :: (Module -> Build Module) -> [Module] -> Build [Module]
mapConcurrentModules f modules
  = mapConcurrent (\mod -> withCheckedModule mod (f mod)) modules


instance Functor Build where
  fmap f (Build ie)  = Build (\env -> fmap f (ie env))

instance Applicative Build where
  pure x = seq x (Build (\env -> return x))
  (<*>)  = ap

instance Monad Build where
  -- return = pure
  (Build ie) >>= f
    = Build (\env -> do x <- ie env
                        case (f x) of
                          Build ie' -> ie' env)

instance F.MonadFail Build where
  fail msg = throwError (\penv -> errorMessageKind ErrGeneral rangeNull (text msg))

onBuildException :: Build b -> Build a -> Build a
onBuildException (Build onExn) (Build b)
  = Build (\env -> (b env) `onException` (onExn env))

buildFinally :: Build b -> Build a -> Build a
buildFinally (Build fin) (Build b)
  = Build (\env -> finally (b env) (fin env))

throwError :: (TP.Env -> ErrorMessage) -> Build a
throwError msg
  = do penv <- getPrettyEnv
       liftIO $ throw (errorsSingle (msg penv))

throwErrorKind :: ErrorKind -> (TP.Env -> Doc) -> Build a
throwErrorKind ekind doc
  = do rng <- getCurrentRange
       throwError (\penv -> errorMessageKind ekind rng (doc penv))

getEnv :: Build Env
getEnv
  = Build (\env -> return env)

withEnv :: (Env -> Env) -> Build a -> Build a
withEnv modify (Build action)
  = Build (\env -> action (modify env))

withVFS :: VFS -> Build a -> Build a
withVFS vfs build
  = withEnv (\env -> env{ envVFS = composeVFS (envVFS env) vfs }) build

lookupVFS :: FilePath -> Build (Maybe (BString,FileTime))
lookupVFS fpath
  = do env <- getEnv
       return (vfsFind (envVFS env) (normalize fpath))

getFlags :: Build Flags
getFlags
  = Build (\env -> return (envFlags env))

getTerminal :: Build Terminal
getTerminal
  = Build (\env -> return (envTerminal env))

getCurrentRange :: Build Range
getCurrentRange
  = do env <- getEnv
       return (makeSourceRange (show (envModName env)) 1 1 1 1)

getColorScheme :: Build ColorScheme
getColorScheme
  = do flags <- getFlags
       return (colorSchemeFromFlags flags)

getPrettyEnv :: Build TP.Env
getPrettyEnv
  = do flags <- getFlags
       env   <- getEnv
       return ((prettyEnvFromFlags flags){ TP.context = envModName env })

hasBuildError :: Build (Maybe Range)
hasBuildError
  = do env  <- getEnv
       errs <- liftIO $ readIORef (envErrors env)
       case find (\err -> errSeverity err >= SevError) (errors errs) of
         Just err -> return (Just (errRange err))
         _        -> return Nothing

throwOnError :: Build ()
throwOnError
  = do errRng <- hasBuildError
       if isJust errRng then throwNil else return ()

throwNil :: Build ()
throwNil
  = liftIO (throw errorsNil)


addErrors :: Errors -> Build ()
addErrors errs0
  = do env <- getEnv
       liftIO $ modifyIORef' (envErrors env) (\errs1 -> mergeErrors errs0 errs1)

addWarningMessage :: ErrorMessage -> Build ()
addWarningMessage warn
  = addErrors (errorsSingle warn)

addErrorMessage :: ErrorMessage -> Build ()
addErrorMessage err
  = addErrors (errorsSingle err)

addErrorMessages :: [ErrorMessage] -> Build ()
addErrorMessages errs
  = addErrors (Errors errs)

addErrorMessageKind :: ErrorKind -> (TP.Env -> Doc) -> Build ()
addErrorMessageKind ekind doc
  = do rng <- getCurrentRange
       penv <- getPrettyEnv
       addErrorMessage (errorMessageKind ekind rng (doc penv))

phaseTimed :: Int -> String -> (TP.Env -> Doc) -> Build a -> Build a
phaseTimed level p doc action
  = do t0 <- liftIO $ getCurrentTime
       phaseVerbose level p doc
       buildFinally (do t1 <- liftIO $ getCurrentTime
                        phaseVerbose level p (\penv -> text (showTimeDiff t1 t0)))
                    action

phase :: String -> (TP.Env -> Doc) -> Build ()
phase p mkdoc
  = do env <- getEnv
       flags <- getFlags
       if (show (envModName env) `endsWith` "@main" && verbose flags <= 1)
         then return ()
         else phaseVerbose 1 p mkdoc

phaseVerbose :: Int -> String -> (TP.Env -> Doc) -> Build ()
phaseVerbose vlevel p doc
  = do flags <- getFlags
       when (verbose flags >= vlevel) $
         phaseShow (verbose flags) p doc

phaseShow :: Int -> String -> (TP.Env -> Doc) -> Build ()
phaseShow v p mkdoc
  = do term    <- getTerminal
       penv    <- getPrettyEnv
       tid     <- liftIO $ myThreadId
       let cscheme = TP.colors penv
           doc = mkdoc penv
           pre = (if isEmptyDoc doc then p else (sfill 8 p ++ ":"))
                 ++ (if v >= 4 then " (thread " ++ showThreadId tid ++ ") " else "")
       liftIO $ termPhase term (color (colorInterpreter cscheme) (text pre) <+> (color (colorSource cscheme) doc))
  where
    showThreadId tid = takeWhile isDigit $ dropWhile (not . isDigit) $ show tid
    sfill n s = s ++ replicate (n - length s) ' '

buildDoesFileExist :: FilePath -> Build Bool
buildDoesFileExist fpath
  = do mb <- lookupVFS fpath
       case mb of
        Just _ -> return True
        _      -> liftIO $ doesFileExist fpath

buildDoesFileExistAndNotEmpty :: FilePath -> Build Bool
buildDoesFileExistAndNotEmpty fpath
  = do mb <- lookupVFS fpath
       case mb of
         Just (content,_) -> return $! not (bstringIsEmpty content)
         _                -> liftIO $ doesFileExistAndNotEmpty fpath

getFileTime :: FilePath -> Build FileTime
getFileTime "" = return fileTime0
getFileTime fpath
  = do mb <- lookupVFS fpath
       case mb of
         Just (_, t) -> return t
         Nothing     -> liftIO $ F.getFileTime fpath

maybeGetFileTime :: FilePath -> Build (Maybe FileTime)
maybeGetFileTime fpath
  = do ft <- getFileTime fpath
       return (if ft == fileTime0 then Nothing else Just ft)

getFileContents :: HasCallStack => FilePath -> Build BString
getFileContents fpath
  = do mb <- lookupVFS fpath
       case mb of
         Just (content, _) -> return content
         Nothing           -> liftIO $ readInput fpath


-- attribute exceptions to a certain module
withModuleName :: ModuleName -> Build a -> Build a
withModuleName mname action
  = withEnv (\env -> env{ envModName = mname }) action

-- catch all errors and keep to them to the module
withCheckedModule :: Module -> Build Module -> Build Module
withCheckedModule mod action
  = withModuleName (modName mod) $
    do res <- checked action
       case res of
         Left errs          -> return mod{ modErrors = mergeErrors errs (modErrors mod) }
         Right (mod',warns) -> return mod'{ modErrors = mergeErrors warns (modErrors mod') }

