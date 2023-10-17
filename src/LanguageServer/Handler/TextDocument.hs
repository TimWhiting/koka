-----------------------------------------------------------------------------
-- The LSP handlers that handle changes to the document
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}

module LanguageServer.Handler.TextDocument
  ( didOpenHandler,
    didChangeHandler,
    didSaveHandler,
    didCloseHandler,
    recompileFile,
  )
where

import Common.Error (checkError, Error)
import Compiler.Compile (Terminal (..), compileModuleOrFile, Loaded (..), CompileTarget (..), compileFile)
import Control.Lens ((^.))
import Control.Monad.Trans (liftIO)
import qualified Data.Map as M
import Data.Maybe (fromJust, fromMaybe)
import qualified Data.Text as T
import Language.LSP.Diagnostics (partitionBySource)
import Language.LSP.Server (Handlers, flushDiagnosticsBySource, publishDiagnostics, sendNotification, getVirtualFile, getVirtualFiles, notificationHandler)
import qualified Language.LSP.Protocol.Types as J
import qualified Language.LSP.Protocol.Lens as J
import LanguageServer.Conversions (toLspDiagnostics)
import LanguageServer.Monad (LSM, modifyLoaded, getLoaded, putLoaded, getTerminal, getFlags, LSState (documentInfos), getLSState, modifyLSState)
import Language.LSP.VFS (virtualFileText, VFS(..), VirtualFile, file_version, virtualFileVersion)
import qualified Data.Text.Encoding as T
import Data.Functor ((<&>))
import qualified Language.LSP.Protocol.Message as J
import Data.ByteString (ByteString)
import Data.Map (Map)
import Text.Read (readMaybe)
import Debug.Trace (trace)
import Control.Exception (try)
import qualified Control.Exception as Exc
import Compiler.Options (Flags)
import Common.File (getFileTime, FileTime, getFileTimeOrCurrent, getCurrentTime)
import GHC.IO (unsafePerformIO)

didOpenHandler :: Handlers LSM
didOpenHandler = notificationHandler J.SMethod_TextDocumentDidOpen $ \msg -> do
  let uri = msg ^. J.params . J.textDocument . J.uri
  let version = msg ^. J.params . J.textDocument . J.version
  flags <- getFlags
  _ <- recompileFile InMemory uri (Just version) False flags
  return ()

didChangeHandler :: Handlers LSM
didChangeHandler = notificationHandler J.SMethod_TextDocumentDidChange $ \msg -> do
  let uri = msg ^. J.params . J.textDocument . J.uri
  let version = msg ^. J.params . J.textDocument . J.version
  flags <- getFlags
  _ <- recompileFile InMemory uri (Just version) False flags
  return ()

didSaveHandler :: Handlers LSM
didSaveHandler = notificationHandler J.SMethod_TextDocumentDidSave $ \msg -> do
  let uri = msg ^. J.params . J.textDocument . J.uri
  flags <- getFlags
  _ <- recompileFile InMemory uri Nothing False flags
  return ()

didCloseHandler :: Handlers LSM
didCloseHandler = notificationHandler J.SMethod_TextDocumentDidClose $ \_msg -> do
  -- TODO: Remove file from LSM state?
  return ()

maybeContents :: Map FilePath (ByteString, FileTime, J.Int32) -> FilePath -> Maybe (ByteString, FileTime)
maybeContents vfs uri = do
  (text, ftime, vers) <- M.lookup uri vfs
  return (text, ftime)

diffVFS :: Map FilePath (ByteString, FileTime, J.Int32) -> Map J.NormalizedUri VirtualFile -> Map FilePath (ByteString, FileTime, J.Int32)
diffVFS oldvfs vfs =
  foldl (\acc (k, v) ->
    let newK = J.fromNormalizedFilePath $ fromJust $ J.uriToNormalizedFilePath k
        text = T.encodeUtf8 $ virtualFileText v
        vers = virtualFileVersion v
    in case M.lookup newK oldvfs of
      Just old@(_, _, vOld) -> if vOld == vers then M.insert newK old acc else M.insert newK (text, unsafePerformIO getCurrentTime, vers) acc
      Nothing -> M.insert newK (text, unsafePerformIO getCurrentTime, vers) acc) M.empty (M.toList vfs)

-- Recompiles the given file, stores the compilation result in
-- LSM's state and emits diagnostics.
recompileFile :: CompileTarget () -> J.Uri -> Maybe J.Int32 -> Bool -> Flags -> LSM (Maybe FilePath)
recompileFile compileTarget uri version force flags =
  case J.uriToFilePath uri of
    Just filePath -> do
      -- Recompile the file
      vFiles <- getVirtualFiles
      let vfs = _vfsMap vFiles
      oldvfs <- documentInfos <$> getLSState
      let newvfs = diffVFS oldvfs vfs
      modifyLSState (\old -> old{documentInfos = newvfs})
      let contents = fst <$> maybeContents newvfs filePath
      loaded1 <- getLoaded
      let modules = do
            l <- loaded1
            return $ loadedModule l : loadedModules l
      term <- getTerminal
      sendNotification J.SMethod_WindowLogMessage $ J.LogMessageParams J.MessageType_Info $ T.pack $ "Recompiling " ++ filePath

      let resultIO :: IO (Either Exc.SomeException (Error (Loaded, Maybe FilePath)))
          resultIO = try $ compileFile (maybeContents newvfs) contents term flags [] (if force then [] else fromMaybe [] modules) compileTarget filePath
      result <- liftIO resultIO
      case result of
        Right res -> do
          outFile <- case checkError res of
            Right ((l, outFile), _) -> do
              putLoaded l
              sendNotification J.SMethod_WindowLogMessage $ J.LogMessageParams J.MessageType_Info $ "Successfully compiled " <> T.pack filePath
              return outFile
            Left e -> do
              sendNotification J.SMethod_WindowLogMessage $ J.LogMessageParams J.MessageType_Error $ T.pack ("Error when compiling " ++ show e) <> T.pack filePath
              return Nothing

          -- Emit the diagnostics (errors and warnings)
          let diagSrc = T.pack "koka"
              diags = toLspDiagnostics diagSrc res
              diagsBySrc = partitionBySource diags
              maxDiags = 100
          if null diags
            then flushDiagnosticsBySource maxDiags (Just diagSrc)
            else publishDiagnostics maxDiags normUri version diagsBySrc
          return outFile
        Left e -> do
          sendNotification J.SMethod_WindowLogMessage $ J.LogMessageParams J.MessageType_Error $ "When compiling file " <> T.pack filePath <> T.pack (" compiler threw exception " ++ show e)
          sendNotification J.SMethod_WindowShowMessage $ J.ShowMessageParams J.MessageType_Error $ "When compiling file " <> T.pack filePath <> T.pack (" compiler threw exception " ++ show e)
          return Nothing
    Nothing -> return Nothing
  where
    normUri = J.toNormalizedUri uri
