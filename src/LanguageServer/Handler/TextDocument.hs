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

import Common.Error (checkError)
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
import LanguageServer.Monad (LSM, modifyLoaded, getLoaded, putLoaded, getTerminal, getFlags)
import Language.LSP.VFS (virtualFileText, VFS(..), VirtualFile)
import qualified Data.Text.Encoding as T
import Data.Functor ((<&>))
import qualified Language.LSP.Protocol.Message as J
import Data.ByteString (ByteString)
import Data.Map (Map)
import Text.Read (readMaybe)
import Debug.Trace (trace)

didOpenHandler :: Handlers LSM
didOpenHandler = notificationHandler J.SMethod_TextDocumentDidOpen $ \msg -> do
  let uri = msg ^. J.params . J.textDocument . J.uri
  let version = msg ^. J.params . J.textDocument . J.version
  _ <- recompileFile InMemory uri (Just version) True
  return ()

didChangeHandler :: Handlers LSM
didChangeHandler = notificationHandler J.SMethod_TextDocumentDidChange $ \msg -> do
  let uri = msg ^. J.params . J.textDocument . J.uri
  let version = msg ^. J.params . J.textDocument . J.version
  _ <- recompileFile InMemory uri (Just version) True -- Need to reload
  return ()

didSaveHandler :: Handlers LSM
didSaveHandler = notificationHandler J.SMethod_TextDocumentDidSave $ \msg -> do
  let uri = msg ^. J.params . J.textDocument . J.uri
  _ <- recompileFile InMemory uri Nothing False
  return()

didCloseHandler :: Handlers LSM
didCloseHandler = notificationHandler J.SMethod_TextDocumentDidClose $ \_msg -> do
  -- TODO: Remove file from LSM state?
  return ()

maybeContents :: Map J.NormalizedUri VirtualFile -> FilePath -> Maybe ByteString
maybeContents vfs uri = do
  M.lookup (J.toNormalizedUri (J.filePathToUri uri)) vfs <&> T.encodeUtf8 . virtualFileText

-- Recompiles the given file, stores the compilation result in
-- LSM's state and emits diagnostics.
recompileFile :: CompileTarget () -> J.Uri -> Maybe J.Int32 -> Bool -> LSM (Maybe FilePath)
recompileFile compileTarget uri version force =
  case J.uriToFilePath uri of
    Just filePath -> do
      flags <- getFlags
      -- Recompile the file
      vFiles <- getVirtualFiles

      let vfs = _vfsMap vFiles
          contents = maybeContents vfs filePath
      loaded1 <- getLoaded
      let modules = do
            l <- loaded1
            return $ loadedModule l : loadedModules l
      term <- getTerminal
      sendNotification J.SMethod_WindowLogMessage $ J.LogMessageParams J.MessageType_Info $ T.pack $ "Recompiling " ++ filePath
      result <- liftIO $ compileFile (maybeContents vfs) contents term flags (fromMaybe [] modules) compileTarget filePath 
      outFile <- case checkError result of
        Right ((l, outFile), _) -> do
          putLoaded l
          sendNotification J.SMethod_WindowLogMessage $ J.LogMessageParams J.MessageType_Info $ "Successfully compiled " <> T.pack filePath
          return outFile
        Left e -> do
          sendNotification J.SMethod_WindowLogMessage $ J.LogMessageParams J.MessageType_Info $ T.pack ("Error when compiling " ++ show e) <> T.pack filePath
          return Nothing

      -- Emit the diagnostics (errors and warnings)
      let diagSrc = T.pack "koka"
          diags = toLspDiagnostics diagSrc result
          diagsBySrc = partitionBySource diags
          maxDiags = 100
      if null diags
        then flushDiagnosticsBySource maxDiags (Just diagSrc)
        else publishDiagnostics maxDiags normUri version diagsBySrc
      return outFile
    Nothing -> return Nothing
  where
    normUri = J.toNormalizedUri uri

-- TODO: Emit messages via LSP's logging mechanism

