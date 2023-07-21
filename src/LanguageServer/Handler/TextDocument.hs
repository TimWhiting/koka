-----------------------------------------------------------------------------
-- The LSP handlers that handle changes to the document
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}

module LanguageServer.Handler.TextDocument
  ( didOpenHandler,
    didChangeHandler,
    didSaveHandler,
    didCloseHandler,
  )
where

import Common.Error (checkError)
import Compiler.Compile (Terminal (..), compileModuleOrFile, Loaded (..))
import Compiler.Options (Flags)
import Control.Lens ((^.))
import Control.Monad.Trans (liftIO)
import qualified Data.Map as M
import Data.Maybe (fromJust, fromMaybe)
import qualified Data.Text as T
import Language.LSP.Diagnostics (partitionBySource)
import Language.LSP.Server (Handlers, flushDiagnosticsBySource, notificationHandler, publishDiagnostics, sendNotification, getVirtualFile, getVirtualFiles)
import qualified Language.LSP.Protocol.Types as J
import qualified Language.LSP.Protocol.Lens as J
import LanguageServer.Conversions (toLspDiagnostics)
import LanguageServer.Monad (LSM, modifyLoaded, getLoaded, putLoaded)
import Language.LSP.VFS (virtualFileText, VFS(..), VirtualFile)
import qualified Data.Text.Encoding as T
import Data.Functor ((<&>))
import qualified Language.LSP.Protocol.Message as J
import Data.ByteString (ByteString)
import Data.Map (Map)

didOpenHandler :: Flags -> Handlers LSM
didOpenHandler flags = notificationHandler J.SMethod_TextDocumentDidOpen $ \msg -> do
  let uri = msg ^. J.params . J.textDocument . J.uri
  let version = msg ^. J.params . J.textDocument . J.version
  recompileFile flags uri (Just version) False

didChangeHandler :: Flags -> Handlers LSM
didChangeHandler flags = notificationHandler J.SMethod_TextDocumentDidChange $ \msg -> do
  let uri = msg ^. J.params . J.textDocument . J.uri
  let version = msg ^. J.params . J.textDocument . J.version
  recompileFile flags uri (Just version) True -- Need to reload

didSaveHandler :: Flags -> Handlers LSM
didSaveHandler flags = notificationHandler J.SMethod_TextDocumentDidSave $ \msg -> do
  let uri = msg ^. J.params . J.textDocument . J.uri
  recompileFile flags uri Nothing False

didCloseHandler :: Flags -> Handlers LSM
didCloseHandler flags = notificationHandler J.SMethod_TextDocumentDidClose $ \_msg -> do
  -- TODO: Remove file from LSM state?
  return ()

maybeContents :: Map J.NormalizedUri VirtualFile -> FilePath -> Maybe ByteString
maybeContents vfs uri = M.lookup (J.toNormalizedUri (read uri)) vfs <&> T.encodeUtf8 . virtualFileText

-- Recompiles the given file, stores the compilation result in
-- LSM's state and emits diagnostics.
recompileFile :: Flags -> J.Uri -> Maybe J.Int32 -> Bool -> LSM ()
recompileFile flags uri version force =
  case J.uriToFilePath uri of
    Just filePath -> do
      -- Recompile the file
      -- TODO: Abstract the logging calls in a better way
      vFiles <- getVirtualFiles

      let vfs = _vfsMap vFiles
          contents = maybeContents vfs filePath
      loaded1 <- getLoaded
      let modules = do
            l <- loaded1
            return $ loadedModule l : loadedModules l
      sendNotification J.SMethod_WindowLogMessage $ J.LogMessageParams J.MessageType_Info $ T.pack ("Recompiling " ++ show uri) <> T.pack filePath
      loaded <- liftIO $ compileModuleOrFile (maybeContents vfs) terminal flags (fromMaybe [] modules) filePath contents True
      case checkError loaded of
        Right (l, _) -> do
          putLoaded l
          sendNotification J.SMethod_WindowLogMessage $ J.LogMessageParams J.MessageType_Info $ "Successfully compiled " <> T.pack filePath
        Left e ->
          sendNotification J.SMethod_WindowLogMessage $ J.LogMessageParams J.MessageType_Info $ T.pack ("Error when compiling " ++ show e) <> T.pack filePath

      -- Emit the diagnostics (errors and warnings)
      let diagSrc = T.pack "koka"
          diags = toLspDiagnostics diagSrc loaded
          diagsBySrc = partitionBySource diags
          maxDiags = 100
      if null diags
        then flushDiagnosticsBySource maxDiags (Just diagSrc)
        else publishDiagnostics maxDiags normUri version diagsBySrc
    Nothing -> return ()
  where
    normUri = J.toNormalizedUri uri

-- TODO: Emit messages via LSP's logging mechanism
terminal :: Terminal
terminal =
  Terminal
    { termError = const $ return (),
      termPhase = const $ return (),
      termPhaseDoc = const $ return (),
      termType = const $ return (),
      termDoc = const $ return ()
    }
