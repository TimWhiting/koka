-----------------------------------------------------------------------------
-- The language server's main module
-----------------------------------------------------------------------------
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
module LanguageServer.Run (runLanguageServer) where

import Compiler.Options (Flags (languageServerPort))
import Control.Monad (void, forever)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.STM
import Control.Concurrent.STM.TChan
import Control.Concurrent
import Language.LSP.Server
import qualified Language.LSP.Protocol.Types as J
import qualified Language.LSP.Protocol.Message as J
import qualified Language.LSP.Server as J
import LanguageServer.Handlers
import LanguageServer.Monad (newLSStateVar, runLSM, LSM, getLSState, LSState (messages))
import Colog.Core (LogAction, WithSeverity)
import qualified Colog.Core as L
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Language.LSP.Logging (defaultClientLogger)
import Network.Simple.TCP
import Network.Socket hiding (connect)
import GHC.IO.IOMode (IOMode(ReadWriteMode))
import GHC.Conc (atomically)

runLanguageServer :: Flags -> [FilePath] -> IO ()
runLanguageServer flags files = do
  connect "localhost" (show $ languageServerPort flags) (\(socket, _) -> do
    handle <- socketToHandle socket ReadWriteMode
    state <- newLSStateVar flags
    initStateVal <- liftIO $ readMVar state
    rin <- atomically newTChan :: IO (TChan ReactorInput)
    void $
      runServerWithHandles
        ioLogger
        lspLogger
        handle
        handle
        $
        ServerDefinition
          { onConfigurationChange = const $ pure $ Right (),
            doInitialize = \env _ -> forkIO (reactor rin) >> forkIO (messageHandler (messages initStateVal) env) >> pure (Right env),
            staticHandlers = \_caps -> lspHandlers rin,
            interpretHandler = \env -> Iso (\lsm -> runLSM lsm state env) liftIO,
            options =
              defaultOptions
                { optTextDocumentSync = Just syncOptions,
                  optExecuteCommandCommands = Just [T.pack "koka/genCode"]
                  -- optCompletionTriggerCharacters = Just ['.', ':', '/']
                -- TODO: ? https://www.stackage.org/haddock/lts-18.21/lsp-1.2.0.0/src/Language.LSP.Server.Core.html#Options
                },
            defaultConfig = ()
          })
  where
    prettyMsg l = "[" <> show (L.getSeverity l) <> "] " <> show (L.getMsg l) <> "\n\n"
    ioLogger :: LogAction IO (WithSeverity LspServerLog)
    ioLogger = L.cmap prettyMsg L.logStringStdout
    stderrLogger :: LogAction IO (WithSeverity T.Text)
    stderrLogger = L.cmap show L.logStringStderr
    lspLogger :: LogAction (LspM config) (WithSeverity LspServerLog)
    lspLogger =
      let clientLogger = L.cmap (fmap (T.pack . show)) defaultClientLogger
      in clientLogger <> L.hoistLogAction liftIO ioLogger
    syncOptions =
      J.TextDocumentSyncOptions
        (Just True) -- open/close notifications
        (Just J.TextDocumentSyncKind_Incremental) -- changes
        (Just False) -- will save
        (Just False) -- will save (wait until requests are sent to server)
        (Just $ J.InR $ J.SaveOptions $ Just False) -- trigger on save, but dont send document

messageHandler :: TChan (String, J.MessageType) -> LanguageContextEnv () -> IO ()
messageHandler msgs env = do
  mVar <- newEmptyMVar
  forever $ do
    (msg, msgType) <- atomically $ readTChan msgs
    runLSM (sendNotification J.SMethod_WindowLogMessage $ J.LogMessageParams msgType $ T.pack msg) mVar env

reactor :: TChan ReactorInput -> IO ()
reactor inp = do
  forever $ do
    ReactorAction act <- atomically $ readTChan inp
    act

