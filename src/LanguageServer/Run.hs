-----------------------------------------------------------------------------
-- The language server's main module
-----------------------------------------------------------------------------
module LanguageServer.Run (runLanguageServer) where

import Compiler.Options (Flags (languageServerPort))
import Control.Monad (void)
import Control.Monad.IO.Class (liftIO)
import Language.LSP.Server
import qualified Language.LSP.Protocol.Types as LSPTypes
import LanguageServer.Handlers (handlers)
import LanguageServer.Monad (newLSStateVar, runLSM)
import Colog.Core (LogAction, WithSeverity)
import qualified Colog.Core as L
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Language.LSP.Logging (defaultClientLogger)
import Network.Simple.TCP
import Network.Socket hiding (connect)
import GHC.IO.IOMode (IOMode(ReadWriteMode))

runLanguageServer :: Flags -> [FilePath] -> IO ()
runLanguageServer flags files = do
  state <- newLSStateVar 
  connect "localhost" (show $ languageServerPort flags) (\(socket, _) -> do 
    handle <- socketToHandle socket ReadWriteMode
    void $
      runServerWithHandles
        ioLogger
        lspLogger
        handle
        handle
        $
        ServerDefinition
          { onConfigurationChange = const $ pure $ Right (),
            doInitialize = \env _ -> pure $ Right env,
            staticHandlers = \clientCapabilities -> handlers flags,
            interpretHandler = \env -> Iso (\lsm -> runLSM lsm state env) liftIO,
            options =
              defaultOptions
                { optTextDocumentSync = Just syncOptions,
                  optCompletionTriggerCharacters = Just ['.', ':', '/']
                -- TODO: ? https://www.stackage.org/haddock/lts-18.21/lsp-1.2.0.0/src/Language.LSP.Server.Core.html#Options
                },
            defaultConfig = ()
          })
  where
    prettyMsg l = "[" <> show (L.getSeverity l) <> "] " <> show (L.getMsg l)
    ioLogger :: LogAction IO (WithSeverity LspServerLog)
    ioLogger = L.cmap (show . prettyMsg) L.logStringStderr
    lspLogger :: LogAction (LspM config) (WithSeverity LspServerLog)
    lspLogger =
      let clientLogger = L.cmap (fmap (T.pack . show)) defaultClientLogger
      in clientLogger <> L.hoistLogAction liftIO ioLogger
    syncOptions =
      LSPTypes.TextDocumentSyncOptions
        (Just True) -- open/close notifications
        (Just LSPTypes.TextDocumentSyncKind_Incremental) -- changes
        (Just False) -- will save
        (Just False) -- will save (wait until requests are sent to server)
        (Just $ LSPTypes.InR $ LSPTypes.SaveOptions $ Just False) -- trigger on save, but dont send document