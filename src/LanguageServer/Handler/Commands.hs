-----------------------------------------------------------------------------
-- The LSP handlers that handles initialization
-----------------------------------------------------------------------------
{-# LANGUAGE OverloadedStrings #-}

module LanguageServer.Handler.Commands (initializedHandler, commandHandler) where

import Compiler.Options (Flags (outFinalPath))
import Language.LSP.Server (Handlers, LspM, notificationHandler, sendNotification, MonadLsp, getVirtualFiles, withIndefiniteProgress)
import qualified Language.LSP.Protocol.Types as J
import qualified Data.Text as T
import LanguageServer.Monad (LSM, requestHandler)
import qualified Language.LSP.Protocol.Message as J
import Data.Aeson as Json
import qualified Language.LSP.Protocol.Lens as J
import Control.Lens ((^.))
import Data.Maybe (mapMaybe, fromJust, fromMaybe)
import GHC.Base (Type)
import LanguageServer.Handler.TextDocument (recompileFile)
import Compiler.Compile (CompileTarget(..))
import Common.Name (newName)
import qualified Language.LSP.Server as J

initializedHandler :: Flags -> Handlers LSM
initializedHandler flags = notificationHandler J.SMethod_Initialized $ \_not -> sendNotification J.SMethod_WindowLogMessage $ J.LogMessageParams J.MessageType_Info "Initialized language server."

commandHandler :: Flags -> Handlers LSM
commandHandler flags = requestHandler J.SMethod_WorkspaceExecuteCommand $ \req resp -> do
  let J.ExecuteCommandParams _ command commandParams = req ^. J.params
  if command == "koka/genCode" then
    case commandParams of
      Just [Json.String filePath] -> do
        withIndefiniteProgress (T.pack "Compiling " <> filePath) J.NotCancellable $ do
          res <- recompileFile (Executable (newName "main") ()) flags (J.filePathToUri $ T.unpack filePath) Nothing True
          sendNotification J.SMethod_WindowLogMessage $ J.LogMessageParams J.MessageType_Info $ T.pack ("Finished generating code for main file " ++ T.unpack filePath ++ " " ++ fromMaybe "No Compiled File" res)
          resp $ Right $ case res of {Just filePath -> J.InL $ Json.String $ T.pack filePath; Nothing -> J.InR J.Null}
      _ -> do
        sendNotification J.SMethod_WindowLogMessage $ J.LogMessageParams J.MessageType_Error $ T.pack "Invalid parameters"
        resp $ Right $ J.InR J.Null
  else
    do
      sendNotification J.SMethod_WindowLogMessage $ J.LogMessageParams J.MessageType_Error $ T.pack ("Unknown command" ++ show req)
      resp $ Right $ J.InR J.Null

liftMaybe:: Monad m => Maybe (m ()) -> m ()
liftMaybe Nothing = return ()
liftMaybe (Just m) = m
