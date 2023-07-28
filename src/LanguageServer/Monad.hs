-----------------------------------------------------------------------------
-- The language server's monad that holds state (e.g. loaded/compiled modules)
-----------------------------------------------------------------------------
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE DataKinds #-}
module LanguageServer.Monad
  ( LSState (..),
    defaultLSState,
    newLSStateVar,
    notificationHandler,
    requestHandler,
    LSM,
    getLSState,
    getTerminal,
    putLSState,
    modifyLSState,
    getLoaded,
    putLoaded,
    modifyLoaded,
    runLSM,
  )
where

import Compiler.Module (Loaded)
import Control.Concurrent.MVar (MVar, modifyMVar, newMVar, putMVar, readMVar, newEmptyMVar)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Trans (lift, liftIO)
import qualified Data.Map as M
import qualified Data.Text as T
import Language.LSP.Server (LanguageContextEnv, LspT, runLspT, sendNotification, Handlers)
import qualified Language.LSP.Protocol.Types as J
import qualified Language.LSP.Protocol.Message as J

import Compiler.Compile (Terminal (..))
import Control.Concurrent (Chan, forkIO)
import Control.Concurrent.Chan (newChan, writeChan)
import Lib.PPrint (Pretty(..), asString)
import GHC.Conc (ThreadId)
import Control.Concurrent.Chan (readChan)
import Type.Pretty (ppType, defaultEnv)
import Control.Concurrent (isEmptyMVar)
import qualified Language.LSP.Server as J
import GHC.Base (Type)

-- The language server's state, e.g. holding loaded/compiled modules.
data LSState = LSState {lsLoaded :: Maybe Loaded, messages :: MVar [(String, J.MessageType)]}

defaultLSState :: IO LSState
defaultLSState = do
  msgVar <- newMVar []
  return LSState {lsLoaded = Nothing, messages = msgVar}

newLSStateVar :: IO (MVar LSState)
newLSStateVar = defaultLSState >>= newMVar 

-- The monad holding (thread-safe) state used by the language server.
type LSM = LspT () (ReaderT (MVar LSState) IO)

-- Fetches the language server's state inside the LSM monad
getLSState :: LSM LSState
getLSState = do
  stVar <- lift ask
  liftIO $ readMVar stVar

-- Replaces the language server's state inside the LSM monad
putLSState :: LSState -> LSM ()
putLSState s = do
  stVar <- lift ask
  liftIO $ putMVar stVar s

-- Updates the language server's state inside the LSM monad
modifyLSState :: (LSState -> LSState) -> LSM ()
modifyLSState m = do
  stVar <- lift ask
  liftIO $ modifyMVar stVar $ \s -> return (m s, ())

-- Fetches the loaded state holding compiled modules
getLoaded :: LSM (Maybe Loaded)
getLoaded = lsLoaded <$> getLSState

-- Replaces the loaded state holding compiled modules
putLoaded :: Loaded -> LSM ()
putLoaded l = modifyLSState $ \s -> s {lsLoaded = Just l}

-- Updates the loaded state holding compiled modules
modifyLoaded :: (Maybe Loaded -> Loaded) -> LSM ()
modifyLoaded m = modifyLSState $ \s -> s {lsLoaded = Just $ m $ lsLoaded s}

-- Runs the language server's state monad.
runLSM :: LSM a -> MVar LSState -> LanguageContextEnv () -> IO a
runLSM lsm stVar cfg = runReaderT (runLspT cfg lsm) stVar

notificationHandler ::forall (m :: J.Method 'J.ClientToServer 'J.Notification). J.SMethod m -> J.Handler LSM m -> Handlers LSM
notificationHandler method handler = J.notificationHandler method $ \req -> do
  res <- handler req
  flushMessages
  return res

requestHandler :: forall (m :: J.Method 'J.ClientToServer 'J.Request). J.SMethod m -> J.Handler LSM m -> Handlers LSM
requestHandler method handler = J.requestHandler method $ \req resp -> do
  handler req resp
  flushMessages  

flushMessages :: LSM ()
flushMessages = do
  msgVar <- messages <$> getLSState
  msgs <- liftIO $ readMVar msgVar
  mapM_ (\(msg, tp) -> sendNotification J.SMethod_WindowLogMessage $ J.LogMessageParams tp $ T.pack msg) msgs

addMessages :: MVar [(String, J.MessageType)] -> (String, J.MessageType) -> IO ()
addMessages msgVar msg =
  modifyMVar msgVar (\oldMsgs -> return (oldMsgs ++ [msg], ()))

getTerminal :: LSM Terminal
getTerminal = do
  msgVar <- messages <$> getLSState
  return $ Terminal
    { termError = \err -> addMessages msgVar (show err, J.MessageType_Error),
      termPhase = \phase -> addMessages msgVar (phase, J.MessageType_Info),
      termPhaseDoc = \doc -> addMessages msgVar (asString doc, J.MessageType_Info),
      termType = \ty -> addMessages msgVar (asString $ ppType defaultEnv ty, J.MessageType_Info),
      termDoc = \doc -> addMessages msgVar (asString doc, J.MessageType_Info)
    }