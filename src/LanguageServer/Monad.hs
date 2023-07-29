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
import Lib.PPrint (Pretty(..), asString, writePrettyLn)
import GHC.Conc (ThreadId)
import Control.Concurrent.Chan (readChan)
import Type.Pretty (ppType, defaultEnv, Env (context, importsMap), ppScheme)
import Control.Concurrent (isEmptyMVar)
import qualified Language.LSP.Server as J
import GHC.Base (Type)
import Lib.Printer (withColorPrinter, withColor, writeLn, ansiDefault, AnsiStringPrinter (AnsiString), Color (Red), ColorPrinter (PAnsiString))
import Compiler.Options (Flags (..), prettyEnvFromFlags, verbose)
import Common.Error (ppErrorMessage)
import Common.ColorScheme (colorSource)
import Common.Name (nameNil)
import Kind.ImportMap (importsEmpty)
import Platform.Var (newVar, takeVar)
import Debug.Trace (trace)

-- The language server's state, e.g. holding loaded/compiled modules.
data LSState = LSState {lsLoaded :: Maybe Loaded, messages :: MVar [(String, J.MessageType)], flags:: Flags, terminal:: Terminal}

trimnl :: [Char] -> [Char]
trimnl str = reverse $ dropWhile (`elem` "\n\r\t ") $ reverse str

defaultLSState :: Flags -> IO LSState
defaultLSState flags = do
  msgVar <- newMVar []
  let withNewPrinter f = do
        ansiConsole <- newVar ansiDefault
        stringVar <- newVar ""
        let p = AnsiString ansiConsole stringVar
        tp <- (f . PAnsiString) p
        ansiString <- takeVar stringVar
        addMessages msgVar (trimnl ansiString, tp)
  
  let cscheme = colorScheme flags
      prettyEnv flags ctx imports = (prettyEnvFromFlags flags){ context = ctx, importsMap = imports }
      term = Terminal (\err -> withNewPrinter $ \p -> do putErrorMessage p (showSpan flags) cscheme err; return J.MessageType_Error)
                (if verbose flags > 1 then (\msg -> withNewPrinter $ \p -> do withColor p (colorSource cscheme) (writeLn p msg); return J.MessageType_Info)
                                         else (\_ -> return ()))
                 (if verbose flags > 0 then (\msg -> withNewPrinter $ \p -> do writePrettyLn p msg; return J.MessageType_Info) else (\_ -> return ()))
                 (\tp -> withNewPrinter $ \p -> do putScheme p (prettyEnv flags nameNil importsEmpty) tp; return J.MessageType_Info)
                 (\msg -> withNewPrinter $ \p -> do writePrettyLn p msg; return J.MessageType_Info)
  return LSState {lsLoaded = Nothing, messages = msgVar, terminal = term, flags = flags}

putScheme p env tp
  = writePrettyLn p (ppScheme env tp)

putErrorMessage p endToo cscheme err
  = writePrettyLn p (ppErrorMessage endToo cscheme err)

newLSStateVar :: Flags -> IO (MVar LSState)
newLSStateVar flags = defaultLSState flags >>= newMVar

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
getTerminal = terminal <$> getLSState