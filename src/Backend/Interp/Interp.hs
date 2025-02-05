module Backend.Interp.Interp where


import Control.Monad
import Control.Monad.State (StateT, MonadState (..))
import Control.Monad.Reader (ReaderT)
import qualified Data.Map.Strict as M
import Core.Core
import Compile.Module (Module)
import Common.Name (Name)

data Value =
  VInt Int
  | VDouble Double
  | VChar Char
  | VString String
  | VCon String [Value]
  | VLam Expr

type Addr = Int

data Handlers = 
  HTop
  | HInt [Operations]

type Operations = [Value]

type Interp a = StateT (M.Map Addr Value, [Module]) (ReaderT Handlers IO) a 

getDef :: Name -> Interp Def
getDef name = do
  (_, modules) <- get
  undefined

interp :: Name -> [Module] -> IO ()
interp mainEntry modules = undefined  -- TODO: Run interp