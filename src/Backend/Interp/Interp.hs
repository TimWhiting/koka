module Backend.Interp.Interp where


import Control.Monad
import Control.Monad.State (StateT)
import Control.Monad.Reader (ReaderT)
import qualified Data.Map.Strict as M
import Core.Core
import Compile.Module (Module)

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

type Interp a = StateT (M.Map Addr Value, Module) (ReaderT Handlers IO) a 

interp :: Expr -> Interp a
interp = undefined 