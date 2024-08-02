module Interpreter.AbstractMachine where
import Core.Core
import Data.Map.Strict as M
import Common.Name
import Kind.Constructors (ConInfo)

newtype Marker = Mark Int

data Ev = Ev Env Handler Marker Evv 

data Handler = Handler {
  label:: Label,
  ops:: M.Map OpName Expr,
  ret:: Expr
}
type Evv = [Ev]
type Kont = [KontFrame]
type PureKont = [PureKontFrame]
type Env = M.Map Var Val 
type Var = Name
type Label = String
type OpName = Name

data Val =
  VInt Int
  | VString String
  | VCon ConInfo [Val]
  | VFun Expr Env
  | VKont Kont

data Sigma =
  Eval Expr Env Kont Evv
  | Apply Kont Val Evv
  | FindPrompt Kont Marker OpName Val Kont
  | ApplyKont Kont Val Kont Evv

data KontFrame = KF PureKont KontDelim
data KontDelim = KHnd Ev | KMask Label 

data PureKontFrame = 
  FLet Env Var Expr
  | FApp [Val] [Expr]
  | FOp OpName [Val] [Expr]
