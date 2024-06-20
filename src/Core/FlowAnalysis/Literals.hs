module Core.FlowAnalysis.Literals where
  
import Data.List (intercalate)
import Core.FlowAnalysis.FixpointMonad
import qualified Core.FlowAnalysis.FixpointMonad as FM
import qualified Data.Map.Strict as M

data LiteralLattice =
    LiteralLattice{
      intVL :: SLattice Integer,
      floatVL :: SLattice Double,
      charVL :: SLattice Char,
      stringVL :: SLattice String
    } deriving (Eq, Ord)

data LiteralChange =
  LiteralChangeInt (SimpleChange Integer)
  | LiteralChangeFloat (SimpleChange Double)
  | LiteralChangeChar (SimpleChange Char)
  | LiteralChangeString (SimpleChange String)
 deriving (Eq, Ord)

instance Show LiteralChange where
  show (LiteralChangeInt LChangeTop) = "int -> top"
  show (LiteralChangeFloat LChangeTop) = "float -> top"
  show (LiteralChangeChar LChangeTop) = "char -> top"
  show (LiteralChangeString LChangeTop) = "string -> top"
  show (LiteralChangeInt (LChangeSingle l)) = "int -> " ++ show l
  show (LiteralChangeFloat (LChangeSingle l)) = "float -> " ++ show l
  show (LiteralChangeChar (LChangeSingle l)) = "char -> " ++ show l
  show (LiteralChangeString (LChangeSingle l)) = "string -> " ++ show l

instance Show LiteralLattice where
  show (LiteralLattice i f c s) = intercalate "," [show i, show f, show c, show s]


litLattice :: LiteralChange -> LiteralLattice
litLattice lit =
  case lit of
    LiteralChangeInt ch -> LiteralLattice (ch `FM.insert` LBottom) LBottom LBottom LBottom
    LiteralChangeFloat ch -> LiteralLattice LBottom (ch `FM.insert` LBottom) LBottom LBottom
    LiteralChangeChar ch -> LiteralLattice LBottom LBottom (ch `FM.insert` LBottom) LBottom
    LiteralChangeString ch -> LiteralLattice LBottom LBottom LBottom (ch `FM.insert` LBottom)

joinLit :: LiteralLattice -> LiteralLattice -> LiteralLattice
joinLit (LiteralLattice i1 f1 c1 s1) (LiteralLattice i2 f2 c2 s2) = LiteralLattice (i1 `join` i2) (f1 `join` f2) (c1 `join` c2) (s1 `join` s2)