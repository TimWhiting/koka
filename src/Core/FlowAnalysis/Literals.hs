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

litContains :: LiteralLattice -> LiteralChange -> Bool
litContains (LiteralLattice i f c s) lit =
  case lit of
    LiteralChangeInt ch -> lte ch i
    LiteralChangeFloat ch -> lte ch f
    LiteralChangeChar ch -> lte ch c
    LiteralChangeString ch -> lte ch s

litBottom :: LiteralLattice
litBottom = LiteralLattice LBottom LBottom LBottom LBottom

litLattice :: LiteralChange -> LiteralLattice
litLattice lit =
  case lit of
    LiteralChangeInt ch -> LiteralLattice (snd $ ch `FM.insert` LBottom) LBottom LBottom LBottom
    LiteralChangeFloat ch -> LiteralLattice LBottom (snd $ ch `FM.insert` LBottom) LBottom LBottom
    LiteralChangeChar ch -> LiteralLattice LBottom LBottom (snd $ ch `FM.insert` LBottom) LBottom
    LiteralChangeString ch -> LiteralLattice LBottom LBottom LBottom (snd $ ch `FM.insert` LBottom)

joinLit :: LiteralChange -> LiteralLattice -> (LiteralChange, LiteralLattice)
joinLit (LiteralChangeInt ch) (LiteralLattice i2 f2 c2 s2) =
    let (change, i) = (ch `FM.insert` i2)
    in (LiteralChangeInt change, LiteralLattice i f2 c2 s2)
joinLit (LiteralChangeFloat ch) (LiteralLattice i2 f2 c2 s2) =
    let (change, f) = (ch `FM.insert` f2)
    in (LiteralChangeFloat change, LiteralLattice i2 f c2 s2)
joinLit (LiteralChangeChar ch) (LiteralLattice i2 f2 c2 s2) =
    let (change, c) = (ch `FM.insert` c2)
    in (LiteralChangeChar change, LiteralLattice i2 f2 c s2)
joinLit (LiteralChangeString ch) (LiteralLattice i2 f2 c2 s2) =
    let (change, s) = (ch `FM.insert` s2)
    in (LiteralChangeString change, LiteralLattice i2 f2 c2 s)

joinLitLattice :: LiteralLattice -> LiteralLattice -> LiteralLattice
joinLitLattice (LiteralLattice i0 f0 c0 s0) (LiteralLattice i1 f1 c1 s1) =
  LiteralLattice (i0 `FM.joinSimple` i1) (f0 `FM.joinSimple` f1) (c0 `FM.joinSimple` c1) (s0 `FM.joinSimple` s1)

litIsBottom :: LiteralLattice -> Bool
litIsBottom (LiteralLattice i f c s) = isBottom i && isBottom f && isBottom c && isBottom s
