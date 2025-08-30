module Core.FlowAnalysis.Literals where

import Data.List (intercalate)
import Core.FlowAnalysis.FixpointMonad
import qualified Core.FlowAnalysis.FixpointMonad as FM
import qualified Data.Map.Strict as M
import Core.Core
import Core.FlowAnalysis.StaticContext (ExprContextId (ExprContextId))
import Common.Name (newName)

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


patSubsumed :: Pattern -> LiteralChange -> Bool
patSubsumed (PatLit (LitInt i)) (LiteralChangeInt (LChangeSingle x)) = i == x
patSubsumed (PatLit (LitFloat i)) (LiteralChangeFloat (LChangeSingle x)) = i == x
patSubsumed (PatLit (LitChar i)) (LiteralChangeChar (LChangeSingle x)) = i == x
patSubsumed (PatLit (LitString i)) (LiteralChangeString (LChangeSingle x)) = i == x
patSubsumed (PatLit (LitInt i)) (LiteralChangeInt LChangeTop) = True
patSubsumed (PatLit (LitFloat i)) (LiteralChangeFloat LChangeTop) = True
patSubsumed (PatLit (LitChar i)) (LiteralChangeChar LChangeTop) = True
patSubsumed (PatLit (LitString i)) (LiteralChangeString LChangeTop) = True
patSubsumed _ _ = False

data LiteralLatticeX =
    LiteralLatticeX{
      intVLX :: SLattice (ExprContextId, Integer),
      floatVLX :: SLattice (ExprContextId, Double),
      charVLX :: SLattice (ExprContextId, Char),
      stringVLX :: SLattice (ExprContextId, String)
    } deriving (Eq, Ord)

lat :: SLattice (ExprContextId, a2) -> SLattice a2
lat (LSingle (s, x)) = LSingle x
lat LTop = LTop
lat LBottom = LBottom

litEx :: LiteralChangeX -> ExprContextId
litEx (LiteralChangeIntX (LChangeSingle (s, _))) = s
litEx (LiteralChangeFloatX (LChangeSingle (s, _))) = s
litEx (LiteralChangeCharX (LChangeSingle (s, _))) = s
litEx (LiteralChangeStringX (LChangeSingle (s, _))) = s
litEx (LiteralChangeIntX LChangeTop) = ExprContextId (-10000) (newName "ltop")
litEx (LiteralChangeFloatX LChangeTop) = ExprContextId (-10000) (newName "ltop")
litEx (LiteralChangeCharX LChangeTop) = ExprContextId (-10000) (newName "ltop")
litEx (LiteralChangeStringX LChangeTop) = ExprContextId (-10000) (newName "ltop")

litXEquiv :: LiteralLatticeX -> LiteralLatticeX -> Bool
litXEquiv (LiteralLatticeX i0 f0 c0 s0) (LiteralLatticeX i1 f1 c1 s1) =
  lat i0 == lat i1 && lat f0 == lat f1 && lat c0 == lat c1 && lat s0 == lat s1

data LiteralChangeX =
  LiteralChangeIntX (SimpleChange (ExprContextId, Integer))
  | LiteralChangeFloatX (SimpleChange (ExprContextId, Double))
  | LiteralChangeCharX (SimpleChange (ExprContextId, Char))
  | LiteralChangeStringX (SimpleChange (ExprContextId, String))
 deriving (Eq, Ord)

instance Show LiteralChangeX where
  show (LiteralChangeIntX LChangeTop) = "int -> top"
  show (LiteralChangeFloatX LChangeTop) = "float -> top"
  show (LiteralChangeCharX LChangeTop) = "char -> top"
  show (LiteralChangeStringX LChangeTop) = "string -> top"
  show (LiteralChangeIntX (LChangeSingle l)) = "int -> " ++ show l
  show (LiteralChangeFloatX (LChangeSingle l)) = "float -> " ++ show l
  show (LiteralChangeCharX (LChangeSingle l)) = "char -> " ++ show l
  show (LiteralChangeStringX (LChangeSingle l)) = "string -> " ++ show l

instance Show LiteralLatticeX where
  show (LiteralLatticeX i f c s) = intercalate "," [show i, show f, show c, show s]

litContainsX :: LiteralLatticeX -> LiteralChangeX -> Bool
litContainsX (LiteralLatticeX i f c s) lit =
  case lit of
    LiteralChangeIntX ch -> lte ch i
    LiteralChangeFloatX ch -> lte ch f
    LiteralChangeCharX ch -> lte ch c
    LiteralChangeStringX ch -> lte ch s

litBottomX :: LiteralLatticeX
litBottomX = LiteralLatticeX LBottom LBottom LBottom LBottom

litLatticeX :: LiteralChangeX -> LiteralLatticeX
litLatticeX lit =
  case lit of
    LiteralChangeIntX ch -> LiteralLatticeX (snd $ ch `insertX` LBottom) LBottom LBottom LBottom
    LiteralChangeFloatX ch -> LiteralLatticeX LBottom (snd $ ch `insertX` LBottom) LBottom LBottom
    LiteralChangeCharX ch -> LiteralLatticeX LBottom LBottom (snd $ ch `insertX` LBottom) LBottom
    LiteralChangeStringX ch -> LiteralLatticeX LBottom LBottom LBottom (snd $ ch `insertX` LBottom)

insertX :: Eq x => SimpleChange (ExprContextId, x) -> SimpleLattice (ExprContextId, x) (SimpleChange (ExprContextId, x)) -> (SimpleChange (ExprContextId, x), SimpleLattice (ExprContextId, x) (SimpleChange (ExprContextId, x)))
insertX _ LTop = (LChangeTop, LTop)
insertX LChangeTop _ = (LChangeTop, LTop)
insertX (LChangeSingle x) LBottom = (LChangeSingle x, LSingle x)
insertX (LChangeSingle (s, x)) (LSingle (s2, x2)) = 
  if x == x2 then (LChangeSingle (s, x), LSingle (s, x)) -- Take the first expression, could end up the second being first in a different path, so we do technically have duplication
  else (LChangeTop, LTop)

lteX :: Eq x => SimpleChange (ExprContextId, x) -> SimpleLattice (ExprContextId, x) (SimpleChange (ExprContextId, x)) -> Bool
lteX _ LTop = True
lteX _ LBottom = False
lteX (LChangeSingle (s, x)) (LSingle (s2, y)) = x == y
lteX LChangeTop _ = False

joinSimpleX :: Eq x => SimpleLattice (ExprContextId, x) (SimpleChange (ExprContextId, x)) -> SimpleLattice (ExprContextId, x) (SimpleChange (ExprContextId, x)) -> SimpleLattice (ExprContextId, x) (SimpleChange (ExprContextId, x))
joinSimpleX LTop _ = LTop
joinSimpleX _ LTop = LTop
joinSimpleX LBottom x = x
joinSimpleX x LBottom = x
joinSimpleX (LSingle (s,x)) (LSingle (s2,y)) = if x == y then LSingle (s, x) else LTop

joinLitX :: LiteralChangeX -> LiteralLatticeX -> (LiteralChangeX, LiteralLatticeX)
joinLitX (LiteralChangeIntX ch) (LiteralLatticeX i2 f2 c2 s2) =
    let (change, i) = (ch `insertX` i2)
    in (LiteralChangeIntX change, LiteralLatticeX i f2 c2 s2)
joinLitX (LiteralChangeFloatX ch) (LiteralLatticeX i2 f2 c2 s2) =
    let (change, f) = (ch `insertX` f2)
    in (LiteralChangeFloatX change, LiteralLatticeX i2 f c2 s2)
joinLitX (LiteralChangeCharX ch) (LiteralLatticeX i2 f2 c2 s2) =
    let (change, c) = (ch `insertX` c2)
    in (LiteralChangeCharX change, LiteralLatticeX i2 f2 c s2)
joinLitX (LiteralChangeStringX ch) (LiteralLatticeX i2 f2 c2 s2) =
    let (change, s) = (ch `insertX` s2)
    in (LiteralChangeStringX change, LiteralLatticeX i2 f2 c2 s)

joinLitLatticeX :: LiteralLatticeX -> LiteralLatticeX -> LiteralLatticeX
joinLitLatticeX (LiteralLatticeX i0 f0 c0 s0) (LiteralLatticeX i1 f1 c1 s1) =
  LiteralLatticeX (i0 `joinSimpleX` i1) (f0 `joinSimpleX` f1) (c0 `joinSimpleX` c1) (s0 `joinSimpleX` s1)

litIsBottomX :: LiteralLatticeX -> Bool
litIsBottomX (LiteralLatticeX i f c s) = isBottom i && isBottom f && isBottom c && isBottom s

patSubsumedX :: Pattern -> LiteralChangeX -> Bool
patSubsumedX (PatLit (LitInt i)) (LiteralChangeIntX (LChangeSingle (_, x))) = i == x
patSubsumedX (PatLit (LitFloat i)) (LiteralChangeFloatX (LChangeSingle (_, x))) = i == x
patSubsumedX (PatLit (LitChar i)) (LiteralChangeCharX (LChangeSingle (_, x))) = i == x
patSubsumedX (PatLit (LitString i)) (LiteralChangeStringX (LChangeSingle (_, x))) = i == x
patSubsumedX (PatLit (LitInt i)) (LiteralChangeIntX LChangeTop) = True
patSubsumedX (PatLit (LitFloat i)) (LiteralChangeFloatX LChangeTop) = True
patSubsumedX (PatLit (LitChar i)) (LiteralChangeCharX LChangeTop) = True
patSubsumedX (PatLit (LitString i)) (LiteralChangeStringX LChangeTop) = True
patSubsumedX _ _ = False
