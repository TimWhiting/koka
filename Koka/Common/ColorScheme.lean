/-
  Ported from Haskell Koka:
  File:   src/Common/ColorScheme.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
namespace Koka.Common.ColorScheme

inductive Color
  | Black | DarkRed | DarkGreen | DarkYellow | DarkBlue | DarkMagenta | DarkCyan
  | Gray | DarkGray | Red | Green | Yellow | Blue | Magenta | Cyan | White
  | Default
  deriving Repr, DecidableEq, Inhabited

instance : ToString Color where
  toString c := match c with
    | .Black => "Black" | .DarkRed => "DarkRed" | .DarkGreen => "DarkGreen" | .DarkYellow => "DarkYellow"
    | .DarkBlue => "DarkBlue" | .DarkMagenta => "DarkMagenta" | .DarkCyan => "DarkCyan" | .Gray => "Gray"
    | .DarkGray => "DarkGray" | .Red => "Red" | .Green => "Green" | .Yellow => "Yellow"
    | .Blue => "Blue" | .Magenta => "Magenta" | .Cyan => "Cyan" | .White => "White" | .Default => "Default"

structure ColorScheme where
  colorType : Color
  colorParameter : Color
  colorKind : Color
  colorMarker : Color
  colorWarning : Color
  colorError : Color
  colorSource : Color
  colorInterpreter : Color
  colorCommand : Color
  colorKeyword : Color
  colorEffect : Color
  colorRange : Color
  colorSep : Color
  colorComment : Color
  colorReserved : Color
  colorReservedOp : Color
  colorSpecial : Color
  colorString : Color
  colorNumber : Color
  colorModule : Color
  colorCons : Color
  colorTypeCon : Color
  colorTypeVar : Color
  colorTypeKeyword : Color
  colorTypeKeywordOp : Color
  colorTypeSpecial : Color
  colorTypeParam : Color
  colorNameQual : Color
  colorImplicitParameter : Color
  colorImplicitExpr : Color
  deriving Repr, DecidableEq, Inhabited

def makeColorScheme (clr : Color) : ColorScheme :=
  { colorType := clr, colorParameter := clr, colorKind := clr, colorMarker := clr, colorWarning := clr
  , colorError := clr, colorSource := clr, colorInterpreter := clr, colorCommand := clr, colorKeyword := clr
  , colorEffect := clr, colorRange := clr, colorSep := clr, colorComment := clr, colorReserved := clr
  , colorReservedOp := clr, colorSpecial := clr, colorString := clr, colorNumber := clr, colorModule := clr
  , colorCons := clr, colorTypeCon := clr, colorTypeVar := clr, colorTypeKeyword := clr, colorTypeKeywordOp := clr
  , colorTypeSpecial := clr, colorTypeParam := clr, colorNameQual := clr, colorImplicitParameter := clr, colorImplicitExpr := clr }

def emptyColorScheme : ColorScheme := makeColorScheme Color.Default

def defaultColor (color clr : Color) : Color :=
  if clr == Color.Default then color else clr

def defaultTo (cs : ColorScheme) (color : Color) : ColorScheme :=
  { colorType := defaultColor color cs.colorType
  , colorParameter := defaultColor color cs.colorParameter
  , colorKind := defaultColor color cs.colorKind
  , colorMarker := defaultColor color cs.colorMarker
  , colorWarning := defaultColor color cs.colorWarning
  , colorError := defaultColor color cs.colorError
  , colorSource := defaultColor color cs.colorSource
  , colorInterpreter := defaultColor color cs.colorInterpreter
  , colorCommand := defaultColor color cs.colorCommand
  , colorKeyword := defaultColor color cs.colorKeyword
  , colorEffect := defaultColor color cs.colorEffect
  , colorRange := defaultColor color cs.colorRange
  , colorSep := defaultColor color cs.colorSep
  , colorComment := defaultColor color cs.colorComment
  , colorReserved := defaultColor color cs.colorReserved
  , colorReservedOp := defaultColor color cs.colorReservedOp
  , colorSpecial := defaultColor color cs.colorSpecial
  , colorString := defaultColor color cs.colorString
  , colorNumber := defaultColor color cs.colorNumber
  , colorModule := defaultColor color cs.colorModule
  , colorCons := defaultColor color cs.colorCons
  , colorTypeCon := defaultColor color cs.colorTypeCon
  , colorTypeVar := defaultColor color cs.colorTypeVar
  , colorTypeKeyword := defaultColor color cs.colorTypeKeyword
  , colorTypeKeywordOp := defaultColor color cs.colorTypeKeywordOp
  , colorTypeSpecial := defaultColor color cs.colorTypeSpecial
  , colorTypeParam := defaultColor color cs.colorTypeParam
  , colorNameQual := defaultColor color cs.colorNameQual
  , colorImplicitParameter := defaultColor color cs.colorImplicitParameter
  , colorImplicitExpr := defaultColor color cs.colorImplicitExpr
  }

def darkColorScheme : ColorScheme :=
  let c := emptyColorScheme
  let c := { c with colorInterpreter := Color.DarkGreen, colorCommand := Color.Green, colorError := Color.Red
                  , colorComment := Color.DarkGreen, colorReserved := Color.DarkYellow, colorSep := c.colorSource
                  , colorSpecial := c.colorSource, colorCons := Color.Yellow, colorModule := Color.DarkCyan
                  , colorNameQual := Color.DarkGray, colorString := Color.Cyan, colorNumber := Color.Default
                  , colorSource := Color.Default, colorParameter := Color.DarkGray, colorRange := Color.DarkCyan
                  , colorMarker := Color.Red, colorWarning := Color.DarkYellow, colorType := Color.DarkCyan
                  , colorEffect := Color.DarkCyan, colorTypeVar := Color.DarkCyan, colorTypeCon := Color.DarkCyan
                  , colorKeyword := Color.DarkYellow, colorTypeSpecial := Color.DarkCyan, colorTypeKeyword := Color.Blue
                  , colorTypeKeywordOp := Color.DarkCyan, colorTypeParam := Color.DarkGray, colorImplicitParameter := Color.Gray
                  , colorImplicitExpr := c.colorSource }
  defaultTo c Color.White

def defaultColorScheme : ColorScheme := darkColorScheme

def lightColorScheme : ColorScheme :=
  let c := darkColorScheme
  let c := { c with colorNumber := Color.DarkGray, colorSource := Color.Default, colorSep := c.colorSource
                  , colorSpecial := c.colorSource, colorCommand := Color.Black, colorError := Color.Red
                  , colorWarning := Color.DarkYellow, colorNameQual := Color.DarkGray, colorRange := c.colorInterpreter
                  , colorMarker := c.colorInterpreter, colorString := Color.DarkRed }
  defaultTo c Color.Black

def colorThemes : List (String × ColorScheme) := [("dark", darkColorScheme), ("light", lightColorScheme)]

def norm (s : String) : String :=
  let nowhite (x : String) := x.toList.dropWhile Char.isWhitespace |>.reverse.dropWhile Char.isWhitespace |>.reverse
  String.ofList (nowhite s |>.map Char.toLower)

def colors : List (String × Color) :=
  [("black", Color.Black), ("darkred", Color.DarkRed), ("darkgreen", Color.DarkGreen), ("darkyellow", Color.DarkYellow)
  , ("darkblue", Color.DarkBlue), ("darkmagenta", Color.DarkMagenta), ("darkcyan", Color.DarkCyan), ("lightgray", Color.Gray)
  , ("gray", Color.DarkGray), ("red", Color.Red), ("green", Color.Green), ("yellow", Color.Yellow), ("blue", Color.Blue)
  , ("magenta", Color.Magenta), ("cyan", Color.Cyan), ("white", Color.White), ("default", Color.Default)
  , ("lightgrey", Color.Gray), ("grey", Color.DarkGray), ("darkgrey", Color.DarkGray)
  , ("navy", Color.DarkBlue), ("teal", Color.DarkCyan), ("maroon", Color.DarkRed), ("purple", Color.DarkMagenta)
  , ("olive", Color.DarkYellow), ("silver", Color.Gray), ("lime", Color.Green), ("aqua", Color.Cyan)
  , ("fuchsia", Color.Magenta), ("darkgray", Color.DarkGray)]

def readColor (s : String) : Option Color :=
  colors.lookup (norm s)

def updaters : List (String × (Color → ColorScheme → ColorScheme)) :=
  [ ("type", fun color scheme => { scheme with colorType := color, colorTypeCon := color, colorTypeVar := color, colorTypeKeyword := color, colorEffect := color })
  , ("kind", fun color scheme => { scheme with colorKind := color })
  , ("marker", fun color scheme => { scheme with colorMarker := color })
  , ("warning", fun color scheme => { scheme with colorWarning := color })
  , ("error", fun color scheme => { scheme with colorError := color })
  , ("source", fun color scheme => { scheme with colorSource := color })
  , ("interpreter", fun color scheme => { scheme with colorInterpreter := color })
  , ("command", fun color scheme => { scheme with colorCommand := color })
  , ("keyword", fun color scheme => { scheme with colorKeyword := color, colorTypeKeyword := color })
  , ("typecon", fun color scheme => { scheme with colorTypeCon := color })
  , ("typevar", fun color scheme => { scheme with colorTypeVar := color })
  , ("typekeyword", fun color scheme => { scheme with colorTypeKeyword := color })
  , ("range", fun color scheme => { scheme with colorRange := color })
  , ("sep", fun color scheme => { scheme with colorSep := color })
  , ("comment", fun color scheme => { scheme with colorComment := color })
  , ("reserved", fun color scheme => { scheme with colorReserved := color })
  , ("reservedop", fun color scheme => { scheme with colorReservedOp := color })
  , ("special", fun color scheme => { scheme with colorSpecial := color })
  , ("string", fun color scheme => { scheme with colorString := color })
  , ("number", fun color scheme => { scheme with colorNumber := color })
  , ("module", fun color scheme => { scheme with colorModule := color })
  , ("effect", fun color scheme => { scheme with colorEffect := color })
  , ("parameter", fun color scheme => { scheme with colorParameter := color })
  , ("cons", fun color scheme => { scheme with colorCons := color })
  , ("constructor", fun color scheme => { scheme with colorCons := color })
  , ("none", fun color _ => makeColorScheme color)
  , ("all", fun color _ => makeColorScheme color)
  , ("implicitparameter", fun color scheme => { scheme with colorImplicitParameter := color })
  , ("implicitexpr", fun color scheme => { scheme with colorImplicitExpr := color })
  ]

def readUpdate (s : String) : Option (Color → ColorScheme → ColorScheme) :=
  updaters.lookup (norm s)

def readColorFlag (s : String) (scheme : ColorScheme) : ColorScheme :=
  let (nameList, xs) := s.toList.span (fun c => c ≠ '=' && c ≠ ':')
  let name := String.ofList nameList
  match xs with
  | c :: clr =>
    if c == '=' || c == ':' then
      match readUpdate name, readColor (String.ofList clr) with
      | some update, some color => update color scheme
      | _, _ => scheme
    else scheme
  | [] =>
    match colorThemes.lookup name with
    | some theme => theme
    | none =>
      match readUpdate name with
      | some update => update Color.Default scheme
      | none => scheme

def splitOnChars (cs : List Char) : List (List Char) :=
  match cs with
  | [] => [[]]
  | c :: cs =>
    let rest := splitOnChars cs
    if c == ',' || c == ';' then [] :: rest
    else match rest with
      | [] => [[c]]
      | r :: rs => (c :: r) :: rs

def readColorFlags (s : String) (scheme : ColorScheme) : ColorScheme :=
  let parts := (splitOnChars s.toList).map String.ofList
  parts.foldl (fun sch part => readColorFlag part sch) scheme

def ansiColor (c : Color) : Int :=
  match c with
  | .Black => 30 | .DarkRed => 31 | .DarkGreen => 32 | .DarkYellow => 33
  | .DarkBlue => 34 | .DarkMagenta => 35 | .DarkCyan => 36 | .Gray => 37
  | .DarkGray => 90 | .Red => 91 | .Green => 92 | .Yellow => 93
  | .Blue => 94 | .Magenta => 95 | .Cyan => 96 | .White => 97
  | .Default => 39

end Koka.Common.ColorScheme
