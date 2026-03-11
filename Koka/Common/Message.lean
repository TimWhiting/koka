/-
  Ported from Haskell Koka:
  File:   src/Common/Message.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Koka.Lib.PPrint
import Koka.Common.Failure
import Koka.Common.Range
import Koka.Common.ColorScheme

namespace Koka.Common.Message

open Koka.Lib.PPrint
open Koka.Common.Range
open Koka.Common.ColorScheme

--------------------------------------------------------------------------
-- Pretty print helpers
--------------------------------------------------------------------------
def ppRange (cwd : String) (endToo : Bool) (colors : ColorScheme) (r : Range) : Doc :=
  color colors.colorRange (textP (showRange cwd endToo r))

def tablex (n : Int) (xs : List (Doc × Doc)) : Doc :=
  let headers := xs.map (·.1)
  let headerwidth := headers.map (fun h => (displayS (renderCompact h)).length) |>.foldl max 0
  indent n <|
    if headerwidth <= 0 then
      vcat (xs.map (·.2))
    else
      let rows := xs.map fun (header, doc) =>
        fill headerwidth header |> beside colon |> beside space |> beside (align doc)
      vcat rows

def table (xs : List (Doc × Doc)) : Doc :=
  tablex 0 xs

--------------------------------------------------------------------------
-- Source from range
--------------------------------------------------------------------------

def removeIndent (ls : List String) : List String :=
  let spaces := ls.map (fun line => (line.takeWhile Char.isWhitespace |>.toString).length)
  let i := spaces.foldl min (spaces.headD 0)
  ls.map (fun line => line.drop i |>.toString)

def limitLines (n : Nat) (ls : List String) : List String :=
  if ls.length <= n then
    removeIndent ls
  else if n <= 2 then
    panic! "Message.docFromRange.limitLines: illegal n"
  else
    let n2 := n / 2
    let pre := ls.take n2
    let post := ls.reverse.take n2 |>.reverse
    let prepost := removeIndent (pre ++ post)
    prepost.take n2 ++ ["..."] ++ prepost.drop n2

def limitLineLen (n : Nat) (line : String) : String :=
  if line.length <= n then
    line
  else
    let n3 := n / 3
    let x := line.take (2 * n3) |>.toString
    let y := line.drop (2 * n3) |>.toString
    let pre := String.ofList (x.toList.reverse.dropWhile Char.isWhitespace).reverse
    let post := String.ofList (y.take n3 |>.toString.toList.reverse.dropWhile Char.isWhitespace).reverse
    pre ++ " ... " ++ post

def docFromRange (colors : ColorScheme) (range : Range) : Doc :=
  let src := sourceFromRange range |>.splitOn "\n"
  let limitedLines := limitLines 3 src |>.map (limitLineLen 80)
  match limitedLines with
  | [] => empty
  | srcLines => color colors.colorSource (align (vcat (srcLines.map textP)))

def docsFromRanges (colors : ColorScheme) (ranges : List Range) : List Doc :=
  ranges.map (docFromRange colors)

end Koka.Common.Message
