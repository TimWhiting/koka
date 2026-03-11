/-
  Ported from Haskell Koka:
  File:   src/Lib/Printer.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Koka.Common.ColorScheme

namespace Koka.Lib.Printer
open Koka.Common.ColorScheme (Color ansiColor)

class Printer (p : Type) where
  write : p → String → IO Unit
  writeText : p → String → IO Unit := write
  writeLn : p → String → IO Unit
  writeTextLn : p → String → IO Unit := writeLn
  flush : p → IO Unit
  withColor : p → Color → IO α → IO α
  withBackColor : p → Color → IO α → IO α
  withReverse : p → Bool → IO α → IO α
  withUnderline : p → Bool → IO α → IO α
  setColor : p → Color → IO Unit
  setBackColor : p → Color → IO Unit
  setReverse : p → Bool → IO Unit
  setUnderline : p → Bool → IO Unit

structure MonoPrinter where
  handle : IO.FS.Handle

instance : Printer MonoPrinter where
  write p s := p.handle.putStr s
  writeLn p s := p.handle.putStrLn s
  flush p := p.handle.flush
  withColor _ _ io := io
  withBackColor _ _ io := io
  withReverse _ _ io := io
  withUnderline _ _ io := io
  setColor _ _ := pure ()
  setBackColor _ _ := pure ()
  setReverse _ _ := pure ()
  setUnderline _ _ := pure ()

def withMonoPrinter (h : IO.FS.Handle) (f : MonoPrinter → IO α) : IO α :=
  f ⟨h⟩

structure FilePrinter where
  handle : IO.FS.Handle

instance : Printer FilePrinter where
  write p s := p.handle.putStr s
  writeLn p s := p.handle.putStrLn s
  flush p := p.handle.flush
  withColor _ _ io := io
  withBackColor _ _ io := io
  withReverse _ _ io := io
  withUnderline _ _ io := io
  setColor _ _ := pure ()
  setBackColor _ _ := pure ()
  setReverse _ _ := pure ()
  setUnderline _ _ := pure ()

def withFilePrinter (fname : String) (f : FilePrinter → IO α) : IO α := do
  let h ← IO.FS.Handle.mk fname IO.FS.Mode.append
  let x ← f ⟨h⟩
  h.flush
  pure x

def withNewFilePrinter (fname : String) (f : FilePrinter → IO α) : IO α := do
  let h ← IO.FS.Handle.mk fname IO.FS.Mode.write
  let x ← f ⟨h⟩
  h.flush
  pure x

structure HtmlPrinter

def htmlEscape (s : String) : String :=
  let escape (c : Char) := match c with
    | '&' => "&amp;"
    | '<' => "&lt;"
    | '>' => "&gt;"
    | '"' => "&quot;"
    | '\'' => "&apos;"
    | '_' => "&#95;"
    | _ => c.toString
  String.ofList (s.toList.flatMap (fun c => (escape c).toList))

def htmlColor (c : Color) : String :=
  match c with
  | Color.Default => "black"
  | _ => (toString c).toLower

def htmlSpan (prop val : String) (io : IO α) : IO α := do
  IO.print s!"<span style='{prop}: {val}'>"
  let x ← io
  IO.print "</span>"
  pure x

instance : Printer HtmlPrinter where
  write _ s := IO.print (htmlEscape s)
  writeLn _ s := IO.println (htmlEscape s)
  flush _ := pure ()
  withColor _ c io := htmlSpan "color" (htmlColor c) io
  withBackColor _ c io := htmlSpan "background-color" (htmlColor c) io
  withReverse _ _ io := io
  withUnderline _ _ io := htmlSpan "text-decoration" "underline" io
  setColor _ _ := pure ()
  setBackColor _ _ := pure ()
  setReverse _ _ := pure ()
  setUnderline _ _ := pure ()

def withHtmlPrinter (f : HtmlPrinter → IO α) : IO α := f ⟨⟩

structure AnsiConsole where
  fcolor : Color
  bcolor : Color
  invert : Bool
  underline : Bool
  deriving Inhabited

def ansiDefault : AnsiConsole := ⟨Color.Default, Color.Default, false, false⟩

def seqReset : String := "0"
def seqUnderline (u : Bool) : String := if u then "4" else ""
def seqReverse (rev : Bool) : String := if rev then "7" else ""
def seqColor (backGround : Bool) (c : Color) : String :=
  let i := ansiColor c
  s!"{i + if backGround then 10 else 0}"

def reqSetConsole (old new : AnsiConsole) : List String :=
  if old.invert > new.invert || old.underline > new.underline then
    [seqReset, seqReverse new.invert, seqUnderline new.underline, seqColor false new.fcolor, seqColor true new.bcolor].filter (!·.isEmpty)
  else
    let diff := [
      if old.invert ≠ new.invert then seqReverse new.invert else "",
      if old.underline ≠ new.underline then seqUnderline new.underline else "",
      if old.fcolor ≠ new.fcolor then seqColor false new.fcolor else "",
      if old.bcolor ≠ new.bcolor then seqColor true new.bcolor else ""
    ].filter (!·.isEmpty)
    diff

def ansiEscape (xs : List String) : String :=
  if xs.isEmpty then ""
  else "\x1b[" ++ String.intercalate ";" xs ++ "m"

def ansiWithColor (color : Color) (s : String) : String :=
  let con0 := ansiDefault
  let con1 := { con0 with fcolor := color }
  let pre := ansiEscape (reqSetConsole con0 con1)
  let post := ansiEscape (reqSetConsole con1 con0)
  pre ++ s ++ post

structure AnsiPrinter where
  state : IO.Ref AnsiConsole

def ansiSetConsole (p : AnsiPrinter) (f : AnsiConsole → AnsiConsole) : IO AnsiConsole := do
  let con ← p.state.get
  let new := f con
  let esc := ansiEscape (reqSetConsole con new)
  if !esc.isEmpty then IO.print esc
  p.state.set new
  pure con

def ansiWithConsole (p : AnsiPrinter) (f : AnsiConsole → AnsiConsole) (io : IO α) : IO α := do
  let old ← ansiSetConsole p f
  let res ← try io catch e => do let _ ← ansiSetConsole p (fun _ => old); throw e
  let _ ← ansiSetConsole p (fun _ => old)
  pure res

instance : Printer AnsiPrinter where
  write _ s := IO.print s
  writeLn _ s := IO.println s
  flush _ := do (← IO.getStdout).flush
  withColor p c io := ansiWithConsole p (fun con => { con with fcolor := c }) io
  withBackColor p c io := ansiWithConsole p (fun con => { con with bcolor := c }) io
  withReverse p r io := ansiWithConsole p (fun con => { con with invert := r }) io
  withUnderline p u io := ansiWithConsole p (fun con => { con with underline := u }) io
  setColor p c := do let _ ← ansiSetConsole p (fun con => { con with fcolor := c }); pure ()
  setBackColor p c := do let _ ← ansiSetConsole p (fun con => { con with bcolor := c }); pure ()
  setReverse p r := do let _ ← ansiSetConsole p (fun con => { con with invert := r }); pure ()
  setUnderline p u := do let _ ← ansiSetConsole p (fun con => { con with underline := u }); pure ()

def withAnsiPrinter (f : AnsiPrinter → IO α) : IO α := do
  let state ← IO.mkRef ansiDefault
  let p : AnsiPrinter := ⟨state⟩
  let res ← try f p catch e => do
    let esc := ansiEscape [seqReset]
    IO.print esc
    (← IO.getStdout).flush
    throw e
  let esc := ansiEscape [seqReset]
  IO.print esc
  (← IO.getStdout).flush
  pure res

structure AnsiStringPrinter where
  state : IO.Ref AnsiConsole
  out : IO.Ref String

def ansiStringSetConsole (p : AnsiStringPrinter) (f : AnsiConsole → AnsiConsole) : IO AnsiConsole := do
  let con ← p.state.get
  let new := f con
  let str ← p.out.get
  p.out.set (str ++ ansiEscape (reqSetConsole con new))
  p.state.set new
  pure con

def ansiStringWithConsole (p : AnsiStringPrinter) (f : AnsiConsole → AnsiConsole) (io : IO α) : IO α := do
  let old ← ansiStringSetConsole p f
  let res ← try io catch e => do let _ ← ansiStringSetConsole p (fun _ => old); throw e
  let _ ← ansiStringSetConsole p (fun _ => old)
  pure res

instance : Printer AnsiStringPrinter where
  write p s := p.out.modify (· ++ s)
  writeLn p s := p.out.modify (· ++ s ++ "\n")
  flush _ := pure ()
  withColor p c io := ansiStringWithConsole p (fun con => { con with fcolor := c }) io
  withBackColor p c io := ansiStringWithConsole p (fun con => { con with bcolor := c }) io
  withReverse p r io := ansiStringWithConsole p (fun con => { con with invert := r }) io
  withUnderline p u io := ansiStringWithConsole p (fun con => { con with underline := u }) io
  setColor p c := do let _ ← ansiStringSetConsole p (fun con => { con with fcolor := c }); pure ()
  setBackColor p c := do let _ ← ansiStringSetConsole p (fun con => { con with bcolor := c }); pure ()
  setReverse p r := do let _ ← ansiStringSetConsole p (fun con => { con with invert := r }); pure ()
  setUnderline p u := do let _ ← ansiStringSetConsole p (fun con => { con with underline := u }); pure ()

structure HtmlTextPrinter where
  out : IO.Ref String

def htmlTextSpan (p : HtmlTextPrinter) (prop val : String) (io : IO α) : IO α := do
  p.out.modify (· ++ s!"<span style='{prop}:{val};'>")
  let x ← io
  p.out.modify (· ++ "</span>")
  pure x

def htmlColor2 (c : Color) : String :=
  match c with
  | .Default => "#000000"
  | .Black => "#000000"
  | .White => "#ffffff"
  | .DarkRed => "#8B0000"
  | .DarkGreen => "#006400"
  | .DarkYellow => "#8B8000"
  | .DarkBlue => "#00008B"
  | .DarkMagenta => "#8B008B"
  | .DarkCyan => "#008B8B"
  | .Gray => "#808080"
  | .DarkGray => "#A9A9A9"
  | .Red => "#FF0000"
  | .Green => "#008000"
  | .Yellow => "#FFFF00"
  | .Blue => "#0000FF"
  | .Magenta => "#FF00FF"
  | .Cyan => "#00FFFF"

instance : Printer HtmlTextPrinter where
  write p s := p.out.modify (· ++ htmlEscape s)
  writeLn p s := p.out.modify (· ++ htmlEscape s ++ "<br>")
  flush _ := pure ()
  withColor p c io := htmlTextSpan p "color" (htmlColor2 c) io
  withBackColor p c io := htmlTextSpan p "background-color" (htmlColor2 c) io
  withReverse _ _ io := io
  withUnderline p _ io := htmlTextSpan p "text-decoration" "underline" io
  setColor _ _ := pure ()
  setBackColor _ _ := pure ()
  setReverse _ _ := pure ()
  setUnderline _ _ := pure ()

def withHtmlTextPrinter (f : HtmlTextPrinter → IO α) : IO α := do
  let out ← IO.mkRef ""
  f ⟨out⟩

inductive ColorPrinter
  | PAnsi (p : AnsiPrinter)
  | PAnsiString (p : AnsiStringPrinter)
  | PMono (p : MonoPrinter)
  | PFile (p : FilePrinter)
  | PHTML (p : HtmlPrinter)
  | PHtmlText (p : HtmlTextPrinter)

def isAnsiPrinter : ColorPrinter → Bool
  | .PAnsi _ => true
  | .PAnsiString _ => true
  | _ => false

def isConsolePrinter : ColorPrinter → Bool
  | _ => false

instance : Printer ColorPrinter where
  write p s := match p with
    | .PAnsi a => Printer.write a s
    | .PAnsiString a => Printer.write a s
    | .PMono a => Printer.write a s
    | .PFile a => Printer.write a s
    | .PHTML a => Printer.write a s
    | .PHtmlText a => Printer.write a s
  writeLn p s := match p with
    | .PAnsi a => Printer.writeLn a s
    | .PAnsiString a => Printer.writeLn a s
    | .PMono a => Printer.writeLn a s
    | .PFile a => Printer.writeLn a s
    | .PHTML a => Printer.writeLn a s
    | .PHtmlText a => Printer.writeLn a s
  flush p := match p with
    | .PAnsi a => Printer.flush a
    | .PAnsiString a => Printer.flush a
    | .PMono a => Printer.flush a
    | .PFile a => Printer.flush a
    | .PHTML a => Printer.flush a
    | .PHtmlText a => Printer.flush a
  withColor p c io := match p with
    | .PAnsi a => Printer.withColor a c io
    | .PAnsiString a => Printer.withColor a c io
    | .PMono a => Printer.withColor a c io
    | .PFile a => Printer.withColor a c io
    | .PHTML a => Printer.withColor a c io
    | .PHtmlText a => Printer.withColor a c io
  withBackColor p c io := match p with
    | .PAnsi a => Printer.withBackColor a c io
    | .PAnsiString a => Printer.withBackColor a c io
    | .PMono a => Printer.withBackColor a c io
    | .PFile a => Printer.withBackColor a c io
    | .PHTML a => Printer.withBackColor a c io
    | .PHtmlText a => Printer.withBackColor a c io
  withReverse p c io := match p with
    | .PAnsi a => Printer.withReverse a c io
    | .PAnsiString a => Printer.withReverse a c io
    | .PMono a => Printer.withReverse a c io
    | .PFile a => Printer.withReverse a c io
    | .PHTML a => Printer.withReverse a c io
    | .PHtmlText a => Printer.withReverse a c io
  withUnderline p c io := match p with
    | .PAnsi a => Printer.withUnderline a c io
    | .PAnsiString a => Printer.withUnderline a c io
    | .PMono a => Printer.withUnderline a c io
    | .PFile a => Printer.withUnderline a c io
    | .PHTML a => Printer.withUnderline a c io
    | .PHtmlText a => Printer.withUnderline a c io
  setColor p c := match p with
    | .PAnsi a => Printer.setColor a c
    | .PAnsiString a => Printer.setColor a c
    | .PMono a => Printer.setColor a c
    | .PFile a => Printer.setColor a c
    | .PHTML a => Printer.setColor a c
    | .PHtmlText a => Printer.setColor a c
  setBackColor p c := match p with
    | .PAnsi a => Printer.setBackColor a c
    | .PAnsiString a => Printer.setBackColor a c
    | .PMono a => Printer.setBackColor a c
    | .PFile a => Printer.setBackColor a c
    | .PHTML a => Printer.setBackColor a c
    | .PHtmlText a => Printer.setBackColor a c
  setReverse p c := match p with
    | .PAnsi a => Printer.setReverse a c
    | .PAnsiString a => Printer.setReverse a c
    | .PMono a => Printer.setReverse a c
    | .PFile a => Printer.setReverse a c
    | .PHTML a => Printer.setReverse a c
    | .PHtmlText a => Printer.setReverse a c
  setUnderline p c := match p with
    | .PAnsi a => Printer.setUnderline a c
    | .PAnsiString a => Printer.setUnderline a c
    | .PMono a => Printer.setUnderline a c
    | .PFile a => Printer.setUnderline a c
    | .PHTML a => Printer.setUnderline a c
    | .PHtmlText a => Printer.setUnderline a c

def withColorPrinter (f : ColorPrinter → IO β) : IO β :=
  withAnsiPrinter (fun p => f (.PAnsi p))

def withHtmlColorPrinter (f : ColorPrinter → IO β) : IO β :=
  withHtmlPrinter (fun p => f (.PHTML p))

def withNoColorPrinter (h : IO.FS.Handle) (f : ColorPrinter → IO β) : IO β :=
  withMonoPrinter h (fun p => f (.PMono p))

def withFileNoColorPrinter (fname : String) (f : ColorPrinter → IO β) : IO β :=
  withFilePrinter fname (fun p => f (.PFile p))

end Koka.Lib.Printer
