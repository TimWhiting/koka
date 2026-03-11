/-
  Ported from Haskell Koka:
  File:   src/Interpreter/Command.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Koka.Lib.PPrint
import Koka.Common.ColorScheme
import Koka.Common.Name

namespace Koka.Interpreter.Command

open Koka.Lib.PPrint
open Koka.Common.ColorScheme
open Koka.Common.Name

--------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------

inductive ShowCommand
  | ShowSource
  | ShowTypeSigs
  | ShowKindSigs
  | ShowSynonyms
  | ShowDefines
  | ShowHelp
  | ShowVersion
  deriving Repr, BEq

inductive Command
  | Quit
  | Error (msg : String)
  | Load (fpaths : List String) (force : Bool)
  | Reload
  | Eval (expr : String)
  | TypeOf (expr : String)
  | KindOf (expr : String)
  | Define (expr : String)
  | TypeDef (expr : String)
  | Options (opts : String)
  | Edit (fpath : String)
  | Shell (cmd : String)
  | ChangeDir (fpath : String)
  | Show (cmd : ShowCommand)
  | None
  deriving Repr, BEq

--------------------------------------------------------------------------
-- Parsing Helpers
--------------------------------------------------------------------------

def removeBackspaces (s : String) : String :=
  let rec go (acc : List Char) (cs : List Char) :=
    match cs with
    | [] => acc.reverse
    | '\x08' :: rest =>
      match acc with
      | [] => go acc rest
      | _ :: as => go as rest
    | c :: rest => go (c :: acc) rest
  String.ofList (go [] s.toList)

-- Parse arguments handling quotes
def parseFilenames (s : String) : List String :=
  let rec go (acc : List String) (curr : List Char) (inQuote : Bool) (cs : List Char) : List String :=
    match cs with
    | [] => if curr.isEmpty then acc else String.ofList curr.reverse :: acc |>.reverse
    | '"' :: rest =>
      if inQuote then go (String.ofList curr.reverse :: acc) [] false rest
      else go acc [] true rest
    | c :: rest =>
      if c.isWhitespace && !inQuote then
        if curr.isEmpty then go acc [] false rest
        else go (String.ofList curr.reverse :: acc) [] false rest
      else go acc (c :: curr) inQuote rest
  -- Start `toList` without trailing whitespaces or anything
  go [] [] false s.trimAscii.toString.toList

def parseCommandExpression (s : String) : Command :=
  let s_trim := s.trimAscii.toString
  if s_trim.isEmpty then Command.None
  else if s_trim.startsWith "fun " || s_trim.startsWith "val " then Command.Define s_trim
  else if s_trim.startsWith "type " || s_trim.startsWith "open type " || s_trim.startsWith "extend type " ||
          s_trim.startsWith "co type " || s_trim.startsWith "div type " || s_trim.startsWith "alias " || s_trim.startsWith "struct "
  then Command.TypeDef s_trim
  else Command.Eval s_trim

def parseCommandCmd (cmd : String) (args : String) : Command :=
  let args_trim := args.trimAscii.toString
  match cmd.toLower with
  | "l" | "load" => Command.Load (parseFilenames args_trim) false
  | "f" | "fload" => Command.Load (parseFilenames args_trim) true
  | "r" | "reload" => Command.Reload
  | "q" | "quit" => Command.Quit
  | "e" | "edit" => Command.Edit args_trim
  | "cd" => Command.ChangeDir args_trim
  | "!" => Command.Shell args_trim
  | "?" | "h" | "help" => Command.Show ShowCommand.ShowHelp
  | "t" | "type" | "b" | "browse" =>
    if args_trim.isEmpty then Command.Show ShowCommand.ShowTypeSigs
    else Command.TypeOf args_trim
  | "set" => Command.Options args_trim
  | "s" | "source" => Command.Show ShowCommand.ShowSource
  | "k" | "kind" =>
    if args_trim.isEmpty then Command.Show ShowCommand.ShowKindSigs
    else Command.KindOf args_trim
  | "d" | "defines" => Command.Show ShowCommand.ShowDefines
  | "alias" => Command.Show ShowCommand.ShowSynonyms
  | "w" | "warranty" | "version" => Command.Show ShowCommand.ShowVersion
  | _ => Command.Error s!"unknown command: :{cmd}"

def parseCommand (input : String) : Command :=
  let s := (removeBackspaces input).dropWhile Char.isWhitespace |>.toString
  if s.isEmpty then Command.None
  else if s.startsWith ":" then
    let cmdPartFull := s.takeWhile (!·.isWhitespace)
    let cmdPart := cmdPartFull.drop 1 |>.toString
    let argsPart := s.drop cmdPartFull.toString.length |>.toString
    parseCommandCmd cmdPart argsPart
  else
    parseCommandExpression s

def readCommand (line : String) : Command :=
  parseCommand line

--------------------------------------------------------------------------
-- Help formatting
--------------------------------------------------------------------------

def commandHelp (colors : ColorScheme) : Doc :=
  let infotext (s : String) := color colors.colorInterpreter (textP s)
  let cmd (c arg explain : String) :=
    fill 12 (textP c) <.> fill 14 (textP arg) <.> infotext explain

  vsep [
    hang 2 (vsep [infotext "commands:", vcat [
      cmd "<expression>" "" "evaluate the given expression",
      cmd ":l[oad]" "{modulename}" "load module(s)",
      cmd ":f[load]" "{modulename}" "force load module(s) rebuilding everything",
      cmd ":r[eload]" "" "reload the current module(s)",
      cmd ":e[dit]" "[filename]" "edit file (and jump to error location)",
      cmd ":set" "<options>" "set (command line) options",
      empty,
      cmd ":t[ype]" "[expression]" "show type signature(s) (of a given expression)",
      cmd ":k[ind]" "" "show kind signatures in scope",
      cmd ":alias" "" "show type alias signatures",
      cmd ":version" "" "show version and warranty information",
      cmd ":cd" "" "show the current directory",
      cmd ":cd" "<directory>" "change the current directory",
      cmd ":!" "<command>" "run a shell command",
      cmd ":?" "" "show this information",
      cmd ":q[uit]" "" "quit the interpreter",
      empty
    ]]),
    hang 2 (vsep [infotext "remarks:", vcat [
      textP "Use :set -? to see help on command line flags."
    ]])
  ]

end Koka.Interpreter.Command
