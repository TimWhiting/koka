/-
  Ported from Haskell Koka:
  File:   src/Platform/cpp/Platform/Console.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Lean

namespace Koka.Platform.Console

-- Note: Lean 4 natively handles output and ANSI escape sequences
-- in `IO.FS.Stream`. Thus, `consoleInit` and state setup from the
-- old FFI `cconsole.c` are not strictly necessary here. We stub
-- out the state configurations and rely on pure string outputs.

def setColor {c : Type} (_color : c) : IO Unit :=
  pure ()

def setBackColor {c : Type} (_color : c) : IO Unit :=
  pure ()

def setReverse (_r : Bool) : IO Unit :=
  pure ()

def setUnderline (_u : Bool) : IO Unit :=
  pure ()

-- | Initialize the console module. Passes 'True' on success.
def withConsole {α : Type} (f : Bool → IO α) : IO α :=
  f true

-- | Restore the console state after a computation
def bracketConsole {α : Type} (io : IO α) : IO α :=
  io

-- | Retrieve the path to the currently executing program.
def getProgramPath : IO String := do
  let p ← IO.appPath
  pure p.toString

end Koka.Platform.Console
