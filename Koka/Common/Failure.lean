/-
  Ported from Haskell Koka:
  File:   src/Common/Failure.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
namespace Koka.Common.Failure

def assertion {α : Type} [Inhabited α] (msg : String) (test : Bool) (x : α) : α :=
  if test then x else panic! msg

def failure {α : Type} [Inhabited α] (msg : String) : α :=
  panic! msg

def todo {α : Type} [Inhabited α] (msg : String) : α :=
  failure ("todo: " ++ msg)

def matchFailure {α : Type} [Inhabited α] (msg : String) : α :=
  failure ("unmatched pattern: " ++ msg)

def raise {α : Type} [Inhabited α] (msg : String) : α :=
  panic! msg

def raiseIO {α : Type} (msg : String) : IO α :=
  throw (IO.userError msg)

def catchIO {α : Type} (act : IO α) (handler : String → IO α) : IO α := do
  try
    act
  catch e =>
    handler (toString e)

end Koka.Common.Failure
