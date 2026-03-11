/-
  Ported from Haskell Koka:
  File:   src/Platform/cpp/Platform/Var.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
namespace Koka.Platform

-- Note: In a fully native Lean 4 codebase, usages of `Var` should be directly replaced
-- with `IO.Ref` or `ST.Ref` depending on the required scoping and mutability context.
def Var (a : Type) := IO.Ref a

def newVar {a : Type} (val : a) : IO (Var a) :=
  IO.mkRef val

def takeVar {a : Type} (v : Var a) : IO a :=
  v.get

def putVar {a : Type} (v : Var a) (val : a) : IO Unit :=
  v.set val

end Koka.Platform
