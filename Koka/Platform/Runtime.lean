/-
  Ported from Haskell Koka:
  File:   src/Platform/cpp/Platform/Runtime.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Lean

namespace Koka.Platform.Runtime

-- | Equivalent of `unsafePerformIO` in Haskell.
-- Note: Lean 4 avoids this strongly, but we can bypass it using `cast` or other hacks
-- if strictly needed. For porting, it's better to refactor usages out, but we provide
-- an unsafe shim here that just executes immediately via an unchecked cast to pure.
unsafe def unsafePerformIOUnsafe {α : Type} (io : IO α) : α :=
  -- This is extremely dangerous and violates Lean's memory model if used for anything
  -- that performs actual state mutations or FFI calls that can be reordered.
  let res := io
  unsafeCast res

axiom unsafePerformIO_axiom {α : Type} : α

@[implemented_by unsafePerformIOUnsafe]
def unsafePerformIO {α : Type} (io : IO α) : α := unsafePerformIO_axiom

-- | Executes an IO action and catches standard IO exceptions.
-- Note: In native Lean 4, it is highly recommended to use the standard `try ... catch e => ...`
-- block directly rather than wrapping it in this function, as it provides better type inference
-- and integration with Lean's `EIO` and `IO` monads.
def exCatch {α : Type} (io : IO α) (handler : String → IO α) : IO α :=
  try
    io
  catch e =>
    handler e.toString

-- | Runs a finalizer after an IO action.
-- Note: Lean 4 has built-in `try ... catch ... finally ...` constructs or resource management
-- via `bracket` and `finally` in the `MonadExcept` and `MonadFinally` typeclasses.
-- Usages of this should ideally be migrated to the native `try ... finally ...` block.
def «finally» {α β : Type} (io : IO α) (post : IO β) : IO α :=
  try
    let res ← io
    let _ ← post
    pure res
  catch e =>
    let _ ← post
    throw e

-- | Placeholder for formatting float as hex string in Haskell's `Numeric.showHFloat`.
-- A complete port might use a C extern binding to `snprintf` with `%a`, but
-- we fallback to standard stringification for now.
def showHFloat (d : Float) (s : String) : String :=
  s!"{d}{s}"

end Koka.Platform.Runtime
