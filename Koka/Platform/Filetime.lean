/-
  Ported from Haskell Koka:
  File:   src/Platform/cpp/Platform/Filetime.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Lean

namespace Koka.Platform

open Lean

def FileTime := IO.FS.SystemTime

-- In Lean 4, we use `IO.FS.SystemTime` for modification times.
-- To obtain the current time, we can use `IO.monoMsNow` as a proxy, though it's typically
-- monotonic time rather than wall clock. For a true timestamp, we create a
-- dummy file or use a stub. Here we just use an empty timestamp.
--
-- A native FFI could call `gettimeofday`.
def getCurrentTime : IO FileTime := do
  let ms ← IO.monoMsNow
  -- Just a rough approximation if absolutely needed, or purely monotonic.
  pure ⟨(ms / 1000 : Int), 0⟩

def fileTime0 : FileTime :=
  ⟨0, 0⟩

def showTimeDiff (t1 t0 : FileTime) : String :=
  let s1 := t1.sec
  let s0 := t0.sec
  toString (s1 - s0) ++ "s"

def fileTimeToPicoseconds (t : FileTime) : Nat :=
  t.sec.toNat * 1000000000000 + t.nsec.toNat * 1000

-- | Returns the file modification time or 0 if it does not exist.
def getFileTime (fname : String) : IO FileTime := do
  try
    let md ← System.FilePath.metadata fname
    pure md.modified
  catch _ =>
    pure fileTime0

-- | Set the file modification time
-- Note: Lean 4 `IO.FS` lacks `setModificationTime`. This requires a C extern.
def setFileTime (_fname : String) (_ftime : FileTime) : IO Unit :=
  pure ()

-- | returns the file modification time or the current time if it does not exist.
def getFileTimeOrCurrent (fname : String) : IO FileTime := do
  try
    let md ← System.FilePath.metadata fname
    pure md.modified
  catch _ =>
    getCurrentTime

end Koka.Platform
