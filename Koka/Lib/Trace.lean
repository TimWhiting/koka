/-
  Ported from Haskell Koka:
  File:   src/Lib/Trace.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Koka.Lib.Printer
import Koka.Lib.PPrint
import Koka.Platform.Runtime
import Koka.Common.ColorScheme

namespace Koka.Lib.Trace

open Koka.Lib.Printer
open Koka.Lib.PPrint
open Koka.Common.ColorScheme
open Koka.Platform.Runtime (unsafePerformIO)

def ctrace {α : Type} (_clr : Color) (msg : String) (x : α) : α :=
  dbg_trace msg
  x

def trace {α : Type} (msg : String) (x : α) : α :=
  ctrace Color.DarkGray msg x

def traceShowM {m : Type → Type} [Monad m] {s : Type} [ToString s] (msg : s) : m Unit :=
  trace (toString msg) (pure ())

def traceM {m : Type → Type} [Monad m] (msg : String) : m Unit :=
  trace msg (pure ())

def traceId (x : String) : String :=
  trace x x

def traceShow {s α : Type} [ToString s] (msg : s) (x : α) : α :=
  trace (toString msg) x

def traceShowId {α : Type} [ToString α] (msg : α) : α :=
  trace (toString msg) msg

def traceDoc {α : Type} (msg : Doc) (x : α) : α :=
  trace (displayS (renderCompact msg)) x

def traceEq {α : Type} [ToString α] (name : String) (val : α) : α :=
  trace (name ++ " = " ++ toString val) val

end Koka.Lib.Trace
