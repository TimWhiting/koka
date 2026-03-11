/-
  Ported from Haskell Koka:
  File:   src/Common/NameMap.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Std.Data.HashMap
import Koka.Common.Name
import Koka.Common.Failure

namespace Koka.Common

open Koka.Common.Name
open Koka.Common.Failure

abbrev NameMap (α : Type) := Std.HashMap Name α

def NameMap.find {α : Type} [Inhabited α] (name : Name) (map : NameMap α) : α :=
  match map.get? name with
  | some x => x
  | none => failure s!"Common.NameMap.find: could not find: {name}"

end Koka.Common
