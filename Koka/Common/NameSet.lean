/-
  Ported from Haskell Koka:
  File:   src/Common/NameSet.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Std.Data.HashSet
import Koka.Common.Name

namespace Koka.Common

open Koka.Common.Name

abbrev NameSet := Std.HashSet Name

end Koka.Common
