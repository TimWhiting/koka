/-
  Ported from Haskell Koka:
  File:   src/Common/IdMap.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Std.Data.HashMap

namespace Koka.Common

abbrev IdMap (α : Type) := Std.HashMap Int α

end Koka.Common
