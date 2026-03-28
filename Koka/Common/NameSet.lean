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

instance : EmptyCollection NameSet := ⟨{}⟩

def NameSet.empty : NameSet := {}

def NameSet.singleton (n : Name) : NameSet :=
  ({} : NameSet).insert n

def NameSet.union (s1 s2 : NameSet) : NameSet :=
  s2.fold (λ acc n => acc.insert n) s1

def NameSet.unions (ss : List NameSet) : NameSet :=
  ss.foldl NameSet.union {}

def NameSet.delete (n : Name) (s : NameSet) : NameSet :=
  s.erase n

end Koka.Common
