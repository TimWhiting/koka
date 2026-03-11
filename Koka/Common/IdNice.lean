/-
  Ported from Haskell Koka:
  File:   src/Common/IdNice.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Std.Data.HashMap
import Koka.Common.Id
import Koka.Common.IdMap

namespace Koka.Common

structure Nice where
  map : IdMap String

def niceEmpty : Nice :=
  ⟨{}⟩

def niceExtend (ids : Ids) (names : List String) (nice : Nice) : Nice :=
  let usedNames := nice.map.fold (fun acc _ v => v :: acc) []
  let isNotUsed (n : String) := !usedNames.contains n
  let niceNames := (names.filter isNotUsed).take ids.length
  let newMap := (ids.zip niceNames).foldl (fun m (id, name) =>
    if m.contains id then m else m.insert id name) nice.map
  ⟨newMap⟩

def niceShow (nice : Nice) (id : Id) : String :=
  match nice.map.get? id with
  | some name => name
  | none => toString id

def nicePretty (nice : Nice) (id : Id) : String :=
  niceShow nice id

end Koka.Common
