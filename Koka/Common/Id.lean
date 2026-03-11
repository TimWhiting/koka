/-
  Ported from Haskell Koka:
  File:   src/Common/Id.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
namespace Koka.Common

abbrev Id := Int
abbrev Ids := List Id

namespace Id

def showId (id : Id) : String :=
  s!"\"{id}\""

def genId (_baseName : String) (i : Int) : Id :=
  i

def newId (i : Int) : Id :=
  i

def newIdFromId (id : Id) : Id :=
  id + 1

def idNil : Id :=
  newId 0

def idNumber (i : Id) : Int :=
  i

end Id
end Koka.Common
