/-
  Ported from Haskell Koka:
  File:   src/Kind/ImportMap.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Koka.Common.Name
import Koka.Lib.Trace

namespace Koka.Kind.ImportMap

open Koka.Common.Name
open Koka.Lib.Trace

-- | Maps short module aliases @core@ to full module paths @std/core@.
-- It is represented as a map from a reversed list of module path components to a full name
-- i.e. import my/core = std/core  ->  [(["core","my"], newModuleName "std/core")]
abbrev ImportMap := List (List String × Name)

def importsEmpty : ImportMap := []

def listLookup {α β} [BEq α] (k : α) : List (α × β) → Option β
  | [] => none
  | (k', v) :: xs => if k == k' then some v else listLookup k xs

def importsExtend (aliasName : Name) (fullName : Name) (imp : ImportMap) : Option ImportMap :=
  let rpath := (splitModuleName aliasName).reverse
  match listLookup rpath imp with
  | none => some ((rpath, fullName) :: imp)
  | some fullName1 => if fullName == fullName1 then some imp else none

-- | Given a fully qualified name, return the shorter aliased name.
-- For example, with @import f = system/foo@ a name @system/foo/bar@ is shortened to @f/bar@.
def importsAlias (name : Name) (imp : ImportMap) : Name :=
  let mname := qualifier name
  let filtered := imp.filter (fun (_, modName) => modName == mname)
  match filtered with
  | [(ralias, _)] =>
    let alias := unsplitModuleName ralias.reverse
    qualify alias (unqualify name)
  | _ => name

def importsList (importMap : ImportMap) : List (Name × Name) :=
  importMap.map (fun (ralias, modName) => (unsplitModuleName ralias.reverse, modName))

def isPrefixOf [BEq α] : List α → List α → Bool
  | [], _ => true
  | _, [] => false
  | x::xs, y::ys => x == y && isPrefixOf xs ys

-- | @importsExpand name map@ takes a qualified name (@core/int@) and expands
-- it to its real fully qualified name (@std/core/int@). It also returns
-- the declared alias suffix (used to find case-errors).
-- On ambiguity, or if not found at all, it returns Left with a list of candidates.
-- Since declarations can have namespace'd names (@int/eq@) we take
-- the longest prefix that matches an import module.
partial def importResolvePath (basename : Name) (rpath : List String) (imports : ImportMap) : Except (List Name) (Name × Name) :=
  match rpath with
  | [] => Except.ok (basename, nameNil) -- unqualified
  | _ =>
    match imports.filter (fun (ralias, _) => isPrefixOf rpath ralias) with
    | [(ralias, modName)] =>
      let qname := qualify modName basename
      let alias := unsplitModuleName (ralias.take rpath.length).reverse
      Except.ok (qname, alias)
    | [] =>
      match rpath with
      | q :: qs =>
        match importResolvePath basename qs imports with
        | Except.ok (qname, alias) => Except.ok (qualifyLocally (newModuleName q) qname, alias)
        | Except.error err => Except.error err
      | [] => unreachable!
    | amb => Except.error (amb.map (fun (ralias, _) => unsplitModuleName ralias.reverse))

def importsExpand (name : Name) (imports : ImportMap) : Except (List Name) (Name × Name) :=
  let rpath := (splitModuleName (qualifier name)).reverse
  importResolvePath (unqualify name) rpath imports

end Koka.Kind.ImportMap
