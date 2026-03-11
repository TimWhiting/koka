/-
  Ported from Haskell Koka:
  File:   src/Common/QNameMap.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Std.Data.HashMap
import Koka.Common.Name
import Koka.Common.Failure

namespace Koka.Common.QNameMap

open Koka.Common.Name
open Koka.Common.Failure

----------------------------------------------------------------
-- Types
----------------------------------------------------------------

abbrev QNameMap (α : Type) := Std.HashMap Name (List (Name × α))

inductive Lookup (α : Type)
  | Found (name : Name) (val : α)
  | Ambiguous (names : List Name)
  | NotFound
  deriving Inhabited, Repr

def empty {α : Type} : QNameMap α :=
  ∅

def isEmpty {α : Type} (m : QNameMap α) : Bool :=
  m.isEmpty

def safeCombine {α : Type} (method : String) (xs ys : List (Name × α)) : List (Name × α) :=
  let ynames := ys.map Prod.fst
  let xnames := xs.map Prod.fst
  if xnames.any (fun x => ynames.contains x) then
    panic! s!"Common.QNameMap.{method}: overlapping names: {xnames} and {ynames}"
  else
    xs ++ ys

def insert {α : Type} (name : Name) (x : α) (m : QNameMap α) : QNameMap α :=
  let k := unqualify name
  match m.get? k with
  | none => m.insert k [(name, x)]
  | some old => m.insert k (safeCombine "insert" [(name, x)] old)

def single {α : Type} (name : Name) (x : α) : QNameMap α :=
  insert name x empty

def fromList {α : Type} (xs : List (Name × α)) : QNameMap α :=
  xs.foldl (fun qm (name, x) => insert name x qm) empty

def lookupQ {α : Type} (name : Name) (m : QNameMap α) : Option α :=
  match m.get? (unqualify name) with
  | none => none
  | some xs =>
    match xs.find? (fun (n, _) => n == name) with
    | some (_, x) => some x
    | none => none

def lookup {α : Type} (context : Name) (name : Name) (m : QNameMap α) : Lookup α :=
  match m.get? (unqualify name) with
  | none => Lookup.NotFound
  | some [(qname, x)] =>
    if !isQualified name then Lookup.Found qname x
    else
      let qname' := if isQualified name then name else qualify context name
      let ms := [(qname, x)].filter (fun (n, _) => n == qname')
      match ms with
      | [(realname, val)] => Lookup.Found realname val
      | _ => Lookup.Ambiguous [qname]
  | some xs =>
    let qname' := if isQualified name then name else qualify context name
    let ms := xs.filter (fun (n, _) => n == qname')
    match ms with
    | [(realname, val)] => Lookup.Found realname val
    | _ => Lookup.Ambiguous (xs.map Prod.fst)

def filterNames {α : Type} (pred : Name → Bool) (m : QNameMap α) : QNameMap α :=
  m.fold (fun acc k xs =>
    let xs' := xs.filter (fun (n, _) => pred n)
    if xs'.isEmpty then acc else acc.insert k xs'
  ) empty

def union {α : Type} (m1 m2 : QNameMap α) : QNameMap α :=
  m2.fold (fun acc k v2 =>
    match acc.get? k with
    | none => acc.insert k v2
    | some v1 => acc.insert k (safeCombine "union" v1 v2)
  ) m1

def unionLeftBias {α : Type} (m1 m2 : QNameMap α) : QNameMap α :=
  m2.fold (fun acc k v2 =>
    match acc.get? k with
    | none => acc.insert k v2
    | some v1 => acc.insert k (v1 ++ v2)
  ) m1

def unions {α : Type} (qs : List (QNameMap α)) : QNameMap α :=
  qs.foldl union empty

def toAscList {α : Type} (m : QNameMap α) : List (Name × α) :=
  let lst_nested := m.toList.map Prod.snd
  let lst := lst_nested.foldl List.append []
  let arr := lst.toArray.qsort (fun a b => compare a.fst b.fst == Ordering.lt)
  arr.toList

end Koka.Common.QNameMap
