/-
  Ported from Haskell Koka:
  File:   src/Common/Unique.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Koka.Common.Id
import Koka.Common.Name

namespace Koka.Common

open Koka.Common.Id
open Koka.Common.Name

class HasUnique (m : Type → Type) where
  updateUnique : (Int → Int) → m Int

def setUnique {m : Type → Type} [Monad m] [HasUnique m] (i : Int) : m PUnit := do
  let _ ← HasUnique.updateUnique (fun _ => i)
  pure PUnit.unit

def unique {m : Type → Type} [Monad m] [HasUnique m] : m Int :=
  HasUnique.updateUnique (· + 1)

def uniques {m : Type → Type} [Monad m] [HasUnique m] (n : Int) : m (List Int) :=
  let rec go (x : Nat) : m (List Int) :=
    match x with
    | 0 => pure []
    | x + 1 => do
      let i ← unique
      let is ← go x
      pure (i :: is)
  go (if n < 0 then 0 else n.toNat)

def uniqueId {m : Type → Type} [Monad m] [HasUnique m] (baseName : String) : m Id := do
  let i ← unique
  pure (genId baseName i)

def uniqueIds {m : Type → Type} [Monad m] [HasUnique m] (baseName : String) (n : Int) : m (List Id) := do
  let is ← uniques n
  pure (is.map (genId baseName))

def uniqueName {m : Type → Type} [Monad m] [HasUnique m] (pre : String) : m Name := do
  let i ← unique
  pure (newHiddenNameEx pre (toString i))

def uniqueNameFrom {m : Type → Type} [Monad m] [HasUnique m] (baseName : Name) : m Name := do
  let i ← unique
  pure (toHiddenUniqueName i "uniq" baseName)

def Unique (α : Type) := Int → α × Int

instance : Functor Unique where
  map f u := fun i => let (x, j) := u i; (f x, j)

instance : Applicative Unique where
  pure x := fun i => (x, i)
  seq f x := fun i =>
    let (g, j) := f i
    let (v, k) := x () j
    (g v, k)

instance : Monad Unique where
  bind u f := fun i =>
    let (x, j) := u i
    f x j

instance : HasUnique Unique where
  updateUnique f := fun i => (i, f i)

def runUnique {α : Type} (i : Int) (u : Unique α) : α × Int :=
  u i

def runUniqueWith {α : Type} (ids : List Id) (u : Unique α) : α :=
  let maxId := ids.foldr (fun id acc => max (idNumber id) acc) 0
  (runUnique (maxId + 1) u).1

def withUnique {m : Type → Type} [Monad m] [HasUnique m] {α : Type} (f : Int → α × Int) : m α := do
  let u ← unique
  let (x, u') := f u
  setUnique u'
  pure x

def liftUnique {m : Type → Type} [Monad m] [HasUnique m] {α : Type} (uniq : Unique α) : m α :=
  withUnique (fun u => runUnique u uniq)

def UniqueT (m : Type → Type) (α : Type) := Int → m (α × Int)

def runUniqueT {m : Type → Type} {α : Type} (i : Int) (u : UniqueT m α) : m (α × Int) :=
  u i

instance {m : Type → Type} [Monad m] : HasUnique (UniqueT m) where
  updateUnique f := fun i => pure (i, f i)

instance {m : Type → Type} [Monad m] : Functor (UniqueT m) where
  map f u := fun i => do
    let (x, j) ← u i
    pure (f x, j)

instance {m : Type → Type} [Monad m] : Applicative (UniqueT m) where
  pure x := fun i => pure (x, i)
  seq f x := fun i => do
    let (g, j) ← f i
    let (v, k) ← x () j
    pure (g v, k)

instance {m : Type → Type} [Monad m] : Monad (UniqueT m) where
  bind u f := fun i => do
    let (x, j) ← u i
    f x j

end Koka.Common
