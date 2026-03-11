/-
  Ported from Haskell Koka:
  File:   src/Lib/Scc.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
import Std.Data.HashMap
import Std.Data.HashSet

namespace Koka.Lib.Scc

open Std

--------------------------------------------------------------------
-- Graph
--------------------------------------------------------------------
structure Graph (V : Type) [BEq V] [Hashable V] where
  g : HashMap V (List V)

def Graph.nodes {V} [BEq V] [Hashable V] (g : Graph V) : List (V × List V) :=
  g.g.toList

def graph {V} [BEq V] [Hashable V] (es : List (V × List V)) : Graph V :=
  let m := es.foldl (fun acc (v, ws) => acc.insert v (ws ++ acc.getD v [])) (∅ : HashMap V (List V))
  Graph.mk m

--------------------------------------------------------------------
-- Graph functions
--------------------------------------------------------------------
def Graph.edges {V} [BEq V] [Hashable V] (g : Graph V) : List (V × V) :=
  g.nodes.flatMap (fun (v, ws) => ws.map (fun w => (v, w)))

def Graph.vertices {V} [BEq V] [Hashable V] (g : Graph V) : List V :=
  g.nodes.map (·.1)

def Graph.successors {V} [BEq V] [Hashable V] (g : Graph V) (val : V) : List V :=
  g.g.getD val []

def Graph.transpose {V} [BEq V] [Hashable V] (g : Graph V) : Graph V :=
  let emptyMap := g.nodes.foldl (fun m (v, _) => m.insert v []) (∅ : HashMap V (List V))
  let add (m : HashMap V (List V)) (vw : V × V) :=
    let (v, w) := vw
    m.insert w (v :: m.getD w [])
  Graph.mk (g.edges.foldl add emptyMap)

--------------------------------------------------------------------
-- Depth first search and forests
--------------------------------------------------------------------
inductive Tree (V : Type) where
  | Node (val : V) (forest : List (Tree V))
  deriving Repr, Inhabited

partial def dfs {V} [BEq V] [Hashable V] (g : Graph V) (vs : List V) : List (Tree V) :=
  let rec go (ms : HashSet V) (curr_vs : List V) : HashSet V × List (Tree V) :=
    match curr_vs with
    | [] => (ms, [])
    | v :: rest =>
      if ms.contains v then
        go ms rest
      else
        let ms0 := ms.insert v
        let succs := g.successors v
        let (ms1, ts1) := go ms0 succs
        let (ms2, ts2) := go ms1 rest
        (ms2, Tree.Node v ts1 :: ts2)
  (go (∅ : HashSet V) vs).2

partial def dff {V} [BEq V] [Hashable V] (g : Graph V) : List (Tree V) :=
  dfs g g.vertices

--------------------------------------------------------------------
-- Orderings
--------------------------------------------------------------------
mutual
  partial def preorderT {V} : Tree V → List V
    | Tree.Node val fs => val :: preorderF fs
  partial def preorderF {V} : List (Tree V) → List V
    | [] => []
    | t :: ts => preorderT t ++ preorderF ts
end

partial def preorder {V} [BEq V] [Hashable V] (g : Graph V) : List V :=
  preorderF (dff g)

mutual
  partial def postorderT {V} (t : Tree V) (tl : List V) : List V :=
    match t with
    | Tree.Node val fs => postorderF fs (val :: tl)

  partial def postorderF {V} (ts : List (Tree V)) (tl : List V) : List V :=
    match ts with
    | [] => tl
    | t :: ts => postorderT t (postorderF ts tl)
end

partial def postorder {V} [BEq V] [Hashable V] (g : Graph V) : List V :=
  postorderF (dff g) []

partial def topsort {V} [BEq V] [Hashable V] (g : Graph V) : List V :=
  (postorder g).reverse

--------------------------------------------------------------------
-- Strongly connected components
--------------------------------------------------------------------
partial def sccF {V} [BEq V] [Hashable V] (g : Graph V) : List (Tree V) :=
  (dfs g.transpose (topsort g)).reverse

partial def sccG {V} [BEq V] [Hashable V] (g : Graph V) : List (List V) :=
  sccF g |>.map preorderT

partial def scc {V} [BEq V] [Hashable V] (nodes : List (V × List V)) : List (List V) :=
  sccG (graph nodes)

--------------------------------------------------------------------
-- Reachable and path
--------------------------------------------------------------------
partial def reachable {V} [BEq V] [Hashable V] (v : V) (g : Graph V) : List V :=
  preorderF (dfs g [v])

partial def path {V} [BEq V] [Hashable V] (v w : V) (g : Graph V) : Bool :=
  reachable v g |>.contains w

end Koka.Lib.Scc
