/-
  Semantic Components for the concrete big-step machine

  Based on Figure 3 (big-steph-components) from the paper.
-/

import DMCFA.Syntax
import Mathlib.Data.Finmap

namespace DMCFA

/-- Value addresses from an infinite set -/
abbrev VAddr := Nat

/-- Environment maps variables to addresses -/
abbrev Env := Var → Option VAddr

/-- Empty environment -/
def Env.empty : Env := fun _ => none

/-- Extend environment -/
def Env.extend (ρ : Env) (x : Var) (a : VAddr) : Env :=
  fun y => if y = x then some a else ρ y

/-- Extend environment with multiple bindings -/
def Env.extendMany (ρ : Env) (bindings : List (Var × VAddr)) : Env :=
  bindings.foldl (fun ρ' (x, a) => ρ'.extend x a) ρ

/-- Closure: binding variables, body, captured environment -/
structure Closure where
  params : List Var
  body : Exp
  env : Env
  params_nodup : params.Nodup

/-- Frame: either a let-continuation or a handler frame -/
inductive Frame where
  | letFrame : Closure → Frame                    -- ([y], e, ρ)
  | handlerFrame : Handler → Env → Frame          -- (h, ρ)

/-- Continuation: list of frames -/
abbrev Kont := List Frame

/-- Denotables: values that can be stored -/
inductive Denotable where
  | closure : Closure → Denotable                       -- Lambda closures
  | kontClosure : Handler → Env → Kont → Denotable      -- Captured continuation (h, ρ, κ)
  | conLabel : ConLabel → Denotable                     -- Constructor
  | succVal : VAddr → Denotable                         -- S(a_v)

instance : Inhabited Denotable := ⟨Denotable.conLabel ConLabel.unit⟩

/-- Store maps addresses to denotables -/
abbrev Store := VAddr → Option Denotable

/-- Empty store -/
def Store.empty : Store := fun _ => none

/-- Extend store -/
@[grind =] def Store.extend (σ : Store) (a : VAddr) (d : Denotable) : Store :=
  fun a' => if a' = a then some d else σ a'

/-- Extend store with multiple bindings -/
@[grind =] def Store.extendMany (σ : Store) (bindings : List (VAddr × Denotable)) : Store :=
  bindings.foldl (fun σ' (a, d) => σ'.extend a d) σ

/-- Values: result of evaluation (either denotable or suspended operation) -/
inductive Value where
  | den : Denotable → Value                            -- A denotable value
  | suspended : OpName → List VAddr → Kont → Value     -- (op, as_v, κ) suspended operation

/-- Check if value is denotable -/
def Value.isDenotable : Value → Bool
  | .den _ => true
  | .suspended _ _ _ => false

/-- Extract denotable if present -/
def Value.toDenotable : Value → Option Denotable
  | .den d => some d
  | .suspended _ _ _ => none

/-- Simple fresh address generator state -/
structure FreshState where
  nextAddr : VAddr
  deriving Repr

/-- Generate fresh address -/
def FreshState.fresh (s : FreshState) : VAddr × FreshState :=
  (s.nextAddr, { nextAddr := s.nextAddr + 1 })

/-- Generate multiple fresh addresses -/
def FreshState.freshMany (s : FreshState) (n : Nat) : List VAddr × FreshState :=
  let addrs := List.range n |>.map (· + s.nextAddr)
  (addrs, { nextAddr := s.nextAddr + n })

/-- Initial fresh state -/
def FreshState.init : FreshState := { nextAddr := 0 }

end DMCFA
