/-
  Semantic components for the locally-nameless ANF machine.

  This mirrors `DMCFA.Components`, but `Env` is now a *stack* of addresses
  (`List VAddr`) rather than a partial map `Var → Option VAddr`: opening a
  binder is *pushing* an address onto the front of the stack, and `AExp.bvar i`
  is resolved by indexing `i` entries in from the front (`bvar 0` = the most
  recently pushed binding). Since pushing never overwrites an existing entry,
  there is no notion of "shadowing" or "freshness w.r.t. ρ's domain".

  The continuation `resume` introduced by `handle_op` is an ordinary stack
  binding (pushed like any other), not a special slot.
-/

import DMCFA.LNSyntax

namespace DMCFA.LN

/-- Value addresses from an infinite set -/
abbrev VAddr := Nat

/-- Environment: a stack of addresses (for `bvar` resolution). -/
structure Env where
  stack : List VAddr

/-- Empty environment -/
def Env.empty : Env := ⟨[]⟩

/-- Push a single address onto the environment (binds `bvar 0`, shifting all
other indices up by one). -/
@[grind =] def Env.push (ρ : Env) (a : VAddr) : Env := ⟨a :: ρ.stack⟩

/-- Push multiple addresses; `as.head` becomes `bvar 0`, etc. -/
@[grind =] def Env.pushMany (ρ : Env) (as : List VAddr) : Env := ⟨as ++ ρ.stack⟩

/-- Resolve a de Bruijn index against the address stack. -/
@[grind =] def Env.lookup (ρ : Env) (i : Nat) : Option VAddr := ρ.stack[i]?

/-- Closure: body and captured environment, plus an optional self-address for
recursive closures. The body binds 1 or 2 more variables than `env` accounts
for: the call-time parameter (`bvar 0` in `body`), and -- if `selfAddr` is
present -- the closure's own address as `bvar 1` (pushed *after* the
parameter at call time, mirroring B&P-LN's `bvar 0 ↦ self, bvar 1 ↦ arg`
convention for `letRec`). -/
structure Closure where
  body : Exp
  env : Env
  selfAddr : Option VAddr := none

/-- Frame: either a let-continuation or a handler frame -/
inductive Frame where
  | letFrame : Exp → Env → Frame          -- (e2, ρ); continuing pushes 1 value, binding `bvar 0` in e2
  | handlerFrame : Handler → Env → Frame  -- (h, ρ)

/-- Continuation: list of frames -/
abbrev Kont := List Frame

/-- Denotables: values that can be stored -/
inductive Denotable where
  | closure : Closure → Denotable                       -- Lambda / recursive-function closures
  | kontClosure : Handler → Env → Kont → Denotable      -- Captured continuation (h, ρ, κ)
  | conLabel : ConLabel → Denotable                      -- Constructor
  | succVal : VAddr → Denotable                          -- S(a_v)

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

end DMCFA.LN
