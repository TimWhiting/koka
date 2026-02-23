# Summary: Practical Type Inference with Levels

**Fan, Xu, Xie — PLDI 2025, DOI 10.1145/3729338**

---

## One-Line Summary

Attach an integer *level* n to every type variable and unification variable (tracking let-nesting depth) and use this for three purposes: (1) efficient let-generalization without context traversal, (2) automatic skolem escape detection during unification, (3) type region scoping.

---

## Core Idea

Standard HM inference (`Algorithm W`) computes `ftv(Γ)` at every let-binding to decide which unification variables to generalize. This is O(|Γ|) per let. The levels approach instead tags each unification variable `â̂ⁿ` with its creation level `n`, so generalization simply picks variables with level > current.

---

## Key Changes to the HM Type System

### Flavour data type
```
type Level = Int
data Flavour = Meta Level | Skolem Level | Bound
```
(vs. original `Meta | Skolem | Bound`)

### Generalization rule (algorithmic)
When entering `let x = e₁ in e₂`:
1. Increment level: `n → n+1`
2. Infer type of `e₁` at level `n+1`
3. Generalize: quantify over all `â̂ᵐ` with `m > n` (instead of `m ∉ ftv(Γ)`)
4. Restore level: `n+1 → n`

```haskell
-- Old:
level <- getLevel
free  <- freeInGamma
tvars = filter (\tv -> not (tvsMember tv free)) (ofuv nrho)

-- New:
level <- getLevel
tvars = filter (\tv -> getTvLevel tv > level) (ofuv nrho)
```

### Skolem scope (automatic)
When subsumption skolemizes `∀a. σ` at level `n`:
- The skolem variable gets level `n+1`
- During unification, `Meta n ↦ τ` is rejected if `τ` contains `Skolem m` with `m > n`
- This replaces ad-hoc post-hoc escape checks

```haskell
-- In unification of (Meta n) with τ:
when (any (\sv -> getTvLevel sv > n) (tvsList (fsv tau))) $
  unifyError (NoMatchSkolem ...)
```

### Polymorphic promotion (novel, not implemented here)
`Γ ⊢ σ ↝±ₘ τ` — when a unification variable `â̂ⁿ` is unified with type `τ` that contains a meta-variable `b̂ᵐ` with `m > n`, the variable `b̂ᵐ` must be "promoted" to level `n` (or lower). This handles higher-rank subsumption correctly.

**Status in this implementation**: NOT implementing promotion. We only add the skolem escape check in unification. This is safe: promotion is needed for full higher-rank level-based inference; the escape check is sufficient for the simpler cases Koka currently handles.

---

## Key Algorithmic Rules

### Fresh type variables
Every fresh unification variable gets the *current level*:
```haskell
freshMeta :: Inf TypeVar
freshMeta = do lv <- getLevel; freshTVar kind (Meta lv)
```

### Skolemization at level n
```haskell
withSkolemized at level n: skolem gets level (n+1)
```
This ensures skolems automatically fail any unification attempt with a meta-variable from an outer scope (level ≤ n).

### Level invariant
**Invariant**: At any point during inference at level `n`, all unresolved meta-variables in scope have level ≤ `n`.

This is maintained by:
- Fresh meta-vars get current level
- Let-body is inferred at level+1
- Generalization picks up variables at level > n (the surrounding level)

---

## Type Regions (Out of Scope)

The levels paper also uses levels to enforce local datatype scoping (type regions): a type constructor defined inside a local scope gets a level and cannot escape. Koka handles this differently; we do not implement this aspect.

---

## Implementation Reference

See: `/Users/timwhiting/level-artifact/impl/level-koka-bench/`

Key files:
- `src/Type/Type.hs:131` — `data Flavour = Meta Level | Skolem Level | Bound`
- `src/Type/TypeVar.hs:543-548` — `getTvLevel`
- `src/Type/InferMonad.hs:875` — `St` with `level :: !Level`
- `src/Type/InferMonad.hs:968-976` — `getLevel`/`setLevel`
- `src/Type/InferMonad.hs:165-168` — level-based generalization (replacing `freeInGamma`)
- `src/Type/Infer.hs:151-145,466-480` — level increment around let-body inference

---

## What the Paper Does NOT Address

- Static overloading / qualified names (the implicits paper handles this)
- Syntactic implicit parameters `?x:τ` (the implicits paper handles this)
- Algorithm WQ / spooky action at a distance (future work, see `algorithm-wq.mdk`)
- Combining levels + implicits (the novel contribution of Koka's implementation)
