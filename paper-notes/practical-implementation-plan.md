# Practical Implementation Plan: Level-Based Type Inference for Koka

**Branch**: `dev`, commit `e5c00c9`
**Goal**: Add integer levels to type variables for efficient generalization and automatic skolem escape detection, without breaking any currently-accepted programs.

---

## Overview of Changes

| Phase | Files | Description |
|-------|-------|-------------|
| 1 | `src/Type/Type.hs` | Add `Level` type, change `Flavour` to carry levels |
| 1 | `src/Type/TypeVar.hs` | Add `getTvLevel`, update constructor refs |
| 2 | `src/Type/InferMonad.hs` | Add `level` to `St`, add `getLevel`/`setLevel` |
| 3 | `src/Type/InferMonad.hs` | Replace `freeInGamma` with level comparison in `generalizeX` |
| 3 | `src/Type/Infer.hs` | Wrap let-body inference with level increment |
| 4 | `src/Type/Unify.hs` | Add level check for skolem escape in unification |
| 5 | — | Build and run test suite |

---

## Phase 1: Add Level to Flavour

### `src/Type/Type.hs`

**Current** (line 124):
```haskell
data Flavour = Meta | Skolem | Bound
             deriving (Eq, Ord, Show)
```

**Change to**:
```haskell
type Level = Int

data Flavour = Meta Level | Skolem Level | Bound
             deriving (Eq, Ord, Show)
```

**Also update** `isMeta` and `isSkolem` predicates:
```haskell
-- Current (line ~283):
isMeta tv  = typevarFlavour tv == Meta
isSkolem tv = typevarFlavour tv == Skolem

-- New:
isMeta tv = case typevarFlavour tv of { Meta _ -> True; _ -> False }
isSkolem tv = case typevarFlavour tv of { Skolem _ -> True; _ -> False }
```

**Export `Level`** from the module export list.

### `src/Type/TypeVar.hs`

**Add** `getTvLevel` function and export it:
```haskell
getTvLevel :: TypeVar -> Level
getTvLevel (TypeVar _ _ flavour)
  = case flavour of
      Meta level   -> level
      Skolem level -> level
      Bound        -> 0
```

**Blast radius of constructor changes**: Search for bare `Meta` and `Skolem` pattern matches throughout the codebase. Key locations:
- `src/Type/Type.hs` — `isMeta`, `isSkolem`
- `src/Type/TypeVar.hs` — `fuv`, `fsv`, `freshTypeVar` calls
- `src/Type/InferMonad.hs` — all `freshTVar kind Meta` / `freshTVar kind Skolem` calls
- `src/Type/Infer.hs` — any explicit `Meta`/`Skolem` constructor usage
- `src/Type/Operations.hs` — instantiation creates Meta vars, skolemize creates Skolem vars
- `src/Type/Pretty.hs` — pretty-printing Flavour
- `src/Type/Unify.hs` — NoMatchSkolem and any Skolem pattern matches

**Strategy**: Use a placeholder `freshMeta`/`freshSkolem` that always creates level-0 vars initially, then update callers in Phase 2.

---

## Phase 2: Level in Inference Monad

### `src/Type/InferMonad.hs`

**Add `level` to `St`** (currently line 1821):
```haskell
data St = St { uniq               :: !Int
             , sub                :: !Sub
             , iconstraints       :: ![ImplicitConstraint]
             , iconstraintsGamma  :: !InfGamma
             , holeAllowed        :: !Bool
             , mbRangeMap         :: !(Maybe RangeMap)
             , level              :: !Level        -- ← NEW
             }
```

**Initialize in `runInfer`** (currently line 1833):
```haskell
(St unique subNull [] infgammaEmpty False mbrm 0)  -- 0 = initial level
```

**Add accessor functions** (add near line 2000):
```haskell
getLevel :: Inf Level
getLevel = level <$> getSt

setLevel :: Level -> Inf ()
setLevel lv = updateSt (\st -> st{ level = lv }) >> return ()
```

**Export** `getLevel` and `setLevel` from the module.

**Update `freshTVar` calls**: Throughout `InferMonad.hs`, any call like:
```haskell
freshTVar kind Meta
freshTVar kind Skolem
```
becomes:
```haskell
do lv <- getLevel; freshTVar kind (Meta lv)
do lv <- getLevel; freshTVar kind (Skolem lv)
```
Note: `freshEffect` and similar helpers that call `freshTVar kind Meta` must also be updated.

**Key locations in `InferMonad.hs`** to update:
- `freshEffect` (line ~1450) — creates Meta effect vars
- `instantiate`/`instantiateNoEx` → delegates to `Type.Operations`
- `withSkolemized` → delegates to `Op.skolemizeEx` (see Operations.hs)

### `src/Type/Operations.hs`

`instantiateEx`, `skolemizeEx` create fresh Meta/Skolem vars. These need to be updated too. However, since `Operations.hs` may not have access to the `Inf` monad directly, the simplest approach is to pass the current level as a parameter. Alternatively, check if `freshTVar` already uses `HasUnique` — it does, so the level must be threaded explicitly or the operations must be lifted into `Inf`.

**Simpler approach**: Since `Operations.hs` functions are called from `InferMonad.hs` wrappers, update the wrappers to pass level. Look at `Op.instantiateEx` and `Op.skolemizeEx` signatures.

---

## Phase 3: Level-Based Let-Generalization

### `src/Type/InferMonad.hs` — `generalizeX`

**Current** (lines 175-188):
```haskell
seff0 <- subst eff0
free0 <- freeInGamma
let free1 = tvsUnion free0 (fuv seff0)
iccore <- tryResolveImplicitConstraints close free1
...
seff  <- subst eff0
srho  <- subst rho0
let free = tvsUnion free0 (fuv seff)
nrho <- normalizeX close free srho
let tvars = filter (\tv -> not (tvsMember tv free)) (ofuv nrho)
```

**Change to**:
```haskell
seff0 <- subst eff0
lv    <- getLevel
free0 <- freeInGamma  -- still needed for normalizeX and resolving implicits
let free1 = tvsUnion free0 (fuv seff0)
iccore <- tryResolveImplicitConstraints close free1
...
seff  <- subst eff0
srho  <- subst rho0
let free = tvsUnion free0 (fuv seff)
nrho <- normalizeX close free srho
let tvars = filter (\tv -> getTvLevel tv > lv) (ofuv nrho)
```

**Note**: `freeInGamma` is still needed for:
- `normalizeX` (to know which effect tail variables to close)
- `tryResolveImplicitConstraints` (to decide which implicits can be resolved)
- `checkSkolemEscape` (post-hoc check — kept as belt-and-suspenders until Phase 4 is validated)

Only the final `tvars` filter changes.

### `src/Type/Infer.hs` — let-binding sites

At each call site of `generalize`, the let-body must be inferred at `level+1`. Find all `generalize contextRange range close $` calls and wrap the inner inference:

```haskell
-- Before:
(resTp, _, resCore) <- generalize rng rng True $
    do (tp, eff, core) <- inferExpr propagated (if isRec then Instantiated else Generalized close) expr
       ...

-- After:
lv <- getLevel
setLevel (lv + 1)
(resTp, _, resCore) <- generalize rng rng True $
    do (tp, eff, core) <- inferExpr propagated (if isRec then Instantiated else Generalized close) expr
       ...
setLevel lv
```

**Critical**: The level increment must happen *before* `generalize` is called (which calls `generalizeX`), and `generalizeX` reads the level *after* the inner inference. So the pattern should be:

```haskell
lv <- getLevel
setLevel (lv + 1)
result <- generalize rng rng close $ do
    ...inference at lv+1...
setLevel lv  -- or use a bracket pattern
```

Or use a helper:
```haskell
withLevel :: Inf a -> Inf a
withLevel inf = do
  lv <- getLevel
  setLevel (lv + 1)
  x <- inf
  setLevel lv
  return x
```

Then `generalizeX` reads the level at the *outer* level (after `setLevel lv`) to compare against variables created at `lv+1`. Wait — this requires careful ordering.

**Correct ordering**:
```
generalizeX runs at level lv (outer level)
  → reads `lv` via `getLevel`
  → keeps variables with level > lv (i.e., level lv+1, created inside the let)
```
So `setLevel lv` must be called *before* `generalizeX` runs its level check. But `generalizeX` is called *after* the inner inference. The pattern in the level-artifact is:

```haskell
-- In Infer.hs (level-artifact):
level <- getLevel
setLevel (level + 1)    -- enter let-body level
result <- generalize ...  -- this calls inferExpr at (level+1), then generalizeX at (level+1)
setLevel level           -- restore
```

But `generalizeX` in the artifact compares `getTvLevel tv > level` where `level` is obtained fresh inside `generalizeX`. So `generalizeX` must be called *after* restoring the level, OR `generalizeX` must be given the outer level.

Looking at the artifact code more carefully: `generalizeX` calls `getLevel` internally. The level stored in `St` is the *current* level during generalization. After the let-body is inferred at `lv+1`, `generalizeX` is called (still at `lv+1`?).

Actually from the artifact:
```haskell
-- Infer.hs line 142-146:
level <- getLevel
setLevel (level + 1)
(rho,tvars,icore) <- instantiateNoEx range stp  -- at level+1
setLevel level
generalize contextRange range close seff rho (icore core0)  -- at level (outer)
```

And in `generalizeX` line 165:
```haskell
level <- getLevel  -- reads the outer level (we're back at lv)
let tvars0 = filter (\tv -> getTvLevel tv > level) ...
```

So the pattern is:
1. `setLevel (lv+1)` — enter let-body level
2. Infer the body (creates Meta vars at lv+1)
3. `setLevel lv` — restore outer level
4. Call `generalizeX` (which reads `lv` and picks up vars at lv+1)

This means in `Infer.hs`, the level increment/decrement wraps just the body inference, not the `generalize` call:

```haskell
lv <- getLevel
setLevel (lv + 1)
(bodyTp, bodyEff, bodyCore) <- inferExpr ...
setLevel lv
(resTp, _, resCore) <- generalize rng rng True (return (bodyTp, bodyEff, bodyCore))
```

But `generalize` is a monadic wrapper that takes `Inf (Rho, Effect, Core.Expr)`. To make this work, we need to either:
a) Inline the inference inside generalize, or
b) Run the inner inference first, then pass results to `generalizeX` directly.

The cleanest approach: since `generalize` takes `Inf (Rho,Effect,Core.Expr)` as the body, wrap the level inside that body:

```haskell
(resTp, _, resCore) <- generalize rng rng True $ do
    lv <- getLevel
    setLevel (lv + 1)
    (tp, eff, core) <- inferExpr ...
    setLevel lv
    return (tp, eff, core)
```

This way, when `generalizeX` is called, the level has been restored to `lv`, so `getLevel` returns `lv` and variables at `lv+1` are correctly identified for generalization.

---

## Phase 4: Level-Based Skolem Scope

### `src/Type/Unify.hs`

In the case where we unify a `Meta n` variable with a type `τ`:

```haskell
-- In the unification solver, when binding meta-variable tv@(TypeVar id kind (Meta lv)) to tau:
let skolems = tvsList (fsv tau)
    escaped = filter (\sv -> getTvLevel sv > lv) skolems
in if not (null escaped)
   then unifyError (NoMatchSkolem (typevarKind (head escaped)))
   else ... -- proceed with binding
```

This check should be added alongside (or replacing) the occurs check.

**Preservation guarantee**: The previous `checkSkolemEscape` in `InferMonad.hs` (post-hoc) catches the same cases via `freeInGamma` traversal. The level-based check catches them earlier (during unification) and is more precise. Keep both checks for now during validation; once tests pass, the post-hoc check can be removed.

---

## Phase 5: Validation

### Build
```bash
cabal build
# or
stack build
```

### Test
```bash
# Run standard test suite
cabal test
# or run Koka's test runner
cd /Users/timwhiting/koka-uv && cabal run koka -- --test
```

### Key test areas
- `test/` — all existing tests must pass
- `test/misc/instance/wrong/` — skolem escape tests (negative tests, must still fail)
- Construct a stress test: 200 nested `let` bindings with simple functions, measure generalization time

### Expected outcome
- All positive tests still type-check
- All negative tests still produce errors
- Generalization time reduced (no more O(|Γ|) per let)

---

## Explicit Out-of-Scope Items

1. **Type regions**: The levels paper uses levels to enforce local datatype scope. Not implemented.

2. **Algorithm WQ / spooky action at a distance**: The implicits paper (§3.3) notes that Algorithm W can cause incorrect disambiguation (`λx. (inc x, show x)` example). Moving to WQ would fix this but may reject currently-accepted programs. Explicitly deferred.

3. **Polymorphic promotion**: The levels paper's novel mechanism `Γ ⊢ σ ↝±ₘ τ` for adjusting unification variable levels during higher-rank subsumption. Not implemented (only the simpler skolem escape check is added).

4. **Prefix Q ↔ Substitution equivalence proof**: Formally connecting HMQ's prefix composition to Koka's threaded substitution. Left as a research contribution.

---

## References

- Levels paper: `/Users/timwhiting/koka-uv/Fan et al. - 2025 - Practical Type Inference with Levels.pdf`
- HMQ paper: `/Users/timwhiting/koka-uv/principal-tr-v7.pdf`
- Implicits paper: `/Users/timwhiting/koka-uv/implicits.pdf`
- Level-artifact implementation: `/Users/timwhiting/level-artifact/impl/level-koka-bench/`
- See also: `levels-summary.md` (this directory) and `level-foundations.mdk` (`/Users/timwhiting/research/implicits/`)
