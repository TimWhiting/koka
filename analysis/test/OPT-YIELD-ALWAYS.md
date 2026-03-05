# DMCFAR Flow Analysis → Monadic Optimization

## Goal

The DMCFAR (Demand-driven Multi-Continuation Flow Analysis with Resumptions) analysis
statically determines, for each function call site, whether control will **always** yield
to a handler (i.e. a monadic bind is always required) or **never** yield (a direct call
suffices).

Koka's CPS/monadic pipeline normally inserts a runtime `yielding()` check before every
effectful call:

```koka
pub inline fun yield-bind(x: a, next: a -> e b): e b
  if yielding() then yield-extend(next) else next(x)
```

Every call that could yield control is compiled to `yield-bind`, which calls `yielding()`
at runtime to decide. The optimization goal is: **when the analysis proves a call always
yields, skip the `yielding()` check and call `yield-extend` directly**.

This is expressed in the compiler by annotating the function in the call site with
`@always-mon`:

```koka
pub noinline extern @always-mon(x: a): a
  c inline "#1"   // identity at runtime; meaningful only to the optimizer
```

If the call being optimized is `f(args)`, we annotate it as `@always-mon(f)(args)`.
The monadic transform (`Core.Monadic`) then recognizes this annotation and generates
`yield-extend` (no runtime check) instead of `yield-bind`.

---

## The Test File: `analysis/test/opt-yield-always.kk`

```koka
effect<a> ctl yield(item: a): ()

fun iterate(xs: list<a>): yield<a> ()
  match xs
    Cons(x, xx) -> { yield(x); iterate(xx) }
    //           ^^^^^^^^^^^
    //           The call yield(x) dispatches through a `ctl` handler.
    //           Since `yield` is a `ctl` operation, control ALWAYS transfers to
    //           the handler -- it never returns inline. The analysis should mark
    //           the @perform1 call inside yield(x) as alwaysMon.
    //           Expected result: no yielding() check before the recursive iterate(xx).
    Nil -> ()


fun foreach(f: a -> e bool, action: () -> <yield<a>|e> ()): e ()
  with ctl yield(x)
    if f(x) then
    //  ^^^^
    //  f(x) may or may not yield (unknown callee), so NO annotation expected here.
      resume(())   // resume is always final for ctl
    else ()
  action()
  //^^^^^^^
  // action() always yields because it calls iterate (which always yields).
  // The analysis should mark this call as alwaysMon.


effect ctl flip(): bool

val amb = handler
  return(x3) [x3]
  ctl flip() resume(False) ++ resume(True)
  //         ^^^^^^^^^^^^^    ^^^^^^^^^^^^^
  //         After each resume, flip returns immediately into the ++ combinator.
  //         The analysis could mark these never-mon (neverMon), but we currently
  //         only implement the alwaysMon side.


pub fun example4()
  foreach(fn(x2: int){ println(x2); x2 <= 1 })
    [1,2,3].iterate
  //        ^^^^^^^
  //        iterate always yields: analysis marks this alwaysMon.
  //        foreach always yields: analysis marks this alwaysMon.


pub fun example4b()
  with return(x) ()
  with amb
  with foreach fn(x1: int)
    if flip() then println(x1) else println("flip false " ++ x1.show)
    x1 <= 1
  [1,2,3].iterate
```

---

## Pipeline

```
Source (.kk)
  │
  ▼
Type-check + Core IR          (src/Compile/Build.hs: buildcTypeCheck)
  │
  ▼
Pre-analysis simplification   (lightweight pass, e.g. beta/eta, dead-code)
  This is the Core the analysis and EffOpt actually see.
  │
  ▼
DMCFAR Analysis               (Core.FlowAnalysis.Full.DMCFAR)
  Produces: alwaysMon map     ExprContext → Bool
  (ExprContexts refer to positions in the *simplified* Core above)
  │
  ▼
EffOpt pass                   (src/Core/EffOpt.hs: EffOpt.opt)
  Walks the same simplified Core, matches each App node's context
  against the alwaysMon map, and wraps the function:
    @always-mon(f)(args)   instead of   f(args)
  Result: annotated Core (same shape as simplified Core + annotations).
  │
  ▼  ⚠️  DIVERGENCE POINT — see caveat below
  │
Main optimization pipeline    (src/Compile/Optimize.hs)
  Heavy inlining, specialisation, simplification, etc.
  The annotated Core is transformed into a potentially very different shape.
  @always-mon is declared noinline to survive, but surrounding expressions
  can still be moved, duplicated, or restructured.
  │
  ▼
Monadic transform             (src/Core/Monadic.hs)
  Sees the *optimized* Core, which may look quite different from what
  EffOpt produced.  Recognises three patterns for @always-mon:
  1. App (Var @always-mon) [f]             -- simple
  2. App (TypeApp (Var @always-mon) _) [f] -- type-applied
  3. App (App (Var @always-mon) [f]) args  -- nested (most common after inlining)
  Each generates applyExtend → yield-extend (no yielding() check).
  Regular App falls through to appBind → yield-bind (has yielding() check).
  │
  ▼
C code generation + clang
```

### ⚠️ Pipeline ordering caveat

There are two distinct sources of mismatch between what EffOpt annotates and what the
monadic transform sees:

1. **Pre-analysis simplification is limited**: The simplification pass before analysis
   is lightweight. Heavy inlining (e.g. inlining `foreach` into `example4`) does not
   happen before the analysis. This means call sites with abstract/unknown arguments
   (like `f` inside the generic `foreach` body) cannot be annotated even if a concrete
   specialisation would allow it. The annotations are thus conservative — only call
   sites where the analysis can see a yielding call through the pre-simplified Core get
   annotated.

2. **The main optimizer runs between annotation and use**: EffOpt inserts annotations
   into the simplified Core, but the monadic transform receives the *optimized* Core
   produced by the heavy optimization pipeline that runs afterwards. The optimizer can
   inline, specialise, and restructure expressions around the `@always-mon` wrappers.
   Since `@always-mon` is `noinline`, the wrapper itself survives, but the overall
   expression shape can change. For example, an annotated `@always-mon(f)` that is
   later applied to arguments becomes the nested pattern
   `App (App (Var @always-mon) [f]) args`, which requires a separate match arm in the
   monadic transform. New shapes introduced by future optimizer passes could break
   recognition entirely and silently fall back to the unoptimised `yield-bind`.

A potential future improvement is either to move EffOpt to run immediately before the
monadic transform (after the main optimizer), using a second analysis pass on the
optimized Core, or to iterate: optimize → analyze → annotate → monadic transform.

---

## Analysis Annotation Points (what the traces show)

When compiled with `--dmcfar`, the monadic transform prints which pattern it matches.
Expected output for this file (grepping for `app.*always-mon`):

| Context path | Function annotated | Meaning |
|---|---|---|
| `[#yield/@handle]` | `@hhandle` | The yield handler dispatch always yields |
| `[yield]` | `@perform1` | The `yield(x)` call (inside the `yield` fun) always yields |
| `[_, iterate]` | `@perform1` | The `yield(x)` call inside `iterate` always yields |
| `[foreach]` | `yield/@handle` | The `action()` call inside `foreach` always yields |
| `[#flip/@handle]` | `@hhandle` | The flip handler dispatch always yields |
| `[flip]` | `@perform0` | The `flip()` call always yields |
| `[amb]` | `Cons` | |
| `[amb]` | `flip/@handle` | The flip handler inside amb always yields |
| `[example4]` | `iterate` | `[1,2,3].iterate` always yields |
| `[example4]` | `foreach` | `foreach(...)` always yields |
| `[_, x, example4b]` | `@perform0` | The flip call in example4b always yields |

---

## How to Verify with `--showfcore`

Run:

```bash
stack run koka -- analysis/test/opt-yield-always.kk --dmcfar --showfcore 2>&1 > /tmp/core.txt
```

### ✅ Check 1: `iterate` has no `yielding()` check

```bash
grep -A80 "^pub fun iterate " /tmp/core.txt | grep "yielding()"
```

**Expected**: no output. The `yield(x)` call in `iterate` is always-mon, so after the
handler dispatch the continuation is passed to `yield-extend` directly. No `yielding()`
should appear in the body of `iterate`.

### ✅ Check 2: `foreach` has no `yielding()` check for `action()`

```bash
grep -A80 "^pub fun foreach " /tmp/core.txt | grep "yielding()"
```

**Expected**: possibly one `yielding()` for the `f(x)` call (which is *not* annotated
because the callee is unknown), but **not** for the `action()` call.

> **Note on `f(x)` and inlining**: The analysis runs on the Core IR *before* any
> inlining or simplification of the call sites in other modules, but *after* the full
> optimization pipeline for already-compiled modules. If, in a particular compilation
> context, `foreach` is inlined into its call site (e.g. `example4`), the abstract
> `f` becomes the concrete `fn(x2){ println(x2); x2 <= 1 }`. The analysis could then
> see that this specific `f(x)` call never yields (since `println` and `<=` are total),
> making it eligible for a `neverMon` annotation. Conversely, if `foreach` is *not*
> inlined, `f` remains an unknown closure and no annotation is possible.
>
> More generally: **any inlining or simplification that the optimizer performs before
> the analysis sees the Core can open up additional annotation opportunities** that
> would not be visible at the source level. This means the analysis should ideally run
> on a form of the Core that has already had as much inlining applied as possible, but
> this conflicts with the current pipeline order where analysis runs immediately after
> type-checking (before optimisation). A future improvement would be to run a
> pre-analysis inlining pass, or to iterate analysis and optimization.

### ✅ Check 3: All `yielding()` calls in user code are gone

```bash
grep -B3 "std/core/hnd/yielding()" /tmp/core.txt | grep "^pub fun \|^fun " | sort -u
```

**Expected**: only standard library functions (`yield-bind`, `yield-bind2`,
`finally-prompt`, `prompt-local-var`) contain `yielding()`. User-defined functions
(`iterate`, `foreach`, `example4`, `example4b`) should **not** appear.

### ✅ Check 4: `yield-extend` is used (not `yield-bind`) at call sites

```bash
grep "std/core/hnd/yield-bind(" /tmp/core.txt | wc -l     # expect 0
grep "std/core/hnd/yield-extend(" /tmp/core.txt | wc -l   # expect > 100
```

### ✅ Check 5: Program output is correct

```bash
stack run koka -- analysis/test/opt-yield-always.kk --dmcfar -e
```

Expected output:
```
1
2
flip false 1
flip false 2
2
1
flip false 2
2
```

---

## Current Status

| Step | Status | Notes |
|---|---|---|
| DMCFAR analysis produces `alwaysMon` map | ✅ Done | ~11 annotated call sites for this file |
| `EffOpt` pass matches contexts and wraps functions | ✅ Done | `src/Core/EffOpt.hs` |
| `@always-mon` defined in `lib/std/core/hnd.kk` | ✅ Done | C inline `"#1"`, noinline |
| `@always-mon` Var uses `InfoExternal` in Core | ✅ Done | Prevents `kk_function_dup` in C backend |
| Monadic transform handles `App (@always-mon) [f]` (simple) | ✅ Done | Uses `applyExtend` |
| Monadic transform handles `App (TypeApp (@always-mon) _) [f]` | ✅ Done | Uses `applyExtend` |
| Monadic transform handles `App (App (@always-mon) [f]) args` (nested) | ✅ Done | Uses `applyExtend` (bug fixed: was using `appBind`) |
| `iterate`/`foreach` have no `yielding()` in final Core | ✅ Verified | Checks 1–4 above pass |
| Program produces correct output | ✅ Verified | Checks 5 passes |
| `neverMon` optimisation | ❌ Not implemented | `neverMon` is disabled; resume calls in `flip` handler are not yet optimised |

---

## Key Files

| File | Role |
|---|---|
| `analysis/test/opt-yield-always.kk` | Test program |
| `src/Core/EffOpt.hs` | Post-analysis pass: inserts `@always-mon` annotations |
| `src/Core/Monadic.hs` | Monadic transform: recognises annotations, emits `yield-extend` |
| `lib/std/core/hnd.kk` | Defines `@always-mon`, `@never-mon`, `yield-extend`, `yield-bind` |
| `src/Common/NamePrim.hs` | `nameAlwaysMon`, `nameNeverMon` constants |
| `src/Compile/Build.hs` | Wires analysis → EffOpt → rest of pipeline |
| `src/Core/FlowAnalysis/Full/DMCFAR/Syntax.hs` | `alwaysMon` / `neverMon` extractors on analysis results |
