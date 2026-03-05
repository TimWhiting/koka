# Design Plan: Monadic Optimization Pass using Flow Analysis

## Goals
- Identify expressions that are `alwaysMonodic` or `neverMonadic` based on fixed-point analysis.
- Wrap these expressions in special internal markers: `nameAlwaysMon` and `nameNeverMon`.
- Work on **`modCore` (optimized)** (which contains simplified/pre-optimized Core) instead of unoptimized Core. This is closer to the final generated code but must occur before the `Monadic` translation phase.
- Simplify the annotation syntax by omitting type applications (variants will be added to `Core.Monadic` to handle these "invalid" but transient Core forms).
- Validate the optimization with [analysis/test/opt-yield-always.kk](analysis/test/opt-yield-always.kk) using trace/debug statements.
- Ensure the optimization is only applied to the **root module** to maintain consistency across boundaries.

## Proposed Changes

### 1. New Module: `Core.EffOpt`
We will implement the optimization logic in [src/Core/EffOpt.hs](src/Core/EffOpt.hs).

- **Cache Preprocessing**: Instead of using the raw `M.Map FixInput FixOutput`, we will preprocess the cache into a more usable form for the optimization pass. This involves merging all analysis results for each unique `ExprContext` (similar to the `alwaysMon` and `neverMon` helpers in [src/Core/FlowAnalysis/Full/DMCFAR/Syntax.hs](src/Core/FlowAnalysis/Full/DMCFAR/Syntax.hs)). This preprocessed map will directly store whether an `ExprContextId` is guaranteed to be `alwaysMon` or `neverMon`.
- **Traversal & Context Tracking**: 
    - Use a recursive traversal that tracks the "shadow" `ExprContext` trail representing the current position in the expression tree.
    - As we descend from parent to child Core expressions, we will narrow down the preprocessed analysis cache to only those entries valid for the current sub-context. 
    - We will **not** build brand new `ExprContext`s from scratch during traversal; instead, we will use the existing parent context to guide the lookup in the preprocessed cache.
- **Annotation Logic**:
    - For each `App` expression identified as an operation or always effectful:
      `App (Var nameAlwaysMon ...) [expr]`. Use `trace` to log when this happens.
    - For each expression identified as never yielding or purely local:
      `App (Var nameNeverMon ...) [expr]`. Use `trace` to log when this happens.
    - Note: These annotations will temporarily be "invalid" Core (missing type applications) but will be consumed and removed by the `Monadic` phase before any later stages see them.

### 2. Integration in `Compile.Build`
In [src/Compile/Build.hs](src/Compile/Build.hs), specifically within the `moduleTypeCheck` function:

- Use `modCore` (which is already simplified) for the analysis and subsequent optimization.
- Ensure the optimization only runs on the **root module**. Compare `modName mod'` with `buildcRoots bc`.
- After the analysis runs (e.g., `evalMainR`), capture the resulting cache.
- Call the new `EffOpt.opt` function:
  ```haskell
  let Just core = modCore mod'
  let optimizedCore = EffOpt.opt (coreProgDefs core) analysisResult
  done mod'{ modCore = Just 0 core{ coreProgDefs = optimizedCore } }
  ```

### 3. Updates to `Core.Monadic`
The `Monadic.hs` file will be updated to handle the simplified annotation variants:

- **Translation Logic**: Update `monExpr'` to handle `nameAlwaysMon`/`nameNeverMon` `Var`s directly, even without type applications.
- **Predicates**: We will **not** update the existing `isAlwaysMon` / `isNeverMon` predicates, as those are used for general heuristics. The analysis-based optimization will be handled explicitly during translation of the annotated nodes.

## Implementation Steps

1.  **Skeleton Implementation**: Flesh out `src/Core/EffOpt.hs` with a basic traversal that accepts the analysis cache.
2.  **Context Tracking Implementation**: Implement the recursive traversal that tracks `ExprContext` trails to identify expression sites in the cache.
3.  **Annotation Logic**: Add logic to insert transient `nameAlwaysMon`/`nameNeverMon` wrappers and include `trace` statements for validation.
4.  **Pipeline Hookup**: Update `src/Compile/Build.hs` to call `EffOpt.opt` for the **root module** only.
5.  **Monadic Support**: Update `src/Core/Monadic.hs` to consume the new transient wrappers.
6.  **Validation**: Test with [analysis/test/opt-yield-always.kk](analysis/test/opt-yield-always.kk) and verify trace output.
