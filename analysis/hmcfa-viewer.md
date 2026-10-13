# HMCFA results viewer: roadmap

Goal: make the results of the full HMCFA analysis explorable from VS Code, in source terms, for
teaching and for debugging the analysis.

Status key: `[x]` done, `[~]` in progress, `[ ]` not started.

## Stage 1: basic interactive view

A command runs the analysis on the current file and opens an interactive view beside the editor.

- [x] Compiler: `Core.FlowAnalysis.Full.DMCFA.View` turns the fixpoint cache into a list of entries
  - [x] expression results: for each evaluated expression, each timestamp it was evaluated at, and the values it produced (this includes intermediate results of larger expressions, not only bindings)
  - [x] binding results: for each variable, each timestamp it was bound at, and the values stored there
  - [x] entries are keyed by core expression, so distinct expressions with the same source range are never merged
  - [x] expressions and call sites carry their source text and range; timestamps are structured (call sites, then handler levels)
  - [x] generated code is flagged: hidden source ranges (`rangeIsHidden`), several core expressions with the same source text (desugared handler clauses), and `@` names
  - [x] entry points: `analyze-*` functions (benchmark convention), falling back to `main`
  - [x] two renderers: JSON for the editor (`hmcfaJson`) and markdown for the command line (`koka --hmcfa-view [--hmcfa-generated] --sensitivity=(d,m) -c file.kk`)
- [x] Language server: `koka/hmcfa` command (`filePath`, `m`, `d`) returning the JSON; checked by driving the server over stdio
- [~] Extension (`src/hmcfa-view.ts`): "Koka: Show HMCFA Analysis" (also a button in the editor title bar) opens a webview. Rendered and exercised in a headless DOM with real results; needs a look inside VS Code
  - [x] timestamps drawn as nested boxes: handler levels from the outside in, then the current call sites
  - [x] sensitivity: m and d steppers in the view, and a status bar item (`HMCFA m=1 d=1`) with presets; both update the workspace settings and re-run
  - [x] click an entry or a call site to select and highlight it in the editor
  - [x] Expressions / Bindings tabs, a text filter, and a toggle for generated code
  - [x] Koka highlighting of source text (a small tokenizer: keywords, numbers, strings, comments, capitalized names)
- [x] Settings: `koka.analysis.callSensitivity` (m), `koka.analysis.handlerSensitivity` (d), `koka.analysis.showGenerated`

Known rough edges:

- [ ] Highlighting uses a hand-written tokenizer, not the extension's TextMate grammar
- [ ] Operators appear as their own expressions (`+` evaluates to the `+` function)
- [ ] Call sites made by generated or library code show as "generated code" (core form in the tooltip); the initial installation of a handler is one of these and deserves a proper label
- [ ] The "same source text" rule for generated code is a heuristic; marking the ranges of the handler desugaring as hidden in the compiler would be the principled fix
- [ ] Function values are shown by their source text or name only

## Stage 2: hover

Hovering an expression shows its HMCFA results next to the demand CFA results.

- [ ] Reuse the demand analysis' source-location lookup (`findContext`) to go from cursor to `ExprContext`
- [ ] Reuse its mapping from abstract values back to source syntax (`findSourceExpr`) for display
- [ ] Cache one analysis run per file version so hovers do not re-run the analysis

## Stage 3: navigation

- [ ] Click an expression: all results for all timestamps at that expression
- [ ] Click a timestamp: all results at that timestamp, with links to the file and code location of each
- [ ] From an expression: select subexpressions and parent expressions
- [ ] From a timestamp: predecessor and successor timestamps, derived from the structure of the timestamps in the cache (a successor extends the call component or the meta-stack component by one step)
- [ ] Jump from a call-site label inside a timestamp to that call site

## Stage 4: beyond the store

- [ ] Continuation store: show captured continuations and which operation captured them
- [ ] Per call site: which functions can be called there (the CFA question, directly)
- [ ] Per operation call: which handler clauses can handle it
- [ ] Compare two sensitivities side by side (for example m = 0 against m = 1)

## Notes

- The cache maps `FixInput` (`Step Conf`, `VStore Addr`, `KStore Addr`) to `FixOutput`. Expression results come from `Step (CEval ctx env timestamp)` entries; a result is an address whose value is in the `VStore` entry for that address.
- A timestamp is a `CombinedCtx`: a static component (call sites, `TKTop` / `TKDelim`) and a dynamic component (the meta-stack of handlers and resumptions, each with the static component it was installed at).
- Source text for a range comes from `Common.Range.sourceFromRange`.
