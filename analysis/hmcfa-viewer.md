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
  - [x] two renderers: JSON for the editor (`hmcfaJson`) and markdown for the command line (`koka --hmcfa-view [--hmcfa-generated] --sensitivity=(h,m) [--hmcfa-entry=name] -c file.kk`)
- [x] Language server: `koka/hmcfa` command (`filePath`, `m`, `h`, `variant`, `entry`) returning the JSON; checked by driving the server over stdio
- [~] Extension (`src/hmcfa-view.ts`): "Koka: Show HMCFA Analysis" (also a button in the editor title bar) opens a webview. Rendered and exercised in a headless DOM with real results; needs a look inside VS Code
  - [x] timestamps drawn as a path from the outside in, newest call last (next to the value): for each handler level, its call sites and then a gate (purple: handle, orange: resume), then the current call sites; every kept call site is shown
  - [x] sensitivity: m and h steppers in the view, and a status bar item (`HMCFA m=1 h=1`) with presets; both update the workspace settings and re-run
  - [x] click an entry or a call site to select and highlight it in the editor
  - [x] two views, Cache (every expression and variable, with its results at each timestamp) and Call stack; filters for expressions, bindings, generated code, and source text apply to both
  - [x] Call stack view: the timestamps as a tree of frames from the outside in (program start, calls, handler and resume gates); each frame lists the variables bound and expressions evaluated in exactly that context
    - a segment cut to its m newest calls is placed below the context its oldest kept call was made in (a context inside the same delimiter that ends with the calls before it and evaluated that call), once, below the shallowest such context; `+n` marks calls that n other contexts could also have made
    - segments with no such context go below "older calls not kept" (first segment) or right below their delimiter (captured stacks)
    - the structure uses the timestamps of hidden (generated) entries too, so the visible frames stay connected
    - a frame lists each source expression once (results at timestamps that land on the frame are joined, and a variable is merged with its binding), in evaluation order: by line, then by end column; the frame of a call comes right after the row of its call expression (or of the with / resume of a delimiter)
  - [x] bindings are placed at the variable's declaration (the binder in the context the binding address records), not at the use the address was looked up with
  - [x] filters for variable references (left out when the variable has a binding in the source, since bindings are immutable) and for top-level functions (definitions and library functions)
  - [x] continuations in their finite form: the frames waiting for the operation's result, outermost first, each with its static context, from the continuation store (a graph: frames may branch, and loop for recursion)
  - [x] both variants of the analysis, DMCFA and DMCFAR (with rebinding), share the viewer code (`Full/HMCFAView.inc`, included by `DMCFA/View.hs` and `DMCFAR/View.hs`); switch in the view, in the status bar picker, with `koka.analysis.variant`, or with `--hmcfa-rebinding` on the command line
  - [x] values that arrive after a resumption: an application or `val` whose argument (or right-hand side) performed an operation gets its value when the resumed continuation continues its frame, so those steps are read too (at the timestamp they continue in)
  - [x] the same for a match scrutinee (`if yield(x) then ...`): the value handed to the `FScrut` frame is shown at the scrutinee
  - [ ] an operation call in tail position (the body's result) hands its value to the caller's frame, so it is shown at the call, not at the operation call
  - [x] call sites carry their expression's id; the call stack connects stacks by these ids and by the contexts evaluated in library code (sent as `contexts`), and call sites in other modules are labeled with their module and not linked
  - [x] local variables (`var x`) are their own kind of delimiter level (green gate), so installing and assigning them line up
  - [x] code after reading a local variable lost every delimiter level (`doHandleLocal` resumed a `local-get` with `dynamic retCtx`, the context outside the variable), so the call stack could not place it (vec.kk). Reads now resume with the read's own dynamic context from the variable's level outwards (`localBodyDyn`, both variants); a read's result now shares the timestamp of the code before the read
  - [ ] an assignment re-installs the variable's level with one more call (`addCallRaw m retCtx bodId`), which pushes older calls off at small m, so code after an assignment can start mid-stack (vec.kk at m <= 3; async.kk even at m = 7, since its queue is assigned four times). The extra call is intended: it keeps code after different assignments apart (resuming in the assignment's own context instead merges `x := 1` / `x := 2` at m <= 2). Options: the viewer treats these calls as part of the variable's level, or the level records only the latest assignment instead of appending
  - [x] timing: the fixpoint time and cache size per entry point (from the compiler), the whole request time (from the extension), and a running timer while the analysis runs
  - [x] Koka highlighting of source text (a small tokenizer: keywords, numbers, strings, comments, capitalized names)
- [x] Settings: `koka.analysis.callSensitivity` (m), `koka.analysis.handlerSensitivity` (h), `koka.analysis.showGenerated`

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

The Call stack tab covers part of this: it nests contexts like the call stack, so going down a frame is a successor timestamp and its parent a predecessor.

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
