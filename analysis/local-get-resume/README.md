# Resuming local-variable reads in HMCFA (DMCFA / DMCFAR)

A `var` in Koka is a `local` effect handler. Reading it (`local-get`) is an operation, and the analysis resumes the
read's continuation with the variable's value. This note compares three ways of choosing the *dynamic context*
that continuation resumes with, measured on the benchmark suite with the existing precision metrics. The change only
affects benchmarks that use `var`, and only the HMCFA analyses (DMCFA and DMCFAR) with `d >= 1`.

## The three modes

Code: `doHandleLocal`, local-get branch, in `src/Core/FlowAnalysis/Full/DMCFA/DMCFA.hs` and
`src/Core/FlowAnalysis/Full/DMCFAR/DMCFA.hs`. `scripts/set-mode.py <mode>` switches between them.

| mode | resume with | effect |
|---|---|---|
| **lose** (the original code) | `dynamic retCtx`: the context *outside* the variable | drops the variable's level and every level inside it, so later operations in the resumed code can fail to find their handler (unsound, as well as imprecise) |
| **add** | `newDelim d m (addCallRaw m retCtx bodId) bodId x`: a new level for the variable, with one more call | treats the resume as re-entering the variable, which pushes older calls and levels off the timestamp |
| **keep** (now in the source) | `localBodyDyn x oCtx (dynamic retCtx)`: the read's own dynamic context, from the variable's level outwards | resumes in the context the read happened in. Falls back to lose only if the variable's level was already pushed off (more than `d` levels) |

Keep needed no change to how continuations are memoised. Two reads of the same variable in the same context share
the resumption, but the continuation address (frame, static context, delimited frame) still tells them apart.

**KCFA needs no change.** Its timestamp is a single list of the last k calls, threaded through the analysis. In
`KCFA.hs` `doHandleLocal`, the `ctx` it resumes with and the `ctx'` stored in the `ROp` are always the same value:
`returnOp` sets both, and `doDoContinue` re-sets both from the threaded time. So KCFA already resumes a read at the
time of the read, like keep. Only DMCFA and DMCFAR keep a separate, delimited handler context (`retCtx`) that differs
from the context of the operation.

Local-set is unchanged in all modes. It resumes with `addCallRaw m retCtx (CtxId vcontextId v)` (DMCFA: `bodId`), so
it still pushes a call off at small `m` (see next steps).

## Other fixes made for this run

- **`parse-int` crashed the analysis** (`Prelude.read: no parse`, in all three `Primitives.hs`). Decimal `xparse`
  called Haskell's `read` on whatever string literal reached it. Once the analysis became precise enough that a
  specific non-numeric string (`"fib-3"` in `koka-gen/build`) reached `parse-int`, it crashed. Add and keep crashed on
  `build` at H(2,2); lose was never precise enough to get there. Now `readMaybe`: a plain decimal gives that number,
  anything else gives `Nothing` or `Just` an unknown int. Koka also accepts `+5`, `1_000` and `0x1f`, which Haskell's
  `read` doesn't, so falling back to both answers keeps the analysis sound for those too. The hex branch still
  answers `Nothing` when `readHex` fails.
- **`koka-gen/coop-communication` no longer type-checks** on this branch (it does with Koka 3.2.9):
  `effects do not match ... inferred <comm<$e>,div,local<_h>|$e>, expected <comm<$e>,div|$e>` at `handle-comm(main1)`.
  This comes from `a0e403d89` ("Fix local inference"), which only isolates `local` at the `var`'s own scope.
  - Removing the `mask<local>` is not enough: `comm`'s effect parameter then includes `local<h>`.
  - What compiles is moving the mask from inside `handle-comm` to its two callers
    (`handle-comm(fn() mask<local>{ main1() })`). This is the same program with one extra lambda each; see
    `coop-communication-mask.patch`. The patch is only applied in the benchmark harness, not in the koka-gen submodule.
  - **Possible type-checker regression:** even with the parameter annotated as `() -> <comm<_e>,div|_e> ()`, the
    checker reports `main1` itself, a parameter declared without `local`, as having `local<_h>`. This looks like the
    implicit `local` added to parameters used inside a `var` scope no longer being removed at depth > 0.

## Method

- **Benchmarks:** the 13 programs that use `var`, 44 examples in all.
  - `handlers/{ambient,unix,scoped,vec,nim}`
  - `suite/complex-flow`
  - `rosetta/{pr4rings,jump-anywhere,monads-writer}`
  - `koka-gen/{build,mini-ppl,music,coop-communication}`
- **Configurations:**
  - The baseline: 0CFA DMCFA (`--dmcfae (0,0)`).
  - KCFA k ∈ {1,2}, and DMCFAR at every (d,m) with d,m ∈ {0,1,2}, (0,0) aside.
  - The baseline, KCFA and d = 0 runs are the same in every mode, so they run once and are shared between modes.
- **Running:** jobs are run like `run-benchmarks.kk` does: one `koka -l <file> <flag> --sensitivity="(d,m)"` per job,
  each in its own copy of `analysis/`. The compiler's own limits apply: a 10-minute timeout per example, and the
  analysis is timed 3 times.
- **Load:** jobs run **one at a time**. Each starts only once the CPU is at least 80% idle, and the idle percentage
  at the start and end of each job is logged in `results/progress.txt`.
  - The machine is an Apple M3 Max with 14 cores and 36 GB of memory.
  - CPU idle was 78.7% or more at every job start, and 82% or more at every job end.
  - No job waited more than 45 s for the machine to quieten.
  - macOS load average is not a usable gate, because it counts threads waiting on I/O.
- **Metric:** strict RIR against 0CFA DMCFA, using `benchmarks/plot_utils.py`. Of the items imprecise in the baseline,
  RIR is the fraction that become precise (size ≤ 1). It is computed for values (store and literals) and for
  continuations, and aggregated with the shifted geometric mean.
- **Re-run:** `build` and `coop-communication` were re-run after the two fixes above. All 299 jobs succeeded.
  `build`'s lose times repeated within 1% across the two runs (H(2,1): 593 s, then 588 s; H(2,2): 1337 s, then
  1336 s).

## Results

### Aggregate (`results/compare.txt`)

Examples that finished in every mode:

| config | Value RIR lose / add / keep | Cont RIR lose / add / keep | total time (s) lose / add / keep |
|---|---|---|---|
| 1-kCFA | 0.058 | 0.092 | 8.1 |
| 2-kCFA (40 ex.) | 0.086 | 0.121 | 19.6 |
| H(1,0) | 0.050 / 0.051 / 0.051 | 0.133 | 4.7 / 0.9 / 0.9 |
| H(1,1) | 0.084 | 0.148 | 148 / 26 / 27 |
| H(1,2) | 0.118 / 0.118 / 0.119 | 0.167 | 955 / 101 / 114 |
| H(2,0) | 0.052 / 0.051 / 0.051 | 0.133 / 0.135 / 0.135 | 9.1 / 2.6 / 2.7 |
| H(2,1) | 0.088 / 0.086 / 0.086 | 0.148 / 0.150 / 0.150 | 243 / 41 / 43 |
| H(2,2) (42 ex.) | 0.127 / 0.128 / 0.129 | 0.162 / 0.163 / 0.163 | 391 / 64 / 171 |

- Lose also times out on `build/mymakefile-example4` and `coop-communication/prime-sieve` at H(2,2); add and keep
  don't.
- In every mode, H(1,2) is above both 1-kCFA and 2-kCFA on both metrics. H(1,1) is above 1-kCFA on both, and above
  2-kCFA on continuations only.

The aggregate hides how individual examples change, so here is the breakdown.

### Per example (`results/breakdown.txt`, `scripts/breakdown.py`)

Lose → keep, over 44 examples × the 6 configurations with d ≥ 1 (264 pairs). A precision change counts if
|ΔRIR| > 0.005.

| outcome | pairs |
|---|---|
| unchanged | 188 |
| same precision, fewer states (< 0.9×) | 47 |
| same precision, more states (> 1.1×) | 10 |
| more precise | 13 |
| less precise / mixed | 2 / 2 (all `coop-communication`) |
| lose timeout fixed | 2 |
| new timeout | 0 |

By kind of program:

1. **No change** (`ambient`, `nim`, `vec`, `jump-anywhere`, `monads-writer`, and almost all of `complex-flow` and
   `mini-ppl`): same
   precision, with states and time within a few percent. These read vars, but not deep enough inside calls or
   handlers for the resume context to matter.
2. **Same precision, cheaper:**
   - `build`: median 0.80× the states and 0.31× the time, and the H(2,2) timeout is gone.
   - `pr4rings`: 0.71× the states and the time.
   - `unix`: slightly fewer states in places.
3. **Small, consistent precision gain** (`music/search-come`, `search-love`): value RIR goes up by 0.01–0.02 at every
   configuration, for example 0.03 → 0.05 at H(1,2). With add the gain at m = 2 is only 0.03, because add pushes a
   call off.
4. **The big change: `coop-communication`**, a cooperative scheduler whose handler clauses and resumed tasks read vars.
   - Median 0.47× the states and 0.11× the time. `send-recv` at H(2,2) drops from 139,901 to 10,785 states.
   - The H(2,2) timeout on `prime-sieve` is gone.
   - Continuation RIR on `send-recv` at d = 2 goes from 0.39 to 0.46, and value RIR at H(2,2) from 0.30 to 0.36.
   - **The only "worse" results:** value RIR drops from 0.04–0.07 to 0.00 on `prime-sieve` and `send-recv` at H(2,0)
     and H(2,1).
   - This is most likely lose being unsound rather than keep being less precise: with the dynamic context gone,
     operations can fail to find their handler, values stop flowing, and the result *looks* more precise. Not yet
     confirmed (see next steps).
5. **Slightly more states, same precision** (`scoped`, `unix`, `mini-ppl`, `complex-flow`): at most 10–15% more
   states, because keep's timestamps stay finer.

Add against keep: nearly identical. Add is slightly cheaper at H(2,2) (driven by `build/mymakefile-example4`: 35,628
states with add, 55,030 with keep), but slightly less precise on `music` at m = 2, and it pushes older calls off.

### The paper's tradeoff plot: 1-kCFA → H(1,1)

`images/kcfa1-to-h11-lose.png` and `images/kcfa1-to-h11-keep.png`, made by `benchmarks/plot_expert_tradeoff_metrics.py`.

- The value panel barely changes. The one red regression is in both, and `music/search-*` appears as a small gain
  with keep.
- The continuation panel changes the story. Lose has four blue trade-offs, where H(1,1) is more precise but slower
  than 1-kCFA. With keep, three of them become green win-wins:

| example | H(1,1) time, lose → keep | 1-kCFA time | with keep |
|---|---|---|---|
| `coop-communication/prime-sieve` | 9.2 s → 0.88 s | 4.4 s | win-win |
| `coop-communication/send-recv` | 11.8 s → 0.32 s | 0.32 s | win-win |
| `coop-communication/spawn` | 0.065 s → 0.015 s | 0.020 s | win-win |
| `build/mymakefile-example1`, `-example2` | 22 s → 7 s | 0.28 s | still a trade-off |

`images/tradeoff_lose_to_keep.png` (and `_to_add.png`) shows each example moving from lose (x) to keep (o) at every
H(d,m) with d ≥ 1, labelled where precision changes.

## Conclusion

Keep is at least as precise as lose wherever lose is plausibly sound, several times cheaper on the programs where
reads happen inside handlers, and removes both of lose's timeouts. It is also the semantically faithful choice: a read
is not a call and should not change the timestamp, which is what KCFA already does. Keep is what the source now uses.

## Next steps

1. **Confirm that lose is unsound on `coop-communication`.** Diff the lose and keep stores for `send-recv` at H(2,0)
   and look for flows that only keep has. These should be handler lookups that lose fails. If they are there, the
   "less precise" pairs are lose missing flows.
2. **Local-set.** It still adds a call (`addCallRaw m retCtx (CtxId vcontextId v)`), which pushes the oldest call off
   at small `m`; this is the remaining loss of context seen in the HMCFA viewer on `handlers/vec.kk`. Try resuming a
   set with the set's own dynamic context, as keep does for reads, and measure it the same way. Also, DMCFA's set uses
   `bodId` where DMCFAR's uses `CtxId vcontextId v`; check whether that difference is intended.
3. **Type checker:** reduce `coop-communication` to a test case and check it against `test/type/masklocal*.kk` and
   `eff-var-local.kk` to decide whether `a0e403d89` over-reports `local` on parameters. Then either fix the checker
   or apply `coop-communication-mask.patch` in the koka-gen submodule.
4. **`parse-int` with hex:** the `readHex` branch still answers `Nothing` on strings `readHex` can't parse but Koka
   can (`-ff`, `0x…`). Give it the same fallback as decimal.
5. **Re-validate against the published numbers.** Run `benchmarks/validate.py` on the lose results against the
   artifact's `results-cached`. Expect differences: the compiler has been rebased, and coop-communication and build
   are now included. Then regenerate the paper's plots (`plot_categorical_metrics.py`, `plot_violin_rir.py`) with
   keep.
6. **Timing:** each job ran the modes in the same order (lose, add, keep), so order effects aren't ruled out. The
   state-count differences explain most of the time differences, but a run in a shuffled order would settle it.

## Reproducing

The scripts expect a working directory containing:

- `bindir`: a file holding the compiler's install `bin` directory, which must contain `koka-lose`, `koka-add` and
  `koka-keep`. Build each with `python3 scripts/set-mode.py <mode> && stack build`, then copy `bin/koka` to
  `bin/koka-<mode>`. The copies must stay in `bin/` to find the standard library.
- `analysis/benchmarks/`: a real copy, not a symlink, so module names come out as `analysis/benchmarks/...`.
  - `handlers` and `suite` come from this branch.
  - `rosetta` and `koka-gen` come from the artifact, with `coop-communication-mask.patch` applied.
- `jobs.txt` (as in `scripts/`), a Python venv with pandas, numpy, matplotlib, seaborn and scipy, and the other
  scripts next to it.

Then:

```sh
nohup ./run-sequential.sh > run.log 2>&1 &   # resumable; skips jobs already in progress.txt; MINIDLE=80
./merge.sh                                   # merged/<mode>/benchmarks/results = shared runs + that mode's runs
venv/bin/python compare.py merged <koka>/benchmarks
venv/bin/python breakdown.py merged <koka>/benchmarks breakdown
```
