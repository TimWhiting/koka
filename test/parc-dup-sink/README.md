# Deferred dup sinking in `Parc`: report, repros, and a failed first attempt

## The defect

An in-place record update **inside a nested match** pays a dup+drop per field
that provably cancels. The same update *not* nested is compiled optimally. One
`match` of nesting is enough to lose it.

`test/parc-dup-sink/nested.kk` (12 lines) is the minimal case. Today it yields:

```c
dup(a); dup(b); dup(d);                                  // hoisted to the OUTER branch
if (unique(r)) { drop(d); drop(c); drop(b); drop(a); _ru = reuse(r); }
else           { decref(r); }
```

while the non-nested `flat.kk` yields the ideal:

```c
if (unique(r)) { _ru = reuse(r); }
else           { dup(a); dup(b); dup(c); dup(d); decref(r); }
```

## Why (root cause, confirmed by reading the passes)

The passes run in different directions:

| pass | direction |
|---|---|
| `Parc` (dup/drop insertion) | **bottom-up** -- body rewritten first, then the binding site PREPENDS its dups (`maybeStats`) |
| `ParcReuse` (find a donor block) | top-down -- `addDeconstructed` flows availability into branches |
| `ParcReuseSpec` (field-wise assign) | bottom-up, local to one `@alloc-at` |

`parcGuard` computes `dups = ownedPvs ∩ liveInThisBranch` and emits them at the
OUTER branch head. The `drop(r)` happens in the INNER branch, and is specialized
*earlier* in Parc's bottom-up order -- at which point the outer dups do not exist
yet, so `specializeDrop` is handed an empty dup set and emits the conservative
"drop every child" form. `fuseDupDrops` can only cancel dups and drops that reach
one `optimizeDupDrops` call; here they never meet.

`specializeDrop` DOES recurse -- but over the **field tree** of the dropped value,
not over control structure, so no amount of recursion reaches an enclosing branch.

Parc's own TODO (`Parc.hs`, above `parcLam`) proposes the same fix:
*"maybe we should track a borrowed set and presume owned, instead of the other
way around?"*

## Why it is worth doing

Measured on `compiler/syntax/lex.kk`'s `alex_advance` in the koka-community port
(a 10-field scan state updated once per input character):

* baseline: **40 refcount/uniqueness ops** for a function whose semantic work is
  "read one character, shift three fields"
* with the (unsound) first attempt: **29**

Interface loading in that port is ~25% refcount traffic, and the lexer is its
largest consumer. The shape -- record update inside a nested match -- is the core
FBIP idiom, so this is not lexer-specific.

## Repros

| file | checks |
|---|---|
| `flat.kk` | non-nested update. MUST stay byte-identical (4 refcount ops) |
| `wildcard-and-shift.kk` | wildcard pattern; field moved to another field. MUST stay identical (4 and 5 ops) |
| `nested.kk` | the defect. Optimal output is `if unique { drop(c); reuse } else { dup(a,b,d); decref }` |
| `nested-sibling.kk` | **the soundness test.** Alternates so BOTH branches run |

`nested.kk` alone is not sufficient: its `Nil` branch never executes, so it
passes even when the transform is unsound. `nested-sibling.kk` is what caught the
use-after-free. Correct output: `[1] [2] [] 200`.

## Attempt 1 (`attempt-1.patch`) -- produces the right code, still crashes

Adds `pending :: TNames` to `Parc.Env`; `parcGuard` defers its pattern dups into
an immediately nested match (`deferrableInto`) and folds any inherited set into
its own `dups`, so dup and drop meet in one `optimizeDupDrops` call.

It produces exactly the intended code on all four repros AND on `alex_advance`
(40 -> 29 ops), and leaves the flat cases byte-identical. **But a large program
built with it segfaults** -- `EXC_BAD_ACCESS` in `kk_utf8_read` on a pointer that
is string data, i.e. a use-after-free.

Soundness constraints discovered so far, both needed:

1. **Sink into EVERY branch, never a subset.** Claiming per-branch means the
   outer must still dup for the unclaiming branches, which then double-dups on
   the claiming path (leak); the mirror case is a use-after-free.
2. **A deferred variable is BORROWED in the nested branches: never dropped
   there.** A branch that does not use it must not drop it -- the enclosing block
   still owns it and its drop releases the children. This was the first bug
   found; the patch has the fix (`drops` subtracts `inherited`).

**The remaining bug is believed to be this:** `deferred` is computed BEFORE
liveness is known (that is the ordering problem in the first place), so it can
contain variables that no branch actually uses -- and the drop-suppression in (2)
is then applied to variables nothing ever claimed. The fix is probably to track
what each branch ACTUALLY claimed and suppress drops only for those, rather than
for the whole deferred set. That is unverified: it is where to start, not a
diagnosis.

## Gates, in this order

1. `nested-sibling.kk` runs and prints `[1] [2] [] 200` (fastest signal)
2. all four repros' generated C matches the table above
3. `stack test` in this worktree (upstream's own suite)
4. in `~/koka-community/compiler`: rebuild the driver with this compiler
   (`./koka -O2 -c compiler/main/driver.kk`), then the 442-test sweep
   (`LANG=C ./koka -O2 -e --include=. scripts/test-runner.kk`, baseline
   **423 PASS / 17 SKIP / 2 MISMATCH / 0 TIMEOUT**) and
   `./scripts/multimodule-gate.sh`
5. re-measure `alex_advance` ops and the warm build

## Practical notes

* `stack build` here takes ~10 minutes. **Do not kill it mid-build** -- it
  corrupts objects (`renameFile ... .o.tmp does not exist`) and costs a full
  rebuild.
* The port's driver is compiled BY this compiler, so a miscompile shows up as a
  segfaulting `compiler_main_driver__main`, not as a Haskell error.
* Check generated C with:
  `awk '/kk_t3_bump_nested\(/{f=1} f{print} f&&/^}/{exit}' .koka/*/*/t3.c`
