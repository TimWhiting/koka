# Koka Porting Strategy

This document outlines the strategy for porting the Koka compiler from Haskell to Lean 4.

## Porting Metadata
All ported files must include a header comment with the original Haskell commit hash and date to track upstream changes.
```lean
/-
  Ported from Haskell Koka:
  File:   src/<PathToHaskellFile>
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
```

## Tracking Partial Definitions
Because Lean is a total language, recursive functions that Lean cannot automatically prove terminating (e.g., parsing loops, division) should be marked as `partial def` initially to unblock porting. We will revisit these later to add termination proofs (`termination_by`).

### Current Partial Definitions:
* `Koka.Common.Name.readQualifiedName`: Mutual recursion parsing loop over strings.
* `Koka.Common.Name.hexDigits`: Tail recursive division loop.
* `Koka.Common.Name.decodePathToModule`: Recursive string slice/drop loop.
* `Koka.Lib.PPrint.flatten` (mutual): Recursion over `Doc` tree structure.
* `Koka.Lib.PPrint.stringP`: Recursion over string slices.
* `Koka.Lib.PPrint.best`, `nicest`, `fits` (mutual): The core rendering engine, non-structural recursion over a list of documents and text fitting.
* `Koka.Lib.PPrint.renderCompact`: Un-indented rendering engine, similar recursion to `best`.
* `Koka.Lib.PPrint.displayP`: Complex recursive rendering to IO `Printer` with dynamic width checking.

## Tracking Unported Definitions
Some Haskell libraries or GHC-specific features do not have direct Lean equivalents yet, or their ports belong to a different layer of the compiler.

### Current Unported Definitions:
* `Common.Failure.HasCallStack`: GHC-specific typeclass constraint. Skipped.
* `Common.Syntax`: Skipped `sepBySpace` and `memberDoc` which depend on `Lib.PPrint`. (To be added once `PPrint` is ported).
* `Common.File`: Skipped `Async` or heavy OS-specific file time formats where Lean's `IO.FS.SystemTime` differs subtly, although basic IO wrappers were implemented.

## Steps for Porting a File

When porting a new Haskell source file to Lean, follow these steps systematically:
- [ ] **Analyze Dependencies**: Check the Haskell `import` block. Ensure all internal dependencies have already been ported. For external dependencies (e.g., containers, text), map them to the corresponding Lean 4 `Std` or `Mathlib` structures (or mark as needing custom implementation).
- [ ] **Create the Lean File**: Create the corresponding `.lean` file with the target namespace (e.g. `Koka.Lib.PPrint`).
- [ ] **Include File Header**: Insert the mandated porting metadata header containing the original Haskell file path, commit hash, and date.
- [ ] **Translate Types and Functions**: 
  - Translate ADTs to `inductive` or `structure`.
  - Translate functions, making use of `partial def` for non-structural recursion initially.
  - Apply `panic!` for `error` calls and assertions.
- [ ] **Resolve Errors**: Ensure the file builds successfully via `lake build Koka`.
- [ ] **Create Audit Report**: Create an audit `<ModuleName>.md` within the relevant `Port/` directory. Create a table checking every function/type for lines, partial annotations, tests, and proofs.
- [ ] **Update Master Checklist**: Add or update the module's row in `porting_audit.md`.
- [ ] **Add Tests and Proofs**: (Optional but recommended) Provide `#eval` tests in a `Test/` file or semantic proofs in a `Proof/` file.

## Porting Audit Requirement
After porting a module or adding significant functionality to an existing port, the following must be updated:
1.  **Module Audit Report**: Update the corresponding `.md` file in the `Port/` directory (e.g., `Koka/Common/Port/Name.md`). Mark functions as ported, update line numbers if necessary, and note any implementation details.
2.  **Master Checklist**: Update `porting_audit.md` in the root directory to reflect the new status (Completed/Partial), updated function counts, tests, and proofs.

## General Mapping Guidelines
* Lists: Lean `List α` or `Array α` (depending on performance needs).
* Maps/Dicts: Lean `Std.HashMap` or `Std.RBMap`.
* State/IO: Lean `IO` and `StateT`.
* Error handling: `ExceptT` or basic `Option` rather than Haskell's `error` where possible, though `panic!` is used for assertions.

## Testing Strategy
* **Setup**: Using standard Lean `#eval` and isolated test files in a `Test/` subdirectory inside each implementation directory (e.g., `Koka/Common/Test/Name.lean`). We can assert basic correctness using `IO` tests.
* **Component-Level Tests**: For each non-trivial function (e.g., path parsers, formatters, and IO wrappers), we will add test cases that assert equivalence with original Haskell output.
* **Printing Tests**: `Lib.PPrint` and its combinators will be tested against standard layout examples to ensure correct text rendering.

## Proofs Strategy
* **Totality and Well-foundedness**: For functions mapped directly, Lean automatically proves totality (termination). For `partial def` functions, we aim to eventually use `termination_by` or refactor them into structurally recursive forms (e.g., fuel-based or passing a length proof).
* **Semantic Properties**: For core data structures like `Name` or basic utilities, we will add formal proofs of correctness for key invariants (e.g., `decodePathToModule(pathToModuleName(x)) == x` or idempotence of certain path operations) where feasible and beneficial.
* **Approach**: We will prioritize proving properties of foundational functions first, as downstream functions rely on their correctness. Where full proofs are too difficult, we will rely on comprehensive tests.
