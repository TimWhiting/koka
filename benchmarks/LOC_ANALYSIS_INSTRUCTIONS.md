# LOC Analysis Task Instructions

## Primary Objective
Populate `analysis/graph-data.kk` with complete dependency graphs for all `analyze-*` functions in the benchmarks directory. Each entry must have accurate LOC counts and complete dependency lists.

## Critical Counting Rules

### Function LOC Counting
1. **ALWAYS count the function definition line as 1 LOC**
   - Example: `fun my-function(x: int): int` counts as 1 LOC
2. Count only executable code lines
3. Exclude blank lines and comments
4. For multi-line expressions, count each line separately

### Effect Definition Counting
- Base formula: `1 + (2 × number_of_operations)`
- Example: `effect<a> amb { fun flip(): bool }` = 1 + 2(1) = 3 LOC

### Field Accessor Counting
- Accessor: 3 LOC (1 function definition, 1 match, 1 branch)

## Type Counting
- The number of lines of code in the type definition.

## Mandatory Verification Process

### Before Adding ANY Function to graph-data.kk:

1. **Read the actual source code**
   - Use `grep_search` to locate the function
   - Use `read_file` to examine the complete implementation
   - Count lines manually, excluding comments and blank lines
   - Verify the function definition line is included in count

2. **Identify all dependencies**
   - List every function called within the function body
   - For each of those functions check if they require implicit parameters
     - Figure out which implicits would be supplied (by finding a function with that name and expected type)
     - Ask the user if this is difficult
   - Track operator usage (e.g., `+`, `==`, `++`)
   - Dependencies on constructors are counted as referencing the type - not the constructors.
     - Omit counting of True / False

3. **Verify standard library functions**
   - Never assume standard library functions are 1 LOC
   - Look up actual implementations in `lib/std/`
   - Common locations:
     - `lib/std/core/list.kk` - list operations
     - `lib/std/core/int.kk` - integer operations
     - `lib/std/core/string.kk` - string operations
     - `lib/std/num/random.kk` - random functions
     - `lib/std/num/float64.kk` - floating point operations

4. **Self-audit before completion**
   - Review your LOC count against the source
   - Confirm all dependencies are listed
   - Check for helper functions you might have missed
   - Verify transitive dependencies exist in graph
   - Verify that you found the right overloaded function (Koka typically has many functions with the same name)
   - Make sure that the name includes the module name and full locally qualified name.

## Systematic File Processing

### For each file:

1. **Announce the file** you're about to process
2. **Count analyze functions** - state how many you found
3. **Process each analyze function**:
   - Read the source code
   - Count LOC accurately
   - Identify all dependencies
   - Verify each dependency exists or needs to be added
4. **Add helper functions** as you discover them
5. **Perform final audit** of all additions
6. **Report completion** with summary before moving on

### Quality Checklist for Each Function:
- [ ] Read actual source code
- [ ] Counted function definition line
- [ ] Excluded comments and blank lines
- [ ] Listed all called functions
- [ ] Verified standard library LOC counts
- [ ] Added any missing helper functions
- [ ] Confirmed all dependencies exist in graph

## Common Mistakes to Avoid

1. ❌ Assuming standard library functions are 1 LOC
2. ❌ Forgetting to count the function definition line
3. ❌ Missing helper functions called by main function
4. ❌ Counting comments or blank lines
5. ❌ Not verifying actual source before adding to graph
6. ❌ Rushing through files without thorough review

## Response Pattern

When processing a file, follow this pattern:

```
Processing: analysis/benchmarks/koka-gen/[filename].kk

Found X analyze-* functions in this file.

[Read source code for each function]

Adding to graph-data.kk:
- analyze-function-1: Y LOC, dependencies: [list]
- analyze-function-2: Z LOC, dependencies: [list]

Helper functions needed:
- helper-1: N LOC, dependencies: [list]
- helper-2: M LOC, dependencies: [list]

[Perform audit]

Audit complete. All functions verified against source.
Ready to move to next file.
```

## Progress Tracking

### Completed Files:
- ✓ suite/*.kk (8 files, 48 analyze functions)
- ✓ handlers/ambient.kk (1 function)
- ✓ koka-gen/interp.kk, interp2.kk (10 functions)
- ✓ koka-gen/build.kk (5 functions)
- ✓ koka-gen/coop-communication.kk (4 functions)
- ✓ koka-gen/mini-ppl.kk (3 functions)
- ✓ koka-gen/music.kk (2 functions)
- ✓ koka-gen/ukanren.kk (2 functions)
- ✓ rosetta/a/abcproblem.kk (1 function)
- ✓ rosetta/p/playing-cards.kk (1 function)
- ✓ rosetta/b/balanced-ternary.kk (1 function)
- ✓ rosetta/c/conjugate-latin-verbs.kk (1 function)
- ✓ rosetta/m/monads-writer.kk (1 function)
- ✓ rosetta/j/jump-anywhere.kk (2 functions)
- ✓ rosetta/n/nim.kk (1 function)
- ✓ rosetta/0-nums/pr4rings.kk (1 function)
- **Total: 84 analyze functions catalogued**

### All analyze-* functions have been catalogued!

## Key Principle

**VERIFY, DON'T ASSUME**

When in doubt, read the source code. Accuracy is more important than speed. Every function added to the graph will be used for analysis, so correctness is critical.
