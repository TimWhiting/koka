# Benchmark Line Counts (Transitive Analysis)

This document provides a *transitive* line count analysis for the Koka benchmarks. Unlike previous counts which measured file size, this analysis traces the execution graph starting from each `analyze-*` entry point, summing the source lines of code (SLOC) of every Koka function called, including those in the standard library.

## Methodology

1.  **Entry Point**: Each `analyze-*` function is treated as a root.
2.  **Dependency Tracing**: We trace all function calls, handlers, and effect definitions required to run the benchmark.
3.  **Counting**:
    *   **Koka SLOC**: The number of lines in the function body + signature.
    *   **StdLib Includes**: Koka implementations in `std/core/list`, etc. are counted (e.g., `map` is ~5 lines).
    *   **Exclusions**: Comments, blank lines, `extern` definitions (C/JS strings), and compiler intrinsics are **not** counted.
4.  **Deduplication**: Shared dependencies (like helper functions used multiple times) are counted only once per benchmark.

## Handlers Benchmarks (`analysis/benchmarks/handlers/`)

### `nim.kk`
| Entry Point | Trace Summary | Total SLOC |
| :--- | :--- | :---: |
| `analyze-example-perfect1` | `example-perfect1`, `perfect`, `game`, `alice-turn`, `bob-turn`, `move`, `player`, `max`(wrapper) | **14** |
| `analyze-example-gtree` | `example-gtree`, `gametree`, `valid-moves`, `game`-cycle, `gtree`, `Take`, `map`, `filter`, `zip` | **42** |
| `analyze-example-check` | `example-check`, `cheat-report`, `check`, `valid-moves`, `find`, `bool`, `player/show` | **32** |
| `analyze-example-pc1` | `example-pc1`, `pc` (strategy), `cheat-report`, `check`, `game`-cycle | **30** |

### `scoped.kk`
| Entry Point | Trace Summary | Total SLOC |
| :--- | :--- | :---: |
| `analyze-example1` | `example1`, `solutions`, `knapsack`, `select`, `nondet`, `list/append` | **22** |
| `analyze-example5` | `example5`, `solutions`, Grammars (`parse`,`expr`,`term`,`factor`,`number`,`digit`), `map`, `join` | **65** |

### `ambient.kk`
| Entry Point | Trace Summary | Total SLOC |
| :--- | :--- | :---: |
| `analyze-example0` | `example0`, `f`, `width` (effect) | **7** |

### `unix.kk`
| Entry Point | Trace Summary | Total SLOC |
| :--- | :--- | :---: |
| `analyze-example1` | `bio` handler, `echo` | **6** |
| `analyze-example5` | `scheduler`, `forking`, `timeshare`, `session-manager`, `status`, `ritchie`, `list/append` | **65** |

## Suite Benchmarks (`analysis/benchmarks/suite/`)

These benchmarks generally test specific compiler features or control flow patterns and have minimal external dependencies.

| File | Entry Point | Dependencies | Total SLOC |
| :--- | :--- | :--- | :---: |
| `basic.kk` | `analyze-list` | Recursive list build/sum | **12** |
| `recursion.kk` | `analyze-iter-sum` | `iter` (recursive) | **5** |
| `nondet.kk` | `analyze-nondet-simple` | `ex2` handler | **8** |
| `nondet.kk` | `analyze-nondet-nested` | `ex2` handler | **8** |

## Summary

The "Handlers" benchmarks vary significantly in complexity:
*   **Micro-benchmarks**: ~10-20 lines (e.g., `perfect` nim strategy, basic ambient state).
*   **System Simulations**: ~60-70 lines (e.g., `unix` scheduler, `scoped` grammars).
*   **StdLib Usage**: The primary cost comes from functional list operations (`map`, `filter`, `zip` etc.), while the effect handling logic itself is famously concise in Koka.
