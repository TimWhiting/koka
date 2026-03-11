# Porting Audit: Lib.Scc

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `Graph` | [x] | - | - | 36-41 | 12-13 | No |
| `nodes` | [x] | - | - | 46 | 15 | No |
| `graph` | [x] | - | - | 50 | 18 | No |
| `edges` | [x] | - | - | 57 | 25 | No |
| `vertices` | [x] | - | - | 61 | 28 | No |
| `successors` | [x] | - | - | 65 | 31 | No |
| `transpose` | [x] | - | - | 69 | 34 | No |
| `Tree`, `Forest` | [x] | - | - | 80-81 | 43-45 | No |
| `dff` | [x] | - | - | 83 | 64 | Yes |
| `dfs`, `tree`, `prune` | [x] | - | - | 87-108 | 47-62 | Yes |
| `preorderT`, `preorderF` | [x] | - | - | 116-120 | 69-74 | Yes |
| `preorder` | [x] | - | - | 112 | 76 | Yes |
| `postorderT`, `postorderF` | [x] | - | - | 126-135 | 80-88 | Yes |
| `postorder` | [x] | - | - | 122 | 90 | Yes |
| `topsort` | [x] | - | - | 184 | 93 | Yes |
| `sccF` | [x] | - | - | 180 | 98 | Yes |
| `sccG` | [x] | - | - | 176 | 101 | Yes |
| `scc` | [x] | - | - | 172 | 104 | Yes |
| `reachable` | [x] | - | - | 190 | 109 | Yes |
| `path` | [x] | - | - | 193 | 112 | Yes |

## Notes
- Lean 4 enforces strict evaluation, meaning the classic functional algorithm mapping out an infinite `Tree` and then `prune`-ing it (using `Set.empty` progressively) results in an infinite loop on graph cycles.
- The `dfs` function was refactored to explicitly interleave `go`, updating the `HashSet` progressively during child evaluations.
- Because termination isn't structurally obvious to Lean for graph traversals via `HashSet`, `dfs` and all functions that depend on it directly (`scc`, `postorder`, `topsort`, `reachable`, etc.) are declared as `partial def`. If correctness checking inside the compiler codebase is required later, fuel mechanisms or well-founded structural bounds via sizes of sets could replace `partial`.
