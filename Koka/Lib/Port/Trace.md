# Porting Audit: Lib.Trace

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `trace` | [x] | - | - | 20-21 | 18-19 | No |
| `traceShowM` | [x] | - | - | 23-24 | 21-22 | No |
| `traceM` | [x] | - | - | 26-27 | 24-25 | No |
| `traceId` | [x] | - | - | 29-30 | 27-28 | No |
| `traceShow` | [x] | - | - | 32-33 | 30-31 | No |
| `traceShowId` | [x] | - | - | 35-36 | 33-34 | No |
| `traceDoc` | [x] | - | - | 38-39 | 36-37 | No |
| `traceEq` | [x] | - | - | 41-42 | 39-40 | No |
| `ctrace` | [x] | - | - | 44-52 | 14-16 | No |

## Notes
- Replaced `unsafePerformIO` and internal custom Koka C PPrint handlers with Lean's native `dbg_trace` macro. This achieves the exact same debugging printouts robustly without polluting standard outputs handling (important for Koka language server protocols).
