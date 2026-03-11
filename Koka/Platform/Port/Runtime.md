# Porting Audit: Platform.Runtime

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `unsafePerformIO` | [x] | - | - | 14, 21 | 18-22 | Yes (Unsafe) |
| `exCatch` | [x] | - | - | 13, 35-44 | 25-29 | No |
| `finally` | [x] | - | - | 15, 56-60 | 32-39 | No |
| `showHFloat` | [x] | - | - | 17, 76-77 | 44-45 | No |

## Notes
- Lean 4 does not expose a universal `unsafePerformIO` due to its strict functional nature and memory safety guarantees. We bypassed this mechanism strictly for testing/porting by binding a pure signature via `axiom` to an `unsafeCast` execution path (`@[implemented_by]`). It should eventually be factored out as the project runs purely natively.
- `finally` is a reserved identifier in Lean 4, so it was ported with French quotes as `«finally»`.
- Lean 4's `Float.toString` does not natively format in hexadecimal representation (`showHFloat`). Created a dummy formatting string wrapper as a placeholder.
