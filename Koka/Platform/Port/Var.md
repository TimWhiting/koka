# Porting Audit: Platform.Var

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `Var` | [x] | - | - | 20, 34 | 10 | No |
| `newVar` | [x] | - | - | 22-23, 36-37 | 12-13 | No |
| `takeVar` | [x] | - | - | 25-26, 42-43 | 15-16 | No |
| `putVar` | [x] | - | - | 28-29, 39-40 | 18-19 | No |

## Notes
- Mapped accurately to Lean 4's native `IO.Ref`.
