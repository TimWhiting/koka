# Porting Audit: Kind.Pretty

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `kindColon` | [x] | - | - | 24-25 | 17-18 | No |
| `keyword` | [x] | - | - | 27-28 | 20-21 | No |
| `niceKinds` | [x] | - | - | 33-35 | 75-76 | No |
| `prettyKind` | [x] | - | - | 37-39 | 78-79 | No |
| `Pretty Kind` | [x] | - | - | 45-47 | 81-82 | No |
| `Prec` | [x] | - | - | 50-51 | 24 | No |
| `precTop` | [x] | - | - | 54 | 26 | No |
| `precQuant` | [x] | - | - | 55 | 27 | No |
| `precArrow` | [x] | - | - | 56 | 28 | No |
| `precApp` | [x] | - | - | 57 | 29 | No |
| `precAtom` | [x] | - | - | 58 | 30 | No |
| `pparens` | [x] | - | - | 60-63 | 32-33 | No |
| `ppKind` | [x] | - | - | 66-81 | 52-73 | Yes |
| `commaParens` | [x] | - | - | 83-84 | 49-50 | No |
| `collectFunArgs` | [x] | - | - | 86-90 | 35-41 | No |
| `collectArgs` | [x] | - | - | 92-95 | 43-47 | No |

## Notes
- Built `collectArgs` and `collectFunArgs` as top-level helpers without `partial`, as Lean resolves them as structurally terminating natively.
- `ppKind` retains `partial` to ignore recursive sizing constraints over `KApp`.
