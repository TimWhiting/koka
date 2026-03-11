# Porting Audit: Platform.Config

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `programName` | [x] | - | - | 20-25 | 10 | No |
| `version` | [x] | - | - | 27-32 | 12 | No |
| `compilerBuildVariant` | [x] | - | - | 34-39 | 14 | No |
| `compiler` | [x] | - | - | 41-50 | 16 | No |
| `exeExtension` | [x] | - | - | 52, 57, 70 | 18 | No |
| `dllExtension` | [x] | - | - | 58, 66, 75 | 19 | No |
| `objExtension` | [x] | - | - | 59, 67, 76 | 20 | No |
| `libExtension` | [x] | - | - | 60, 68, 77 | 21 | No |
| `libPrefix` | [x] | - | - | 61, 69, 78 | 22 | No |
| `pathSep` | [x] | - | - | 53, 62, 71, 80 | 23 | No |
| `pathDelimiter` | [x] | - | - | 53, 63, 72, 81 | 24 | No |
| `sourceExtension` | [x] | - | - | 84-85 | 26 | No |
| `buildDate`, `buildTime` | [x] | - | - | 87-96 | 28-29 | No |

## Notes
- OS detections mapped cleanly via standard `System.Platform.isWindows` and `System.Platform.isOSX` logic directly compiled into the constants.
- Compiler name defaults to `lean4` instead of `ghc`.
