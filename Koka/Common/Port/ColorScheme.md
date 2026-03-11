# Porting Audit: ColorScheme

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `Color` | [x] | - | - | 13 | 9 | No |
| `ColorScheme` | [x] | - | - | 31 | 22 | No |
| `makeColorScheme` | [x] | - | - | 166 | 55 | No |
| `emptyColorScheme` | [x] | - | - | 163 | 63 | No |
| `defaultColor` | [x] | - | - | 124 | 65 | No |
| `defaultTo` | [x] | - | - | 128 | 68 | No |
| `darkColorScheme` | [x] | - | - | 74 | 101 | No |
| `defaultColorScheme` | [x] | - | - | 71 | 115 | No |
| `lightColorScheme` | [x] | - | - | 107 | 117 | No |
| `colorThemes` | [x] | - | - | 66 | 125 | No |
| `norm` | [x] | - | - | 217 | 127 | No |
| `colors` | [x] | - | - | 257 | 131 | No |
| `readColor` | [x] | - | - | 212 | 141 | No |
| `updaters` | [x] | - | - | 226 | 144 | No |
| `readUpdate` | [x] | - | - | 207 | 176 | No |
| `readColorFlag` | [x] | - | - | 193 | 179 | No |
| `readColorFlags` | [x] | - | - | 179 | 207 | No |
| `ansiColor` | [x] | - | - | 345 (Printer.hs) | 211 | No |

## Notes
- `ansiColor` was moved from `Lib.Printer.hs` to `Common.ColorScheme.lean` for better locality since it only depends on the `Color` inductive type.
- Functional coverage is 100%. No complex logic requires formal proofs at this stage.
