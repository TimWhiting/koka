# Porting Audit: Common.Message

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `ppRange` | [x] | - | - | 28-30 | 18-19 | No |
| `tablex` | [x] | - | - | 35-42 | 21-29 | No |
| `table` | [x] | - | - | 32-33 | 31-32 | No |
| `removeIndent` | [x] | - | - | 81-84 | 38-41 | No |
| `limitLines` | [x] | - | - | 70-79 | 43-52 | No |
| `limitLineLen` | [x] | - | - | 61-68 | 54-64 | No |
| `docFromRange` | [x] | - | - | 55-59 | 66-71 | No |
| `docsFromRanges` | [x] | - | - | 51-53 | 73-74 | No |
| `sourceFromRanges` | [-] | - | - | 47-49 | - | No |

## Notes
- Ported `Common.Message` with string slicing operations replaced by list conversions, and maximum width formatting via `displayS (renderCompact ...)`.
- Mapped `isSpace` to `Char.isWhitespace`.
- `sourceFromRanges` wasn't ported as `docsFromRanges` subsumes its utility entirely and does not rely on it, saving an unnecessary translation.
