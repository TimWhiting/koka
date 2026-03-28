# Porting Audit: Syntax.Layout

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `lexSource` | [ ] | - | - | 28 | - | Yes (Missing) |
| `layout` | [x] | - | - | 36 | 268 | No |
| `isLexError` | [x] | - | - | 51 | 21 | No |
| `removeWhite` | [x] | - | - | 54 | 25 | No |
| `removeWhiteSpace` | [x] | - | - | 58 | 28 | No |
| `endLine` | [x] | - | - | 71 | 34 | No |
| `startLine` | [x] | - | - | 74 | 35 | No |
| `startCol` | [x] | - | - | 77 | 36 | No |
| `endCol` | [x] | - | - | 80 | 37 | No |
| `before` | [x] | - | - | 84 | 39 | No |
| `after` | [x] | - | - | 87 | 40 | No |
| `associateComments` | [x] | - | - | 94 | 42 | No |
| `combineLineComments` | [x] | - | - | 157 | 97 | No |
| `checkIds` | [x] | - | - | 175 | 140 | No |
| `checkComments` | [x] | - | - | 201 | 142 | No |
| `Layout` | [x] | - | - | 226 | 166 | No |
| `indentLayout` | [x] | - | - | 228 | 261 | No |
| `brace` | [x] | - | - | 233 | 225 | No |
| `insertLCurly` | [x] | - | - | 279 | 170 | No |
| `insertRCurly` | [x] | - | - | 283 | 174 | No |
| `insertSemi` | [x] | - | - | 288 | 186 | No |
| `isExprContinuation` | [x] | - | - | 292 | 208 | No |
| `isStartContinuationToken`| [x] | - | - | 296 | 191 | No |
| `isEndContinuationToken` | [x] | - | - | 306 | 200 | No |
| `lineLayout` | [x] | - | - | 338 | 319 | No |
| `semiInsert` | [x] | - | - | 344 | 322 | No |
| `identifyModules` | [x] | - | - | 382 | 314 | No |
| `replaceModules` | [x] | - | - | 392 | 280 | No |
| `scanImports` | [x] | - | - | 402 | 289 | No |
| `scanImport` | [x] | - | - | 418 | 305 | No |

## Notes
- Functional parity is high, but some top-level wrappers and deprecated functions are missing.
- `lexSource` requires `Lexer` and `Source` utilities.
- `lineLayout` is deprecated but should be included for completeness.
