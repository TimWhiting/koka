# Porting Audit: PPrint

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `Doc` | [x] | - | - | 294 | 15 | No |
| `SimpleDoc` | [x] | - | - | 306 | 30 | No |
| `Pretty` class | [x] | - | - | 214 | 173 | No |
| `combinators (<.>, etc)` | [x] | - | [x] | 131-144 | 43-128 | No |
| `align/hang/indent` | [x] | - | - | 280-285 | 220-227 | No |
| `fill/fillBreak` | [x] | - | - | 266-272 | 214-218 | No |
| `encloseSep/list/etc` | [x] | - | - | 94-105 | 144-153 | No |
| `sep/cat/hsep/vsep/etc`| [x] | - | - | 118-126 | 135-142 | No |
| `string/int/float/etc` | [x] | - | - | 181-204 | 161-172 | No |
| `renderPretty/best/nice`| [x] | - | - | 481-517 | 230-263 | No |
| `renderCompact` | [x] | - | - | 531 | 275 | No |
| `displayS/asString` | [x] | - | - | 550, 557 | 308, 319 | No |
| `displayP` | [x] | - | - | 565 | 322 | No |
| `writePretty/W/Ln` | [x] | - | - | 594-602 | 358-370 | No |
| `writeDoc/W` | [x] | - | - | 633-637 | 377-388 | No |
| `makeMarkdown` | [x] | - | - | 313 | 306 | No |
| `inspection (dcontains,etc)` | [x] | - | - | 366-382 | 344-365 | No |

## Notes
- Core Wadler-style pretty printing engine is fully ported with functional parity.
- **Implementation**: Instead of Haskell's lazy `displayIO`, Lean uses `displayP` which interacts with the `Printer` typeclass abstractions.
- Unit tests for basic combinators are in `Koka/Lib/Test/PPrint.lean`.
