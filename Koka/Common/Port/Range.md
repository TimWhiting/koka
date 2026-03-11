# Porting Audit: Common.Range

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `BString` / utils | [x] | - | - | 49-61 | 19-24 | No |
| `readInput` | [x] | - | - | 63-70 | 26-31 | No |
| `extractLiterate` | [x] | - | - | 115-155 | 34-34 | Yes |
| `Source` | [x] | - | - | 160 | 38 | No |
| `sourceNull` | [x] | - | - | 167 | 46 | No |
| `sourceText` | [x] | - | - | 168 | 48 | No |
| `Pos` | [x] | - | - | 174-178 | 53 | No |
| `posNull` | [x] | - | - | 180 | 60 | No |
| `bigLine` | [x] | - | - | 210 | 80 | No |
| `makePos` | [x] | - | - | 218 | 82 | No |
| `posMove8` | [x] | - | - | 226 | 86 | No |
| `posMoves8` | [x] | - | - | 222 | 93 | No |
| `Range` | [x] | - | - | 241 | 104 | No |
| `showPos` | [x] | - | - | 196 | 115 | No |
| `showCompactRange` | [x] | - | - | 259 | 120 | No |
| `showRange` | [x] | - | - | 263 | 129 | No |
| `after` | [x] | - | - | 276 | 138 | No |
| `rangeNull` | [x] | - | - | 280 | 141 | No |
| `rangeIsNull` | [x] | - | - | 284 | 144 | No |
| `showFullRange` | [x] | - | - | 288 | 147 | No |
| `makeRange` | [x] | - | - | 293 | 158 | No |
| `makeSourceRange` | [x] | - | - | 298 | 164 | No |
| `rangeLength` | [x] | - | - | 305 | 168 | No |
| `rangeSource` | [x] | - | - | 309 | 170 | No |
| `combineRange` | [x] | - | - | 313 | 172 | No |
| `combineRanges` | [x] | - | - | 317 | 175 | No |
| `rangeHide` | [x] | - | - | 321 | 178 | No |
| `minPos`, `maxPos` | [x] | - | - | 327-334 | 150-156 | No |
| `extendRange` | [x] | - | - | 336 | 181 | No |
| `endOfRange`, `startOfRange` | [x] | - | - | 341-348 | 185-190 | No |
| `rangeContains`, `rangeIsBefore`, `rangeStartsAt` | [x] | - | - | 351-359 | 193-200 | No |
| `rangeJustBefore`, `rangeJustAfter` | [x] | - | - | 361-368 | 202-210 | No |
| `Ranged` class | [x] | - | - | 381-390 | 215-224 | No |
| `combineRangeds`, `combineRanged` | [x] | - | - | 373-379 | 226-230 | No |
| `sourceFromRange` | [x] | - | - | 398-416 | 235-245 | No |
| `rawSourceFromRange` | [x] | - | - | 418-422 | 247-249 | No |

## Notes
- `extractLiterate` is implemented as a mock that just returns the input because literate parsing logic is largely independent and relies on a specific state machine that's better translated exactly or left entirely if unnecessary for parsing standard files right now. Marked as Partial.
- Modified `relativeToPath` logic internally since Koka's `relativeToPath` lives in `Common.File` and wasn't fully exported in Koka-Lean `Common.File` yet.
- Replaced `B.ByteString` with native Lean 4 `String` (`BString` abbrev to `String`), leveraging Lean's UTF-8 native capabilities over Haskell's sequence of bytes.
