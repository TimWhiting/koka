# Porting Audit: Name

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `Name` | [x] | - | - | 105 | 19 | No |
| `hashStr` | [x] | - | - | 308 | 32 | No |
| `nameLocal` | [x] | - | - | 121 | 46 | No |
| `nameCaseEqual/Overlap` | [x] | - | - | 125-141 | 52-73 | No |
| `lowerCompare` | [x] | - | - | 147 | 87 | No |
| `isIdChar/Start/End` | [x] | [x] | - | 201-211 | 128-135 | No |
| `isSymbolId/wrapId` | [x] | - | - | 213-220 | 137-142 | No |
| `showName/Plain/etc` | [x] | - | - | 225-242 | 144-160 | No |
| `newName/Qualified/etc` | [x] | - | - | 286-300 | 165-175 | No |
| `nameMapStem` | [x] | - | [x] | 311 | 177 | No |
| `isModuleName/Qualified` | [x] | - | - | 369-373 | 181-185 | No |
| `isSymbolName/isWildcard` | [x] | - | - | 381-392 | 190-197 | No |
| `unqualify/qualify/etc` | [x] | [x] | [x] | 463-517 | 213-252 | No |
| `mergeCommonPath` | [x] | - | - | 533 | 257 | No |
| `toConstructor/VarName` | [x] | - | - | 554-562 | 272-279 | No |
| `prepend/postpend` | [x] | [x] | [x] | 586-599 | 289-302 | No |
| `typeQualifiedName/Of/Get` | [x] | - | - | 612-622 | 334-340 | No |
| `isHiddenName/StartsWith` | [x] | - | - | 411, 669 | 208, 357 | No |
| `toUniqueName` | [x] | - | - | 657 | 351 | No |
| `makeFreshHiddenName` | [ ] | - | - | 665 | - | Yes |
| `to/isHandler/Op/etc` | [x] | - | - | 714-801 | 390-445 | No |
| `toLazyIndirectConName` | [x] | - | - | 808 | 449 | No |
| `readQualifiedName` | [x] | - | - | 317 | 478 | No |
| `missingQualifier` | [x] | - | - | 418 | 513 | No |
| `asciiEncode/moduleNameToPath` | [x] | - | - | 914-945 | 547-607 | No |
| `decodePathToModule/pathToModuleName` | [x] | [x] | - | 918 | 609-618 | No |
| `isImplicitParamName/to/from/split` | [x] | - | - | 850-866 | 628-640 | No |
| `showHex/Binary/HexFloat` | [x] | - | - | 1014-1036 | 543-568 | No |

## Notes
- **Partial**: `makeFreshHiddenName` is missing as it requires `Common.Range`.
- **Partial**: `showBinary` and `showHexFloat` are missing.
- **Porting decision**: `readTupled`/`showTupled` were omitted as they are legacy/deprecated in the current Haskell codebase.
- Significant test coverage in `Koka/Common/Test/Name.lean`.
- Some formal proofs for name property preservation in `Koka/Common/Proof/Name.lean`.
