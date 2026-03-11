# Porting Audit: File

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `FileName` | [x] | - | - | 134 | 21 | No |
| `startsWith/endsWith` | [x] | - | - | 105 | 9-12 | No |
| `splitOn/trim` | [x] | - | - | 113-122 | 15-18 | No |
| `isPathSep/Delimiter` | [x] | - | - | 259-264 | 23-26 | No |
| `normalize/With` | [x] | - | - | 237-245 | 29-40 | No |
| `splitPath` | [x] | - | - | 196 | 46 | No |
| `joinPaths/Path` | [x] | - | - | 211-215 | 54-73 | No |
| `dirname/notdir` | [x] | - | - | 156-162 | 75-79 | No |
| `extname/basename` | [x] | - | - | 137-145 | 81-87 | No |
| `notext/noexts` | [x] | - | - | 167-171 | 94-98 | No |
| `ensureExt` | [x] | - | - | 152 | 101 | No |
| `isAbsolute` | [x] | - | - | 468 | 104 | No |
| `commonPathPrefix` | [x] | - | - | 446 | 110 | No |
| `getCwd` | [x] | - | [x] | 268 | 115 | No |
| `runSystem/Raw/Cmd` | [x] | - | - | 276-294 | 119-127 | No |
| `runCmdRead/Env` | [x] | - | - | 301-315 | 129-140 | No |
| `getFileTime` | [x] | - | [x] | 333 (impl) | 142 | No |
| `fileTimeCompare` | [x] | - | - | 333 | 146 | No |
| `maxFileTime/s` | [x] | - | - | 340-344 | 155-158 | No |
| `doesFileExistAndNotEmpty` | [x] | - | - | 348 | 161 | No |
| `read/writeTextFile` | [x] | - | - | 362-369 | 168-175 | No |
| `copyTextFile/With` | [x] | - | - | 373-383 | 178-185 | No |
| `copyBinaryFile` | [x] | - | - | 394 | 192 | No |
| `copyBinaryIfNewer` | [x] | - | - | 410 | 199 | No |
| `copyTextIfNewer/With` | [x] | - | - | 420-429 | 209-219 | No |
| `removeFileIfExists` | [x] | - | - | 438 | 229 | No |
| `getProgramPath` | [x] | - | [x] | 443 | 232 | No |
| `getEnvVar/Paths` | [x] | - | [x] | 583-590 | 236-243 | No |
| `realPath` | [x] | - | - | 597 | 245 | No |
| `findMaximalPrefixPath` | [x] | - | [x] | 477 | 251 | No |
| `getMaximalPrefixPath` | [x] | - | - | 487 | 259 | No |
| `makeRelativeToPaths` | [x] | - | - | 575 | 264 | No |
| `searchPaths/Ex/Canonical` | [ ] | - | - | 517-552 | - | Yes |
| `searchProgram` | [ ] | - | - | 605 | - | Yes |
| `isLiteralDoc` | [ ] | - | - | 125 | - | Yes |
| `undelimPaths` | [~] | - | - | 176 | 242 (inline) | Yes |

## Notes
- **Partial**: Search-related functionality (`searchPaths`, `searchProgram`) is missing and needs implementation.
- **Partial**: Windows-specific drive letter handling in `undelimPaths` is simplified in the current port.
- Core IO and path manipulation functions are tested in `Koka/Common/Test/File.lean`.
- Parity is high for essential operations, but incomplete for compiler search logic.
