# Porting Audit: Compile.Package

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `PackageName` | [x] | - | - | 40 | 25 | No |
| `Package` | [x] | - | - | 44-47 | 27-32 | No |
| `Packages` | [x] | - | - | 41-42 | 34-37 | No |
| `packagesEmpty` | [x] | - | - | 49-50 | 39-40 | No |
| `pkgName` | [x] | - | - | 52-53 | 42-45 | No |
| `node_modules` | [x] | - | - | 185-186 | 51 | No |
| `node_path` | [x] | - | - | 182-183 | 52 | No |
| `package_json` | [x] | - | - | 188-189 | 53 | No |
| `packageBase` | [x] | - | - | 112-117 | 58-63 | No |
| `visiblePackages` | [x] | - | - | 99-110 | 65-76 | Yes |
| `packageFromDir` | [x] | - | - | 74-79 | 78-82 | No |
| `packageInfoFromDir` | [x] | - | - | 68-72 | 84-87 | No |
| `searchPackages` | [x] | - | - | 82-96 | 89-106 | Yes |
| `joinPkgs` | [x] | - | - | 173-177 | 111-114 | No |
| `joinPkg` | [x] | - | - | 170-171 | 116-117 | No |
| `readSubPackages` | [x] | - | - | 143-168 | 119-149 | Yes |
| `getHomeDirectory` | [x] | - | - | 132 | 158-163 | No |
| `discoverPackages` | [x] | - | - | 123-141 | 151-179 | Yes |
| `ppPackages` | [x] | - | - | 207-210 | 182-188 | Yes |
| `Show Package` | [x] | - | - | 195-205 | 193-195 | No |

## Notes
- Wrote safe `isFileSafe` and `isDirSafe` wrappers for `System.FilePath.pathExists` to replace `IO.FS.metadata` lookups because `IO.FS.Metadata` does not easily expose type tagging in Lean 4 currently.
- Marked filesystem walking and search lookups as `partial` as they depend on unbounded IO or unbounded recursive structures (e.g., `Package` subpackages). 
- Translated Parsec JSON accessors to use `Koka.Lib.JSON` wrapper correctly inside `readPackage`.
