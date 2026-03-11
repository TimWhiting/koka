# Porting Audit: Platform.Filetime

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `FileTime` | [x] | - | - | 30 | 12 | No |
| `getCurrentTime` | [x] | - | - | 32-34 | 21-24 | No |
| `fileTime0` | [x] | - | - | 36-38 | 26-27 | No |
| `showTimeDiff` | [x] | - | - | 40-42 | 29-32 | No |
| `fileTimeToPicoseconds` | [x] | - | - | 44-50 | 34-35 | No |
| `getFileTime` | [x] | - | - | 73-77 | 38-43 | No |
| `setFileTime` | [x] | - | - | 80-82 | 47-48 | No |
| `getFileTimeOrCurrent` | [x] | - | - | 85-88 | 51-56 | No |

## Notes
- `FileTime` accurately maps to Lean's native `IO.FS.SystemTime`.
- `getCurrentTime` utilizes `IO.monoMsNow` converting explicitly to `Int` seconds.
- `setFileTime` is currently a stub because `IO.FS.setModificationTime` does not exist natively in standard Lean 4 without C FFI. Usually Koka uses this for cache backdating. It is kept as `pure ()` for now.
