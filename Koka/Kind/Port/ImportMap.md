# Porting Audit: Kind.ImportMap

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `ImportMap` | [x] | - | - | 30 | 18 | No |
| `importsEmpty` | [x] | - | - | 32-33 | 20 | No |
| `listLookup` | [x] | - | - | - | 22-24 | No |
| `importsExtend` | [x] | - | - | 35-40 | 26-30 | No |
| `importsAlias` | [x] | - | - | 44-50 | 34-40 | No |
| `importsList` | [x] | - | - | 52-54 | 42-43 | No |
| `isPrefixOf` | [x] | - | - | 125-127 | 45-48 | No |
| `importResolvePath` | [x] | - | - | 67-85 | 56-74 | Yes |
| `importsExpand` | [x] | - | - | 62-65 | 76-78 | No |

## Notes
- `isPrefixOf` was implemented natively as Lean 4's out of the box functions did not readily apply to Lists cleanly without additional equality typeclass constraints.
- `importResolvePath` was marked `partial` since Lean's termination checker failed to realize that the `rpath` length shrinks monotonically across the outer matching loops, primarily because it's a structural recursion unproved over nested tuple unpackings.
