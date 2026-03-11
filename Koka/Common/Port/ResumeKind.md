# Porting Audit: Common.ResumeKind

| Function / Type | Ported | Proofs | Tests | HS Line | Lean Line | Partial |
| :--- | :---: | :---: | :---: | :---: | :---: | :---: |
| `ResumeKind` | [x] | - | - | 14-23 | 9-18 | No |

## Notes
- Trivial enumeration translation. Implements `Repr`, `BEq`, `Inhabited`, `Ord`, and `ToString` directly mirroring Haskell derived implementations.
