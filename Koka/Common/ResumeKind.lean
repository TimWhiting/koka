/-
  Ported from Haskell Koka:
  File:   src/Common/ResumeKind.hs
  Commit: ce386575abc463be5a8fd6a3821ee050aeea6d19
  Date:   2026-03-06T10:50:08-07:00
-/
namespace Koka.Common.ResumeKind

inductive ResumeKind
  | ResumeNever
  | ResumeTail
  | ResumeScopedOnce
  | ResumeScoped
  | ResumeOnce
  | ResumeNormal
  | ResumeOnceRaw
  | ResumeNormalRaw
  deriving Repr, BEq, Inhabited

local instance : Ord ResumeKind where
  compare
    | .ResumeNever, .ResumeNever => Ordering.eq
    | .ResumeNever, _ => Ordering.lt
    | _, .ResumeNever => Ordering.gt
    | .ResumeTail, .ResumeTail => Ordering.eq
    | .ResumeTail, _ => Ordering.lt
    | _, .ResumeTail => Ordering.gt
    | .ResumeScopedOnce, .ResumeScopedOnce => Ordering.eq
    | .ResumeScopedOnce, _ => Ordering.lt
    | _, .ResumeScopedOnce => Ordering.gt
    | .ResumeScoped, .ResumeScoped => Ordering.eq
    | .ResumeScoped, _ => Ordering.lt
    | _, .ResumeScoped => Ordering.gt
    | .ResumeOnce, .ResumeOnce => Ordering.eq
    | .ResumeOnce, _ => Ordering.lt
    | _, .ResumeOnce => Ordering.gt
    | .ResumeNormal, .ResumeNormal => Ordering.eq
    | .ResumeNormal, _ => Ordering.lt
    | _, .ResumeNormal => Ordering.gt
    | .ResumeOnceRaw, .ResumeOnceRaw => Ordering.eq
    | .ResumeOnceRaw, _ => Ordering.lt
    | _, .ResumeOnceRaw => Ordering.gt
    | .ResumeNormalRaw, .ResumeNormalRaw => Ordering.eq

instance : ToString ResumeKind where
  toString
    | .ResumeNever => "never"
    | .ResumeTail  => "tail"
    | .ResumeScopedOnce => "scoped once"
    | .ResumeScoped => "scoped"
    | .ResumeOnce  => "once"
    | .ResumeNormal => "normal"
    | .ResumeOnceRaw => "once (no finalization)"
    | .ResumeNormalRaw => "normal (no finalization)"

end Koka.Common.ResumeKind
