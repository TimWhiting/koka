import Koka.Common.Name

open Koka.Common.Name

namespace Koka.Common.Proof.Name

-- Proof that unqualify is idempotent
theorem unqualify_idempotent (n : Name) : unqualify (unqualify n) = unqualify n := by
  -- unqualify n = newQualified "" n.stem
  -- unqualify (newQualified "" n.stem) = newQualified "" (newQualified "" n.stem).stem
  -- Since newQualified sets the stem to the second argument, this should be trivial via rfl
  rfl

-- Proof that unqualifyFull is idempotent
theorem unqualifyFull_idempotent (n : Name) : unqualifyFull (unqualifyFull n) = unqualifyFull n := by
  rfl

-- Helper lemmas about character classes
theorem isIdStartChar_imp_isIdEndChar {c : Char} : isIdStartChar c → isIdEndChar c := by
  intro h
  simp [isIdEndChar]
  simp [isIdStartChar] at h
  match h with
  | .inl (.inl h1) => left; simp [isIdChar]; left; left; left; unfold Char.isAlphanum; grind
  | .inl (.inr h2) => left; simp [isIdChar]; left; left; right; assumption
  | .inr h3 => left; simp [isIdChar]; left; right; assumption

theorem isIdChar_imp_isIdEndChar {c : Char} : isIdChar c → isIdEndChar c := by
  intro h
  simp [isIdEndChar]
  left; exact h

/--
  `postpend` is designed to preserve the category of a name (symbol vs identifier).
  If it starts as a symbol (operator), it stays a symbol.
  If it starts as an identifier, it stays an identifier.
--/
theorem postpend_preserves_isSymbolName (n : Name) (post : String) :
  isSymbolName (postpend post n) = isSymbolName n := by
  simp [postpend]
  split
  case isTrue h =>
    -- If it's a symbol, it stays a symbol because it ends with rsyms (non-id-chars)
    simp [isSymbolName, nameMapStem]
    sorry
  case isFalse h =>
    -- If it's an identifier, it stays an identifier because it ends with post or ys (id-chars)
    simp [isSymbolName, nameMapStem]
    sorry

end Koka.Common.Proof.Name
