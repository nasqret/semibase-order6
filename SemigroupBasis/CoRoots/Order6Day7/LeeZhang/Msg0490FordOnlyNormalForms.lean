import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0490FordOnlySemantics

/-! Computable normal words and their certified opposite, after the actual
unrestricted proof. No quotient choice or bounded premise is used. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordOnly

open SemigroupBasis Order6Sunday

theorem normal_eq_of_derives {left right : Word Nat} (derivation : Derives basis left right) :
    normal left = normal right :=
  normal_eq_of_signature (signature_of_valid5553 ⟨left, right⟩
    (Derives.sound representative_basis5553.1 derivation))

theorem normal_eq_iff_derives (identity : Identity Nat) :
    normal identity.lhs = normal identity.rhs ↔ Derives basis identity.lhs identity.rhs := by
  constructor
  · intro equal
    have first := derives_normal identity.lhs
    rw [equal] at first
    exact first.trans (derives_normal identity.rhs).symm
  · exact normal_eq_of_derives

theorem normal_idempotent (word : Word Nat) : normal (normal word) = normal word :=
  (normal_eq_of_derives (derives_normal word)).symm

theorem normal_eq_iff_valid_of_basis {A : Type} (G : Semigroup A)
    (complete : BasisFor G basis) (identity : Identity Nat) :
    normal identity.lhs = normal identity.rhs ↔ identity.SatisfiedBy G :=
  (normal_eq_iff_derives identity).trans
    ⟨fun derivation => Derives.sound complete.1 derivation, complete.2 identity⟩

def oppositeNormal (word : Word Nat) : Word Nat := (normal word.reverse).reverse

theorem derives_oppositeNormal (word : Word Nat) :
    Derives (reversedBasis basis) word (oppositeNormal word) := by
  simpa [oppositeNormal, Word.reverse_reverse] using (derives_normal word.reverse).reverse

theorem oppositeNormal_eq_iff_derives (identity : Identity Nat) :
    oppositeNormal identity.lhs = oppositeNormal identity.rhs ↔
      Derives (reversedBasis basis) identity.lhs identity.rhs := by
  constructor
  · intro equal
    have first := derives_oppositeNormal identity.lhs
    rw [equal] at first
    exact first.trans (derives_oppositeNormal identity.rhs).symm
  · intro derivation
    have reversed := derivation.reverse
    rw [reversedBasis_reversedBasis] at reversed
    exact congrArg Word.reverse (normal_eq_of_derives reversed)

theorem oppositeNormal_idempotent (word : Word Nat) :
    oppositeNormal (oppositeNormal word) = oppositeNormal word :=
  ((oppositeNormal_eq_iff_derives ⟨word, oppositeNormal word⟩).2 (derives_oppositeNormal word)).symm

theorem oppositeNormal_eq_iff_valid_of_basis {A : Type} (G : Semigroup A)
    (complete : BasisFor G basis) (identity : Identity Nat) :
    oppositeNormal identity.lhs = oppositeNormal identity.rhs ↔ identity.SatisfiedBy G.opposite :=
  (oppositeNormal_eq_iff_derives identity).trans
    ⟨fun derivation => Derives.sound complete.oppositeReversed.1 derivation,
      complete.oppositeReversed.2 identity⟩

abbrev normal5553 := normal
abbrev oppositeNormal5553 := oppositeNormal
abbrev normal9546 := normal
abbrev oppositeNormal9546 := oppositeNormal

theorem normal_eq_iff_valid5553 (identity : Identity Nat) :
    normal5553 identity.lhs = normal5553 identity.rhs ↔
      identity.SatisfiedBy L6FordOnly.Sigma09a2Finite.S6_5553.table.semigroup :=
  normal_eq_iff_valid_of_basis _ representative_basis5553 identity

theorem oppositeNormal_eq_iff_valid5553 (identity : Identity Nat) :
    oppositeNormal5553 identity.lhs = oppositeNormal5553 identity.rhs ↔
      identity.SatisfiedBy L6FordOnly.Sigma09a2Finite.S6_5553.table.semigroup.opposite :=
  oppositeNormal_eq_iff_valid_of_basis _ representative_basis5553 identity

theorem normal_eq_iff_valid9546 (identity : Identity Nat) :
    normal9546 identity.lhs = normal9546 identity.rhs ↔
      identity.SatisfiedBy L6FordOnly.Sigma09a2Finite.S6_9546.table.semigroup :=
  normal_eq_iff_valid_of_basis _ representative_basis9546 identity

theorem oppositeNormal_eq_iff_valid9546 (identity : Identity Nat) :
    oppositeNormal9546 identity.lhs = oppositeNormal9546 identity.rhs ↔
      identity.SatisfiedBy L6FordOnly.Sigma09a2Finite.S6_9546.table.semigroup.opposite :=
  oppositeNormal_eq_iff_valid_of_basis _ representative_basis9546 identity

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordOnly
