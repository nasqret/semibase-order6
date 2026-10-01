import SemigroupBasis.CoRoots.Order6SporadicSection16CanonicalUniqueness
import SemigroupBasis.CoRoots.Order6SporadicSection16Models
import SemigroupBasis.Opposite

/-! Unconditional finite-basis theorems for all six tables of Lee-Zhang
Section16. The proof handles simple words explicitly and otherwise uses the
proved canonical derivations, invariant necessity and canonical uniqueness.
The opposite endpoints are the standard reversed-identity transport. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection16

open SemigroupBasis

theorem derives_of_valid {S : Type u} (G : Semigroup S) (models : Models G basis)
    (necessity : ∀ identity : Identity Nat, identity.SatisfiedBy G →
      Lemma16_2Invariants identity.lhs identity.rhs)
    (identity : Identity Nat) (valid : identity.SatisfiedBy G) :
    Derives basis identity.lhs identity.rhs := by
  have same := necessity identity valid
  by_cases leftSimple : identity.lhs.toList.Nodup
  · have trivial := simple_left_identity_trivial identity same.toFactorInvariants leftSimple
    rw [trivial]
    exact Derives.refl _
  · by_cases rightSimple : identity.rhs.toList.Nodup
    · have trivial := simple_left_identity_trivial ⟨identity.rhs,identity.lhs⟩
        (lemma16_2Invariants_symm same).toFactorInvariants rightSimple
      change identity.rhs = identity.lhs at trivial
      rw [trivial]
      exact Derives.refl _
    · obtain ⟨left,leftWF,leftDerives⟩ := existsCanonicalWord identity.lhs leftSimple
      obtain ⟨right,rightWF,rightDerives⟩ := existsCanonicalWord identity.rhs rightSimple
      have canonicalValid := canonicalized_identity_valid G models identity valid left right
        leftDerives rightDerives
      have canonicalSame := necessity ⟨canonicalWord left,canonicalWord right⟩ canonicalValid
      have equal := canonicalWord_unique left right leftWF rightWF canonicalSame
      rw [equal] at leftDerives
      exact leftDerives.trans rightDerives.symm

theorem basisFor_of_lemma16_2 {S : Type u} (G : Semigroup S) (models : Models G basis)
    (necessity : ∀ identity : Identity Nat, identity.SatisfiedBy G →
      Lemma16_2Invariants identity.lhs identity.rhs) : BasisFor G basis :=
  ⟨models, derives_of_valid G models necessity⟩

namespace S6_3813
theorem representative_basis : BasisFor table.semigroup basis :=
  basisFor_of_lemma16_2 table.semigroup models_basis lemma16_2
theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed
end S6_3813

namespace S6_3815
theorem representative_basis : BasisFor table.semigroup basis :=
  basisFor_of_lemma16_2 table.semigroup models_basis lemma16_2
theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed
end S6_3815

namespace S6_3826
theorem representative_basis : BasisFor table.semigroup basis :=
  basisFor_of_lemma16_2 table.semigroup models_basis lemma16_2
theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed
end S6_3826

namespace S6_3828
theorem representative_basis : BasisFor table.semigroup basis :=
  basisFor_of_lemma16_2 table.semigroup models_basis lemma16_2
theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed
end S6_3828

namespace S6_6437
theorem representative_basis : BasisFor table.semigroup basis :=
  basisFor_of_lemma16_2 table.semigroup models_basis lemma16_2
theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed
end S6_6437

namespace S6_6444
theorem representative_basis : BasisFor table.semigroup basis :=
  basisFor_of_lemma16_2 table.semigroup models_basis lemma16_2
theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed
end S6_6444


end SemigroupBasis.CoRoots.Order6SporadicSection16
