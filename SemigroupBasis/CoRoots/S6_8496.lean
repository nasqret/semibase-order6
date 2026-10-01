import SemigroupBasis.CoRoots.S6_8496PublishedSemantics

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6PublishedMonoid14.S6_8496

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6PublishedMonoid14

private abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

/-- The global lower-order invariants align simple separators, and the target
probe oracle aligns every intervening ordered square bank. -/
theorem valid_canonicalDecomposition_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    {leftSegments rightSegments : List (List Nat × Nat)}
    {leftFinal rightFinal : List Nat}
    (leftDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        identity.lhs.toList identity.lhs.toList
          leftSegments leftFinal)
    (rightDecomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        identity.rhs.toList identity.rhs.toList
          rightSegments rightFinal) :
    renderCanonicalDecomposition leftSegments leftFinal =
      renderCanonicalDecomposition rightSegments rightFinal := by
  have separatorEq :=
    separatorSequence_eq_of_capped_firstOccurrences
      (left := identity.lhs) (right := identity.rhs)
      leftDecomposition rightDecomposition
      (valid_cappedMultiplicity_eq identity valid)
      (valid_firstOccurrenceSequence_eq identity valid)
  have agreement :=
    canonicalDecompositionAgreement_of_oracle
      identity.lhs identity.rhs
      (valid_canonicalGapOracle identity valid)
      leftDecomposition rightDecomposition separatorEq
  exact renderCanonicalDecomposition_eq_of_agreement agreement

/-- Every identity valid in the exact six-element monoid-I table follows from
the four displayed Lee--Li identities. -/
theorem derives_of_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  obtain ⟨leftSegments, leftFinal, leftDecomposition⟩ :=
    S5_254.existsGloballySimpleSeparatorDecomposition
      identity.lhs.toList
  obtain ⟨rightSegments, rightFinal, rightDecomposition⟩ :=
    S5_254.existsGloballySimpleSeparatorDecomposition
      identity.rhs.toList
  have leftNormal :=
    listDerivesCanonicalDecomposition
      identity.lhs.toList leftDecomposition
  have rightNormal :=
    listDerivesCanonicalDecomposition
      identity.rhs.toList rightDecomposition
  have canonicalEq :=
    valid_canonicalDecomposition_eq identity valid
      leftDecomposition rightDecomposition
  have middle :
      ListDerives
        (renderCanonicalDecomposition leftSegments leftFinal)
        (renderCanonicalDecomposition rightSegments rightFinal) := by
    rw [canonicalEq]
    exact S5_107.ListDerives.refl _
  have combined :
      ListDerives identity.lhs.toList identity.rhs.toList :=
    leftNormal.trans (middle.trans rightNormal.symm)
  cases identity with
  | mk left right =>
      cases left with
      | mk leftHead leftTail =>
          cases right with
          | mk rightHead rightTail =>
              exact S5_107.ListDerives.toWord combined

/-- Unrestricted identity basis theorem for catalogue class `S6_8496`. -/
theorem basis_complete : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derives_of_valid identity valid

/-- The reversed four-law system is complete for the anti-isomorphic class. -/
theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using basis_complete.oppositeReversed

end SemigroupBasis.CoRoots.Order6PublishedMonoid14.S6_8496
