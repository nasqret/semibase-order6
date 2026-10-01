import SemigroupBasis.Generated.Order6FactorIntersection.FirstSequenceShortLong.S6_3367
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_3367

open SemigroupBasis

abbrev representativeSemigroup := SemigroupBasis.Generated.Order6FactorIntersection.FirstSequenceShortLong.S6_3367.table.semigroup

abbrev representativeBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionFirstSequenceShortLong.basis

theorem representative_basis_complete :
    BasisFor representativeSemigroup representativeBasis :=
  SemigroupBasis.Generated.Order6FactorIntersection.FirstSequenceShortLong.S6_3367.representative_basis

abbrev currentSemigroup := (SemigroupBasis.Generated.Order6FactorIntersection.FirstSequenceShortLong.S6_3367.table.semigroup).opposite

abbrev currentBasis : List (Identity Nat) :=
  reversedBasis (SemigroupBasis.CoRoots.Order6FactorIntersectionFirstSequenceShortLong.basis)

theorem current_basis_complete :
    BasisFor currentSemigroup currentBasis :=
  SemigroupBasis.Generated.Order6FactorIntersection.FirstSequenceShortLong.S6_3367.representative_basis.oppositeReversed

abbrev sourceSemigroup := currentSemigroup

abbrev sourceBasis : List (Identity Nat) := currentBasis

theorem basis_complete : BasisFor sourceSemigroup sourceBasis :=
  current_basis_complete

end SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_3367
