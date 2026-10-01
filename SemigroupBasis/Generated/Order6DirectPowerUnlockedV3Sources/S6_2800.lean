import SemigroupBasis.CoRoots.Order6LongSupportThresholdRoots
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2800

open SemigroupBasis

abbrev representativeSemigroup := SemigroupBasis.CoRoots.Order6LongSupportThresholdRoots.S6_2800.table.semigroup

abbrev representativeBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6LongSupportThresholdRoots.basis

theorem representative_basis_complete :
    BasisFor representativeSemigroup representativeBasis :=
  SemigroupBasis.CoRoots.Order6LongSupportThresholdRoots.S6_2800.representative_basis

abbrev currentSemigroup := (SemigroupBasis.CoRoots.Order6LongSupportThresholdRoots.S6_2800.table.semigroup).opposite

abbrev currentBasis : List (Identity Nat) :=
  reversedBasis (SemigroupBasis.CoRoots.Order6LongSupportThresholdRoots.basis)

theorem current_basis_complete :
    BasisFor currentSemigroup currentBasis :=
  SemigroupBasis.CoRoots.Order6LongSupportThresholdRoots.S6_2800.representative_basis.oppositeReversed

abbrev sourceSemigroup := currentSemigroup

abbrev sourceBasis : List (Identity Nat) := currentBasis

theorem basis_complete : BasisFor sourceSemigroup sourceBasis :=
  current_basis_complete

end SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2800
