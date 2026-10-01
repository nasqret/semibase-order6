import SemigroupBasis.Generated.Order6FactorIntersection.Head3Tail2.S6_5640
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_5640

open SemigroupBasis

abbrev representativeSemigroup := SemigroupBasis.Generated.Order6FactorIntersection.Head3Tail2.S6_5640.table.semigroup

abbrev representativeBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6Head3Tail2.basis

theorem representative_basis_complete :
    BasisFor representativeSemigroup representativeBasis :=
  SemigroupBasis.Generated.Order6FactorIntersection.Head3Tail2.S6_5640.representative_basis

abbrev currentSemigroup := (SemigroupBasis.Generated.Order6FactorIntersection.Head3Tail2.S6_5640.table.semigroup).opposite

abbrev currentBasis : List (Identity Nat) :=
  reversedBasis (SemigroupBasis.CoRoots.Order6Head3Tail2.basis)

theorem current_basis_complete :
    BasisFor currentSemigroup currentBasis :=
  SemigroupBasis.Generated.Order6FactorIntersection.Head3Tail2.S6_5640.representative_basis.oppositeReversed

abbrev sourceSemigroup := currentSemigroup

abbrev sourceBasis : List (Identity Nat) := currentBasis

theorem basis_complete : BasisFor sourceSemigroup sourceBasis :=
  current_basis_complete

end SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_5640
