import SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_5325

open SemigroupBasis

abbrev representativeSemigroup := SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.S6_5325.table.semigroup

abbrev representativeBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.PrefixResidueFour.basis

theorem representative_basis_complete :
    BasisFor representativeSemigroup representativeBasis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.S6_5325.representative_basis

abbrev currentSemigroup := (SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.S6_5325.table.semigroup).opposite

abbrev currentBasis : List (Identity Nat) :=
  reversedBasis (SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.PrefixResidueFour.basis)

theorem current_basis_complete :
    BasisFor currentSemigroup currentBasis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.S6_5325.representative_basis.oppositeReversed

abbrev sourceSemigroup := currentSemigroup

abbrev sourceBasis : List (Identity Nat) := currentBasis

theorem basis_complete : BasisFor sourceSemigroup sourceBasis :=
  current_basis_complete

end SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_5325
