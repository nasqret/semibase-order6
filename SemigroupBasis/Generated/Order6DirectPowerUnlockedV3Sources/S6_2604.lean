import SemigroupBasis.Generated.Order6FactorPairS3_4S4_20.S6_2604
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2604

open SemigroupBasis

abbrev representativeSemigroup := SemigroupBasis.Generated.Order6FactorPairS3_4S4_20.S6_2604.table.semigroup

abbrev representativeBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_4S4_20.basis

theorem representative_basis_complete :
    BasisFor representativeSemigroup representativeBasis :=
  SemigroupBasis.Generated.Order6FactorPairS3_4S4_20.S6_2604.representative_basis

abbrev currentSemigroup := SemigroupBasis.Generated.Order6FactorPairS3_4S4_20.S6_2604.table.semigroup

abbrev currentBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_4S4_20.basis

theorem current_basis_complete :
    BasisFor currentSemigroup currentBasis :=
  SemigroupBasis.Generated.Order6FactorPairS3_4S4_20.S6_2604.representative_basis

abbrev sourceSemigroup := currentSemigroup

abbrev sourceBasis : List (Identity Nat) := currentBasis

theorem basis_complete : BasisFor sourceSemigroup sourceBasis :=
  current_basis_complete

end SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2604
