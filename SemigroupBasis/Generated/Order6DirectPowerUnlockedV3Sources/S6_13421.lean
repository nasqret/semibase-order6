import SemigroupBasis.Generated.Order6FactorPairS4_116opS5_841.S6_13421
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_13421

open SemigroupBasis

abbrev representativeSemigroup := SemigroupBasis.Generated.Order6FactorPairS4_116opS5_841.S6_13421.table.semigroup

abbrev representativeBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS4_116opS5_841.basis

theorem representative_basis_complete :
    BasisFor representativeSemigroup representativeBasis :=
  SemigroupBasis.Generated.Order6FactorPairS4_116opS5_841.S6_13421.representative_basis

abbrev currentSemigroup := SemigroupBasis.Generated.Order6FactorPairS4_116opS5_841.S6_13421.table.semigroup

abbrev currentBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS4_116opS5_841.basis

theorem current_basis_complete :
    BasisFor currentSemigroup currentBasis :=
  SemigroupBasis.Generated.Order6FactorPairS4_116opS5_841.S6_13421.representative_basis

abbrev sourceSemigroup := currentSemigroup

abbrev sourceBasis : List (Identity Nat) := currentBasis

theorem basis_complete : BasisFor sourceSemigroup sourceBasis :=
  current_basis_complete

end SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_13421
