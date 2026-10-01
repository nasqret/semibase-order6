import SemigroupBasis.CoRoots.Order6HeadSupportCap
import SemigroupBasis.Opposite

namespace SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_5552

open SemigroupBasis

abbrev representativeSemigroup := SemigroupBasis.CoRoots.Order6HeadSupportCap.S6_5552.table.semigroup

abbrev representativeBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6HeadSupportCap.basis

theorem representative_basis_complete :
    BasisFor representativeSemigroup representativeBasis :=
  SemigroupBasis.CoRoots.Order6HeadSupportCap.S6_5552.representative_basis

abbrev currentSemigroup := (SemigroupBasis.CoRoots.Order6HeadSupportCap.S6_5552.table.semigroup).opposite

abbrev currentBasis : List (Identity Nat) :=
  reversedBasis (SemigroupBasis.CoRoots.Order6HeadSupportCap.basis)

theorem current_basis_complete :
    BasisFor currentSemigroup currentBasis :=
  SemigroupBasis.CoRoots.Order6HeadSupportCap.S6_5552.representative_basis.oppositeReversed

abbrev sourceSemigroup := currentSemigroup

abbrev sourceBasis : List (Identity Nat) := currentBasis

theorem basis_complete : BasisFor sourceSemigroup sourceBasis :=
  current_basis_complete

end SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_5552
