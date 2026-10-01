import SemigroupBasis.Generated.S5_831Transfers

namespace SemigroupBasis.CoRoots.S5_831Family

open SemigroupBasis

namespace S5_831

theorem models :
    Models Generated.Catalogue.S5_831.table.semigroup
      SemigroupBasis.CoRoots.S5_831.basis :=
  SemigroupBasis.CoRoots.S5_831.models

theorem oppositeModels :
    Models Generated.Catalogue.S5_831.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_831.expectedOppositeBasis :=
  SemigroupBasis.CoRoots.S5_831.opposite_basis_complete.1

theorem basisFor :
    BasisFor Generated.Catalogue.S5_831.table.semigroup
      SemigroupBasis.CoRoots.S5_831.basis :=
  SemigroupBasis.CoRoots.S5_831.basis_complete

theorem oppositeBasisFor :
    BasisFor Generated.Catalogue.S5_831.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_831.expectedOppositeBasis :=
  SemigroupBasis.CoRoots.S5_831.opposite_basis_complete

end S5_831

namespace S5_832

theorem models :
    Models Generated.Catalogue.S5_832.table.semigroup
      SemigroupBasis.CoRoots.S5_831.basis :=
  SemigroupBasis.Generated.S5_831Transfers.S5_832.targetModels

theorem oppositeModels :
    Models Generated.Catalogue.S5_832.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_831.expectedOppositeBasis :=
  SemigroupBasis.Generated.S5_831Transfers.S5_832.oppositeBasisFor.1

theorem basisFor :
    BasisFor Generated.Catalogue.S5_832.table.semigroup
      SemigroupBasis.CoRoots.S5_831.basis :=
  SemigroupBasis.Generated.S5_831Transfers.S5_832.representativeBasisFor

theorem oppositeBasisFor :
    BasisFor Generated.Catalogue.S5_832.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_831.expectedOppositeBasis :=
  SemigroupBasis.Generated.S5_831Transfers.S5_832.oppositeBasisFor

end S5_832

/-- Aggregate proposition used as the single WMI axiom-audit target. -/
structure FamilyBasisEndpoints : Prop where
  s5_831 :
    BasisFor Generated.Catalogue.S5_831.table.semigroup
      SemigroupBasis.CoRoots.S5_831.basis
  s5_831_opposite :
    BasisFor Generated.Catalogue.S5_831.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_831.expectedOppositeBasis
  s5_832 :
    BasisFor Generated.Catalogue.S5_832.table.semigroup
      SemigroupBasis.CoRoots.S5_831.basis
  s5_832_opposite :
    BasisFor Generated.Catalogue.S5_832.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_831.expectedOppositeBasis

theorem allEndpoints : FamilyBasisEndpoints where
  s5_831 := S5_831.basisFor
  s5_831_opposite := S5_831.oppositeBasisFor
  s5_832 := S5_832.basisFor
  s5_832_opposite := S5_832.oppositeBasisFor

end SemigroupBasis.CoRoots.S5_831Family
