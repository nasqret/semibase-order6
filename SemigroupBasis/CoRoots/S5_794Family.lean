import SemigroupBasis.CoRoots.S5_794Completeness
import SemigroupBasis.Generated.S5_794Transfers

namespace SemigroupBasis.CoRoots.S5_794Family

open SemigroupBasis

namespace S5_802

theorem models :
    Models Generated.Catalogue.S5_802.table.semigroup
      SemigroupBasis.CoRoots.S5_794.basis :=
  SemigroupBasis.CoRoots.S5_794.catalogueS5_802Models

theorem oppositeModels :
    Models Generated.Catalogue.S5_802.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_794.oppositeBasis :=
  models.oppositeReversed

theorem basisFor_of_publishedCompleteness
    (completeness :
      SemigroupBasis.CoRoots.S5_794.M14CompletenessObligation) :
    BasisFor Generated.Catalogue.S5_802.table.semigroup
      SemigroupBasis.CoRoots.S5_794.basis :=
  SemigroupBasis.CoRoots.S5_794.catalogueS5_802BasisFor_of_publishedCompleteness
    completeness

theorem oppositeBasisFor_of_publishedCompleteness
    (completeness :
      SemigroupBasis.CoRoots.S5_794.M14CompletenessObligation) :
    BasisFor Generated.Catalogue.S5_802.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_794.oppositeBasis :=
  (basisFor_of_publishedCompleteness completeness).oppositeReversed

theorem basisFor :
    BasisFor Generated.Catalogue.S5_802.table.semigroup
      SemigroupBasis.CoRoots.S5_794.basis :=
  SemigroupBasis.CoRoots.S5_794.catalogueS5_802BasisFor

theorem oppositeBasisFor :
    BasisFor Generated.Catalogue.S5_802.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_794.oppositeBasis :=
  basisFor.oppositeReversed

end S5_802

namespace S5_794

theorem models :
    Models Generated.Catalogue.S5_794.table.semigroup
      SemigroupBasis.CoRoots.S5_794.basis :=
  SemigroupBasis.Generated.S5_794Transfers.S5_794.targetModels

theorem oppositeModels :
    Models Generated.Catalogue.S5_794.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_794.oppositeBasis :=
  models.oppositeReversed

theorem basisFor_of_publishedCompleteness
    (completeness :
      SemigroupBasis.CoRoots.S5_794.M14CompletenessObligation) :
    BasisFor Generated.Catalogue.S5_794.table.semigroup
      SemigroupBasis.CoRoots.S5_794.basis :=
  SemigroupBasis.Generated.S5_794Transfers.S5_794.representativeBasisFor_of_root
    (S5_802.basisFor_of_publishedCompleteness completeness)

theorem oppositeBasisFor_of_publishedCompleteness
    (completeness :
      SemigroupBasis.CoRoots.S5_794.M14CompletenessObligation) :
    BasisFor Generated.Catalogue.S5_794.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_794.oppositeBasis :=
  (basisFor_of_publishedCompleteness completeness).oppositeReversed

theorem basisFor :
    BasisFor Generated.Catalogue.S5_794.table.semigroup
      SemigroupBasis.CoRoots.S5_794.basis :=
  SemigroupBasis.Generated.S5_794Transfers.S5_794.representativeBasisFor_of_root
    S5_802.basisFor

theorem oppositeBasisFor :
    BasisFor Generated.Catalogue.S5_794.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_794.oppositeBasis :=
  basisFor.oppositeReversed

end S5_794

namespace S5_810

theorem models :
    Models Generated.Catalogue.S5_810.table.semigroup
      SemigroupBasis.CoRoots.S5_794.basis :=
  SemigroupBasis.Generated.S5_794Transfers.S5_810.targetModels

theorem oppositeModels :
    Models Generated.Catalogue.S5_810.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_794.oppositeBasis :=
  models.oppositeReversed

theorem basisFor_of_publishedCompleteness
    (completeness :
      SemigroupBasis.CoRoots.S5_794.M14CompletenessObligation) :
    BasisFor Generated.Catalogue.S5_810.table.semigroup
      SemigroupBasis.CoRoots.S5_794.basis :=
  SemigroupBasis.Generated.S5_794Transfers.S5_810.representativeBasisFor_of_root
    (S5_802.basisFor_of_publishedCompleteness completeness)

theorem oppositeBasisFor_of_publishedCompleteness
    (completeness :
      SemigroupBasis.CoRoots.S5_794.M14CompletenessObligation) :
    BasisFor Generated.Catalogue.S5_810.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_794.oppositeBasis :=
  (basisFor_of_publishedCompleteness completeness).oppositeReversed

theorem basisFor :
    BasisFor Generated.Catalogue.S5_810.table.semigroup
      SemigroupBasis.CoRoots.S5_794.basis :=
  SemigroupBasis.Generated.S5_794Transfers.S5_810.representativeBasisFor_of_root
    S5_802.basisFor

theorem oppositeBasisFor :
    BasisFor Generated.Catalogue.S5_810.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_794.oppositeBasis :=
  basisFor.oppositeReversed

end S5_810

/-- All six requested endpoints follow from exactly the published M14
completeness proposition; the finite transfer work introduces no additional
mathematical premise. -/
structure FamilyBasisEndpoints : Prop where
  s5_794 :
    BasisFor Generated.Catalogue.S5_794.table.semigroup
      SemigroupBasis.CoRoots.S5_794.basis
  s5_794_opposite :
    BasisFor Generated.Catalogue.S5_794.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_794.oppositeBasis
  s5_802 :
    BasisFor Generated.Catalogue.S5_802.table.semigroup
      SemigroupBasis.CoRoots.S5_794.basis
  s5_802_opposite :
    BasisFor Generated.Catalogue.S5_802.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_794.oppositeBasis
  s5_810 :
    BasisFor Generated.Catalogue.S5_810.table.semigroup
      SemigroupBasis.CoRoots.S5_794.basis
  s5_810_opposite :
    BasisFor Generated.Catalogue.S5_810.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_794.oppositeBasis

theorem endpoints_of_publishedCompleteness
    (completeness :
      SemigroupBasis.CoRoots.S5_794.M14CompletenessObligation) :
    FamilyBasisEndpoints where
  s5_794 := S5_794.basisFor_of_publishedCompleteness completeness
  s5_794_opposite :=
    S5_794.oppositeBasisFor_of_publishedCompleteness completeness
  s5_802 := S5_802.basisFor_of_publishedCompleteness completeness
  s5_802_opposite :=
    S5_802.oppositeBasisFor_of_publishedCompleteness completeness
  s5_810 := S5_810.basisFor_of_publishedCompleteness completeness
  s5_810_opposite :=
    S5_810.oppositeBasisFor_of_publishedCompleteness completeness

/-- Unconditional basis endpoints for all three representatives and their
opposites. -/
theorem endpoints : FamilyBasisEndpoints where
  s5_794 := S5_794.basisFor
  s5_794_opposite := S5_794.oppositeBasisFor
  s5_802 := S5_802.basisFor
  s5_802_opposite := S5_802.oppositeBasisFor
  s5_810 := S5_810.basisFor
  s5_810_opposite := S5_810.oppositeBasisFor

end SemigroupBasis.CoRoots.S5_794Family
