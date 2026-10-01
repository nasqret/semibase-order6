import SemigroupBasis.CoRoots.S5_863Completeness
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_863Family

open SemigroupBasis

namespace S5_863

theorem models :
    Models Generated.Catalogue.S5_863.table.semigroup
      SemigroupBasis.CoRoots.S5_863.basis :=
  SemigroupBasis.CoRoots.S5_863.catalogueModels

/-- Direct completeness endpoint for the singleton `S5_863` family. -/
theorem basisFor :
    BasisFor Generated.Catalogue.S5_863.table.semigroup
      SemigroupBasis.CoRoots.S5_863.basis :=
  SemigroupBasis.CoRoots.S5_863.basis_complete_of_signature
    Generated.Catalogue.S5_863.table.semigroup models
    SemigroupBasis.CoRoots.S5_863.valid_sameSignature

/-- Completeness endpoint for the opposite table and reversed basis. -/
theorem oppositeBasisFor :
    BasisFor Generated.Catalogue.S5_863.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_863.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_863.oppositeBasis] using
    basisFor.oppositeReversed

end S5_863

/-- Aggregate proposition used as the singleton family audit surface. -/
structure FamilyBasisEndpoints : Prop where
  direct :
    BasisFor Generated.Catalogue.S5_863.table.semigroup
      SemigroupBasis.CoRoots.S5_863.basis
  opposite :
    BasisFor Generated.Catalogue.S5_863.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_863.oppositeBasis

theorem endpoints : FamilyBasisEndpoints where
  direct := S5_863.basisFor
  opposite := S5_863.oppositeBasisFor

end SemigroupBasis.CoRoots.S5_863Family
