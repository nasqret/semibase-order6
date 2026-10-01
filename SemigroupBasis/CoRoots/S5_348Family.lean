import SemigroupBasis.CoRoots.S5_348Completeness
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_348Family

open SemigroupBasis

namespace S5_348

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_348.table.semigroup
      SemigroupBasis.CoRoots.S5_348.basis :=
  SemigroupBasis.CoRoots.S5_348.models_of_finite_checks
    Generated.Catalogue.S5_348.table (by decide)

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_348.table.semigroup
      SemigroupBasis.CoRoots.S5_348.basis :=
  SemigroupBasis.CoRoots.S5_348.basis_complete_of_signature
    Generated.Catalogue.S5_348.table.semigroup models
    S5_348FamilyInvariant.S5_348.valid_sameSignature

theorem representative_basis :
    BasisFor Generated.Catalogue.S5_348.table.semigroup
      SemigroupBasis.CoRoots.S5_348.basis :=
  basis_complete

theorem opposite_basis :
    BasisFor Generated.Catalogue.S5_348.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_348.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_348.oppositeBasis] using
    basis_complete.oppositeReversed

end S5_348

namespace S5_354

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_354.table.semigroup
      SemigroupBasis.CoRoots.S5_348.basis :=
  SemigroupBasis.CoRoots.S5_348.models_of_finite_checks
    Generated.Catalogue.S5_354.table (by decide)

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_354.table.semigroup
      SemigroupBasis.CoRoots.S5_348.basis :=
  SemigroupBasis.CoRoots.S5_348.basis_complete_of_signature
    Generated.Catalogue.S5_354.table.semigroup models
    S5_348FamilyInvariant.S5_354.valid_sameSignature

theorem representative_basis :
    BasisFor Generated.Catalogue.S5_354.table.semigroup
      SemigroupBasis.CoRoots.S5_348.basis :=
  basis_complete

theorem opposite_basis :
    BasisFor Generated.Catalogue.S5_354.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_348.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_348.oppositeBasis] using
    basis_complete.oppositeReversed

end S5_354

end SemigroupBasis.CoRoots.S5_348Family
