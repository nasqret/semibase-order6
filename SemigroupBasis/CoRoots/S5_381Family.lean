import SemigroupBasis.CoRoots.S5_381Completeness
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_381Family

open SemigroupBasis

namespace S5_381

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_381.table.semigroup
      SemigroupBasis.CoRoots.S5_381.basis :=
  SemigroupBasis.CoRoots.S5_381.models_of_finite_checks
    Generated.Catalogue.S5_381.table (by decide)

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_381.table.semigroup
      SemigroupBasis.CoRoots.S5_381.basis :=
  SemigroupBasis.CoRoots.S5_381.basis_complete_of_signature
    Generated.Catalogue.S5_381.table.semigroup models
    S5_381FamilyInvariant.S5_381.valid_sameSignature

theorem representative_basis :
    BasisFor Generated.Catalogue.S5_381.table.semigroup
      SemigroupBasis.CoRoots.S5_381.basis :=
  basis_complete

theorem opposite_basis :
    BasisFor Generated.Catalogue.S5_381.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_381.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_381.oppositeBasis] using
    basis_complete.oppositeReversed

end S5_381

namespace S5_610

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_610.table.semigroup
      SemigroupBasis.CoRoots.S5_381.basis :=
  SemigroupBasis.CoRoots.S5_381.models_of_finite_checks
    Generated.Catalogue.S5_610.table (by decide)

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_610.table.semigroup
      SemigroupBasis.CoRoots.S5_381.basis :=
  SemigroupBasis.CoRoots.S5_381.basis_complete_of_signature
    Generated.Catalogue.S5_610.table.semigroup models
    S5_381FamilyInvariant.S5_610.valid_sameSignature

theorem representative_basis :
    BasisFor Generated.Catalogue.S5_610.table.semigroup
      SemigroupBasis.CoRoots.S5_381.basis :=
  basis_complete

theorem opposite_basis :
    BasisFor Generated.Catalogue.S5_610.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_381.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_381.oppositeBasis] using
    basis_complete.oppositeReversed

end S5_610

end SemigroupBasis.CoRoots.S5_381Family
