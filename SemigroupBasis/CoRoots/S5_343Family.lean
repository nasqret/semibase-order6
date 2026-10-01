import SemigroupBasis.CoRoots.S5_343Completeness
import SemigroupBasis.CoRoots.S5_343Factors
import SemigroupBasis.Generated.CatalogueOrder5Part03
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_343Family

open SemigroupBasis
open SemigroupBasis.CoRoots

namespace S5_343

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_343.table.semigroup
      SemigroupBasis.CoRoots.S5_343.basis :=
  SemigroupBasis.CoRoots.S5_343.modelsOfFiniteChecks
    Generated.Catalogue.S5_343.table (by decide)

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_343.table.semigroup
      SemigroupBasis.CoRoots.S5_343.basis :=
  S5_343Completeness.basis_complete_of_signature
    Generated.Catalogue.S5_343.table.semigroup models
    S5_343Factors.S5_343.valid_signature

theorem representative_basis :
    BasisFor Generated.Catalogue.S5_343.table.semigroup
      SemigroupBasis.CoRoots.S5_343.basis :=
  basis_complete

theorem opposite_basis :
    BasisFor Generated.Catalogue.S5_343.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_343.expectedReversedBasis := by
  rw [← SemigroupBasis.CoRoots.S5_343.reversedBasis_eq_expected]
  exact basis_complete.oppositeReversed

end S5_343

namespace S5_592

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_592.table.semigroup
      SemigroupBasis.CoRoots.S5_343.basis :=
  SemigroupBasis.CoRoots.S5_343.modelsOfFiniteChecks
    Generated.Catalogue.S5_592.table (by decide)

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_592.table.semigroup
      SemigroupBasis.CoRoots.S5_343.basis :=
  S5_343Completeness.basis_complete_of_signature
    Generated.Catalogue.S5_592.table.semigroup models
    S5_343Factors.S5_592.valid_signature

theorem representative_basis :
    BasisFor Generated.Catalogue.S5_592.table.semigroup
      SemigroupBasis.CoRoots.S5_343.basis :=
  basis_complete

theorem opposite_basis :
    BasisFor Generated.Catalogue.S5_592.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_343.expectedReversedBasis := by
  rw [← SemigroupBasis.CoRoots.S5_343.reversedBasis_eq_expected]
  exact basis_complete.oppositeReversed

end S5_592

end SemigroupBasis.CoRoots.S5_343Family
