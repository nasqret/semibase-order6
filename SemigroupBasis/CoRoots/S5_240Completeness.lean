import SemigroupBasis.CoRoots.S5_240Semantics

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_240

open SemigroupBasis

theorem models :
    Models Generated.Catalogue.S5_240.table.semigroup basis :=
  models_of_finite_checks
    Generated.Catalogue.S5_240.table (by decide)

/-- Unconditional completeness for the exact stored S5_240 orientation. -/
theorem basis_complete :
    BasisFor Generated.Catalogue.S5_240.table.semigroup basis :=
  basis_complete_of_endpointSuffix
    Generated.Catalogue.S5_240.table.semigroup
    models valid_signature

/-- Unconditional completeness for the literal reverse-word basis on the
opposite semigroup. -/
theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_240.table.semigroup.opposite
      oppositeBasis := by
  simpa [oppositeBasis] using basis_complete.oppositeReversed

theorem representative_basis :
    BasisFor Generated.Catalogue.S5_240.table.semigroup basis :=
  basis_complete

theorem opposite_basis :
    BasisFor Generated.Catalogue.S5_240.table.semigroup.opposite
      (reversedBasis basis) := by
  simpa [oppositeBasis] using opposite_basis_complete

end SemigroupBasis.CoRoots.S5_240
