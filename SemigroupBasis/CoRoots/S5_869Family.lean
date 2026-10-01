import SemigroupBasis.CoRoots.S5_869Completeness
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_869Family

open SemigroupBasis

namespace S5_869

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_869.table.semigroup
      SemigroupBasis.CoRoots.S5_869.basis :=
  SemigroupBasis.CoRoots.S5_869.models_of_finite_checks
    Generated.Catalogue.S5_869.table (by decide)

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_869.table.semigroup
      SemigroupBasis.CoRoots.S5_869.basis :=
  SemigroupBasis.CoRoots.S5_869.basis_complete_of_signature
    Generated.Catalogue.S5_869.table.semigroup models
    SemigroupBasis.CoRoots.S5_869.valid_sameSignature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_869.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_869.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_869.oppositeBasis] using
    basis_complete.oppositeReversed

end S5_869

namespace S5_871

set_option maxRecDepth 100000 in
theorem models :
    Models Generated.Catalogue.S5_871.table.semigroup
      SemigroupBasis.CoRoots.S5_869.basis :=
  SemigroupBasis.CoRoots.S5_869.models_of_finite_checks
    Generated.Catalogue.S5_871.table (by decide)

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_871.table.semigroup
      SemigroupBasis.CoRoots.S5_869.basis :=
  SemigroupBasis.CoRoots.S5_869.basis_complete_of_signature
    Generated.Catalogue.S5_871.table.semigroup models
    SemigroupBasis.CoRoots.S5_871.valid_sameSignature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_871.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_869.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_869.oppositeBasis] using
    basis_complete.oppositeReversed

end S5_871

end SemigroupBasis.CoRoots.S5_869Family
