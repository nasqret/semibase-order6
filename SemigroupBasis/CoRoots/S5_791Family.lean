import SemigroupBasis.CoRoots.S5_791Completeness
import SemigroupBasis.CoRoots.S5_791Factors
import SemigroupBasis.CoRoots.S5_791Invariant
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_791Family

open SemigroupBasis

private theorem s4_70Models :
    Models Generated.S4_70.table.semigroup
      SemigroupBasis.CoRoots.S5_791.basis :=
  SemigroupBasis.CoRoots.S5_791.models_of_finite_checks
    Generated.S4_70.table (by decide)

private theorem s3_16Models :
    Models Generated.S3_16.table.semigroup
      SemigroupBasis.CoRoots.S5_791.basis :=
  SemigroupBasis.CoRoots.S5_791.models_of_finite_checks
    Generated.S3_16.table (by decide)

namespace S5_791

theorem models :
    Models Generated.Catalogue.S5_791.table.semigroup
      SemigroupBasis.CoRoots.S5_791.basis := by
  intro identity member
  exact
    (SemigroupBasis.CoRoots.S5_791Factors.S5_791.valid_iff_factors
      identity).2
      ⟨s4_70Models identity member, s3_16Models identity member⟩

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_791.table.semigroup
      SemigroupBasis.CoRoots.S5_791.basis :=
  SemigroupBasis.CoRoots.S5_791.basis_complete_of_signature
    Generated.Catalogue.S5_791.table.semigroup models
    SemigroupBasis.CoRoots.S5_791FamilyInvariant.S5_791.valid_sameSignature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_791.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_791.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_791.oppositeBasis] using
    basis_complete.oppositeReversed

theorem representative_basis :
    BasisFor Generated.Catalogue.S5_791.table.semigroup
      SemigroupBasis.CoRoots.S5_791.basis :=
  basis_complete

theorem opposite_basis :
    BasisFor Generated.Catalogue.S5_791.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_791.oppositeBasis :=
  opposite_basis_complete

end S5_791

namespace S5_807

theorem models :
    Models Generated.Catalogue.S5_807.table.semigroup
      SemigroupBasis.CoRoots.S5_791.basis := by
  intro identity member
  exact
    (SemigroupBasis.CoRoots.S5_791Factors.S5_807.valid_iff_factors
      identity).2
      ⟨s4_70Models identity member, s3_16Models identity member⟩

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_807.table.semigroup
      SemigroupBasis.CoRoots.S5_791.basis :=
  SemigroupBasis.CoRoots.S5_791.basis_complete_of_signature
    Generated.Catalogue.S5_807.table.semigroup models
    SemigroupBasis.CoRoots.S5_791FamilyInvariant.S5_807.valid_sameSignature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_807.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_791.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_791.oppositeBasis] using
    basis_complete.oppositeReversed

theorem representative_basis :
    BasisFor Generated.Catalogue.S5_807.table.semigroup
      SemigroupBasis.CoRoots.S5_791.basis :=
  basis_complete

theorem opposite_basis :
    BasisFor Generated.Catalogue.S5_807.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_791.oppositeBasis :=
  opposite_basis_complete

end S5_807

end SemigroupBasis.CoRoots.S5_791Family
