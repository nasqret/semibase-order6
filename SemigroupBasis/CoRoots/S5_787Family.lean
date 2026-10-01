import SemigroupBasis.CoRoots.S5_787Completeness
import SemigroupBasis.CoRoots.S5_787Factors
import SemigroupBasis.CoRoots.S5_787Invariant
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_787Family

open SemigroupBasis

private theorem s4_69Models :
    Models Generated.Catalogue.S4_69.table.semigroup
      SemigroupBasis.CoRoots.S5_787.basis :=
  SemigroupBasis.CoRoots.S5_787.models_of_finite_checks
    Generated.Catalogue.S4_69.table (by decide)

private theorem s2_4Models :
    Models Generated.Catalogue.S2_4.table.semigroup
      SemigroupBasis.CoRoots.S5_787.basis :=
  SemigroupBasis.CoRoots.S5_787.models_of_finite_checks
    Generated.Catalogue.S2_4.table (by decide)

private theorem s3_15Models :
    Models Generated.Catalogue.S3_15.table.semigroup
      SemigroupBasis.CoRoots.S5_787.basis :=
  SemigroupBasis.CoRoots.S5_787.models_of_finite_checks
    Generated.Catalogue.S3_15.table (by decide)

namespace S5_787

theorem models :
    Models Generated.Catalogue.S5_787.table.semigroup
      SemigroupBasis.CoRoots.S5_787.basis := by
  intro identity member
  exact
    (SemigroupBasis.CoRoots.S5_787Factors.S5_787.valid_iff_factors
      identity).2
      ⟨s4_69Models identity member, s2_4Models identity member⟩

/-- Exact representative endpoint for `S5_787`, conditional only on the
single normalization theorem isolated in `S5_787Normalization`. -/
theorem basis_complete :
    BasisFor Generated.Catalogue.S5_787.table.semigroup
      SemigroupBasis.CoRoots.S5_787.basis :=
  SemigroupBasis.CoRoots.S5_787.basis_complete_of_signature
    Generated.Catalogue.S5_787.table.semigroup models
    SemigroupBasis.CoRoots.S5_787FamilyInvariant.S5_787.valid_sameSignature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_787.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_787.basis) :=
  basis_complete.oppositeReversed

end S5_787

namespace S5_789

theorem models :
    Models Generated.Catalogue.S5_789.table.semigroup
      SemigroupBasis.CoRoots.S5_787.basis := by
  intro identity member
  exact
    (SemigroupBasis.CoRoots.S5_787Factors.S5_789.valid_iff_factors
      identity).2
      ⟨s4_69Models identity member, s2_4Models identity member⟩

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_789.table.semigroup
      SemigroupBasis.CoRoots.S5_787.basis :=
  SemigroupBasis.CoRoots.S5_787.basis_complete_of_signature
    Generated.Catalogue.S5_789.table.semigroup models
    SemigroupBasis.CoRoots.S5_787FamilyInvariant.S5_789.valid_sameSignature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_789.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_787.basis) :=
  basis_complete.oppositeReversed

end S5_789

namespace S5_796

theorem models :
    Models Generated.Catalogue.S5_796.table.semigroup
      SemigroupBasis.CoRoots.S5_787.basis := by
  intro identity member
  exact
    (SemigroupBasis.CoRoots.S5_787Factors.S5_796.valid_iff_factors
      identity).2
      ⟨s4_69Models identity member, s3_15Models identity member⟩

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_796.table.semigroup
      SemigroupBasis.CoRoots.S5_787.basis :=
  SemigroupBasis.CoRoots.S5_787.basis_complete_of_signature
    Generated.Catalogue.S5_796.table.semigroup models
    SemigroupBasis.CoRoots.S5_787FamilyInvariant.S5_796.valid_sameSignature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_796.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_787.basis) :=
  basis_complete.oppositeReversed

end S5_796

end SemigroupBasis.CoRoots.S5_787Family
