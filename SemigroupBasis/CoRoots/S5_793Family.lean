import SemigroupBasis.CoRoots.S5_793Completeness
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_793Family

open SemigroupBasis
open SemigroupBasis.Examples

private theorem s4_71Models :
    Models Generated.S4_71.table.semigroup
      SemigroupBasis.CoRoots.S5_793.basis :=
  SemigroupBasis.CoRoots.S5_793.models_of_finite_checks
    Generated.S4_71.table (by decide)

private theorem s2_4Models :
    Models Generated.Catalogue.S2_4.table.semigroup
      SemigroupBasis.CoRoots.S5_793.basis :=
  SemigroupBasis.CoRoots.S5_793.models_of_finite_checks
    Generated.Catalogue.S2_4.table (by decide)

private theorem s3_15Models :
    Models Generated.Catalogue.S3_15.table.semigroup
      SemigroupBasis.CoRoots.S5_793.basis :=
  SemigroupBasis.CoRoots.S5_793.models_of_finite_checks
    Generated.Catalogue.S3_15.table (by decide)

namespace S5_793

theorem models :
    Models Generated.Catalogue.S5_793.table.semigroup
      SemigroupBasis.CoRoots.S5_793.basis := by
  intro identity member
  exact
    (S5_793Factors.S5_793.valid_iff_factors identity).2
      ⟨s4_71Models identity member, s2_4Models identity member⟩

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_793.table.semigroup
      SemigroupBasis.CoRoots.S5_793.basis :=
  SemigroupBasis.CoRoots.S5_793.basis_complete_of_signature
    Generated.Catalogue.S5_793.table.semigroup models
    S5_793FamilyInvariant.S5_793.valid_sameSignature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_793.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_793.basis) :=
  basis_complete.oppositeReversed

end S5_793

namespace S5_801

theorem models :
    Models Generated.Catalogue.S5_801.table.semigroup
      SemigroupBasis.CoRoots.S5_793.basis := by
  intro identity member
  exact
    (S5_793Factors.S5_801.valid_iff_factors identity).2
      ⟨s4_71Models identity member, s3_15Models identity member⟩

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_801.table.semigroup
      SemigroupBasis.CoRoots.S5_793.basis :=
  SemigroupBasis.CoRoots.S5_793.basis_complete_of_signature
    Generated.Catalogue.S5_801.table.semigroup models
    S5_793FamilyInvariant.S5_801.valid_sameSignature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_801.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_793.basis) :=
  basis_complete.oppositeReversed

end S5_801

namespace S5_843

theorem models :
    Models Generated.Catalogue.S5_843.table.semigroup
      SemigroupBasis.CoRoots.S5_793.basis := by
  intro identity member
  exact
    (S5_793Factors.S5_843.valid_iff_factors identity).2
      ⟨s4_71Models identity member, s3_15Models identity member⟩

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_843.table.semigroup
      SemigroupBasis.CoRoots.S5_793.basis :=
  SemigroupBasis.CoRoots.S5_793.basis_complete_of_signature
    Generated.Catalogue.S5_843.table.semigroup models
    S5_793FamilyInvariant.S5_843.valid_sameSignature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_843.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_793.basis) :=
  basis_complete.oppositeReversed

end S5_843

end SemigroupBasis.CoRoots.S5_793Family
