import SemigroupBasis.CoRoots.S5_788Completeness
import SemigroupBasis.CoRoots.S5_788Factors
import SemigroupBasis.CoRoots.S5_788Invariant
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_788Family

open SemigroupBasis

private theorem s4_69Models :
    Models Generated.Catalogue.S4_69.table.semigroup
      SemigroupBasis.CoRoots.S5_788.basis :=
  SemigroupBasis.CoRoots.S5_788.models_of_finite_checks
    Generated.Catalogue.S4_69.table (by decide)

private theorem s3_16Models :
    Models Generated.S3_16.table.semigroup
      SemigroupBasis.CoRoots.S5_788.basis :=
  SemigroupBasis.CoRoots.S5_788.models_of_finite_checks
    Generated.S3_16.table (by decide)

namespace S5_788

theorem models :
    Models Generated.Catalogue.S5_788.table.semigroup
      SemigroupBasis.CoRoots.S5_788.basis := by
  intro identity member
  exact
    (SemigroupBasis.CoRoots.S5_788Factors.S5_788.valid_iff_factors
      identity).2
      ⟨s4_69Models identity member, s3_16Models identity member⟩

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_788.table.semigroup
      SemigroupBasis.CoRoots.S5_788.basis :=
  SemigroupBasis.CoRoots.S5_788.basis_complete_of_signature
    Generated.Catalogue.S5_788.table.semigroup models
    SemigroupBasis.CoRoots.S5_788FamilyInvariant.S5_788.valid_sameSignature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_788.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_788.basis) :=
  basis_complete.oppositeReversed

end S5_788

namespace S5_805

theorem models :
    Models Generated.Catalogue.S5_805.table.semigroup
      SemigroupBasis.CoRoots.S5_788.basis := by
  intro identity member
  exact
    (SemigroupBasis.CoRoots.S5_788Factors.S5_805.valid_iff_factors
      identity).2
      ⟨s4_69Models identity member, s3_16Models identity member⟩

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_805.table.semigroup
      SemigroupBasis.CoRoots.S5_788.basis :=
  SemigroupBasis.CoRoots.S5_788.basis_complete_of_signature
    Generated.Catalogue.S5_805.table.semigroup models
    SemigroupBasis.CoRoots.S5_788FamilyInvariant.S5_805.valid_sameSignature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_805.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_788.basis) :=
  basis_complete.oppositeReversed

end S5_805

namespace S5_811

theorem models :
    Models Generated.Catalogue.S5_811.table.semigroup
      SemigroupBasis.CoRoots.S5_788.basis := by
  intro identity member
  exact
    (SemigroupBasis.CoRoots.S5_788Factors.S5_811.valid_iff_factors
      identity).2
      ⟨s4_69Models identity member, s3_16Models identity member⟩

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_811.table.semigroup
      SemigroupBasis.CoRoots.S5_788.basis :=
  SemigroupBasis.CoRoots.S5_788.basis_complete_of_signature
    Generated.Catalogue.S5_811.table.semigroup models
    SemigroupBasis.CoRoots.S5_788FamilyInvariant.S5_811.valid_sameSignature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_811.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_788.basis) :=
  basis_complete.oppositeReversed

end S5_811

end SemigroupBasis.CoRoots.S5_788Family
