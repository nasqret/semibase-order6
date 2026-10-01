import SemigroupBasis.CoRoots.S5_790Completeness
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_790Family

open SemigroupBasis
open SemigroupBasis.Examples

private theorem s4_70Models :
    Models Generated.S4_70.table.semigroup
      SemigroupBasis.CoRoots.S5_790.basis :=
  SemigroupBasis.CoRoots.S5_790.models_of_finite_checks
    Generated.S4_70.table (by decide)

private theorem s2_4Models :
    Models leftZeroTwo.semigroup
      SemigroupBasis.CoRoots.S5_790.basis :=
  SemigroupBasis.CoRoots.S5_790.models_of_finite_checks
    leftZeroTwo (by decide)

private theorem s3_15Models :
    Models leftNormalBandFifteen.semigroup
      SemigroupBasis.CoRoots.S5_790.basis :=
  SemigroupBasis.CoRoots.S5_790.models_of_finite_checks
    leftNormalBandFifteen (by decide)

namespace S5_790

theorem models :
    Models Generated.Catalogue.S5_790.table.semigroup
      SemigroupBasis.CoRoots.S5_790.basis := by
  intro identity member
  exact
    (SemigroupBasis.CoRoots.S5_790Factors.S5_790.valid_iff_factors
      identity).2
      ⟨s4_70Models identity member, s2_4Models identity member⟩

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_790.table.semigroup
      SemigroupBasis.CoRoots.S5_790.basis :=
  SemigroupBasis.CoRoots.S5_790.basis_complete_of_signature
    Generated.Catalogue.S5_790.table.semigroup models
    SemigroupBasis.CoRoots.S5_790FamilyInvariant.S5_790.valid_sameSignature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_790.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_790.basis) :=
  basis_complete.oppositeReversed

end S5_790

namespace S5_792

theorem models :
    Models Generated.Catalogue.S5_792.table.semigroup
      SemigroupBasis.CoRoots.S5_790.basis := by
  intro identity member
  exact
    (SemigroupBasis.CoRoots.S5_790Factors.S5_792.valid_iff_factors
      identity).2
      ⟨s4_70Models identity member, s2_4Models identity member⟩

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_792.table.semigroup
      SemigroupBasis.CoRoots.S5_790.basis :=
  SemigroupBasis.CoRoots.S5_790.basis_complete_of_signature
    Generated.Catalogue.S5_792.table.semigroup models
    SemigroupBasis.CoRoots.S5_790FamilyInvariant.S5_792.valid_sameSignature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_792.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_790.basis) :=
  basis_complete.oppositeReversed

end S5_792

namespace S5_798

theorem models :
    Models Generated.Catalogue.S5_798.table.semigroup
      SemigroupBasis.CoRoots.S5_790.basis := by
  intro identity member
  exact
    (SemigroupBasis.CoRoots.S5_790Factors.S5_798.valid_iff_factors
      identity).2
      ⟨s4_70Models identity member, s3_15Models identity member⟩

theorem basis_complete :
    BasisFor Generated.Catalogue.S5_798.table.semigroup
      SemigroupBasis.CoRoots.S5_790.basis :=
  SemigroupBasis.CoRoots.S5_790.basis_complete_of_signature
    Generated.Catalogue.S5_798.table.semigroup models
    SemigroupBasis.CoRoots.S5_790FamilyInvariant.S5_798.valid_sameSignature

theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_798.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_790.basis) :=
  basis_complete.oppositeReversed

end S5_798

end SemigroupBasis.CoRoots.S5_790Family
