import SemigroupBasis.CoRoots.S5_213Completeness
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_213Family

open SemigroupBasis

namespace S5_213

theorem models :
    Models Generated.Catalogue.S5_213.table.semigroup
      SemigroupBasis.CoRoots.S5_213.basis :=
  SemigroupBasis.CoRoots.S5_213.models_of_finite_checks
    Generated.Catalogue.S5_213.table (by decide)

theorem opposite_models :
    Models Generated.Catalogue.S5_213.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_213.basis) :=
  models.oppositeReversed

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_213.table.semigroup) :
    S5_213Syntax.SameCappedSingletonSignature
      identity.lhs identity.rhs :=
  S5_213Invariant.sameSignature_of_s5_213_valid identity valid

/-- Representative completeness endpoint. -/
theorem basis_complete :
    BasisFor Generated.Catalogue.S5_213.table.semigroup
      SemigroupBasis.CoRoots.S5_213.basis :=
  SemigroupBasis.CoRoots.S5_213.basis_complete
    Generated.Catalogue.S5_213.table.semigroup
    models valid_sameSignature

/-- Opposite endpoint obtained by the repository's reverse-word theorem. -/
theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_213.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_213.basis) :=
  basis_complete.oppositeReversed

end S5_213

namespace S5_498

theorem models :
    Models Generated.Catalogue.S5_498.table.semigroup
      SemigroupBasis.CoRoots.S5_213.basis :=
  SemigroupBasis.CoRoots.S5_213.models_of_finite_checks
    Generated.Catalogue.S5_498.table (by decide)

theorem opposite_models :
    Models Generated.Catalogue.S5_498.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_213.basis) :=
  models.oppositeReversed

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_498.table.semigroup) :
    S5_213Syntax.SameCappedSingletonSignature
      identity.lhs identity.rhs :=
  S5_213Invariant.sameSignature_of_s5_498_valid identity valid

/-- Representative completeness endpoint. -/
theorem basis_complete :
    BasisFor Generated.Catalogue.S5_498.table.semigroup
      SemigroupBasis.CoRoots.S5_213.basis :=
  SemigroupBasis.CoRoots.S5_213.basis_complete
    Generated.Catalogue.S5_498.table.semigroup
    models valid_sameSignature

/-- Opposite endpoint; `S5_498` is catalogued as self-dual, but the theorem
uses only the formal opposite construction. -/
theorem opposite_basis_complete :
    BasisFor Generated.Catalogue.S5_498.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.S5_213.basis) :=
  basis_complete.oppositeReversed

end S5_498

end SemigroupBasis.CoRoots.S5_213Family
