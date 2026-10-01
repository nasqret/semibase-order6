import SemigroupBasis.CoRoots.S5_110Completeness
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_110Family

open SemigroupBasis

namespace S5_110

theorem models :
    Models Generated.Catalogue.S5_110.table.semigroup
      SemigroupBasis.CoRoots.S5_110.basis :=
  SemigroupBasis.CoRoots.S5_110.models

theorem valid_sameSignature
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        Generated.Catalogue.S5_110.table.semigroup) :
    S5_110Syntax.SameCappedSingletonSignature
      identity.lhs identity.rhs :=
  S5_110Invariant.sameSignature_of_s5_110_valid identity valid

/-- Unconditional direct completeness endpoint for S5_110. -/
theorem basisFor :
    BasisFor Generated.Catalogue.S5_110.table.semigroup
      SemigroupBasis.CoRoots.S5_110.basis :=
  SemigroupBasis.CoRoots.S5_110.basis_complete
    Generated.Catalogue.S5_110.table.semigroup
    models valid_sameSignature

/-- Unconditional endpoint for the opposite table and reversed basis. -/
theorem oppositeBasisFor :
    BasisFor Generated.Catalogue.S5_110.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_110.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_110.oppositeBasis] using
    basisFor.oppositeReversed

end S5_110

/-- Aggregate proposition used as the singleton-family audit surface. -/
structure FamilyBasisEndpoints : Prop where
  direct :
    BasisFor Generated.Catalogue.S5_110.table.semigroup
      SemigroupBasis.CoRoots.S5_110.basis
  opposite :
    BasisFor Generated.Catalogue.S5_110.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_110.oppositeBasis

theorem endpoints : FamilyBasisEndpoints where
  direct := S5_110.basisFor
  opposite := S5_110.oppositeBasisFor

end SemigroupBasis.CoRoots.S5_110Family
