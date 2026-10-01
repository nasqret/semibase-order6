import SemigroupBasis.CoRoots.S5_860Invariant
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_860Family

open SemigroupBasis

namespace S5_860

theorem models :
    Models Generated.Catalogue.S5_860.table.semigroup
      SemigroupBasis.CoRoots.S5_860.basis :=
  SemigroupBasis.CoRoots.S5_860.table_models_basis

/-- Unconditional direct basis endpoint for the exact `S5_860` table. -/
theorem basisFor :
    BasisFor Generated.Catalogue.S5_860.table.semigroup
      SemigroupBasis.CoRoots.S5_860.basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact
    SemigroupBasis.CoRoots.S5_860.derivesOfSameSupportSimpleEndpointsSignature
      (SemigroupBasis.CoRoots.S5_860.valid_sameSignature
        identity valid)

/-- Unconditional endpoint for the opposite table and the literal reversed
eight-law basis. -/
theorem oppositeBasisFor :
    BasisFor Generated.Catalogue.S5_860.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_860.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_860.oppositeBasis] using
    basisFor.oppositeReversed

end S5_860

/-- Aggregate proposition exposing both anti-isomorphism orientations. -/
structure FamilyBasisEndpoints : Prop where
  direct :
    BasisFor Generated.Catalogue.S5_860.table.semigroup
      SemigroupBasis.CoRoots.S5_860.basis
  opposite :
    BasisFor Generated.Catalogue.S5_860.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_860.oppositeBasis

theorem endpoints : FamilyBasisEndpoints where
  direct := S5_860.basisFor
  opposite := S5_860.oppositeBasisFor

end SemigroupBasis.CoRoots.S5_860Family
