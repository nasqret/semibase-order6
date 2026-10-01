import SemigroupBasis.CoRoots.S5_1155Completeness
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.S5_1155Family

open SemigroupBasis

namespace S5_1155

/-- Unconditional direct basis endpoint for the exact `S5_1155` table. -/
theorem basisFor :
    BasisFor SemigroupBasis.CoRoots.S5_1155.table.semigroup
      SemigroupBasis.CoRoots.S5_1155.basis := by
  refine ⟨SemigroupBasis.CoRoots.S5_1155.models, ?_⟩
  intro identity valid
  exact
    SemigroupBasis.CoRoots.S5_1155.canonicalCompleteness.derive
      identity.lhs identity.rhs
      (SemigroupBasis.CoRoots.S5_1155.sameSemanticSignature_of_valid
        identity valid)

/-- Unconditional endpoint for the opposite table and reversed basis. -/
theorem oppositeBasisFor :
    BasisFor SemigroupBasis.CoRoots.S5_1155.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_1155.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_1155.oppositeBasis] using
    basisFor.oppositeReversed

end S5_1155

/-- Aggregate proposition exposing both anti-isomorphism orientations. -/
structure FamilyBasisEndpoints : Prop where
  direct :
    BasisFor SemigroupBasis.CoRoots.S5_1155.table.semigroup
      SemigroupBasis.CoRoots.S5_1155.basis
  opposite :
    BasisFor SemigroupBasis.CoRoots.S5_1155.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_1155.oppositeBasis

theorem endpoints : FamilyBasisEndpoints where
  direct := S5_1155.basisFor
  opposite := S5_1155.oppositeBasisFor

end SemigroupBasis.CoRoots.S5_1155Family
