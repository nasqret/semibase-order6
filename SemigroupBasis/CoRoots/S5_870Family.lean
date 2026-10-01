import SemigroupBasis.CoRoots.S5_870Invariant

namespace SemigroupBasis.CoRoots.S5_870Family

open SemigroupBasis

namespace S5_870

/-- Direct basis endpoint for the exact catalogue representative. -/
theorem basisFor :
    BasisFor SemigroupBasis.CoRoots.S5_870.table.semigroup
      SemigroupBasis.CoRoots.S5_870.basis := by
  refine ⟨SemigroupBasis.CoRoots.S5_870.models, ?_⟩
  intro identity valid
  exact SemigroupBasis.CoRoots.S5_870.basisDerivesOfGapSignatureEq
    identity.lhs identity.rhs
    (SemigroupBasis.CoRoots.S5_870.tableGapSignatureSeparation.separate
      identity valid)

/-- Opposite endpoint with the literal reversed eight-law basis. -/
theorem oppositeBasisFor :
    BasisFor SemigroupBasis.CoRoots.S5_870.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_870.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_870.oppositeBasis] using
    basisFor.oppositeReversed

end S5_870

/-- Both orientations required by the anti-isomorphism classification. -/
structure FamilyBasisEndpoints : Prop where
  direct :
    BasisFor SemigroupBasis.CoRoots.S5_870.table.semigroup
      SemigroupBasis.CoRoots.S5_870.basis
  opposite :
    BasisFor SemigroupBasis.CoRoots.S5_870.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_870.oppositeBasis

theorem endpoints : FamilyBasisEndpoints where
  direct := S5_870.basisFor
  opposite := S5_870.oppositeBasisFor

end SemigroupBasis.CoRoots.S5_870Family
