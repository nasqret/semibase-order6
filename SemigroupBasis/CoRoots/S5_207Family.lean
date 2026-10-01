import SemigroupBasis.CoRoots.S5_207Invariant

namespace SemigroupBasis.CoRoots.S5_207Family

open SemigroupBasis

namespace S5_207

/-- Unconditional direct basis endpoint for the exact catalogue table. -/
theorem basisFor :
    BasisFor SemigroupBasis.CoRoots.S5_207.table.semigroup
      SemigroupBasis.CoRoots.S5_207.basis := by
  refine ⟨SemigroupBasis.CoRoots.S5_207.models, ?_⟩
  intro identity valid
  exact
    SemigroupBasis.CoRoots.S5_207.derivesOfSameMarkerSignature
      identity.lhs identity.rhs
      (SemigroupBasis.CoRoots.S5_207.valid_sameMarkerSignature
        identity valid)

/-- Unconditional endpoint for the opposite table and literal reversed
five-law basis. -/
theorem oppositeBasisFor :
    BasisFor SemigroupBasis.CoRoots.S5_207.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_207.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_207.oppositeBasis] using
    basisFor.oppositeReversed

end S5_207

/-- Both orientations required by the anti-isomorphism classification. -/
structure FamilyBasisEndpoints : Prop where
  direct :
    BasisFor SemigroupBasis.CoRoots.S5_207.table.semigroup
      SemigroupBasis.CoRoots.S5_207.basis
  opposite :
    BasisFor SemigroupBasis.CoRoots.S5_207.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_207.oppositeBasis

theorem endpoints : FamilyBasisEndpoints where
  direct := S5_207.basisFor
  opposite := S5_207.oppositeBasisFor

end SemigroupBasis.CoRoots.S5_207Family
