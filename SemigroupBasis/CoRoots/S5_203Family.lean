import SemigroupBasis.CoRoots.S5_203Invariant

namespace SemigroupBasis.CoRoots.S5_203Family

open SemigroupBasis

namespace S5_203

/-- Unconditional direct basis endpoint for the exact catalogue table. -/
theorem basisFor :
    BasisFor SemigroupBasis.CoRoots.S5_203.table.semigroup
      SemigroupBasis.CoRoots.S5_203.basis :=
  SemigroupBasis.CoRoots.S5_203.basis_complete_of_supportTerminalState
    SemigroupBasis.CoRoots.S5_203.table.semigroup
    SemigroupBasis.CoRoots.S5_203.models
    SemigroupBasis.CoRoots.S5_203.valid_sameSupportTerminalStateSignature

/-- Unconditional endpoint for the opposite table and literal reversed
ten-law basis. -/
theorem oppositeBasisFor :
    BasisFor SemigroupBasis.CoRoots.S5_203.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_203.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_203.oppositeBasis] using
    basisFor.oppositeReversed

end S5_203

/-- Both orientations required by the anti-isomorphism classification. -/
structure FamilyBasisEndpoints : Prop where
  direct :
    BasisFor SemigroupBasis.CoRoots.S5_203.table.semigroup
      SemigroupBasis.CoRoots.S5_203.basis
  opposite :
    BasisFor SemigroupBasis.CoRoots.S5_203.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_203.oppositeBasis

theorem endpoints : FamilyBasisEndpoints where
  direct := S5_203.basisFor
  opposite := S5_203.oppositeBasisFor

end SemigroupBasis.CoRoots.S5_203Family
