import SemigroupBasis.CoRoots.S5_216Invariant
import SemigroupBasis.CoRoots.S5_216Normalization

namespace SemigroupBasis.CoRoots.S5_216Family

open SemigroupBasis

namespace S5_216

/-- Unconditional direct basis endpoint for the exact catalogue table. -/
theorem basisFor :
    BasisFor SemigroupBasis.CoRoots.S5_216.table.semigroup
      SemigroupBasis.CoRoots.S5_216.basis := by
  refine ⟨SemigroupBasis.CoRoots.S5_216.models, ?_⟩
  intro identity valid
  exact
    SemigroupBasis.CoRoots.S5_216.derivesOfSameHeadContentLengthSignature
      identity.lhs identity.rhs
      (SemigroupBasis.CoRoots.S5_216.valid_sameSignature identity valid)

/-- Unconditional endpoint for the opposite table and literal reversed
four-law basis. -/
theorem oppositeBasisFor :
    BasisFor SemigroupBasis.CoRoots.S5_216.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_216.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_216.oppositeBasis] using
    basisFor.oppositeReversed

end S5_216

/-- Both orientations required by the anti-isomorphism classification. -/
structure FamilyBasisEndpoints : Prop where
  direct :
    BasisFor SemigroupBasis.CoRoots.S5_216.table.semigroup
      SemigroupBasis.CoRoots.S5_216.basis
  opposite :
    BasisFor SemigroupBasis.CoRoots.S5_216.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_216.oppositeBasis

theorem endpoints : FamilyBasisEndpoints where
  direct := S5_216.basisFor
  opposite := S5_216.oppositeBasisFor

end SemigroupBasis.CoRoots.S5_216Family
