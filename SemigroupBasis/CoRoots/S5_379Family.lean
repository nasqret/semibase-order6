import SemigroupBasis.CoRoots.S5_379Completeness

namespace SemigroupBasis.CoRoots.S5_379Family

open SemigroupBasis

namespace S5_379

/-- Unconditional direct basis endpoint for the exact catalogue table. -/
theorem basisFor :
    BasisFor SemigroupBasis.CoRoots.S5_379.table.semigroup
      SemigroupBasis.CoRoots.S5_379.basis := by
  refine ⟨SemigroupBasis.CoRoots.S5_379.models, ?_⟩
  intro identity valid
  exact
    SemigroupBasis.CoRoots.S5_379.derives_of_sameComponentSimpleSignature
        (SemigroupBasis.CoRoots.S5_379.valid_sameSignature
          identity valid)

/-- Unconditional endpoint for the opposite table and literal reversed
six-law basis. -/
theorem oppositeBasisFor :
    BasisFor SemigroupBasis.CoRoots.S5_379.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_379.oppositeBasis := by
  simpa [SemigroupBasis.CoRoots.S5_379.oppositeBasis] using
    basisFor.oppositeReversed

end S5_379

/-- Both orientations required by the anti-isomorphism classification. -/
structure FamilyBasisEndpoints : Prop where
  direct :
    BasisFor SemigroupBasis.CoRoots.S5_379.table.semigroup
      SemigroupBasis.CoRoots.S5_379.basis
  opposite :
    BasisFor SemigroupBasis.CoRoots.S5_379.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_379.oppositeBasis

theorem endpoints : FamilyBasisEndpoints where
  direct := S5_379.basisFor
  opposite := S5_379.oppositeBasisFor

end SemigroupBasis.CoRoots.S5_379Family
