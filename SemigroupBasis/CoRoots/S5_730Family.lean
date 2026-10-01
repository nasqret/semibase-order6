import SemigroupBasis.CoRoots.S5_730Completeness

namespace SemigroupBasis.CoRoots.S5_730

open SemigroupBasis

/-- Unconditional exact-basis endpoint for the stored representative. -/
theorem basisFor : BasisFor table.semigroup basis := by
  refine And.intro models ?_
  intro identity valid
  exact derivesOfSameSignature
    (valid_sameSignature identity valid)

/-- Unconditional reverse-word basis for the opposite representative. -/
theorem oppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using basisFor.oppositeReversed

end SemigroupBasis.CoRoots.S5_730
