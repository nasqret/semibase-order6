import SemigroupBasis.CoRoots.S5_254Canonical
import SemigroupBasis.CoRoots.S5_254Semantics

namespace SemigroupBasis.CoRoots.S5_254

open SemigroupBasis

/-- The displayed fifteen identities form a complete identity basis for the
catalogue representative `S5_254`. -/
theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfSameM18Signature
    (sameM18Signature_of_valid identity valid)

/-- Reversing every identity gives a complete basis for the opposite
orientation in the anti-isomorphism class. -/
theorem oppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using basisFor.oppositeReversed

end SemigroupBasis.CoRoots.S5_254
