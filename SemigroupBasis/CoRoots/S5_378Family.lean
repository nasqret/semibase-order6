import SemigroupBasis.CoRoots.S5_378ExactCutAssembly

namespace SemigroupBasis.CoRoots.S5_378

open SemigroupBasis

/-- The seven displayed identities form a basis for the direct catalogue
representative. -/
theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfSameSignature
    (valid_sameSignature identity valid)

/-- Literal word reversal gives a basis for the distinct opposite
orientation. -/
theorem oppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using basisFor.oppositeReversed

structure FamilyBasisEndpoints : Prop where
  direct : BasisFor table.semigroup basis
  opposite : BasisFor table.semigroup.opposite oppositeBasis

theorem endpoints : FamilyBasisEndpoints :=
  ⟨basisFor, oppositeBasisFor⟩

end SemigroupBasis.CoRoots.S5_378
