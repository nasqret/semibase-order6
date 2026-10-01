import SemigroupBasis.CoRoots.S5_804Semantics

namespace SemigroupBasis.CoRoots.S5_804

open SemigroupBasis

/-- Two words with the same exact connected-cut signature derive from the
eight displayed laws by normalization to their common canonical render. -/
theorem derivesOfSameConnectedCutSignature
    {left right : Word Nat}
    (same : SameConnectedCutSignature left right) :
    Derives basis left right := by
  have leftNormal := derivesCanonical left
  have rightNormal := derivesCanonical right
  have canonicalEq := canonicalRender_eq_of_sameSignature same
  rw [canonicalEq] at leftNormal
  exact leftNormal.trans rightNormal.symm

/-- Source-authored completeness of the exact eight-law basis for the
catalogue representative. -/
theorem basisFor :
    BasisFor Generated.Catalogue.S5_804.table.semigroup basis := by
  refine ⟨catalogueModels, ?_⟩
  intro identity valid
  exact derivesOfSameConnectedCutSignature
    (valid_sameConnectedCutSignature identity valid)

/-- Source-authored opposite endpoint for the literal reversed basis. -/
theorem oppositeBasisFor :
    BasisFor Generated.Catalogue.S5_804.table.semigroup.opposite
      oppositeBasis := by
  simpa [oppositeBasis] using basisFor.oppositeReversed

end SemigroupBasis.CoRoots.S5_804
