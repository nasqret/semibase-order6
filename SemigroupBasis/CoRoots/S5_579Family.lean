import SemigroupBasis.CoRoots.S5_579Canonical

namespace SemigroupBasis.CoRoots.S5_579

open SemigroupBasis

/-- Equality of the exact combinatorial signature is sufficient for
derivability from the two displayed identities. -/
theorem derivesOfSameS5_579Signature
    {left right : Word Nat}
    (same : SameS5_579Signature left right) :
    Derives basis left right := by
  have leftNormal := derivesCanonical left
  have rightNormal := derivesCanonical right
  have canonicalEqual := canonicalWord_eq_of_sameSignature same
  exact leftNormal.trans <| by
    rw [canonicalEqual]
    exact rightNormal.symm

/-- Source-authored direct completeness endpoint for the catalogue
representative `S5_579`. -/
theorem basisFor : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derivesOfSameS5_579Signature (valid_signature identity valid)

/-- Source-authored opposite endpoint with every identity word reversed. -/
theorem oppositeBasisFor :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using basisFor.oppositeReversed

end SemigroupBasis.CoRoots.S5_579
