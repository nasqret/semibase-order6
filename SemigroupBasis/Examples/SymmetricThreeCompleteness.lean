import SemigroupBasis.Examples.SymmetricThreeCompletenessTransitionEncoding

namespace SemigroupBasis.Examples.SymmetricThreeCompleteness

open SemigroupBasis

/-- The three displayed positive-word identities form a complete identity
basis for the exact catalogue table `S6_4337 = S3`. -/
theorem symmetricThreeBasisComplete :
    BasisFor SemigroupBasis.Examples.symmetricThree.semigroup
      SemigroupBasis.Examples.symmetricThreeBasis := by
  refine ⟨symmetricThreeModels, ?_⟩
  intro identity valid
  apply classOf_eq_iff.mp
  rw [classOf_schreierNormalForm identity.lhs,
    classOf_schreierNormalForm identity.rhs]
  rw [schreierProduct_eq_of_modCounts
      (transitionKeysFrom [] identity.lhs.toList)
      (transitionKeysFrom [] identity.rhs.toList)
      (transitionKey_modCounts_of_valid identity valid),
    finalState_eq_of_valid identity valid]

end SemigroupBasis.Examples.SymmetricThreeCompleteness
