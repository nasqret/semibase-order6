import SemigroupBasis.CoRoots.S5_381Normalization

namespace SemigroupBasis.CoRoots.S5_381

open SemigroupBasis

/-- Generic completeness bridge for the exact
simple-sequence/last-gap/optional-initial invariant. -/
theorem basis_complete_of_signature
    {S : Type}
    (semigroup : Semigroup S)
    (modelsSemigroup : Models semigroup basis)
    (validSignature :
      ∀ identity : Identity Nat, identity.SatisfiedBy semigroup →
        S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
          identity.lhs identity.rhs) :
    BasisFor semigroup basis := by
  refine ⟨modelsSemigroup, ?_⟩
  intro identity valid
  exact derives_of_sameSimpleSequenceLastGapInitialSignature
    (validSignature identity valid)

end SemigroupBasis.CoRoots.S5_381
