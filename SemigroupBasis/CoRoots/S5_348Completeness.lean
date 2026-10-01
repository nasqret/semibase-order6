import SemigroupBasis.CoRoots.S5_348Normalization

namespace SemigroupBasis.CoRoots.S5_348

open SemigroupBasis

/-- Generic completeness bridge for the exact capped/simple-sequence/
first-gap/optional-final invariant. -/
theorem basis_complete_of_signature
    {S : Type}
    (semigroup : Semigroup S)
    (modelsSemigroup : Models semigroup basis)
    (validSignature :
      ∀ identity : Identity Nat, identity.SatisfiedBy semigroup →
        S5_348Invariant.SameSimpleSequenceFirstGapFinalSignature
          identity.lhs identity.rhs) :
    BasisFor semigroup basis := by
  refine ⟨modelsSemigroup, ?_⟩
  intro identity valid
  exact derives_of_sameSimpleSequenceFirstGapFinalSignature
    (validSignature identity valid)

end SemigroupBasis.CoRoots.S5_348
