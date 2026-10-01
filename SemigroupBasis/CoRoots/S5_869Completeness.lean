import SemigroupBasis.CoRoots.S5_869Normalization

namespace SemigroupBasis.CoRoots.S5_869

open SemigroupBasis

/-- Generic completeness bridge for the initial-second-gap normal form. -/
theorem basis_complete_of_signature
    {S : Type}
    (semigroup : Semigroup S)
    (modelsSemigroup : Models semigroup basis)
    (validSignature :
      ∀ identity : Identity Nat, identity.SatisfiedBy semigroup →
        SameInitialSecondGapSignature identity.lhs identity.rhs) :
    BasisFor semigroup basis := by
  refine ⟨modelsSemigroup, ?_⟩
  intro identity valid
  exact derives_of_sameInitialSecondGapSignature
    (validSignature identity valid)

end SemigroupBasis.CoRoots.S5_869
