import SemigroupBasis.CoRoots.S5_793Normalization

namespace SemigroupBasis.CoRoots.S5_793

open SemigroupBasis

/-- Generic completeness bridge for the exact
first/simple-sequence/last-gap invariant. -/
theorem basis_complete_of_signature
    {S : Type}
    (semigroup : Semigroup S)
    (modelsSemigroup : Models semigroup basis)
    (validSignature :
      ∀ identity : Identity Nat, identity.SatisfiedBy semigroup →
        S5_793Invariant.SameFirstSimpleLastGapSignature
          identity.lhs identity.rhs) :
    BasisFor semigroup basis := by
  refine ⟨modelsSemigroup, ?_⟩
  intro identity valid
  exact derives_of_sameFirstSimpleLastGapSignature
    (validSignature identity valid)

end SemigroupBasis.CoRoots.S5_793
