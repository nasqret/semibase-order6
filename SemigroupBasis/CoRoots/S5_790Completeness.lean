import SemigroupBasis.CoRoots.S5_790Normalization

namespace SemigroupBasis.CoRoots.S5_790

open SemigroupBasis

/-- Generic completeness bridge for the component/first normal form. -/
theorem basis_complete_of_signature
    {S : Type}
    (semigroup : Semigroup S)
    (modelsSemigroup : Models semigroup basis)
    (validSignature :
      ∀ identity : Identity Nat, identity.SatisfiedBy semigroup →
        S5_790Invariant.SameComponentFirstSignature
          identity.lhs identity.rhs) :
    BasisFor semigroup basis := by
  refine ⟨modelsSemigroup, ?_⟩
  intro identity valid
  exact derives_of_sameComponentFirstSignature
    (validSignature identity valid)

end SemigroupBasis.CoRoots.S5_790
