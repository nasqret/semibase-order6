import SemigroupBasis.CoRoots.S5_791ComponentInitialNormalForm

namespace SemigroupBasis.CoRoots.S5_791

open SemigroupBasis

/-- Generic completeness bridge for the component/initial normal form. -/
theorem basis_complete_of_signature
    {S : Type}
    (semigroup : Semigroup S)
    (modelsSemigroup : Models semigroup basis)
    (validSignature :
      ∀ identity : Identity Nat, identity.SatisfiedBy semigroup →
        S5_791Invariant.SameComponentInitialSignature
          identity.lhs identity.rhs) :
    BasisFor semigroup basis := by
  refine ⟨modelsSemigroup, ?_⟩
  intro identity valid
  exact derives_of_sameComponentInitialSignature
    (validSignature identity valid)

end SemigroupBasis.CoRoots.S5_791

