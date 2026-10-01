import SemigroupBasis.CoRoots.S5_788Normalization

namespace SemigroupBasis.CoRoots.S5_788

open SemigroupBasis

/-- Generic completeness bridge for the separator/initial normal form. -/
theorem basis_complete_of_signature
    {S : Type}
    (semigroup : Semigroup S)
    (modelsSemigroup : Models semigroup basis)
    (validSignature :
      ∀ identity : Identity Nat, identity.SatisfiedBy semigroup →
        S5_788Invariant.SameSeparatorInitialSignature
          identity.lhs identity.rhs) :
    BasisFor semigroup basis := by
  refine ⟨modelsSemigroup, ?_⟩
  intro identity valid
  exact derives_of_sameSeparatorInitialSignature
    (validSignature identity valid)

end SemigroupBasis.CoRoots.S5_788
