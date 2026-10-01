import SemigroupBasis.CoRoots.S5_787Normalization

namespace SemigroupBasis.CoRoots.S5_787

open SemigroupBasis

/-- Generic completeness bridge for the separator/first normal form. -/
theorem basis_complete_of_signature
    {S : Type}
    (semigroup : Semigroup S)
    (modelsSemigroup : Models semigroup basis)
    (validSignature :
      ∀ identity : Identity Nat, identity.SatisfiedBy semigroup →
        S5_787Invariant.SameSeparatorFirstSignature
          identity.lhs identity.rhs) :
    BasisFor semigroup basis := by
  refine ⟨modelsSemigroup, ?_⟩
  intro identity valid
  exact derives_of_sameSeparatorFirstSignature
    (validSignature identity valid)

end SemigroupBasis.CoRoots.S5_787
