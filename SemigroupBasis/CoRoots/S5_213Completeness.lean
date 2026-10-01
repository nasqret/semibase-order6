import SemigroupBasis.CoRoots.S5_213Invariant
import SemigroupBasis.CoRoots.S5_213Normalization

namespace SemigroupBasis.CoRoots.S5_213

open SemigroupBasis

/-- Generic completeness reduction from the exact family signature. -/
theorem basis_complete
    {S : Type}
    (semigroup : Semigroup S)
    (modelsSemigroup : Models semigroup basis)
    (validSignature :
      ∀ identity : Identity Nat, identity.SatisfiedBy semigroup →
        S5_213Syntax.SameCappedSingletonSignature
          identity.lhs identity.rhs) :
    BasisFor semigroup basis := by
  refine ⟨modelsSemigroup, ?_⟩
  intro identity valid
  exact
    S5_213Normalization.derives_of_sameSignature
      (validSignature identity valid)

end SemigroupBasis.CoRoots.S5_213
