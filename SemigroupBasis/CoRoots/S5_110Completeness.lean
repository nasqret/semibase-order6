import SemigroupBasis.CoRoots.S5_110Invariant
import SemigroupBasis.CoRoots.S5_110Normalization

namespace SemigroupBasis.CoRoots.S5_110

open SemigroupBasis

/-- Generic completeness reduction from the cap-two singleton-order
signature. -/
theorem basis_complete
    {S : Type}
    (semigroup : Semigroup S)
    (modelsSemigroup : Models semigroup basis)
    (validSignature :
      ∀ identity : Identity Nat, identity.SatisfiedBy semigroup →
        S5_110Syntax.SameCappedSingletonSignature
          identity.lhs identity.rhs) :
    BasisFor semigroup basis := by
  refine ⟨modelsSemigroup, ?_⟩
  intro identity valid
  exact
    S5_110Normalization.derives_of_sameSignature
      (validSignature identity valid)

end SemigroupBasis.CoRoots.S5_110
