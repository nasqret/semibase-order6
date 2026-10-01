import SemigroupBasis.CoRoots.S5_441Normalization

namespace SemigroupBasis.CoRoots.S5_441

open SemigroupBasis

/-- Generic completeness bridge for the parity-separator normal form.

It remains only to show that the candidate basis is sound for the semigroup
and that every valid identity preserves the full parity-separator signature. -/
theorem basis_complete_of_signature
    {S : Type}
    (G : Semigroup S)
    (modelsG : Models G basis)
    (validSignature :
      ∀ identity : Identity Nat, identity.SatisfiedBy G →
        SemigroupBasis.CoRoots.S5_441Invariant.SameParitySeparatorSignature
          identity.lhs identity.rhs) :
    BasisFor G basis := by
  refine ⟨modelsG, ?_⟩
  intro identity valid
  exact derives_of_sameParitySeparatorSignature
    (validSignature identity valid)

end SemigroupBasis.CoRoots.S5_441
