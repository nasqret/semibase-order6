import SemigroupBasis.CoRoots.S5_863Canonical

namespace SemigroupBasis.CoRoots.S5_863

open SemigroupBasis

/-- Words with the same exact `S5_863` signature are interderivable from the
five-law basis. -/
theorem derivesOfSignature
    {left right : Word Nat}
    (same : SameInitialSimpleFinalSignature left right) :
    Derives basis left right := by
  have leftNormal := derivesCoreCanonical left
  have rightNormal := derivesCoreCanonical right
  exact leftNormal.trans <| by
    rw [same.coreCanonicalWord_eq]
    exact rightNormal.symm

/-- Generic completeness bridge for the exact `S5_863` signature. -/
theorem basis_complete_of_signature
    {S : Type}
    (semigroup : Semigroup S)
    (modelsSemigroup : Models semigroup basis)
    (validSignature :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy semigroup →
          SameInitialSimpleFinalSignature
            identity.lhs identity.rhs) :
    BasisFor semigroup basis := by
  refine ⟨modelsSemigroup, ?_⟩
  intro identity valid
  exact derivesOfSignature (validSignature identity valid)

end SemigroupBasis.CoRoots.S5_863
