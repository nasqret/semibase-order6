import SemigroupBasis.CoRoots.S5_343Normalization
import SemigroupBasis.CoRoots.S5_343Syntax

namespace SemigroupBasis.CoRoots.S5_343Completeness

open SemigroupBasis
open SemigroupBasis.CoRoots

/-- Generic completeness bridge for the four endpoint normal forms. -/
theorem basis_complete_of_signature
    {S : Type}
    (G : Semigroup S)
    (modelsG : Models G S5_343.basis)
    (validSignature :
      ∀ identity : Identity Nat, identity.SatisfiedBy G →
        S5_343Syntax.SameEndpointSequenceSignature
          identity.lhs identity.rhs) :
    BasisFor G S5_343.basis := by
  refine ⟨modelsG, ?_⟩
  intro identity valid
  have leftNormal :=
    S5_343Normalization.derivesEndpointCanonical identity.lhs
  have rightNormal :=
    S5_343Normalization.derivesEndpointCanonical identity.rhs
  have canonicalEqual :=
    (validSignature identity valid).endpointCanonicalWord_eq
  exact leftNormal.trans <| by
    rw [canonicalEqual]
    exact rightNormal.symm

end SemigroupBasis.CoRoots.S5_343Completeness
