import SemigroupBasis.CoRoots.S5_345Normalization
import SemigroupBasis.CoRoots.S5_345Syntax

namespace SemigroupBasis.CoRoots.S5_345

open SemigroupBasis

/-- Generic completeness bridge for the `S5_345` canonical form. -/
theorem basis_complete_of_signature
    {S : Type}
    (G : Semigroup S)
    (modelsG : Models G basis)
    (validSignature :
      ∀ identity : Identity Nat, identity.SatisfiedBy G →
        SameInitialSimpleTerminalSignature
          identity.lhs identity.rhs) :
    BasisFor G basis := by
  refine ⟨modelsG, ?_⟩
  intro identity valid
  have leftNormal := derivesCanonical identity.lhs
  have rightNormal := derivesCanonical identity.rhs
  have canonicalEqual :=
    (validSignature identity valid).canonicalWord_eq
  exact leftNormal.trans <| by
    rw [canonicalEqual]
    exact rightNormal.symm

end SemigroupBasis.CoRoots.S5_345
