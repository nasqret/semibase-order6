import SemigroupBasis.CoRoots.S5_107Family
import SemigroupBasis.CoRoots.S5_107Syntax

namespace SemigroupBasis.CoRoots.S5_107

open SemigroupBasis

/-- Generic completeness bridge for the `S5_107` canonical form.

A semigroup has the published basis once it models the basis, every valid
identity has the simple-adjacency signature, every word derives to its
canonical word, and equal signatures have equal canonical words. -/
theorem basis_complete_of_signature
    {S : Type}
    (G : Semigroup S)
    (modelsG : Models G basis)
    (validSignature :
      ∀ e : Identity Nat, e.SatisfiedBy G →
        SameSimpleAdjacencySignature e.lhs e.rhs)
    (normalizes :
      ∀ word : Word Nat,
        Derives basis word (simpleAdjacencyCanonicalWord word))
    (canonicalEqual :
      ∀ {left right : Word Nat},
        SameSimpleAdjacencySignature left right →
          simpleAdjacencyCanonicalWord left =
            simpleAdjacencyCanonicalWord right) :
    BasisFor G basis := by
  refine ⟨modelsG, ?_⟩
  intro e valid
  have leftNormal := normalizes e.lhs
  have rightNormal := normalizes e.rhs
  have middle :
      Derives basis
        (simpleAdjacencyCanonicalWord e.lhs)
        (simpleAdjacencyCanonicalWord e.rhs) := by
    rw [canonicalEqual (validSignature e valid)]
    exact Derives.refl _
  exact leftNormal.trans (middle.trans rightNormal.symm)

end SemigroupBasis.CoRoots.S5_107
