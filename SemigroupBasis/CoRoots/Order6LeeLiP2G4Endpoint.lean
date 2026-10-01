import SemigroupBasis.CoRoots.Order6LeeLiP2G4CanonicalWitness

/-!
# Lee--Li P2 group G4: generic finite-member endpoint

The shared G4 normalizer proves that every nonempty word derives to
`canonicalG4`.  A finite member therefore supplies only validity of the three
displayed laws and a semantic certificate separating distinct canonical
forms.  This module packages that final argument once for all six G4 roots.
-/

namespace SemigroupBasis.CoRoots.Order6LeeLiP2G4

open SemigroupBasis

/-- Semantic separation required from a concrete G4 member. -/
def CanonicalSeparation (G : Semigroup S) : Prop :=
  ∀ {u v : List Nat}, u ≠ [] → v ≠ [] →
    ({ lhs := wordOfD u, rhs := wordOfD v } : Identity Nat).SatisfiedBy G →
      canonicalG4 u = canonicalG4 v

/-- The generic G4 endpoint.  Per-member modules discharge only the finite
`Models` and `CanonicalSeparation` certificates. -/
theorem basisFor_of_models_canonicalSeparation
    {G : Semigroup S}
    (models : Models G basisG4)
    (separates : CanonicalSeparation G) :
    BasisFor G basisG4 := by
  refine ⟨models, ?_⟩
  intro identity valid
  have lhsNonempty : identity.lhs.toList ≠ [] := by
    simp [Word.toList]
  have rhsNonempty : identity.rhs.toList ≠ [] := by
    simp [Word.toList]
  have sameCanonical := separates lhsNonempty rhsNonempty valid
  have lhsDerives :
      Derives basisG4 identity.lhs
        (wordOfD (canonicalG4 identity.lhs.toList)) := by
    simpa [wordOfD, Word.toList] using
      derives_canonical identity.lhs.toList lhsNonempty
  have rhsDerives :
      Derives basisG4 identity.rhs
        (wordOfD (canonicalG4 identity.rhs.toList)) := by
    simpa [wordOfD, Word.toList] using
      derives_canonical identity.rhs.toList rhsNonempty
  exact lhsDerives.trans <| by
    rw [sameCanonical]
    exact rhsDerives.symm

end SemigroupBasis.CoRoots.Order6LeeLiP2G4
