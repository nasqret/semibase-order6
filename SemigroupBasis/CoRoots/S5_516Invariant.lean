import SemigroupBasis.CoRoots.S5_516

namespace SemigroupBasis.CoRoots.S5_516

open SemigroupBasis

/-- Equality of variable support, ignoring multiplicity. -/
abbrev SameSupport :=
  SemigroupBasis.CoRoots.S5_196.SameSupport

/-- The initial variable occurs globally exactly once. This is stated as
the established terminal predicate on the reversed word. -/
def SimpleInitial (word : Word Nat) (letter : Nat) : Prop :=
  SemigroupBasis.CoRoots.S5_196.SimpleFinal word.reverse letter

def SameSimpleInitial (left right : Word Nat) : Prop :=
  ∀ letter, SimpleInitial left letter ↔ SimpleInitial right letter

/-- Short words are literal. Long words are classified by support and by
the identity of the initial variable exactly when it occurs once. -/
def ExactBasisClass (left right : Word Nat) : Prop :=
  left = right ∨
    (3 ≤ left.toList.length ∧
      3 ≤ right.toList.length ∧
      SameSupport left right ∧
      SameSimpleInitial left right)

theorem sameSupport_reverse_iff (left right : Word Nat) :
    SameSupport left.reverse right.reverse ↔
      SameSupport left right := by
  constructor
  · intro same letter
    simpa using same letter
  · intro same letter
    simpa using same letter

/-- The explicit initial-uniqueness class is exactly the reverse-word
dual of the established `S5_196` terminal-uniqueness class. -/
theorem exactBasisClass_iff_dual (left right : Word Nat) :
    ExactBasisClass left right ↔
      SemigroupBasis.CoRoots.S5_196.ExactBasisClass
        left.reverse right.reverse := by
  constructor
  · intro same
    rcases same with equal |
        ⟨leftLong, rightLong, support, simple⟩
    · subst right
      exact Or.inl rfl
    · exact Or.inr
        ⟨by simpa using leftLong,
          by simpa using rightLong,
          (sameSupport_reverse_iff left right).2 support,
          by simpa [SameSimpleInitial, SimpleInitial] using simple⟩
  · intro same
    rcases same with equal |
        ⟨leftLong, rightLong, support, simple⟩
    · left
      have reversed :=
        congrArg (fun word : Word Nat => word.reverse) equal
      simpa using reversed
    · exact Or.inr
        ⟨by simpa using leftLong,
          by simpa using rightLong,
          (sameSupport_reverse_iff left right).1 support,
          by simpa [SameSimpleInitial, SimpleInitial] using simple⟩

/-- Exact derivational characterization for the literal reversed
`S5_196` presentation. -/
theorem derivesInitialMarker_iff_exactBasisClass
    {left right : Word Nat} :
    Derives initialMarkerBasis left right ↔
      ExactBasisClass left right := by
  rw [exactBasisClass_iff_dual]
  constructor
  · intro derivation
    have reversed :
        Derives SemigroupBasis.CoRoots.S5_196.basis
          left.reverse right.reverse := by
      simpa [initialMarkerBasis_eq_reversedS5_196] using
        derivation.reverse
    exact
      SemigroupBasis.CoRoots.S5_196.derives_iff_exactBasisClass.mp
        reversed
  · intro same
    have dual :
        Derives SemigroupBasis.CoRoots.S5_196.basis
          left.reverse right.reverse :=
      SemigroupBasis.CoRoots.S5_196.derives_iff_exactBasisClass.mpr
        same
    simpa [initialMarkerBasis_eq_reversedS5_196] using dual.reverse

/-- Complete syntactic characterization of derivability from the exact
authoritative seven-law basis. -/
theorem derives_iff_exactBasisClass
    {left right : Word Nat} :
    Derives basis left right ↔
      ExactBasisClass left right := by
  constructor
  · intro derivation
    exact derivesInitialMarker_iff_exactBasisClass.mp
      (derivesInitialMarkerOfBasis derivation)
  · intro same
    exact derivesBasisOfInitialMarker
      (derivesInitialMarker_iff_exactBasisClass.mpr same)

/-- Generic completeness theorem once a table has supplied the exact
finite semantic separators. -/
theorem basis_complete_of_exact
    (table : FiniteTable)
    (models : Models table.semigroup basis)
    (separates :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy table.semigroup →
          ExactBasisClass identity.lhs identity.rhs) :
    BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derives_iff_exactBasisClass.mpr
    (separates identity valid)

end SemigroupBasis.CoRoots.S5_516
