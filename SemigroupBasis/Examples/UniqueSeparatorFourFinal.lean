import SemigroupBasis.Examples.UniqueSeparatorFourCapDerives
import SemigroupBasis.Examples.UniqueSeparatorFourCanonicalize
import SemigroupBasis.Examples.UniqueSeparatorFourSortDerives
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Sorted saturated square segments obtained from the deterministic
endpoint cap of a word. -/
def uniqueSeparatorFourNormalRawSegments (word : Word Nat) :
    List UniqueSeparatorSquareSegment :=
  uniqueSeparatorSortSquareSegments
    (uniqueSeparatorSplitLinear
      (uniqueSeparatorSaturate
        (uniqueSeparatorEndpointCap word.toList)))

/-- Canonical square segments attached to a word. -/
def uniqueSeparatorFourNormalSegments (word : Word Nat) :
    List UniqueSeparatorCanonicalSegment :=
  uniqueSeparatorCanonicalizeSegments
    (uniqueSeparatorFourNormalRawSegments word)

/-- The rendered canonical normal form of a word. -/
def uniqueSeparatorFourNormalRender (word : Word Nat) : List Nat :=
  uniqueSeparatorCanonicalRender
    (uniqueSeparatorFourNormalSegments word)

/-- The two derivational phases before canonical pair-collapse: endpoint
capping, followed by saturation and sorting within every quadratic block. -/
theorem uniqueSeparatorFour_derivesRawNormal (word : Word Nat) :
    UniqueSeparatorListDerives word.toList
      (uniqueSeparatorRenderSquareSegments
        (uniqueSeparatorFourNormalRawSegments word)) := by
  exact
    (uniqueSeparatorEndpointCap_derives word.toList).trans <| by
      simpa [uniqueSeparatorFourNormalRawSegments] using
        uniqueSeparatorEndpointCapSaturateSort_derives word.toList

theorem uniqueSeparatorFourNormalRender_eq_raw (word : Word Nat) :
    uniqueSeparatorFourNormalRender word =
      uniqueSeparatorRenderSquareSegments
        (uniqueSeparatorFourNormalRawSegments word) := by
  simpa [uniqueSeparatorFourNormalRender,
    uniqueSeparatorFourNormalSegments,
    uniqueSeparatorFourNormalRawSegments,
    uniqueSeparatorCanonicalSegments,
    uniqueSeparatorSortedRawSegments] using
      (uniqueSeparatorEndpointCapSaturateSort_eq_canonicalRender
        word.toList).symm

theorem uniqueSeparatorFourNormalSegments_canonical (word : Word Nat) :
    UniqueSeparatorCanonical
      (uniqueSeparatorFourNormalSegments word) := by
  simpa [uniqueSeparatorFourNormalSegments,
    uniqueSeparatorFourNormalRawSegments,
    uniqueSeparatorCanonicalSegments,
    uniqueSeparatorSortedRawSegments] using
      uniqueSeparatorCanonicalSegments_canonical word.toList

/-- Every word derives to the rendered canonical segment normal form. -/
theorem uniqueSeparatorFour_derivesNormal (word : Word Nat) :
    UniqueSeparatorListDerives word.toList
      (uniqueSeparatorFourNormalRender word) := by
  have derivation := uniqueSeparatorFour_derivesRawNormal word
  rw [← uniqueSeparatorFourNormalRender_eq_raw word] at derivation
  exact derivation

private theorem uniqueSeparatorListDerives_toWord
    (word : Word Nat) {head : Nat} {tail : List Nat}
    (derivation :
      UniqueSeparatorListDerives word.toList (head :: tail)) :
    Derives uniqueSeparatorFourBasis word
      (uniqueSeparatorWordOfCons head tail) := by
  cases word with
  | mk wordHead wordTail =>
      exact derivation.toWord

private theorem uniqueSeparatorListDerives_fromWord_target_ne_nil
    (word : Word Nat) {target : List Nat}
    (derivation :
      UniqueSeparatorListDerives word.toList target) :
    target ≠ [] := by
  cases word with
  | mk wordHead wordTail =>
      exact derivation.target_ne_nil

private theorem uniqueSeparatorFourBasis_complete_of_normalization
    (canonical :
      ∀ word : Word Nat,
        UniqueSeparatorCanonical
          (uniqueSeparatorFourNormalSegments word))
    (renderEq :
      ∀ word : Word Nat,
        uniqueSeparatorFourNormalRender word =
          uniqueSeparatorRenderSquareSegments
            (uniqueSeparatorFourNormalRawSegments word)) :
    BasisFor uniqueSeparatorFour.semigroup
      uniqueSeparatorFourBasis := by
  refine ⟨uniqueSeparatorFourBasis_models, ?_⟩
  intro identity valid
  have derivesNormal :
      ∀ word : Word Nat,
        UniqueSeparatorListDerives word.toList
          (uniqueSeparatorFourNormalRender word) := by
    intro word
    have derivation := uniqueSeparatorFour_derivesRawNormal word
    rw [← renderEq word] at derivation
    exact derivation
  have lhsListDerivation := derivesNormal identity.lhs
  have rhsListDerivation := derivesNormal identity.rhs
  have lhsNonempty :
      uniqueSeparatorFourNormalRender identity.lhs ≠ [] := by
    exact uniqueSeparatorListDerives_fromWord_target_ne_nil
      identity.lhs lhsListDerivation
  have rhsNonempty :
      uniqueSeparatorFourNormalRender identity.rhs ≠ [] := by
    exact uniqueSeparatorListDerives_fromWord_target_ne_nil
      identity.rhs rhsListDerivation
  cases lhsRenderShape :
      uniqueSeparatorFourNormalRender identity.lhs with
  | nil =>
      exact False.elim (lhsNonempty lhsRenderShape)
  | cons lhsHead lhsTail =>
      cases rhsRenderShape :
          uniqueSeparatorFourNormalRender identity.rhs with
      | nil =>
          exact False.elim (rhsNonempty rhsRenderShape)
      | cons rhsHead rhsTail =>
          rw [lhsRenderShape] at lhsListDerivation
          rw [rhsRenderShape] at rhsListDerivation
          have lhsDerivation :=
            uniqueSeparatorListDerives_toWord
              identity.lhs lhsListDerivation
          have rhsDerivation :=
            uniqueSeparatorListDerives_toWord
              identity.rhs rhsListDerivation
          have normalizedEval :
              ∀ valuation : Nat → Fin 4,
                uniqueSeparatorFour.semigroup.eval valuation
                    (uniqueSeparatorWordOfCons lhsHead lhsTail) =
                  uniqueSeparatorFour.semigroup.eval valuation
                    (uniqueSeparatorWordOfCons rhsHead rhsTail) := by
            intro valuation
            have lhsSound :=
              lhsDerivation.sound
                uniqueSeparatorFourBasis_models valuation
            have rhsSound :=
              rhsDerivation.sound
                uniqueSeparatorFourBasis_models valuation
            exact lhsSound.symm.trans <|
              (valid valuation).trans rhsSound
          have segmentsEqual :
              uniqueSeparatorFourNormalSegments identity.lhs =
                uniqueSeparatorFourNormalSegments identity.rhs := by
            apply uniqueSeparatorCanonical_eq_of_consEqualEval
              (canonical identity.lhs) (canonical identity.rhs)
            · simpa [uniqueSeparatorFourNormalRender] using
                lhsRenderShape
            · simpa [uniqueSeparatorFourNormalRender] using
                rhsRenderShape
            · exact normalizedEval
          have renderedEqual :
              uniqueSeparatorFourNormalRender identity.lhs =
                uniqueSeparatorFourNormalRender identity.rhs := by
            simp [uniqueSeparatorFourNormalRender, segmentsEqual]
          have normalWordsEqual :
              uniqueSeparatorWordOfCons lhsHead lhsTail =
                uniqueSeparatorWordOfCons rhsHead rhsTail := by
            apply Word.toList_injective
            change lhsHead :: lhsTail = rhsHead :: rhsTail
            rw [← lhsRenderShape, ← rhsRenderShape, renderedEqual]
          have bridge :
              Derives uniqueSeparatorFourBasis
                (uniqueSeparatorWordOfCons lhsHead lhsTail)
                (uniqueSeparatorWordOfCons rhsHead rhsTail) := by
            cases normalWordsEqual
            exact Derives.refl _
          exact lhsDerivation.trans <|
            bridge.trans rhsDerivation.symm

/-- Unrestricted completeness of Edmunds' seven-law identity basis for the
catalogue representative `S4_69`. -/
theorem uniqueSeparatorFourBasis_complete :
    BasisFor uniqueSeparatorFour.semigroup
      uniqueSeparatorFourBasis :=
  uniqueSeparatorFourBasis_complete_of_normalization
    uniqueSeparatorFourNormalSegments_canonical
    uniqueSeparatorFourNormalRender_eq_raw

def uniqueSeparatorFourOppositeBasis : List (Identity Nat) :=
  reversedBasis uniqueSeparatorFourBasis

/-- The formally reversed basis is complete for the opposite semigroup. -/
theorem uniqueSeparatorFourOppositeBasis_complete :
    BasisFor uniqueSeparatorFour.semigroup.opposite
      uniqueSeparatorFourOppositeBasis := by
  simpa [uniqueSeparatorFourOppositeBasis] using
    uniqueSeparatorFourBasis_complete.oppositeReversed

end SemigroupBasis.Examples
