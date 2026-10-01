import SemigroupBasis.CoRoots.Order6SporadicSection27BetaNormalization
import SemigroupBasis.CoRoots.Order6SporadicSection27F9CertificateExtraction

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6SporadicSection27

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_870

private abbrev F9Table : FiniteTable :=
  SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13559.table

private abbrev ListDerives := S5_107.ListDerives basis

/-!
## Unrestricted canonical assembly for the direct F9 target

The normalization layer works on lists because a derivation may temporarily
expose an empty target.  Semigroup words are nonempty, so the helper below
recovers the target word and keeps its literal beta-block witness alongside
the word-level derivation.
-/

private theorem normalizeWord (word : Word Nat) :
    ∃ (blocks : List FirstOccurrenceGapBlock) (target : Word Nat),
      BetaCanonicalBlocks blocks ∧
        gapBlockMarkers blocks =
          firstOccurrenceSequenceList word.toList ∧
        renderGapBlocks blocks = target.toList ∧
        Derives basis word target := by
  rcases word with ⟨head, tail⟩
  obtain ⟨blocks, canonical, markers, derivation⟩ :=
    listDerivesToBetaCanonicalBlocks (head :: tail)
  obtain ⟨targetHead, targetTail, targetShape, wordDerivation⟩ :=
    S5_107.ListDerives.from_cons derivation
  refine ⟨blocks, S5_107.listWordOfCons targetHead targetTail,
    canonical, markers, ?_, ?_⟩
  · simpa [S5_107.listWordOfCons, Word.toList] using targetShape
  · simpa [S5_107.listWordOfCons] using wordDerivation

/-- The direct F9 target is complete as soon as the literal least-differing
beta-block separator has been extracted.  This theorem is unrestricted: its
normal forms and uniqueness statement quantify over arbitrary words. -/
theorem f9_basisFor_of_separates
    (separates : F9SeparatesDistinctBetaCanonicalBlocks) :
    BasisFor F9Table.semigroup basis := by
  refine ⟨
    SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13559.models,
    ?_⟩
  intro identity valid
  obtain ⟨leftBlocks, leftTarget, leftCanonical, leftMarkers,
      leftRendered, leftDerivation⟩ := normalizeWord identity.lhs
  obtain ⟨rightBlocks, rightTarget, rightCanonical, rightMarkers,
      rightRendered, rightDerivation⟩ := normalizeWord identity.rhs
  have sameFirstOccurrences :=
    f9_valid_firstOccurrenceSequenceList_eq identity valid
  have sameMarkers :
      gapBlockMarkers leftBlocks = gapBlockMarkers rightBlocks :=
    leftMarkers.trans <| sameFirstOccurrences.trans rightMarkers.symm
  have targetValid :
      (Identity.mk leftTarget rightTarget).SatisfiedBy F9Table.semigroup := by
    intro valuation
    exact
      (leftDerivation.sound
          SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13559.models
          valuation).symm.trans <|
        (valid valuation).trans <|
          rightDerivation.sound
            SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13559.models
            valuation
  have sameBlocks :=
    betaCanonicalBlocks_eq_of_f9_valid separates
      leftCanonical rightCanonical leftRendered rightRendered
      sameMarkers targetValid
  have sameTarget : leftTarget = rightTarget := by
    apply Word.toList_injective
    calc
      leftTarget.toList = renderGapBlocks leftBlocks := leftRendered.symm
      _ = renderGapBlocks rightBlocks := congrArg renderGapBlocks sameBlocks
      _ = rightTarget.toList := rightRendered
  have back : Derives basis leftTarget identity.rhs := by
    simpa only [sameTarget] using rightDerivation.symm
  exact leftDerivation.trans back

/-- Semantic payload plus literal Cases 1/2/3 extraction is sufficient for
the exact direct S6_13559 basis theorem. -/
theorem f9_basisFor_of_paperCases
    (extracts : F9PaperCasesExtracted) :
    BasisFor F9Table.semigroup basis :=
  f9_basisFor_of_separates
    (f9SeparatesDistinctBetaCanonicalBlocks_of_paperCases extracts)

/-- Unconditional completeness of the direct F9/S6_13559 basis. -/
theorem f9_basisFor :
    SemigroupBasis.BasisFor
      SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13559.table.semigroup
      SemigroupBasis.CoRoots.Order6SporadicSection27.basis :=
  f9_basisFor_of_paperCases f9PaperCasesExtracted

end SemigroupBasis.CoRoots.Order6SporadicSection27

namespace SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13559

theorem representative_basis :
    SemigroupBasis.BasisFor table.semigroup
      SemigroupBasis.CoRoots.Order6SporadicSection27.basis :=
  SemigroupBasis.CoRoots.Order6SporadicSection27.f9_basisFor

theorem opposite_basis :
    SemigroupBasis.BasisFor table.semigroup.opposite
      SemigroupBasis.CoRoots.Order6SporadicSection27.oppositeBasis := by
  simpa only [SemigroupBasis.CoRoots.Order6SporadicSection27.oppositeBasis]
    using (SemigroupBasis.BasisFor.oppositeReversed representative_basis)

end SemigroupBasis.Generated.Order6SporadicSection27F9G1Targets.S6_13559
