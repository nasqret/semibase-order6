import SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_207ParityMarkerSyntax
import SemigroupBasis.CoRoots.S5_441Invariant

/-!
# Unrestricted exact D009 marker-state / parity completeness

The marker separator is used only semantically.  All transformations are
derivations from the frozen eight laws, so the four saturated-final bridges
preserve both marker states and cyclic occurrence parity by soundness.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 6000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_207

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6FactorPairS2S5356
open SemigroupBasis.CoRoots.S5_207.DirectCompletenessArchitecture

private abbrev targetBasis : List (Identity Nat) := Rank009.basis

/-- Frozen B8 derivations preserve the full concrete S5_207 marker state. -/
theorem derivationMarkerSignature
    {left right : Word Nat}
    (derivation : Derives targetBasis left right) :
    SameMarkerSignature left right := by
  let identity : Identity Nat := ⟨left, right⟩
  have valid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.S5_207.table.semigroup := by
    intro valuation
    exact derivation.sound Rank009.rightModels valuation
  exact SemigroupBasis.CoRoots.S5_207.valid_sameMarkerSignature
    identity valid

/-- Frozen B8 derivations preserve unrestricted per-variable cyclic parity. -/
theorem derivationOccurrenceParity
    {left right : Word Nat}
    (derivation : Derives targetBasis left right) :
    ∀ letter,
      left.toList.count letter % 2 =
        right.toList.count letter % 2 := by
  let identity : Identity Nat := ⟨left, right⟩
  have valid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup := by
    intro valuation
    exact derivation.sound Rank009.leftModels valuation
  exact
    SemigroupBasis.CoRoots.S5_441Invariant.sameOccurrenceParity_of_s3_11_valid
      identity valid

/-- Aligned finals reduce to exact capped-prefix counts and prefix parity. -/
theorem derivesAlignedFinalOfSignatures
    (left right : List Nat) (final : Nat)
    (same :
      SameMarkerSignature
        (wordOfPrefixFinal left final)
        (wordOfPrefixFinal right final))
    (parity : ∀ letter,
      (wordOfPrefixFinal left final).toList.count letter % 2 =
        (wordOfPrefixFinal right final).toList.count letter % 2) :
    Derives targetBasis
      (wordOfPrefixFinal left final)
      (wordOfPrefixFinal right final) := by
  have capped : ∀ letter,
      min (left.count letter) 2 = min (right.count letter) 2 := by
    intro letter
    have marker := same letter
    rw [markerState_wordOfPrefixFinal,
      markerState_wordOfPrefixFinal] at marker
    have counts := congrArg prefixMultiplicityOfState marker
    simpa [splitMarkerState] using counts
  have prefixParity : ∀ letter,
      left.count letter % 2 = right.count letter % 2 := by
    intro letter
    have counts := parity letter
    simp only [toList_wordOfPrefixFinal, List.count_append,
      List.count_cons, List.count_nil] at counts
    omega
  have permutation := thresholdParityReduce_perm_of_signatures
    capped prefixParity
  exact (derivesNormalizePrefix left final).trans <|
    (derivesPrefixPermutation permutation final).trans <|
      (derivesNormalizePrefix right final).symm

/-- Genuine unrestricted B8 completeness for complete marker state plus parity. -/
theorem derivesOfSameMarkerParitySignature
    (left right : Word Nat)
    (same : SameMarkerSignature left right)
    (parity : ∀ letter,
      left.toList.count letter % 2 =
        right.toList.count letter % 2) :
    Derives targetBasis left right := by
  classical
  let leftSplit := splitPrefixFinal left
  let rightSplit := splitPrefixFinal right
  let leftPrefix := thresholdParityReduce leftSplit.1
  have leftReconstruct :
      wordOfPrefixFinal leftSplit.1 leftSplit.2 = left :=
    wordOfPrefixFinal_split left
  have rightReconstruct :
      wordOfPrefixFinal rightSplit.1 rightSplit.2 = right :=
    wordOfPrefixFinal_split right
  have renderedSame :
      SameMarkerSignature
        (wordOfPrefixFinal leftSplit.1 leftSplit.2)
        (wordOfPrefixFinal rightSplit.1 rightSplit.2) := by
    rw [leftReconstruct, rightReconstruct]
    exact same
  have renderedParity : ∀ letter,
      (wordOfPrefixFinal leftSplit.1 leftSplit.2).toList.count letter % 2 =
        (wordOfPrefixFinal rightSplit.1 rightSplit.2).toList.count letter % 2 := by
    intro letter
    rw [leftReconstruct, rightReconstruct]
    exact parity letter
  have splitStates : ∀ letter,
      splitMarkerState leftSplit.1 leftSplit.2 letter =
        splitMarkerState rightSplit.1 rightSplit.2 letter := by
    intro letter
    simpa only [markerState_wordOfPrefixFinal] using
      renderedSame letter
  rw [← leftReconstruct, ← rightReconstruct]
  by_cases finalsEqual : leftSplit.2 = rightSplit.2
  · rw [finalsEqual]
    exact derivesAlignedFinalOfSignatures
      leftSplit.1 rightSplit.1 rightSplit.2
      (by simpa [finalsEqual] using renderedSame)
      (by
        intro letter
        simpa [finalsEqual] using renderedParity letter)
  · have oldState :
        markerStateFrom (leftSplit.1.count leftSplit.2) true =
          markerStateFrom (rightSplit.1.count leftSplit.2) false := by
      simpa only [splitMarkerState, beq_self_eq_true,
        beq_eq_false_iff_ne.mpr (Ne.symm finalsEqual)] using
        splitStates leftSplit.2
    have newState :
        markerStateFrom (leftSplit.1.count rightSplit.2) false =
          markerStateFrom (rightSplit.1.count rightSplit.2) true := by
      simpa only [splitMarkerState, beq_self_eq_true,
        beq_eq_false_iff_ne.mpr finalsEqual] using
        splitStates rightSplit.2
    have oldSaturated :=
      SemigroupBasis.CoRoots.S5_207.markerStateFrom_true_false_forces_two
        (leftSplit.1.count leftSplit.2)
        (rightSplit.1.count leftSplit.2) oldState
    have newSaturated :=
      SemigroupBasis.CoRoots.S5_207.markerStateFrom_false_true_forces_two
        (leftSplit.1.count rightSplit.2)
        (rightSplit.1.count rightSplit.2) newState
    have oldLower : 2 ≤ leftPrefix.count leftSplit.2 := by
      have capped := thresholdParityReduce_capped_count
        leftSplit.2 leftSplit.1
      change min (leftPrefix.count leftSplit.2) 2 =
        min (leftSplit.1.count leftSplit.2) 2 at capped
      rw [oldSaturated.1] at capped
      omega
    have newLower : 2 ≤ leftPrefix.count rightSplit.2 := by
      have capped := thresholdParityReduce_capped_count
        rightSplit.2 leftSplit.1
      change min (leftPrefix.count rightSplit.2) 2 =
        min (leftSplit.1.count rightSplit.2) 2 at capped
      rw [newSaturated.1] at capped
      omega
    have oldUpper : leftPrefix.count leftSplit.2 ≤ 3 :=
      thresholdParityReduce_count_le_three leftSplit.2 leftSplit.1
    have newUpper : leftPrefix.count rightSplit.2 ≤ 3 :=
      thresholdParityReduce_count_le_three rightSplit.2 leftSplit.1
    obtain ⟨switched, switchedDerivation⟩ :=
      derivesSaturatedFinalChoice
        leftPrefix leftSplit.2 rightSplit.2 finalsEqual
        oldLower oldUpper newLower newUpper
    have normalized :
        Derives targetBasis
          (wordOfPrefixFinal leftSplit.1 leftSplit.2)
          (wordOfPrefixFinal leftPrefix leftSplit.2) :=
      derivesNormalizePrefix leftSplit.1 leftSplit.2
    have changeFinal := normalized.trans switchedDerivation
    have changeMarker := derivationMarkerSignature changeFinal
    have changeParity := derivationOccurrenceParity changeFinal
    have switchedSame :
        SameMarkerSignature
          (wordOfPrefixFinal switched rightSplit.2)
          (wordOfPrefixFinal rightSplit.1 rightSplit.2) := by
      intro letter
      exact (changeMarker letter).symm.trans
        (renderedSame letter)
    have switchedParity : ∀ letter,
        (wordOfPrefixFinal switched rightSplit.2).toList.count letter % 2 =
          (wordOfPrefixFinal rightSplit.1 rightSplit.2).toList.count letter % 2 := by
      intro letter
      exact (changeParity letter).symm.trans
        (renderedParity letter)
    exact changeFinal.trans <|
      derivesAlignedFinalOfSignatures
        switched rightSplit.1 rightSplit.2 switchedSame switchedParity

end SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_207
