import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463BalancedSwaps
import SemigroupBasis.CoRoots.S5_254Canonical

/-! Exact-count balanced-core separator extraction. The pure interval selector and
separator decomposition are reused from the published M18 proof. Unlike the
M18 normalization, the square bank is never deduplicated here; every removed
pair remains in the exact count certificate. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.BalancedCore

open SemigroupBasis

private abbrev ListDerives : List Nat → List Nat → Prop := S5_107.ListDerives basis

private abbrev MinimalRepeatedGapIntervalSelectionObligation :=
  S5_254.MinimalRepeatedGapIntervalSelectionObligation

private theorem minimalRepeatedGapIntervalSelection :
    MinimalRepeatedGapIntervalSelectionObligation := S5_254.minimalRepeatedGapIntervalSelection

@[simp] theorem count_renderSquareBank (labels : List Nat) (tested : Nat) :
    (renderSquareBank labels).count tested = 2 * labels.count tested :=
  S5_254.count_renderSquareBank labels tested

/-- Once the refinement-minimal, repeat-free-interior selector is supplied,
the derivational part of one pair extraction is complete: a repeated separator
gap derives to a word with one adjacent square, in the original outer
contexts. -/
theorem listDerivesExtractPairFromRepeatedGap_of_selection
    (selection : MinimalRepeatedGapIntervalSelectionObligation)
    (prefixWords gap suffix : List Nat)
    (globallyRepeated : ∀ letter, letter ∈ gap →
      2 ≤ (prefixWords ++ gap ++ suffix).count letter)
    (locallyRepeated : ∃ letter, 2 ≤ gap.count letter) :
    ∃ gapPrefix letter middle gapSuffix,
      gap = gapPrefix ++ [letter] ++ middle ++ [letter] ++ gapSuffix ∧
        ListDerives
          (prefixWords ++ gap ++ suffix)
          (prefixWords ++ gapPrefix ++ middle ++ [letter, letter] ++
            gapSuffix ++ suffix) := by
  obtain ⟨gapPrefix, letter, middle, gapSuffix,
      gapShape, external⟩ :=
    selection prefixWords gap suffix globallyRepeated locallyRepeated
  refine ⟨gapPrefix, letter, middle, gapSuffix, gapShape, ?_⟩
  have gathered :=
    listDerivesGatherExternallyWitnessedPair letter
      (prefixWords ++ gapPrefix) middle (gapSuffix ++ suffix) external
  rw [gapShape]
  simpa [List.append_assoc] using gathered

/-- The same conditional extraction with the adjacent square moved to the
right boundary of the selected gap. This is the form consumed by the square
bank normalizer. -/
theorem listDerivesExtractPairToGapBoundary_of_selection
    (selection : MinimalRepeatedGapIntervalSelectionObligation)
    (prefixWords gap suffix : List Nat)
    (globallyRepeated : ∀ letter, letter ∈ gap →
      2 ≤ (prefixWords ++ gap ++ suffix).count letter)
    (locallyRepeated : ∃ letter, 2 ≤ gap.count letter) :
    ∃ gapPrefix letter middle gapSuffix,
      gap = gapPrefix ++ [letter] ++ middle ++ [letter] ++ gapSuffix ∧
        ListDerives
          (prefixWords ++ gap ++ suffix)
          (prefixWords ++ gapPrefix ++ middle ++ gapSuffix ++
            [letter, letter] ++ suffix) := by
  obtain ⟨gapPrefix, letter, middle, gapSuffix,
      gapShape, gathered⟩ :=
    listDerivesExtractPairFromRepeatedGap_of_selection
      selection prefixWords gap suffix globallyRepeated locallyRepeated
  refine ⟨gapPrefix, letter, middle, gapSuffix, gapShape, ?_⟩
  have moved :=
    listDerivesPairAcrossContext
      (prefixWords ++ gapPrefix ++ middle) letter gapSuffix suffix
  exact gathered.trans <| by
    simpa [List.append_assoc] using moved

/-- Unconditional one-pair extraction using the constructed
refinement-minimal, repeat-free-interior selector. -/
theorem listDerivesExtractPairFromRepeatedGap
    (prefixWords gap suffix : List Nat)
    (globallyRepeated : ∀ letter, letter ∈ gap →
      2 ≤ (prefixWords ++ gap ++ suffix).count letter)
    (locallyRepeated : ∃ letter, 2 ≤ gap.count letter) :
    ∃ gapPrefix letter middle gapSuffix,
      gap = gapPrefix ++ [letter] ++ middle ++ [letter] ++ gapSuffix ∧
        ListDerives
          (prefixWords ++ gap ++ suffix)
          (prefixWords ++ gapPrefix ++ middle ++ [letter, letter] ++
            gapSuffix ++ suffix) :=
  listDerivesExtractPairFromRepeatedGap_of_selection
    minimalRepeatedGapIntervalSelection prefixWords gap suffix
      globallyRepeated locallyRepeated

/-- Unconditional one-pair extraction in square-bank boundary form. -/
theorem listDerivesExtractPairToGapBoundary
    (prefixWords gap suffix : List Nat)
    (globallyRepeated : ∀ letter, letter ∈ gap →
      2 ≤ (prefixWords ++ gap ++ suffix).count letter)
    (locallyRepeated : ∃ letter, 2 ≤ gap.count letter) :
    ∃ gapPrefix letter middle gapSuffix,
      gap = gapPrefix ++ [letter] ++ middle ++ [letter] ++ gapSuffix ∧
        ListDerives
          (prefixWords ++ gap ++ suffix)
          (prefixWords ++ gapPrefix ++ middle ++ gapSuffix ++
            [letter, letter] ++ suffix) :=
  listDerivesExtractPairToGapBoundary_of_selection
    minimalRepeatedGapIntervalSelection prefixWords gap suffix
      globallyRepeated locallyRepeated

/-- Extract every local parity pair from one separator gap. The residue is
one-limited, and the exact count equation certifies that the square-bank
labels account for all removed pairs. The outer contexts remain arbitrary,
so previously extracted pairs may be carried in `suffix`. -/
theorem listDerivesExtractAllGapPairs
    (prefixWords gap suffix : List Nat)
    (globallyRepeated : ∀ letter, letter ∈ gap →
      2 ≤ (prefixWords ++ gap ++ suffix).count letter) :
    ∃ residue labels,
      ListDerives
        (prefixWords ++ gap ++ suffix)
        (prefixWords ++ residue ++ renderSquareBank labels ++ suffix) ∧
        (∀ tested,
          gap.count tested =
            residue.count tested + 2 * labels.count tested) ∧
          ∀ tested, residue.count tested ≤ 1 := by
  by_cases locallyRepeated : ∃ letter, 2 ≤ gap.count letter
  · obtain ⟨gapPrefix, letter, middle, gapSuffix,
        gapShape, extracted⟩ :=
      listDerivesExtractPairToGapBoundary
        prefixWords gap suffix globallyRepeated locallyRepeated
    let reduced := gapPrefix ++ middle ++ gapSuffix
    have reducedShorter : reduced.length < gap.length := by
      rw [gapShape]
      simp [reduced] <;> omega
    have reducedGloballyRepeated :
        ∀ tested, tested ∈ reduced →
          2 ≤
            (prefixWords ++ reduced ++
              ([letter, letter] ++ suffix)).count tested := by
      intro tested memberReduced
      have memberGap : tested ∈ gap := by
        dsimp [reduced] at memberReduced
        rcases List.mem_append.mp memberReduced with
          memberLeft | memberSuffix
        · rcases List.mem_append.mp memberLeft with
            memberPrefix | memberMiddle
          · rw [gapShape]
            simp [memberPrefix]
          · rw [gapShape]
            simp [memberMiddle]
        · rw [gapShape]
          simp [memberSuffix]
      have original := globallyRepeated tested memberGap
      have rearrangedCount :
          (prefixWords ++ reduced ++
            ([letter, letter] ++ suffix)).count tested =
            (prefixWords ++ gap ++ suffix).count tested := by
        rw [gapShape]
        dsimp [reduced]
        simp only [List.count_append, List.count_cons, List.count_nil]
        omega
      rw [rearrangedCount]
      exact original
    obtain ⟨residue, labels, recurse, reducedCounts, residueLimited⟩ :=
      listDerivesExtractAllGapPairs
        prefixWords reduced ([letter, letter] ++ suffix)
          reducedGloballyRepeated
    have combined := extracted.trans <| by
      simpa [reduced, List.append_assoc] using recurse
    refine ⟨residue, labels ++ [letter], ?_, ?_, residueLimited⟩
    · simpa [renderSquareBank, List.flatMap_append,
        List.append_assoc] using combined
    · intro tested
      have reducedCount := reducedCounts tested
      rw [gapShape]
      dsimp [reduced] at reducedCount
      by_cases equal : letter = tested
      · subst tested
        simp [List.count_append] at reducedCount ⊢
        omega
      · simp [List.count_append] at reducedCount
        simp [List.count_append, equal] <;> omega
  · refine ⟨gap, [], ?_, ?_, ?_⟩
    · simpa [renderSquareBank, List.append_assoc] using
        S5_107.ListDerives.refl (basis := basis)
          (prefixWords ++ gap ++ suffix)
    · intro tested
      simp
    · intro tested
      have notTwo : ¬2 ≤ gap.count tested := by
        intro atLeastTwo
        exact locallyRepeated ⟨tested, atLeastTwo⟩
      omega
termination_by gap.length
decreasing_by
  exact reducedShorter

/-- The residue-permutation interface asks only for permuting a one-limited
residue when every displayed residue letter has a witness in an outer
context. -/
def ExternallyWitnessedResiduePermutationObligation : Prop :=
  ∀ (prefixWords source target suffix : List Nat),
    source.Perm target →
    (∀ letter, letter ∈ source →
      letter ∈ prefixWords ∨ letter ∈ suffix) →
    (∀ letter, source.count letter ≤ 1) →
    ListDerives
      (prefixWords ++ source ++ suffix)
      (prefixWords ++ target ++ suffix)

/-- Adjacent externally witnessed swaps lift to every permutation of a
one-limited residue. -/
theorem externallyWitnessedResiduePermutation :
    ExternallyWitnessedResiduePermutationObligation := by
  intro prefixWords source target suffix permutation external limited
  induction permutation generalizing prefixWords with
  | nil =>
      simpa using
        S5_107.ListDerives.refl (basis := basis) (prefixWords ++ suffix)
  | cons head _ induction =>
      have derivation :=
        induction (prefixWords ++ [head]) (by
          intro letter member
          rcases external letter (List.Mem.tail head member) with
            inPrefix | inSuffix
          · exact Or.inl (List.mem_append_left [head] inPrefix)
          · exact Or.inr inSuffix) (by
          intro letter
          have fullBound := limited letter
          simp only [List.count_cons] at fullBound
          omega)
      simpa [List.append_assoc] using derivation
  | swap first second rest =>
      have secondExternal : second ∈ prefixWords ∨ second ∈ suffix :=
        external second (by simp)
      have firstExternal : first ∈ prefixWords ∨ first ∈ suffix :=
        external first (by simp)
      simpa [List.append_assoc] using
        listDerivesSwapExternallyWitnessedAdjacent
          prefixWords [] second first rest suffix
            secondExternal firstExternal
  | trans firstPermutation _ firstInduction secondInduction =>
      have firstDerivation :=
        firstInduction prefixWords external limited
      have secondDerivation :=
        secondInduction prefixWords (by
          intro letter member
          exact external letter
            ((firstPermutation.mem_iff).mpr member)) (by
          intro letter
          rw [← firstPermutation.count letter]
          exact limited letter)
      exact firstDerivation.trans secondDerivation

/-- Sort the parity residue while retaining the multiplicity-exact bank. -/
theorem listDerivesSortedSeparatorGapRawBank
    (prefixWords gap suffix : List Nat)
    (globallyRepeated : ∀ letter, letter ∈ gap →
      2 ≤ (prefixWords ++ gap ++ suffix).count letter) :
    ∃ labels,
      ListDerives (prefixWords ++ gap ++ suffix)
        (prefixWords ++ S5_254.canonicalGapParityResidue gap ++ renderSquareBank labels ++ suffix) ∧
      ∀ tested, gap.count tested =
        (S5_254.canonicalGapParityResidue gap).count tested + 2 * labels.count tested := by
  obtain ⟨residue, labels, extracted, counts, limited⟩ :=
    listDerivesExtractAllGapPairs prefixWords gap suffix globallyRepeated
  have external : ∀ letter, letter ∈ residue →
      letter ∈ prefixWords ∨ letter ∈ renderSquareBank labels ++ suffix := by
    intro letter member
    exact S5_254.residueLetterExternalAfterPairExtraction
      prefixWords gap suffix residue labels globallyRepeated counts limited letter member
  have sorted := externallyWitnessedResiduePermutation prefixWords residue
    (S5_254.canonicalGapResidue residue) (renderSquareBank labels ++ suffix)
    (List.mergeSort_perm _ _).symm external limited
  have parity : ∀ tested, residue.count tested = gap.count tested % 2 := by
    intro tested
    have countEq := counts tested
    have bound := limited tested
    omega
  have canonicalEq := S5_254.canonicalGapResidue_eq_parityResidue gap residue parity
  refine ⟨labels, extracted.trans ?_, ?_⟩
  · simpa [canonicalEq, List.append_assoc] using sorted
  · intro tested
    have sortedCount : (S5_254.canonicalGapParityResidue gap).count tested =
        residue.count tested := by
      rw [← canonicalEq]
      exact (List.mergeSort_perm residue (fun left right : Nat => decide (left ≤ right))).count tested
    rw [sortedCount]
    exact counts tested

private theorem listDerivesRawSeparatorAssemblyContext
    {whole source : List Nat}
    {segments : List (List Nat × Nat)} {finalGap : List Nat}
    (decomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        whole source segments finalGap)
    (prefixWords suffix : List Nat)
    (countInvariant : ∀ tested,
      (prefixWords ++ source ++ suffix).count tested = whole.count tested) :
    ∃ labels,
      ListDerives
        (prefixWords ++ source ++ suffix)
        (prefixWords ++
          S5_254.renderCanonicalSeparatorSkeleton segments finalGap ++
          renderSquareBank labels ++ suffix) ∧
        ∀ tested,
          (prefixWords ++
            S5_254.renderCanonicalSeparatorSkeleton segments finalGap ++
            renderSquareBank labels ++ suffix).count tested =
              whole.count tested := by
  induction decomposition generalizing prefixWords suffix with
  | final gap gapRepeated =>
      have globallyRepeated : ∀ letter, letter ∈ gap →
          2 ≤ (prefixWords ++ gap ++ suffix).count letter := by
        intro letter member
        rw [countInvariant letter]
        exact gapRepeated letter member
      obtain ⟨labels, normalized, gapCounts⟩ :=
        listDerivesSortedSeparatorGapRawBank
          prefixWords gap suffix globallyRepeated
      refine ⟨labels, ?_, ?_⟩
      · simpa [S5_254.renderCanonicalSeparatorSkeleton,
          List.append_assoc] using normalized
      · intro tested
        have originalCount := countInvariant tested
        have gapCount := gapCounts tested
        simp only [S5_254.renderCanonicalSeparatorSkeleton,
          List.count_append, count_renderSquareBank] at originalCount ⊢
        omega
  | step gap separator remainder segments finalGap
      separatorSimple gapRepeated tail tailInduction =>
      have globallyRepeated : ∀ letter, letter ∈ gap →
          2 ≤
            (prefixWords ++ gap ++
              ((separator :: remainder) ++ suffix)).count letter := by
        intro letter member
        have original :
            (prefixWords ++ gap ++
              ((separator :: remainder) ++ suffix)).count letter =
                whole.count letter := by
          simpa [List.append_assoc] using countInvariant letter
        have repeated := gapRepeated letter member
        rw [original]
        exact repeated
      obtain ⟨headLabels, headNormalized, headCounts⟩ :=
        listDerivesSortedSeparatorGapRawBank
          prefixWords gap ((separator :: remainder) ++ suffix)
            globallyRepeated
      have movedHeadBank :=
        listDerivesSquareBankAcrossContext
          (prefixWords ++ S5_254.canonicalGapParityResidue gap)
          headLabels (separator :: remainder) suffix
      have headStep :
          ListDerives
            (prefixWords ++ (gap ++ separator :: remainder) ++ suffix)
            ((prefixWords ++ S5_254.canonicalGapParityResidue gap ++ [separator]) ++
              remainder ++ renderSquareBank headLabels ++ suffix) := by
        have normalizedHead :
            ListDerives
              (prefixWords ++ (gap ++ separator :: remainder) ++ suffix)
              (prefixWords ++ S5_254.canonicalGapParityResidue gap ++
                renderSquareBank headLabels ++
                  ((separator :: remainder) ++ suffix)) := by
          simpa [List.append_assoc] using headNormalized
        have movedHeadBank' :
            ListDerives
              (prefixWords ++ S5_254.canonicalGapParityResidue gap ++
                renderSquareBank headLabels ++
                  ((separator :: remainder) ++ suffix))
              ((prefixWords ++ S5_254.canonicalGapParityResidue gap ++ [separator]) ++
                remainder ++ renderSquareBank headLabels ++ suffix) := by
          simpa [List.append_assoc] using movedHeadBank
        exact normalizedHead.trans movedHeadBank'
      have nextCountInvariant : ∀ tested,
          (((prefixWords ++ S5_254.canonicalGapParityResidue gap ++ [separator]) ++
              remainder) ++
              (renderSquareBank headLabels ++ suffix)).count tested =
            whole.count tested := by
        intro tested
        have originalCount := countInvariant tested
        have gapCount := headCounts tested
        simp only [List.count_append, List.count_cons,
          List.count_nil, count_renderSquareBank] at originalCount ⊢
        omega
      obtain ⟨tailLabels, tailStep, tailCounts⟩ :=
        tailInduction
          (prefixWords ++ S5_254.canonicalGapParityResidue gap ++ [separator])
          (renderSquareBank headLabels ++ suffix)
          nextCountInvariant
      have tailStep' :
          ListDerives
            ((prefixWords ++ S5_254.canonicalGapParityResidue gap ++ [separator]) ++
              remainder ++ renderSquareBank headLabels ++ suffix)
            (prefixWords ++
              S5_254.renderCanonicalSeparatorSkeleton
                ((gap, separator) :: segments) finalGap ++
              renderSquareBank (tailLabels ++ headLabels) ++ suffix) := by
        simpa [S5_254.renderCanonicalSeparatorSkeleton, renderSquareBank,
          List.flatMap_append, List.append_assoc] using tailStep
      refine ⟨tailLabels ++ headLabels, headStep.trans tailStep', ?_⟩
      intro tested
      simpa [S5_254.renderCanonicalSeparatorSkeleton, renderSquareBank,
        List.flatMap_append, List.append_assoc] using tailCounts tested

/-- Normalize every gap in one whole-word decomposition, move every raw local
bank to the global right boundary, and preserve exact occurrence counts. -/
theorem listDerivesRawSeparatorAssembly
    {whole : List Nat} {segments : List (List Nat × Nat)}
    {finalGap : List Nat}
    (decomposition :
      S5_254.GloballySimpleSeparatorDecomposition
        whole whole segments finalGap) :
    ∃ labels,
      ListDerives whole
        (S5_254.renderCanonicalSeparatorSkeleton segments finalGap ++
          renderSquareBank labels) ∧
        ∀ tested,
          (S5_254.renderCanonicalSeparatorSkeleton segments finalGap ++
            renderSquareBank labels).count tested = whole.count tested := by
  simpa using
    listDerivesRawSeparatorAssemblyContext
      decomposition [] [] (by simp)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.BalancedCore
