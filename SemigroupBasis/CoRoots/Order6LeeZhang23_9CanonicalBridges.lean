import SemigroupBasis.CoRoots.Order6LeeZhang23_9InventoryBridge

/-!
# Lee--Zhang Proposition 23.9 canonical rendering bridges

This file exposes the purely combinatorial interface needed by the later
four-law normalization.  It turns the canonical list of rendered nonfinal
factor words back into an actual list of successor factors, identifies the
fixed final factor and the square bank, and removes the total-list wrapper's
empty fallback.

No derivation theorem is stated or used here.
-/

namespace SemigroupBasis.CoRoots.Order6LeeZhang23_9CanonicalBridges

open SemigroupBasis
open Order6LeeZhang23_9Scanner
open Order6LeeZhang23_9CanonicalData
open Order6LeeZhang23_9InventoryBridge

/-! ## Factor-facing form of the canonical nonfinal inventory -/

/-- The actual successor factors underlying the canonical nonfinal words.
They are sorted by their complete rendered words. -/
def canonicalNonfinalFactors (word : Word Nat) : List SuccessorFactor :=
  sortedSuccessorFactors
    (blockBearingNonfinalFactors word.toList)

/-- Rendering after sorting successor factors is the same literal list of
blocks as sorting their rendered words. -/
theorem map_renderSuccessorFactor_sortedSuccessorFactors
    (factors : List SuccessorFactor) :
    (sortedSuccessorFactors factors).map renderSuccessorFactor =
      S5_107.sortedSimpleBlocks
        (factors.map renderSuccessorFactor) := by
  have renderedPermutation :
      ((sortedSuccessorFactors factors).map
          renderSuccessorFactor).Perm
        (S5_107.sortedSimpleBlocks
          (factors.map renderSuccessorFactor)) := by
    have sourcePermutation :
        ((sortedSuccessorFactors factors).map
            renderSuccessorFactor).Perm
          (factors.map renderSuccessorFactor) :=
      (sortedSuccessorFactors_perm factors).map
        renderSuccessorFactor
    have targetPermutation :
        (S5_107.sortedSimpleBlocks
            (factors.map renderSuccessorFactor)).Perm
          (factors.map renderSuccessorFactor) := by
      unfold S5_107.sortedSimpleBlocks
      exact List.mergeSort_perm _ _
    exact sourcePermutation.trans targetPermutation.symm
  have renderedPairwise :
      ((sortedSuccessorFactors factors).map
          renderSuccessorFactor).Pairwise (· ≤ ·) := by
    simpa [List.pairwise_map, successorFactorLe] using
      ((sortedSuccessorFactors_pairwise factors).imp
        fun relation => of_decide_eq_true relation)
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe =>
      List.le_antisymm leftLe rightLe)
    renderedPairwise
    (S5_107.sortedSimpleBlocks_pairwise
      (factors.map renderSuccessorFactor))
    renderedPermutation

/-- The canonical factor list only permutes the direct block-bearing
nonfinal source factors. -/
theorem canonicalNonfinalFactors_perm_blockBearingNonfinal
    (word : Word Nat) :
    (canonicalNonfinalFactors word).Perm
      (blockBearingNonfinalFactors word.toList) := by
  exact sortedSuccessorFactors_perm _

/-- Under a non-simple inventory decomposition, the canonical rendered-word
list is literally the rendering projection of the canonical factor list. -/
theorem canonicalNonfinalFactorWords_eq_map_render
    {word : Word Nat}
    (inventory : ReversedInventoryDecomposition word) :
    canonicalNonfinalFactorWords word =
      (canonicalNonfinalFactors word).map
        renderSuccessorFactor := by
  rw [canonicalNonfinalFactorWords_eq_sorted_blockBearingNonfinal
      word inventory.first inventory.rest inventory.rawShape,
    canonicalNonfinalFactors,
    map_renderSuccessorFactor_sortedSuccessorFactors]

/-- Inventory-facing form of the factor permutation used by the later B4
normalizer. -/
theorem canonicalNonfinalFactors_perm_of_inventory
    {word : Word Nat}
    (_inventory : ReversedInventoryDecomposition word) :
    (canonicalNonfinalFactors word).Perm
      (blockBearingNonfinalFactors word.toList) :=
  canonicalNonfinalFactors_perm_blockBearingNonfinal word

/-- The canonical rendered words permute the rendered direct block-bearing
factors. -/
theorem canonicalNonfinalFactorWords_perm_renderedBlockBearing
    {word : Word Nat}
    (inventory : ReversedInventoryDecomposition word) :
    (canonicalNonfinalFactorWords word).Perm
      ((blockBearingNonfinalFactors word.toList).map
        renderSuccessorFactor) := by
  rw [canonicalNonfinalFactorWords_eq_map_render inventory]
  exact
    (canonicalNonfinalFactors_perm_blockBearingNonfinal word).map
      renderSuccessorFactor

/-- Rendering a factor list is flattening the list of its rendered words. -/
theorem renderSuccessorFactors_eq_flatten_map
    (factors : List SuccessorFactor) :
    renderSuccessorFactors factors =
      (factors.map renderSuccessorFactor).flatten := by
  induction factors with
  | nil =>
      rfl
  | cons factor rest induction =>
      simp [renderSuccessorFactors, induction]

/-- The canonical nonfinal factor renderer is exactly the flattened
canonical nonfinal rendered-word list. -/
theorem renderCanonicalNonfinalFactors_eq
    {word : Word Nat}
    (inventory : ReversedInventoryDecomposition word) :
    renderSuccessorFactors (canonicalNonfinalFactors word) =
      (canonicalNonfinalFactorWords word).flatten := by
  rw [renderSuccessorFactors_eq_flatten_map,
    canonicalNonfinalFactorWords_eq_map_render inventory]

/-! ## Fixed final factor and square-factor rendering -/

/-- The canonical final word is the literal source-oriented translation of
the raw first reversed factor. -/
theorem canonicalFinalFactorWord_eq_render_final
    {word : Word Nat}
    (inventory : ReversedInventoryDecomposition word) :
    canonicalFinalFactorWord word =
      renderSuccessorFactor
        (reverseTerminatedFactor inventory.first) := by
  unfold canonicalFinalFactorWord
  rw [inventory.retainedShape]
  rfl

/-- Regard a displayed square as one successor factor. -/
def squareFactor (marker : Nat) : SuccessorFactor :=
  (marker, [marker])

@[simp]
theorem renderSuccessorFactor_squareFactor (marker : Nat) :
    renderSuccessorFactor (squareFactor marker) = [marker, marker] :=
  rfl

/-- Rendering square factors is exactly the established square-bank
renderer. -/
theorem renderSuccessorFactors_map_squareFactor
    (markers : List Nat) :
    renderSuccessorFactors (markers.map squareFactor) =
      S5_107.renderMultipleSquares markers := by
  induction markers with
  | nil =>
      rfl
  | cons marker rest induction =>
      simp [renderSuccessorFactors, S5_107.renderMultipleSquares,
        induction]

/-! ## Empty inventory and the total canonical-word wrapper -/

/-- With no globally multiple letter, the canonical list is the source list
literally. -/
theorem canonicalList_eq_toList_of_no_multiples
    (word : Word Nat)
    (noMultiples :
      ¬ ∃ marker, 2 ≤ word.toList.count marker) :
    canonicalList word = word.toList := by
  have factorsEmpty : successorFactors word.toList = [] := by
    apply Classical.byContradiction
    intro nonempty
    exact noMultiples
      ((successorFactors_ne_nil_iff_exists_multiple
        word.toList).mp nonempty)
  have initialEqual : canonicalInitialBlock word = word.toList := by
    have rebuilt := reconstruct word.toList
    rw [factorsEmpty] at rebuilt
    simpa [canonicalInitialBlock, renderSuccessorFactors] using rebuilt
  have squareMarkersEmpty : canonicalSquareMarkers word = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro marker member
    have successorMember :
        marker ∈ successorMarkers word.toList :=
      (mem_canonicalSquareMarkers_iff_successorMarker
        word marker).mp member
    exact noMultiples
      ⟨marker,
        (mem_successorMarkers_iff
          word.toList marker).mp successorMember⟩
  have rawEmpty : reversedRawFactors word.toList = [] := by
    apply Classical.byContradiction
    intro nonempty
    obtain ⟨factor, factorMember⟩ :=
      List.exists_mem_of_ne_nil
        (reversedRawFactors word.toList) nonempty
    have factorMember' :
        factor ∈
          S5_107.terminatedBlocks word.toList.reverse := by
      simpa [reversedRawFactors] using factorMember
    have reversedMultiple :=
      S5_107.terminatedBlocks_marker_multiple
        word.toList.reverse factor factorMember'
    exact noMultiples ⟨factor.2, by
      simpa only [List.count_reverse] using reversedMultiple⟩
  have retainedEmpty : reversedRetainedFactors word = [] := by
    have s5RawEmpty :
        S5_402.terminatedBlocks word.reverse.toList = [] := by
      rw [← reversedRawFactors_eq_s5_402 word]
      exact rawEmpty
    have s5SortedEmpty :
        S5_402.sortedTerminatedBlocks word.reverse.toList = [] := by
      unfold S5_402.sortedTerminatedBlocks
      rw [s5RawEmpty]
    unfold reversedRetainedFactors
    change S5_402.retainedSortedFactors word.reverse.toList = []
    unfold S5_402.retainedSortedFactors
    rw [s5SortedEmpty]
  have nonfinalEmpty : canonicalNonfinalFactorWords word = [] := by
    simp [canonicalNonfinalFactorWords, retainedEmpty]
  have finalEmpty : canonicalFinalFactorWord word = [] := by
    simp [canonicalFinalFactorWord, retainedEmpty]
  simp [canonicalList, canonicalData, CanonicalData.render,
    initialEqual, squareMarkersEmpty, nonfinalEmpty, finalEmpty,
    S5_107.renderMultipleSquares]

/-- The deterministic canonical list of a nonempty word is nonempty. -/
theorem canonicalList_ne_nil (word : Word Nat) :
    canonicalList word ≠ [] := by
  cases markersShape : canonicalSquareMarkers word with
  | nil =>
      have noMultiples :
          ¬ ∃ marker, 2 ≤ word.toList.count marker := by
        rintro ⟨marker, multiple⟩
        have markerMember :
            marker ∈ canonicalSquareMarkers word :=
          (mem_canonicalSquareMarkers_iff_successorMarker
            word marker).mpr <|
            (mem_successorMarkers_iff
              word.toList marker).mpr multiple
        rw [markersShape] at markerMember
        exact List.not_mem_nil markerMember
      rw [canonicalList_eq_toList_of_no_multiples word noMultiples]
      cases word with
      | mk head tail =>
          simp [Word.toList]
  | cons marker rest =>
      simp [canonicalList, canonicalData, CanonicalData.render,
        markersShape, S5_107.renderMultipleSquares]

/-- The total wrapper never takes its empty fallback on canonical data. -/
@[simp]
theorem canonicalWord_toList (word : Word Nat) :
    (canonicalWord word).toList = canonicalList word := by
  cases shape : canonicalList word with
  | nil =>
      exact (canonicalList_ne_nil word shape).elim
  | cons head tail =>
      simp [canonicalWord, wordOfListOr, shape, Word.toList]

/-! ## A nonempty word for the preserved initial simple block -/

/-- A globally simple source head lies in a nonempty initial simple block. -/
theorem initialSimpleBlock_ne_nil_of_head_simple
    (word : Word Nat)
    (headSimple : S5_107.SimpleIn word word.head) :
    initialSimpleBlock word.toList ≠ [] := by
  intro initialEmpty
  have renderedShape :
      renderSuccessorFactors (successorFactors word.toList) =
        word.toList := by
    have rebuilt := reconstruct word.toList
    rw [initialEmpty] at rebuilt
    simpa using rebuilt
  cases factorsShape : successorFactors word.toList with
  | nil =>
      have emptyWord : ([] : List Nat) = word.toList := by
        simpa [factorsShape, renderSuccessorFactors] using renderedShape
      cases word with
      | mk head tail =>
          simp [Word.toList] at emptyWord
  | cons factor rest =>
      have factorMember :
          factor ∈ successorFactors word.toList := by
        rw [factorsShape]
        simp
      have factorMultiple :
          2 ≤ word.toList.count factor.1 :=
        successorFactor_marker_multiple
          word.toList factor.2 factor.1 factorMember
      have renderedCons :
          renderSuccessorFactors (factor :: rest) =
            word.toList := by
        simpa [factorsShape] using renderedShape
      have markerEq : factor.1 = word.head := by
        have heads := congrArg List.head? renderedCons
        simpa [renderSuccessorFactors, renderSuccessorFactor,
          Word.toList] using heads
      rw [markerEq] at factorMultiple
      unfold S5_107.SimpleIn at headSimple
      omega

/-- Canonical-data spelling of initial-block nonemptiness. -/
theorem canonicalInitialBlock_ne_nil_of_head_simple
    (word : Word Nat)
    (headSimple : S5_107.SimpleIn word word.head) :
    canonicalInitialBlock word ≠ [] := by
  simpa [canonicalInitialBlock] using
    initialSimpleBlock_ne_nil_of_head_simple word headSimple

/-- Total word wrapper for the preserved initial simple block. -/
def canonicalInitialWord (word : Word Nat) : Word Nat :=
  wordOfListOr word.head (canonicalInitialBlock word)

/-- Under the simple-head premise, the initial wrapper renders literally to
the complete initial simple block. -/
theorem canonicalInitialWord_toList_of_head_simple
    (word : Word Nat)
    (headSimple : S5_107.SimpleIn word word.head) :
    (canonicalInitialWord word).toList =
      canonicalInitialBlock word := by
  cases shape : canonicalInitialBlock word with
  | nil =>
      exact
        (canonicalInitialBlock_ne_nil_of_head_simple
          word headSimple shape).elim
  | cons head tail =>
      simp [canonicalInitialWord, wordOfListOr, shape, Word.toList]

end SemigroupBasis.CoRoots.Order6LeeZhang23_9CanonicalBridges
