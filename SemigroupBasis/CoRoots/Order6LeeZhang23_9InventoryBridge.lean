import SemigroupBasis.CoRoots.Order6LeeZhang23_9CanonicalData

/-!
# Lee--Zhang Proposition 23.9 raw inventory bridge

This file relates the reversed terminated-block scan used by the source
factorization to the retained inventory used by the canonical data.  Every
statement is combinatorial: the raw first factor becomes the literally fixed
final successor factor, the raw tail splits into block-bearing and marker-only
parts, and the distinct raw markers permute to the complete global square
bank.

No derivation theorem is used in this file.
-/

namespace SemigroupBasis.CoRoots.Order6LeeZhang23_9InventoryBridge

open SemigroupBasis
open Order6LeeZhang23_9Scanner
open Order6LeeZhang23_9CanonicalData

/-- The terminated factors of the reversed source list, before sorting or
filtering. -/
def reversedRawFactors
    (letters : List Nat) : List (List Nat × Nat) :=
  S5_107.terminatedBlocks letters.reverse

/-- The raw scanner used here is the established scanner underlying the
`S5_402` retained inventory. -/
theorem reversedRawFactors_eq_s5_402 (word : Word Nat) :
    reversedRawFactors word.toList =
      S5_402.terminatedBlocks word.reverse.toList := by
  simpa [reversedRawFactors, Word.toList_reverse] using
    (S5_402.terminatedBlocks_eq_s5_107
      word.reverse.toList).symm

/-- If the raw reversed scan is nonempty, the retained inventory keeps its
first factor literally and deterministically sorts exactly the block-bearing
part of the raw tail. -/
theorem reversedRetainedFactors_eq_of_raw_cons
    (word : Word Nat) (first : List Nat × Nat)
    (rest : List (List Nat × Nat))
    (shape :
      reversedRawFactors word.toList = first :: rest) :
    reversedRetainedFactors word =
      first :: S5_402.sortedTerminatedFactors
        (S5_402.blockBearingFactors rest) := by
  have rawShape :
      S5_402.terminatedBlocks word.reverse.toList =
        first :: rest := by
    rw [← reversedRawFactors_eq_s5_402 word]
    exact shape
  have sortedShape :
      S5_402.sortedTerminatedBlocks word.reverse.toList =
        first :: S5_402.sortedTerminatedTail rest := by
    unfold S5_402.sortedTerminatedBlocks
    rw [rawShape]
  unfold reversedRetainedFactors S5_402.retainedSortedFactors
  simp only [sortedShape]
  rw [S5_402.blockBearingFactors_sortedTerminatedTail]

/-- Reversing the raw factor order and translating each factor gives the
source-oriented successor list, with the raw first factor literally last. -/
theorem successorFactors_eq_of_reversedRaw_cons
    (letters : List Nat) (first : List Nat × Nat)
    (rest : List (List Nat × Nat))
    (shape : reversedRawFactors letters = first :: rest) :
    successorFactors letters =
      rest.reverse.map reverseTerminatedFactor ++
        [reverseTerminatedFactor first] := by
  unfold reversedRawFactors at shape
  unfold successorFactors
  rw [shape, List.reverse_cons, List.map_append]
  rfl

/-- The canonical cut removes exactly the translated raw first factor from
the end of the source-oriented successor list. -/
theorem nonfinalSuccessorFactors_eq_of_reversedRaw_cons
    (letters : List Nat) (first : List Nat × Nat)
    (rest : List (List Nat × Nat))
    (shape : reversedRawFactors letters = first :: rest) :
    nonfinalSuccessorFactors letters =
      rest.reverse.map reverseTerminatedFactor := by
  have sourceShape :=
    successorFactors_eq_of_reversedRaw_cons
      letters first rest shape
  have cutShape :
      finalFactorCut letters =
        (rest.reverse.map reverseTerminatedFactor).length := by
    unfold finalFactorCut
    rw [sourceShape, List.length_append]
    simp
  unfold nonfinalSuccessorFactors
  rw [cutShape, sourceShape,
    List.take_append_of_le_length (Nat.le_refl _),
    List.take_length]

/-- The final side of the canonical cut is the singleton translated raw first
factor.  This is the fixed controller used by every later factor permutation. -/
theorem finalSuccessorFactors_eq_of_reversedRaw_cons
    (letters : List Nat) (first : List Nat × Nat)
    (rest : List (List Nat × Nat))
    (shape : reversedRawFactors letters = first :: rest) :
    finalSuccessorFactors letters =
      [reverseTerminatedFactor first] := by
  have sourceShape :=
    successorFactors_eq_of_reversedRaw_cons
      letters first rest shape
  have cutShape :
      finalFactorCut letters =
        (rest.reverse.map reverseTerminatedFactor).length := by
    unfold finalFactorCut
    rw [sourceShape, List.length_append]
    simp
  unfold finalSuccessorFactors
  rw [cutShape, sourceShape,
    List.drop_append_of_le_length (Nat.le_refl _),
    List.drop_length, List.nil_append]

/-! ## Translating the raw tail partition -/

/-- Filtering translated factors for nonempty successor blocks is exactly
filtering the raw factors for nonempty blocks, followed by reversal and
translation. -/
theorem blockBearing_reverse_map_reverseTerminatedFactor :
    ∀ factors : List (List Nat × Nat),
      ((factors.reverse.map reverseTerminatedFactor).filter
          fun factor => decide (factor.2 ≠ [])) =
        (S5_402.blockBearingFactors factors).reverse.map
          reverseTerminatedFactor
  | [] => by
      rfl
  | (block, marker) :: rest => by
      by_cases blockEmpty : block = []
      · subst block
        rw [List.reverse_cons, List.map_append, List.filter_append,
          blockBearing_reverse_map_reverseTerminatedFactor rest]
        simp [S5_402.blockBearingFactors,
          reverseTerminatedFactor]
      · have reverseNonempty : block.reverse ≠ [] := by
          simpa using blockEmpty
        rw [List.reverse_cons, List.map_append, List.filter_append,
          blockBearing_reverse_map_reverseTerminatedFactor rest]
        simp [S5_402.blockBearingFactors,
          reverseTerminatedFactor, blockEmpty, reverseNonempty]

/-- The analogous exact conversion for marker-only factors. -/
theorem markerOnly_reverse_map_reverseTerminatedFactor :
    ∀ factors : List (List Nat × Nat),
      ((factors.reverse.map reverseTerminatedFactor).filter
          fun factor => decide (factor.2 = [])) =
        (S5_402.markerOnlyFactors factors).reverse.map
          reverseTerminatedFactor
  | [] => by
      rfl
  | (block, marker) :: rest => by
      by_cases blockEmpty : block = []
      · subst block
        rw [List.reverse_cons, List.map_append, List.filter_append,
          markerOnly_reverse_map_reverseTerminatedFactor rest]
        simp [S5_402.markerOnlyFactors,
          reverseTerminatedFactor]
      · have reverseNonempty : block.reverse ≠ [] := by
          simpa using blockEmpty
        rw [List.reverse_cons, List.map_append, List.filter_append,
          markerOnly_reverse_map_reverseTerminatedFactor rest]
        simp [S5_402.markerOnlyFactors,
          reverseTerminatedFactor, blockEmpty, reverseNonempty]

/-- The source-oriented block-bearing nonfinal factors are the translated
reverse of the raw block-bearing tail. -/
theorem blockBearingNonfinalFactors_eq_of_reversedRaw_cons
    (letters : List Nat) (first : List Nat × Nat)
    (rest : List (List Nat × Nat))
    (shape : reversedRawFactors letters = first :: rest) :
    blockBearingNonfinalFactors letters =
      (S5_402.blockBearingFactors rest).reverse.map
        reverseTerminatedFactor := by
  unfold blockBearingNonfinalFactors
  rw [nonfinalSuccessorFactors_eq_of_reversedRaw_cons
    letters first rest shape]
  exact blockBearing_reverse_map_reverseTerminatedFactor rest

/-- The source-oriented marker-only nonfinal factors are the translated
reverse of the raw marker-only tail. -/
theorem markerOnlyNonfinalFactors_eq_of_reversedRaw_cons
    (letters : List Nat) (first : List Nat × Nat)
    (rest : List (List Nat × Nat))
    (shape : reversedRawFactors letters = first :: rest) :
    markerOnlyNonfinalFactors letters =
      (S5_402.markerOnlyFactors rest).reverse.map
        reverseTerminatedFactor := by
  unfold markerOnlyNonfinalFactors
  rw [nonfinalSuccessorFactors_eq_of_reversedRaw_cons
    letters first rest shape]
  exact markerOnly_reverse_map_reverseTerminatedFactor rest

/-- Stable block-bearing/marker-only partitioning only permutes the raw tail. -/
theorem reversedRawTail_partition_perm
    (rest : List (List Nat × Nat)) :
    (S5_402.blockBearingFactors rest ++
        S5_402.markerOnlyFactors rest).Perm rest :=
  S5_402.blockBearingFactors_append_markerOnlyFactors_perm rest

private theorem reverse_perm_self
    (factors : List (List Nat × Nat)) :
    factors.reverse.Perm factors := by
  rw [List.perm_iff_count]
  intro factor
  simp

/-- Translating the retained tail only permutes the block-bearing nonfinal
source factors.  The fixed final factor is outside both lists. -/
theorem forwardRetainedTail_perm_blockBearingNonfinal
    (word : Word Nat) (first : List Nat × Nat)
    (rest : List (List Nat × Nat))
    (shape : reversedRawFactors word.toList = first :: rest) :
    (((reversedRetainedFactors word).drop 1).map
        reverseTerminatedFactor).Perm
      (blockBearingNonfinalFactors word.toList) := by
  rw [reversedRetainedFactors_eq_of_raw_cons
      word first rest shape,
    blockBearingNonfinalFactors_eq_of_reversedRaw_cons
      word.toList first rest shape]
  change
    ((S5_402.sortedTerminatedFactors
        (S5_402.blockBearingFactors rest)).map
          reverseTerminatedFactor).Perm
      (List.map reverseTerminatedFactor
        (S5_402.blockBearingFactors rest).reverse)
  have sortedPermutation :=
    (S5_402.sortedTerminatedFactors_perm
      (S5_402.blockBearingFactors rest)).map
        reverseTerminatedFactor
  have reversePermutation :=
    (reverse_perm_self
      (S5_402.blockBearingFactors rest)).symm.map
        reverseTerminatedFactor
  exact sortedPermutation.trans reversePermutation

/-- Rendering the retained tail in source orientation only permutes the
rendered block-bearing nonfinal source factors. -/
theorem forwardRetainedFactorWords_perm_blockBearingNonfinalWords
    (word : Word Nat) (first : List Nat × Nat)
    (rest : List (List Nat × Nat))
    (shape : reversedRawFactors word.toList = first :: rest) :
    (((reversedRetainedFactors word).drop 1).map
        forwardFactorWord).Perm
      ((blockBearingNonfinalFactors word.toList).map
        renderSuccessorFactor) := by
  have translatedPermutation :=
    (forwardRetainedTail_perm_blockBearingNonfinal
      word first rest shape).map renderSuccessorFactor
  simpa [List.map_map, forwardFactorWord, Function.comp_def] using
    translatedPermutation

/-- Thus the canonical sorting step is exactly sorting the rendered
block-bearing nonfinal source factors.  This is the pure sorting bridge used
by the later derivational normalization. -/
theorem canonicalNonfinalFactorWords_eq_sorted_blockBearingNonfinal
    (word : Word Nat) (first : List Nat × Nat)
    (rest : List (List Nat × Nat))
    (shape : reversedRawFactors word.toList = first :: rest) :
    canonicalNonfinalFactorWords word =
      S5_107.sortedSimpleBlocks
        ((blockBearingNonfinalFactors word.toList).map
          renderSuccessorFactor) := by
  have renderedPermutation :=
    forwardRetainedFactorWords_perm_blockBearingNonfinalWords
      word first rest shape
  have sortedEquality :=
    S5_107.sortedSimpleBlocks_eq_of_perm renderedPermutation
  simpa [canonicalNonfinalFactorWords,
    reversedRetainedFactors_eq_of_raw_cons word first rest shape] using
      sortedEquality

/-! ## Complete global square-bank inventory -/

/-- Deduplicating all raw reversed markers and sorting them yields exactly the
global canonical square-marker bank.  The raw first/final marker is included. -/
theorem rawDistinctMarkers_perm_canonicalSquareMarkers
    (word : Word Nat) :
    (S5_107.distinctLetters
        (S5_107.terminatedFactorMarkers
          (reversedRawFactors word.toList))).Perm
      (canonicalSquareMarkers word) := by
  simpa [reversedRawFactors, canonicalSquareMarkers,
    Word.toList_reverse] using
      (S5_107.distinctTerminatedMarkers_perm_sortedMultipleLetters
        word.reverse.toList)

/-! ## One packaged non-simple inventory -/

/-- All pure data needed by the later normalization, with the raw first factor
serving as the fixed final controller. -/
structure ReversedInventoryDecomposition (word : Word Nat) where
  first : List Nat × Nat
  rest : List (List Nat × Nat)
  rawShape : reversedRawFactors word.toList = first :: rest
  retainedShape :
    reversedRetainedFactors word =
      first :: S5_402.sortedTerminatedFactors
        (S5_402.blockBearingFactors rest)
  sourceShape :
    successorFactors word.toList =
      rest.reverse.map reverseTerminatedFactor ++
        [reverseTerminatedFactor first]
  blockBearingShape :
    blockBearingNonfinalFactors word.toList =
      (S5_402.blockBearingFactors rest).reverse.map
        reverseTerminatedFactor
  markerOnlyShape :
    markerOnlyNonfinalFactors word.toList =
      (S5_402.markerOnlyFactors rest).reverse.map
        reverseTerminatedFactor
  retainedTailPermutation :
    (((reversedRetainedFactors word).drop 1).map
        reverseTerminatedFactor).Perm
      (blockBearingNonfinalFactors word.toList)

/-- Every non-simple word has a packaged reversed inventory decomposition. -/
theorem exists_reversedInventoryDecomposition
    (word : Word Nat)
    (nonSimple : ∃ marker, 2 ≤ word.toList.count marker) :
    Nonempty (ReversedInventoryDecomposition word) := by
  obtain ⟨marker, multiple⟩ := nonSimple
  have reverseMultiple :
      2 ≤ word.toList.reverse.count marker := by
    simpa only [List.count_reverse] using multiple
  have markerMember :
      marker ∈ S5_107.terminatedFactorMarkers
        (reversedRawFactors word.toList) := by
    exact
      (S5_107.mem_terminatedFactorMarkers_iff
        marker word.toList.reverse).mpr reverseMultiple
  have rawNonempty : reversedRawFactors word.toList ≠ [] := by
    intro empty
    rw [empty] at markerMember
    simpa [S5_107.terminatedFactorMarkers] using markerMember
  obtain ⟨first, rest, shape⟩ :=
    List.exists_cons_of_ne_nil rawNonempty
  exact ⟨{
    first := first
    rest := rest
    rawShape := shape
    retainedShape :=
      reversedRetainedFactors_eq_of_raw_cons
        word first rest shape
    sourceShape :=
      successorFactors_eq_of_reversedRaw_cons
        word.toList first rest shape
    blockBearingShape :=
      blockBearingNonfinalFactors_eq_of_reversedRaw_cons
        word.toList first rest shape
    markerOnlyShape :=
      markerOnlyNonfinalFactors_eq_of_reversedRaw_cons
        word.toList first rest shape
    retainedTailPermutation :=
      forwardRetainedTail_perm_blockBearingNonfinal
        word first rest shape }⟩

end SemigroupBasis.CoRoots.Order6LeeZhang23_9InventoryBridge
