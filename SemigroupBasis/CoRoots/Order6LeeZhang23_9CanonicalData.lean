import SemigroupBasis.CoRoots.Order6LeeZhang23_9Invariant
import SemigroupBasis.CoRoots.Order6LeeZhang23_9Scanner
import SemigroupBasis.CoRoots.S5_107MarkerCombinatorics
import SemigroupBasis.CoRoots.S5_402SignatureBridge

/-!
# Lee--Zhang Proposition 23.9 canonical data

This file is combinatorial.  It records the literal nonfinal/final split of
the successor scanner and defines the deterministic data used by the later
simple-endpoint normalization proof.  The global square bank is computed
from the complete multiple-letter support; in particular it is not computed
from only the retained or nonfinal factors.

The equality proofs below use only the pure scanner/signature declarations
from the imported modules.  No derivation or fixed-basis theorem is invoked.
-/

namespace SemigroupBasis.CoRoots.Order6LeeZhang23_9CanonicalData

open SemigroupBasis
open Order6LeeZhang23_9Syntax
open Order6LeeZhang23_9Invariant
open Order6LeeZhang23_9Scanner

/-! ## Literal nonfinal/final split of the source scanner -/

/-- Cut immediately before the final successor factor, when one exists. -/
def finalFactorCut (letters : List Nat) : Nat :=
  (successorFactors letters).length - 1

/-- Every source successor factor except the final one. -/
def nonfinalSuccessorFactors
    (letters : List Nat) : List SuccessorFactor :=
  (successorFactors letters).take (finalFactorCut letters)

/-- The final successor factor as a list of length at most one.  Keeping the
list presentation makes the empty (all-simple) case uniform. -/
def finalSuccessorFactors
    (letters : List Nat) : List SuccessorFactor :=
  (successorFactors letters).drop (finalFactorCut letters)

/-- The cut is a literal decomposition of the complete source scan. -/
theorem nonfinal_append_final_successorFactors
    (letters : List Nat) :
    nonfinalSuccessorFactors letters ++
        finalSuccessorFactors letters =
      successorFactors letters := by
  exact List.take_append_drop
    (finalFactorCut letters) (successorFactors letters)

/-- The final residual contains at most one factor. -/
theorem finalSuccessorFactors_length_le_one
    (letters : List Nat) :
    (finalSuccessorFactors letters).length ≤ 1 := by
  simp only [finalSuccessorFactors, finalFactorCut,
    List.length_drop]
  omega

/-- Reconstruction with the nonfinal/final boundary exposed. -/
theorem reconstruct_nonfinal_final (letters : List Nat) :
    initialSimpleBlock letters ++
        renderSuccessorFactors (nonfinalSuccessorFactors letters) ++
        renderSuccessorFactors (finalSuccessorFactors letters) =
      letters := by
  calc
    initialSimpleBlock letters ++
          renderSuccessorFactors (nonfinalSuccessorFactors letters) ++
          renderSuccessorFactors (finalSuccessorFactors letters) =
        initialSimpleBlock letters ++
          (renderSuccessorFactors (nonfinalSuccessorFactors letters) ++
            renderSuccessorFactors (finalSuccessorFactors letters)) :=
      List.append_assoc _ _ _
    _ = initialSimpleBlock letters ++
        renderSuccessorFactors
          (nonfinalSuccessorFactors letters ++
            finalSuccessorFactors letters) :=
      congrArg (fun tail => initialSimpleBlock letters ++ tail)
        (renderSuccessorFactors_append
          (nonfinalSuccessorFactors letters)
          (finalSuccessorFactors letters)).symm
    _ = initialSimpleBlock letters ++
        renderSuccessorFactors (successorFactors letters) := by
      rw [nonfinal_append_final_successorFactors]
    _ = letters := reconstruct letters

/-! ## Marker-only and block-bearing nonfinal factors -/

/-- Nonfinal factors carrying a nonempty simple successor block. -/
def blockBearingNonfinalFactors
    (letters : List Nat) : List SuccessorFactor :=
  (nonfinalSuccessorFactors letters).filter
    fun factor => decide (factor.2 ≠ [])

/-- Nonfinal factors carrying no simple successor block. -/
def markerOnlyNonfinalFactors
    (letters : List Nat) : List SuccessorFactor :=
  (nonfinalSuccessorFactors letters).filter
    fun factor => decide (factor.2 = [])

/-- Stable partitioning by block emptiness only permutes the nonfinal list. -/
theorem blockBearing_append_markerOnly_nonfinal_perm
    (letters : List Nat) :
    (blockBearingNonfinalFactors letters ++
        markerOnlyNonfinalFactors letters).Perm
      (nonfinalSuccessorFactors letters) := by
  simpa [blockBearingNonfinalFactors,
    markerOnlyNonfinalFactors] using
    (List.filter_append_perm
      (fun factor : SuccessorFactor =>
        decide (factor.2 ≠ []))
      (nonfinalSuccessorFactors letters))

/-- Every retained nonfinal factor has a nonempty successor block. -/
theorem blockBearingNonfinal_block_ne_nil
    (letters : List Nat) :
    ∀ factor ∈ blockBearingNonfinalFactors letters,
      factor.2 ≠ [] := by
  intro factor member
  have tested := (List.mem_filter.mp member).2
  exact of_decide_eq_true tested

/-- Every discarded marker-only nonfinal factor has an empty block. -/
theorem markerOnlyNonfinal_block_eq_nil
    (letters : List Nat) :
    ∀ factor ∈ markerOnlyNonfinalFactors letters,
      factor.2 = [] := by
  intro factor member
  have tested := (List.mem_filter.mp member).2
  exact of_decide_eq_true tested

/-! ## Pure lexicographic sorting of successor factors -/

/-- Compare successor factors by their complete rendered words.  Since a
rendered factor is `marker :: block`, this is marker-first lexicographic
order, including a deterministic block tie-breaker. -/
def successorFactorLe
    (left right : SuccessorFactor) : Bool :=
  decide
    (renderSuccessorFactor left ≤ renderSuccessorFactor right)

/-- Sort an arbitrary complete successor-factor list. -/
def sortedSuccessorFactors
    (factors : List SuccessorFactor) : List SuccessorFactor :=
  factors.mergeSort successorFactorLe

/-- The requested whole-scan lexicographic projection. -/
def sortedWholeSuccessorFactors
    (letters : List Nat) : List SuccessorFactor :=
  sortedSuccessorFactors (successorFactors letters)

private theorem renderSuccessorFactor_injective :
    Function.Injective renderSuccessorFactor := by
  intro left right equal
  rcases left with ⟨leftMarker, leftBlock⟩
  rcases right with ⟨rightMarker, rightBlock⟩
  simpa [renderSuccessorFactor] using equal

private theorem successorFactorLe_transitive
    (left middle right : SuccessorFactor)
    (leftMiddle : successorFactorLe left middle = true)
    (middleRight : successorFactorLe middle right = true) :
    successorFactorLe left right = true := by
  unfold successorFactorLe at leftMiddle middleRight ⊢
  exact decide_eq_true <|
    List.le_trans
      (of_decide_eq_true leftMiddle)
      (of_decide_eq_true middleRight)

private theorem successorFactorLe_total
    (left right : SuccessorFactor) :
    (successorFactorLe left right ||
      successorFactorLe right left) = true := by
  rcases List.le_total
      (renderSuccessorFactor left)
      (renderSuccessorFactor right) with leftRight | rightLeft
  · simp [successorFactorLe, leftRight]
  · simp [successorFactorLe, rightLeft]

private theorem successorFactorLe_antisymm
    {left right : SuccessorFactor}
    (leftRight : successorFactorLe left right = true)
    (rightLeft : successorFactorLe right left = true) :
    left = right := by
  unfold successorFactorLe at leftRight rightLeft
  apply renderSuccessorFactor_injective
  exact List.le_antisymm
    (of_decide_eq_true leftRight)
    (of_decide_eq_true rightLeft)

/-- Sorted successor factors are pairwise lexicographically ordered. -/
theorem sortedSuccessorFactors_pairwise
    (factors : List SuccessorFactor) :
    (sortedSuccessorFactors factors).Pairwise
      (fun left right => successorFactorLe left right = true) := by
  simpa [sortedSuccessorFactors] using
    List.pairwise_mergeSort
      successorFactorLe_transitive successorFactorLe_total factors

/-- Sorting preserves the complete factor multiset. -/
theorem sortedSuccessorFactors_perm
    (factors : List SuccessorFactor) :
    (sortedSuccessorFactors factors).Perm factors := by
  exact List.mergeSort_perm _ _

/-- Equal factor multisets have literally equal sorted representatives. -/
theorem sortedSuccessorFactors_eq_of_perm
    {left right : List SuccessorFactor}
    (permutation : left.Perm right) :
    sortedSuccessorFactors left = sortedSuccessorFactors right := by
  have sortedPermutation :
      (sortedSuccessorFactors left).Perm
        (sortedSuccessorFactors right) :=
    (List.mergeSort_perm _ _).trans <|
      permutation.trans (List.mergeSort_perm _ _).symm
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftRight rightLeft =>
      successorFactorLe_antisymm leftRight rightLeft)
    (sortedSuccessorFactors_pairwise left)
    (sortedSuccessorFactors_pairwise right)
    sortedPermutation

/-! ## Signature-determined retained data -/

/-- The established retained factor list on the reversed word.  Its first
factor is the fixed final successor factor in the source orientation; its
tail contains exactly the block-bearing nonfinal factors. -/
def reversedRetainedFactors
    (word : Word Nat) : List (List Nat × Nat) :=
  S5_402.retainedSortedFactors word.reverse.toList

/-- Translate a reversed terminated factor to its complete source-oriented
successor-factor word. -/
def forwardFactorWord
    (factor : List Nat × Nat) : List Nat :=
  renderSuccessorFactor (reverseTerminatedFactor factor)

@[simp]
theorem forwardFactorWord_mk
    (block : List Nat) (marker : Nat) :
    forwardFactorWord (block, marker) = marker :: block.reverse :=
  rfl

/-- The literal initial simple block in source orientation. -/
def canonicalInitialBlock (word : Word Nat) : List Nat :=
  initialSimpleBlock word.toList

/-- Complete global multiple-marker bank, sorted and deduplicated.  This is
the support of *all* raw successor markers, including the final factor and
marker-only factors. -/
def canonicalSquareMarkers (word : Word Nat) : List Nat :=
  S5_107.sortedMultipleLetters word.reverse.toList

/-- Marker-first lexicographically sorted block-bearing nonfinal residuals. -/
def canonicalNonfinalFactorWords
    (word : Word Nat) : List (List Nat) :=
  match reversedRetainedFactors word with
  | [] => []
  | _ :: rest =>
      S5_107.sortedSimpleBlocks (rest.map forwardFactorWord)

/-- The fixed final residual in source orientation. -/
def canonicalFinalFactorWord (word : Word Nat) : List Nat :=
  match reversedRetainedFactors word with
  | [] => []
  | first :: _ => forwardFactorWord first

/-- The four deterministic components of the simple-endpoint normal data. -/
structure CanonicalData where
  initialBlock : List Nat
  squareMarkers : List Nat
  nonfinalFactorWords : List (List Nat)
  finalFactorWord : List Nat

/-- Compute all deterministic canonical components. -/
def canonicalData (word : Word Nat) : CanonicalData where
  initialBlock := canonicalInitialBlock word
  squareMarkers := canonicalSquareMarkers word
  nonfinalFactorWords := canonicalNonfinalFactorWords word
  finalFactorWord := canonicalFinalFactorWord word

/-- Render canonical data as a list. -/
def CanonicalData.render (data : CanonicalData) : List Nat :=
  data.initialBlock ++
    S5_107.renderMultipleSquares data.squareMarkers ++
    data.nonfinalFactorWords.flatten ++
    data.finalFactorWord

/-- Initial block, global square bank, sorted block-bearing nonfinal
residuals, and the fixed final residual. -/
def canonicalList (word : Word Nat) : List Nat :=
  (canonicalData word).render

/-- Total list-to-word wrapper; the original head is only a fallback for an
empty list and is preserved by the published signature. -/
def wordOfListOr (fallback : Nat) : List Nat → Word Nat
  | [] => Word.singleton fallback
  | head :: tail => ⟨head, tail⟩

/-- Word-level deterministic canonical data. -/
def canonicalWord (word : Word Nat) : Word Nat :=
  wordOfListOr word.head (canonicalList word)

/-! ## Exact data uniqueness from the Lee--Zhang signature -/

/-- The sorted global square bank has exactly the complete raw scanner
marker support. -/
theorem mem_canonicalSquareMarkers_iff_successorMarker
    (word : Word Nat) (marker : Nat) :
    marker ∈ canonicalSquareMarkers word ↔
      marker ∈ successorMarkers word.toList := by
  rw [mem_successorMarkers_iff]
  simpa [canonicalSquareMarkers, Word.toList_reverse,
    List.count_reverse] using
    (S5_107.sortedMultipleLetters_mem_iff
      marker word.reverse.toList)

/-- The global bank contains no duplicate marker. -/
theorem canonicalSquareMarkers_nodup (word : Word Nat) :
    (canonicalSquareMarkers word).Nodup := by
  exact S5_107.sortedMultipleLetters_nodup word.reverse.toList

/-- The global bank is monotonically sorted. -/
theorem canonicalSquareMarkers_pairwise (word : Word Nat) :
    (canonicalSquareMarkers word).Pairwise (· ≤ ·) := by
  exact S5_107.sortedMultipleLetters_pairwise word.reverse.toList

/-- The source initial simple block is determined literally by the compact
Lee--Zhang signature. -/
theorem canonicalInitialBlock_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameLeeZhang23_9Signature left right) :
    canonicalInitialBlock left = canonicalInitialBlock right := by
  have finalEq :
      S5_107.terminatedFinalBlock left.reverse.toList =
        S5_107.terminatedFinalBlock right.reverse.toList := by
    rw [← S5_402.terminatedFinalBlock_eq_s5_107,
      ← S5_402.terminatedFinalBlock_eq_s5_107]
    exact S5_402.terminatedFinalBlock_eq_of_sameSignature
      same.reversedS5_402
  simpa [canonicalInitialBlock, initialSimpleBlock,
    Word.toList_reverse] using congrArg List.reverse finalEq

/-- The complete retained reversed factor inventory is signature data. -/
theorem reversedRetainedFactors_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameLeeZhang23_9Signature left right) :
    reversedRetainedFactors left = reversedRetainedFactors right := by
  exact S5_402.retainedSortedFactors_eq_of_sameSignature
    same.reversedS5_402

/-- The complete global square bank is signature data. -/
theorem canonicalSquareMarkers_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameLeeZhang23_9Signature left right) :
    canonicalSquareMarkers left = canonicalSquareMarkers right := by
  exact S5_402.sortedMultipleLetters_eq_of_sameSignature
    same.reversedS5_402

/-- Sorting the forward-rendered retained tail produces equal nonfinal data. -/
theorem canonicalNonfinalFactorWords_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameLeeZhang23_9Signature left right) :
    canonicalNonfinalFactorWords left =
      canonicalNonfinalFactorWords right := by
  unfold canonicalNonfinalFactorWords
  rw [reversedRetainedFactors_eq_of_sameSignature same]

/-- The fixed final residual is determined literally by the signature. -/
theorem canonicalFinalFactorWord_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameLeeZhang23_9Signature left right) :
    canonicalFinalFactorWord left =
      canonicalFinalFactorWord right := by
  unfold canonicalFinalFactorWord
  rw [reversedRetainedFactors_eq_of_sameSignature same]

/-- All four canonical-data components are literally signature-determined. -/
theorem canonicalData_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameLeeZhang23_9Signature left right) :
    canonicalData left = canonicalData right := by
  unfold canonicalData
  rw [canonicalInitialBlock_eq_of_sameSignature same,
    canonicalSquareMarkers_eq_of_sameSignature same,
    canonicalNonfinalFactorWords_eq_of_sameSignature same,
    canonicalFinalFactorWord_eq_of_sameSignature same]

/-- Compact-signature equality gives literal canonical-list equality. -/
theorem canonicalList_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameLeeZhang23_9Signature left right) :
    canonicalList left = canonicalList right := by
  exact congrArg CanonicalData.render
    (canonicalData_eq_of_sameSignature same)

/-- The explicit published six-coordinate signature gives the same literal
canonical-list equality. -/
theorem canonicalList_eq_of_samePublishedSignature
    {left right : Word Nat}
    (same : SamePublishedLeeZhang23_9Signature left right) :
    canonicalList left = canonicalList right := by
  exact canonicalList_eq_of_sameSignature
    (sameLeeZhang23_9Signature_of_published same)

/-- Word-level canonical representatives agree under the compact signature. -/
theorem canonicalWord_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameLeeZhang23_9Signature left right) :
    canonicalWord left = canonicalWord right := by
  unfold canonicalWord
  rw [same.head, canonicalList_eq_of_sameSignature same]

end SemigroupBasis.CoRoots.Order6LeeZhang23_9CanonicalData
