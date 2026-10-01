import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedCanonicalSquareCover

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OrderedSquareForm

open CrossFactor CrossSweep BinaryPowers FactorContexts OccurrenceWitnesses
  MarkedZones SquareCoalescing MaximalFactors MaximalSquareCover CanonicalSquareCover

/-- A block derivation lifts through every actual separator, including empty ones. -/
theorem chain_derives {left right : Word Nat} (step : Derives basis left right)
    (gaps : List (List Nat)) :
    Derives basis (chain left gaps) (chain right gaps) := by
  induction gaps with
  | nil => exact step
  | cons letters rest ih =>
      change Derives basis
        (gap left (contextWord letters) ++ chain left rest)
        (gap right (contextWord letters) ++ chain right rest)
      exact (Derives.appendRight (gap_derives step (contextWord letters))
        (chain left rest)).trans
        (Derives.prepend (gap right (contextWord letters)) ih)

theorem framed_chain_derives {left right : Word Nat}
    (step : Derives basis left right) (gaps : List (List Nat))
    (before after : List Nat) :
    Derives basis
      (Context.frame (contextWord before) (contextWord after) (chain left gaps))
      (Context.frame (contextWord before) (contextWord after) (chain right gaps)) :=
  Context.frame_derives (chain_derives step gaps) (contextWord before) (contextWord after)

theorem outside_swap (x y : Nat) (letters : List Nat)
    (clean : Outside y x letters) : Outside x y letters := by
  intro letter member
  exact ⟨(clean letter member).2, (clean letter member).1⟩

theorem binaryTag_swap (x y letter : Nat) :
    binaryTag x y letter = binaryTag y x letter := by
  simp only [binaryTag, or_comm]

/-- Keep the y/x codec verbatim; replace only its square by the chosen x/y square. -/
def reorientedSquareBlocks (x y : Nat) (before middle after : List Nat) : Word Nat :=
  Context.frame (contextWord (encodeLeft y x before).1)
    (contextWord (encodeRight y x after).2)
    (chain (square (Word.singleton x) (Word.singleton y))
      (keepNonempty (actualGaps y x before middle after)))

def reorientedPieces (x y : Nat) (before middle after : List Nat) : List (Word Nat) :=
  framedPieces (square (Word.singleton x) (Word.singleton y))
    (gapWords (actualGaps y x before middle after))
    (encodeLeft y x before).1 (encodeRight y x after).2

theorem coalesced_reorient (x y : Nat) (before middle after : List Nat) :
    Derives basis (coalescedSquareBlocks y x before middle after)
      (reorientedSquareBlocks x y before middle after) :=
  framed_chain_derives (square_comm (Word.singleton y) (Word.singleton x))
    (keepNonempty (actualGaps y x before middle after))
    (encodeLeft y x before).1 (encodeRight y x after).2

theorem reorientedPieces_flatten (x y : Nat) (before middle after : List Nat) :
    flatten (reorientedPieces x y before middle after) =
      (reorientedSquareBlocks x y before middle after).toList := by
  unfold reorientedPieces
  rw [flatten_framedPieces, gapWords_lists]
  rfl

theorem reorientedPieces_good (x y : Nat) (before middle after : List Nat) :
    Good (binaryTag x y) (reorientedPieces x y before middle after) := by
  apply framedPieces_good x y _ (square_head_tag x y) (square_constant x y)
  · exact outside_swap x y _ (coalesced_boundaries y x before middle after).1
  · exact outside_swap x y _ (coalesced_boundaries y x before middle after).2.1
  · intro piece member
    exact outside_swap x y _ (actual_gaps_outside y x before middle after piece.toList
      (gapWords_member (actualGaps y x before middle after) piece member))

theorem reorientedPieces_positive (x y : Nat) (before middle after : List Nat)
    (piece : Word Nat) (member : piece ∈ reorientedPieces x y before middle after)
    (positive : binaryTag x y piece.head = true) :
    piece = square (Word.singleton x) (Word.singleton y) := by
  have headClean : Outside x y (encodeLeft y x before).1 :=
    outside_swap x y _ (coalesced_boundaries y x before middle after).1
  have tailClean : Outside x y (encodeRight y x after).2 :=
    outside_swap x y _ (coalesced_boundaries y x before middle after).2.1
  apply framedPieces_positive x y _ _ _ _ headClean tailClean _ piece member positive
  intro part inside
  exact outside_swap x y _ (actual_gaps_outside y x before middle after part.toList
    (gapWords_member (actualGaps y x before middle after) part inside))

theorem reoriented_maximal_square_cover (x y : Nat) (before middle after : List Nat) :
    SquareCover x y (reorientedSquareBlocks x y before middle after) := by
  refine ⟨reorientedPieces x y before middle after,
    reorientedPieces_flatten x y before middle after,
    reorientedPieces_good x y before middle after, ?_, ?_⟩
  · intro piece member
    exact piece_nonempty piece
  · intro piece member positive
    exact reorientedPieces_positive x y before middle after piece member positive

theorem canonical_reorientedPieces (x y : Nat) (before middle after : List Nat) :
    decompose (binaryTag x y) (reorientedSquareBlocks x y before middle after).toList =
      reorientedPieces x y before middle after := by
  rw [← reorientedPieces_flatten x y before middle after]
  exact decompose_flatten_good (binaryTag x y) _
    (reorientedPieces_good x y before middle after)

theorem reoriented_canonical (x y : Nat) (before middle after : List Nat) :
    CanonicalSquareForm x y (reorientedSquareBlocks x y before middle after) :=
  cover_canonical x y _ (reoriented_maximal_square_cover x y before middle after)

/-- The original C1/C2 hypotheses now yield ONE prescribed square orientation. -/
theorem related_ordered_square_cover (x y : Nat) (word : Word Nat)
    (different : x ≠ y) (xRepeated : 2 ≤ word.toList.count x)
    (yRepeated : 2 ≤ word.toList.count y) (related : PairRelated x y word.toList) :
    ∃ normal : Word Nat, Derives basis word normal ∧ SquareCover x y normal := by
  rcases related_coalesced x y word different xRepeated yRepeated related with forward | backward
  · obtain ⟨before, middle, after, step⟩ := forward
    exact ⟨coalescedSquareBlocks x y before middle after, step,
      coalesced_maximal_square_cover x y before middle after⟩
  · obtain ⟨before, middle, after, step⟩ := backward
    exact ⟨reorientedSquareBlocks x y before middle after,
      step.trans (coalesced_reorient x y before middle after),
      reoriented_maximal_square_cover x y before middle after⟩

/-- Every canonical binary factor is the chosen square, with no orientation disjunction.
This binary normalization theorem is not full Lemma19.2/19.3 or BasisFor. -/
theorem related_ordered_canonical_square_form (x y : Nat) (word : Word Nat)
    (different : x ≠ y) (xRepeated : 2 ≤ word.toList.count x)
    (yRepeated : 2 ≤ word.toList.count y) (related : PairRelated x y word.toList) :
    ∃ normal : Word Nat, Derives basis word normal ∧ CanonicalSquareForm x y normal := by
  obtain ⟨normal, step, cover⟩ :=
    related_ordered_square_cover x y word different xRepeated yRepeated related
  exact ⟨normal, step, cover_canonical x y normal cover⟩

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OrderedSquareForm

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OrderedSquareForm.chain_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OrderedSquareForm.framed_chain_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OrderedSquareForm.outside_swap
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OrderedSquareForm.binaryTag_swap
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OrderedSquareForm.coalesced_reorient
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OrderedSquareForm.reorientedPieces_flatten
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OrderedSquareForm.reorientedPieces_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OrderedSquareForm.reorientedPieces_positive
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OrderedSquareForm.reoriented_maximal_square_cover
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OrderedSquareForm.canonical_reorientedPieces
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OrderedSquareForm.reoriented_canonical
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OrderedSquareForm.related_ordered_square_cover
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.OrderedSquareForm.related_ordered_canonical_square_form
