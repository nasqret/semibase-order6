import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedOrderedSquareForm

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPerfect

open BinaryPowers FactorContexts OccurrenceWitnesses MarkedZones SquareCoalescing
  MaximalFactors MaximalSquareCover CanonicalSquareCover OrderedSquareForm

/-- The paper's non-vacuous two-letter perfect factorization. There is one more
square than separators. Separators are nonempty Words; only exterior contexts
may be empty. The chosen order x,y is alphabetic when x < y. -/
def Perfect (x y : Nat) (word : Word Nat) : Prop :=
  ∃ leading trailing : List Nat, ∃ gaps : List (Word Nat),
    Outside x y leading ∧ Outside x y trailing ∧
    (∀ separator ∈ gaps, Outside x y separator.toList) ∧
    word = Context.frame (contextWord leading) (contextWord trailing)
      (chain (square (Word.singleton x) (Word.singleton y)) (gaps.map Word.toList))

theorem framed_block_member (block : Word Nat) (gaps : List (Word Nat))
    (leading trailing : List Nat) :
    block ∈ framedPieces block gaps leading trailing := by
  exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))

/-- The factorization is actual and has at least one positive component. -/
theorem perfect_factorization (x y : Nat) (word : Word Nat) (perfect : Perfect x y word) :
    ∃ pieces : List (Word Nat),
      flatten pieces = word.toList ∧ Good (binaryTag x y) pieces ∧
      (∀ piece ∈ pieces, piece.toList ≠ []) ∧
      square (Word.singleton x) (Word.singleton y) ∈ pieces ∧
      (∀ piece ∈ pieces, binaryTag x y piece.head = true →
        piece = square (Word.singleton x) (Word.singleton y)) := by
  obtain ⟨leading, trailing, gaps, headClean, tailClean, clean, equal⟩ := perfect
  refine ⟨framedPieces (square (Word.singleton x) (Word.singleton y)) gaps leading trailing,
    ?_, framedPieces_good x y _ (square_head_tag x y) (square_constant x y)
      gaps leading trailing headClean tailClean clean, ?_,
    framed_block_member _ gaps leading trailing, ?_⟩
  · exact (flatten_framedPieces _ gaps leading trailing).trans
      (congrArg Word.toList equal.symm)
  · intro piece member
    exact piece_nonempty piece
  · intro piece member positive
    exact framedPieces_positive x y _ gaps leading trailing
      headClean tailClean clean piece member positive

theorem perfect_cover (x y : Nat) (word : Word Nat) (perfect : Perfect x y word) :
    SquareCover x y word := by
  obtain ⟨pieces, letters, good, nonempty, squareMember, squares⟩ :=
    perfect_factorization x y word perfect
  exact ⟨pieces, letters, good, nonempty, squares⟩

theorem perfect_canonical (x y : Nat) (word : Word Nat) (perfect : Perfect x y word) :
    CanonicalSquareForm x y word :=
  cover_canonical x y word (perfect_cover x y word perfect)

theorem perfect_has_canonical_square (x y : Nat) (word : Word Nat)
    (perfect : Perfect x y word) :
    square (Word.singleton x) (Word.singleton y) ∈
      decompose (binaryTag x y) word.toList := by
  obtain ⟨pieces, letters, good, nonempty, squareMember, squares⟩ :=
    perfect_factorization x y word perfect
  have canonical : decompose (binaryTag x y) word.toList = pieces := by
    rw [← letters]
    exact decompose_flatten_good (binaryTag x y) pieces good
  rw [canonical]
  exact squareMember

theorem perfect_literal_square_factor (x y : Nat) (word : Word Nat)
    (perfect : Perfect x y word) :
    ∃ before after : List Nat, word.toList = before ++ ([x, y, x, y] ++ after) := by
  obtain ⟨before, after, split, framed, uniform⟩ :=
    factor_as_frame (binaryTag x y) word (square (Word.singleton x) (Word.singleton y))
      (perfect_has_canonical_square x y word perfect)
  refine ⟨flatten before, flatten after, ?_⟩
  exact (congrArg Word.toList framed).trans (frame_of_lists_toList _ _ _)

/-- Both marked letters really are non-simple in the resulting perfect word. -/
theorem perfect_repeated (x y : Nat) (word : Word Nat) (different : x ≠ y)
    (perfect : Perfect x y word) :
    2 ≤ word.toList.count x ∧ 2 ≤ word.toList.count y := by
  obtain ⟨before, after, split⟩ := perfect_literal_square_factor x y word perfect
  have countX : ([x, y, x, y] : List Nat).count x = 2 := by
    simp only [List.count_cons_self, List.count_cons_of_ne (Ne.symm different), List.count_nil]
  have countY : ([x, y, x, y] : List Nat).count y = 2 := by
    simp only [List.count_cons_self, List.count_cons_of_ne different, List.count_nil]
  constructor
  · rw [split, List.count_append, List.count_append, countX]
    omega
  · rw [split, List.count_append, List.count_append, countY]
    omega

theorem coalesced_perfect (x y : Nat) (before middle after : List Nat) :
    Perfect x y (coalescedSquareBlocks x y before middle after) := by
  refine ⟨(encodeLeft x y before).1, (encodeRight x y after).2,
    gapWords (actualGaps x y before middle after),
    (coalesced_boundaries x y before middle after).1,
    (coalesced_boundaries x y before middle after).2.1, ?_, ?_⟩
  · intro separator member
    exact actual_gaps_outside x y before middle after separator.toList
      (gapWords_member (actualGaps x y before middle after) separator member)
  · rw [gapWords_lists]
    rfl

theorem reoriented_perfect (x y : Nat) (before middle after : List Nat) :
    Perfect x y (reorientedSquareBlocks x y before middle after) := by
  refine ⟨(encodeLeft y x before).1, (encodeRight y x after).2,
    gapWords (actualGaps y x before middle after),
    outside_swap x y _ (coalesced_boundaries y x before middle after).1,
    outside_swap x y _ (coalesced_boundaries y x before middle after).2.1, ?_, ?_⟩
  · intro separator member
    exact outside_swap x y _ (actual_gaps_outside y x before middle after separator.toList
      (gapWords_member (actualGaps y x before middle after) separator member))
  · rw [gapWords_lists]
    rfl

theorem related_perfect (x y : Nat) (word : Word Nat)
    (different : x ≠ y) (xRepeated : 2 ≤ word.toList.count x)
    (yRepeated : 2 ≤ word.toList.count y) (related : PairRelated x y word.toList) :
    ∃ normal : Word Nat, Derives basis word normal ∧ Perfect x y normal := by
  rcases related_coalesced x y word different xRepeated yRepeated related with forward | backward
  · obtain ⟨before, middle, after, step⟩ := forward
    exact ⟨coalescedSquareBlocks x y before middle after, step,
      coalesced_perfect x y before middle after⟩
  · obtain ⟨before, middle, after, step⟩ := backward
    exact ⟨reorientedSquareBlocks x y before middle after,
      step.trans (coalesced_reorient x y before middle after),
      reoriented_perfect x y before middle after⟩

theorem pairRelated_swap (x y : Nat) (letters : List Nat)
    (related : PairRelated x y letters) : PairRelated y x letters := by
  rcases related with first | second | third | fourth
  · exact Or.inr (Or.inl first)
  · exact Or.inl second
  · exact Or.inr (Or.inr (Or.inr third))
  · exact Or.inr (Or.inr (Or.inl fourth))

/-- Lemma19.2, with the alphabetic square represented by min/max. The conclusion
has an actual non-vacuous perfect factorization, not merely a conditional
property of possibly absent factors. No length/rank/window bound is assumed. -/
theorem lemma19_2 (x y : Nat) (word : Word Nat)
    (different : x ≠ y) (xRepeated : 2 ≤ word.toList.count x)
    (yRepeated : 2 ≤ word.toList.count y) (related : PairRelated x y word.toList) :
    ∃ normal : Word Nat,
      Derives basis word normal ∧ Perfect (min x y) (max x y) normal := by
  by_cases ordered : x < y
  · simpa only [Nat.min_eq_left (Nat.le_of_lt ordered), Nat.max_eq_right (Nat.le_of_lt ordered)] using
      related_perfect x y word different xRepeated yRepeated related
  · have reverse : y < x := by omega
    simpa only [Nat.min_eq_right (Nat.le_of_lt reverse), Nat.max_eq_left (Nat.le_of_lt reverse)] using
      related_perfect y x word (Ne.symm different) yRepeated xRepeated
        (pairRelated_swap x y word.toList related)

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPerfect

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPerfect.framed_block_member
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPerfect.perfect_factorization
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPerfect.perfect_cover
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPerfect.perfect_canonical
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPerfect.perfect_has_canonical_square
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPerfect.perfect_literal_square_factor
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPerfect.perfect_repeated
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPerfect.coalesced_perfect
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPerfect.reoriented_perfect
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPerfect.related_perfect
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPerfect.pairRelated_swap
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.BinaryPerfect.lemma19_2
