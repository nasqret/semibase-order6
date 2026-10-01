import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSquareCoalescing

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover

open CrossFactor CrossSweep CrossLeftSweep AnchorPropagation MiddleSweep
  BinaryPowers SquareAlgebra PerfectSweeps FactorContexts OccurrenceWitnesses
  MarkedZones SquareCoalescing MaximalFactors

/-- Empty contexts contribute no factor, never an empty semigroup word. -/
def optionalPieces : List Nat → List (Word Nat)
  | [] => []
  | first :: later => [⟨first, later⟩]

/-- Retain exactly the nonempty separators as genuine words. -/
def gapWords : List (List Nat) → List (Word Nat)
  | [] => []
  | [] :: rest => gapWords rest
  | (first :: later) :: rest => ⟨first, later⟩ :: gapWords rest

def afterSquares (block : Word Nat) : List (Word Nat) → List Nat → List (Word Nat)
  | [], trailing => optionalPieces trailing
  | separator :: rest, trailing =>
      separator :: block :: afterSquares block rest trailing

def squarePieces (block : Word Nat) (gaps : List (Word Nat))
    (trailing : List Nat) : List (Word Nat) :=
  block :: afterSquares block gaps trailing

def framedPieces (block : Word Nat) (gaps : List (Word Nat))
    (leading trailing : List Nat) : List (Word Nat) :=
  optionalPieces leading ++ squarePieces block gaps trailing

theorem flatten_optional (letters : List Nat) :
    flatten (optionalPieces letters) = letters := by
  cases letters with
  | nil => rfl
  | cons first later =>
      change (first :: later) ++ [] = first :: later
      exact List.append_nil _

theorem flatten_append (left right : List (Word Nat)) :
    flatten (left ++ right) = flatten left ++ flatten right := by
  induction left with
  | nil => rfl
  | cons piece rest ih =>
      simp only [List.cons_append, flatten, ih, List.append_assoc]

theorem gapWords_lists (rawGaps : List (List Nat)) :
    (gapWords rawGaps).map Word.toList = keepNonempty rawGaps := by
  induction rawGaps with
  | nil => rfl
  | cons letters rest ih =>
      cases letters with
      | nil => exact ih
      | cons first later =>
          change (first :: later) :: (gapWords rest).map Word.toList =
            (first :: later) :: keepNonempty rest
          rw [ih]

theorem gapWords_member (rawGaps : List (List Nat)) (piece : Word Nat)
    (member : piece ∈ gapWords rawGaps) : piece.toList ∈ rawGaps := by
  induction rawGaps with
  | nil => cases member
  | cons letters rest ih =>
      cases letters with
      | nil => exact List.mem_cons.mpr (Or.inr (ih member))
      | cons first later =>
          change piece ∈ (⟨first, later⟩ : Word Nat) :: gapWords rest at member
          rcases List.mem_cons.mp member with equal | inside
          · subst piece
            exact List.mem_cons.mpr (Or.inl rfl)
          · exact List.mem_cons.mpr (Or.inr (ih inside))

theorem chain_cons_word (block separator : Word Nat) (rest : List (List Nat)) :
    chain block (separator.toList :: rest) =
      (block ++ separator) ++ chain block rest := by
  cases separator
  rfl

theorem flatten_squarePieces (block : Word Nat) (gaps : List (Word Nat))
    (trailing : List Nat) :
    flatten (squarePieces block gaps trailing) =
      (chain block (gaps.map Word.toList)).toList ++ trailing := by
  induction gaps with
  | nil =>
      change block.toList ++ flatten (optionalPieces trailing) = block.toList ++ trailing
      rw [flatten_optional]
  | cons separator rest ih =>
      change block.toList ++ (separator.toList ++ flatten (squarePieces block rest trailing)) =
        (chain block (separator.toList :: rest.map Word.toList)).toList ++ trailing
      rw [ih, chain_cons_word]
      simp only [Word.toList_append, List.append_assoc]

theorem flatten_framedPieces (block : Word Nat) (gaps : List (Word Nat))
    (leading trailing : List Nat) :
    flatten (framedPieces block gaps leading trailing) =
      (Context.frame (contextWord leading) (contextWord trailing)
        (chain block (gaps.map Word.toList))).toList := by
  rw [framedPieces, flatten_append, flatten_optional, flatten_squarePieces]
  exact (frame_of_lists_toList leading trailing (chain block (gaps.map Word.toList))).symm

theorem outside_tag (x y : Nat) (letters : List Nat) (clean : Outside x y letters)
    (letter : Nat) (inside : letter ∈ letters) : binaryTag x y letter = false := by
  cases tag : binaryTag x y letter with
  | false => rfl
  | true =>
      have excluded := clean letter inside
      rcases (binaryTag_true x y letter).mp tag with equal | equal
      · exact False.elim (excluded.1 equal)
      · exact False.elim (excluded.2 equal)

theorem outside_head_tag (x y : Nat) (piece : Word Nat)
    (clean : Outside x y piece.toList) : binaryTag x y piece.head = false := by
  exact outside_tag x y piece.toList clean piece.head (List.mem_cons.mpr (Or.inl rfl))

theorem outside_constant (x y : Nat) (piece : Word Nat)
    (clean : Outside x y piece.toList) : Constant (binaryTag x y) piece := by
  intro letter inside
  exact (outside_tag x y piece.toList clean letter inside).trans
    (outside_head_tag x y piece clean).symm

theorem square_head_tag (x y : Nat) :
    binaryTag x y (square (Word.singleton x) (Word.singleton y)).head = true := by
  exact (binaryTag_true x y x).mpr (Or.inl rfl)

theorem square_constant (x y : Nat) :
    Constant (binaryTag x y) (square (Word.singleton x) (Word.singleton y)) := by
  intro letter member
  change letter ∈ [x, y, x, y] at member
  have tag : binaryTag x y letter = true := by
    rcases List.mem_cons.mp member with equal | member
    · exact (binaryTag_true x y letter).mpr (Or.inl equal)
    · rcases List.mem_cons.mp member with equal | member
      · exact (binaryTag_true x y letter).mpr (Or.inr equal)
      · rcases List.mem_cons.mp member with equal | member
        · exact (binaryTag_true x y letter).mpr (Or.inl equal)
        · exact (binaryTag_true x y letter).mpr (Or.inr (List.mem_singleton.mp member))
  exact tag.trans (square_head_tag x y).symm

theorem squarePieces_good (x y : Nat) (block : Word Nat)
    (positive : binaryTag x y block.head = true) (uniform : Constant (binaryTag x y) block)
    (gaps : List (Word Nat)) (trailing : List Nat)
    (tailClean : Outside x y trailing)
    (clean : ∀ piece ∈ gaps, Outside x y piece.toList) :
    Good (binaryTag x y) (squarePieces block gaps trailing) := by
  revert clean
  induction gaps with
  | nil =>
      intro clean
      cases trailing with
      | nil => exact Good.last uniform
      | cons first later =>
          have negative := outside_head_tag x y (⟨first, later⟩ : Word Nat) tailClean
          exact Good.step uniform (by rw [positive, negative]; decide)
            (Good.last (outside_constant x y (⟨first, later⟩ : Word Nat) tailClean))
  | cons separator rest ih =>
      intro clean
      have separatorClean := clean separator (List.mem_cons.mpr (Or.inl rfl))
      have negative := outside_head_tag x y separator separatorClean
      have restClean : ∀ piece ∈ rest, Outside x y piece.toList := by
        intro piece member
        exact clean piece (List.mem_cons.mpr (Or.inr member))
      change Good (binaryTag x y) (block :: separator :: block :: afterSquares block rest trailing)
      exact Good.step uniform (by rw [positive, negative]; decide)
        (Good.step (outside_constant x y separator separatorClean)
          (by rw [negative, positive]; decide) (ih restClean))

theorem framedPieces_good (x y : Nat) (block : Word Nat)
    (positive : binaryTag x y block.head = true) (uniform : Constant (binaryTag x y) block)
    (gaps : List (Word Nat)) (leading trailing : List Nat)
    (headClean : Outside x y leading) (tailClean : Outside x y trailing)
    (clean : ∀ piece ∈ gaps, Outside x y piece.toList) :
    Good (binaryTag x y) (framedPieces block gaps leading trailing) := by
  have core := squarePieces_good x y block positive uniform gaps trailing tailClean clean
  cases leading with
  | nil => exact core
  | cons first later =>
      have negative := outside_head_tag x y (⟨first, later⟩ : Word Nat) headClean
      exact Good.step (outside_constant x y (⟨first, later⟩ : Word Nat) headClean)
        (by rw [negative, positive]; decide) core

theorem squarePieces_member (block : Word Nat) (gaps : List (Word Nat))
    (trailing : List Nat) (piece : Word Nat)
    (member : piece ∈ squarePieces block gaps trailing) :
    piece = block ∨ piece ∈ gaps ∨ piece.toList = trailing := by
  induction gaps generalizing piece with
  | nil =>
      cases trailing with
      | nil => exact Or.inl (List.mem_singleton.mp member)
      | cons first later =>
          change piece ∈ [block, (⟨first, later⟩ : Word Nat)] at member
          rcases List.mem_cons.mp member with equal | inside
          · exact Or.inl equal
          · have equal := List.mem_singleton.mp inside
            exact Or.inr (Or.inr (congrArg Word.toList equal))
  | cons separator rest ih =>
      change piece ∈ block :: separator :: squarePieces block rest trailing at member
      rcases List.mem_cons.mp member with equal | inside
      · exact Or.inl equal
      · rcases List.mem_cons.mp inside with equal | later
        · exact Or.inr (Or.inl (List.mem_cons.mpr (Or.inl equal)))
        · rcases ih piece later with equal | gapMember | tailEqual
          · exact Or.inl equal
          · exact Or.inr (Or.inl (List.mem_cons.mpr (Or.inr gapMember)))
          · exact Or.inr (Or.inr tailEqual)

theorem squarePieces_positive (x y : Nat) (block : Word Nat)
    (gaps : List (Word Nat)) (trailing : List Nat)
    (tailClean : Outside x y trailing)
    (clean : ∀ part ∈ gaps, Outside x y part.toList)
    (piece : Word Nat) (member : piece ∈ squarePieces block gaps trailing)
    (positive : binaryTag x y piece.head = true) : piece = block := by
  rcases squarePieces_member block gaps trailing piece member with equal | inside | tailEqual
  · exact equal
  · have negative := outside_head_tag x y piece (clean piece inside)
    have impossible : (false : Bool) = true := negative.symm.trans positive
    cases impossible
  · have pieceClean : Outside x y piece.toList := by
      rw [tailEqual]
      exact tailClean
    have negative := outside_head_tag x y piece pieceClean
    have impossible : (false : Bool) = true := negative.symm.trans positive
    cases impossible

theorem framedPieces_positive (x y : Nat) (block : Word Nat)
    (gaps : List (Word Nat)) (leading trailing : List Nat)
    (headClean : Outside x y leading) (tailClean : Outside x y trailing)
    (clean : ∀ part ∈ gaps, Outside x y part.toList)
    (piece : Word Nat) (member : piece ∈ framedPieces block gaps leading trailing)
    (positive : binaryTag x y piece.head = true) : piece = block := by
  rcases List.mem_append.mp member with first | later
  · cases leading with
    | nil => cases first
    | cons head tail =>
        have equal : piece = (⟨head, tail⟩ : Word Nat) := List.mem_singleton.mp first
        subst piece
        have negative := outside_head_tag x y (⟨head, tail⟩ : Word Nat) headClean
        have impossible : (false : Bool) = true := negative.symm.trans positive
        cases impossible
  · exact squarePieces_positive x y block gaps trailing tailClean clean piece later positive

/-- This uses the actual codec output, not a caller-supplied rendering. -/
def actualPieces (x y : Nat) (before middle after : List Nat) : List (Word Nat) :=
  framedPieces (square (Word.singleton x) (Word.singleton y))
    (gapWords (actualGaps x y before middle after))
    (encodeLeft x y before).1 (encodeRight x y after).2

theorem actualPieces_flatten (x y : Nat) (before middle after : List Nat) :
    flatten (actualPieces x y before middle after) =
      (coalescedSquareBlocks x y before middle after).toList := by
  unfold actualPieces
  rw [flatten_framedPieces, gapWords_lists]
  rfl

theorem actualPieces_good (x y : Nat) (before middle after : List Nat) :
    Good (binaryTag x y) (actualPieces x y before middle after) := by
  apply framedPieces_good x y _ (square_head_tag x y) (square_constant x y)
  · exact (coalesced_boundaries x y before middle after).1
  · exact (coalesced_boundaries x y before middle after).2.1
  · intro piece member
    exact actual_gaps_outside x y before middle after piece.toList
      (gapWords_member (actualGaps x y before middle after) piece member)

theorem actualPieces_positive (x y : Nat) (before middle after : List Nat)
    (piece : Word Nat) (member : piece ∈ actualPieces x y before middle after)
    (positive : binaryTag x y piece.head = true) :
    piece = square (Word.singleton x) (Word.singleton y) := by
  apply framedPieces_positive x y _ _ _ _
    (coalesced_boundaries x y before middle after).1
    (coalesced_boundaries x y before middle after).2.1 _ piece member positive
  intro part inside
  exact actual_gaps_outside x y before middle after part.toList
    (gapWords_member (actualGaps x y before middle after) part inside)

/-- Maximality is witnessed by homogeneity and a tag change at every boundary. -/
def SquareCover (x y : Nat) (word : Word Nat) : Prop :=
  ∃ pieces : List (Word Nat),
    flatten pieces = word.toList ∧ Good (binaryTag x y) pieces ∧
    (∀ piece ∈ pieces, piece.toList ≠ []) ∧
    (∀ piece ∈ pieces, binaryTag x y piece.head = true →
      piece = square (Word.singleton x) (Word.singleton y))

theorem coalesced_maximal_square_cover (x y : Nat) (before middle after : List Nat) :
    SquareCover x y (coalescedSquareBlocks x y before middle after) := by
  refine ⟨actualPieces x y before middle after, actualPieces_flatten x y before middle after,
    actualPieces_good x y before middle after, ?_, ?_⟩
  · intro piece member
    exact piece_nonempty piece
  · intro piece member positive
    exact actualPieces_positive x y before middle after piece member positive

/-- The original occurrence hypotheses yield a genuine square-factor normal form.
The two ordered-square orientations remain explicit. Full completeness is separate. -/
theorem related_maximal_square_cover (x y : Nat) (word : Word Nat)
    (different : x ≠ y) (xRepeated : 2 ≤ word.toList.count x)
    (yRepeated : 2 ≤ word.toList.count y) (related : PairRelated x y word.toList) :
    (∃ normal : Word Nat, Derives basis word normal ∧ SquareCover x y normal) ∨
    (∃ normal : Word Nat, Derives basis word normal ∧ SquareCover y x normal) := by
  rcases related_coalesced x y word different xRepeated yRepeated related with forward | backward
  · obtain ⟨before, middle, after, step⟩ := forward
    exact Or.inl ⟨coalescedSquareBlocks x y before middle after, step,
      coalesced_maximal_square_cover x y before middle after⟩
  · obtain ⟨before, middle, after, step⟩ := backward
    exact Or.inr ⟨coalescedSquareBlocks y x before middle after, step,
      coalesced_maximal_square_cover y x before middle after⟩

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.flatten_optional
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.flatten_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.gapWords_lists
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.gapWords_member
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.chain_cons_word
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.flatten_squarePieces
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.flatten_framedPieces
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.outside_tag
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.outside_head_tag
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.outside_constant
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.square_head_tag
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.square_constant
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.squarePieces_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.framedPieces_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.squarePieces_member
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.squarePieces_positive
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.framedPieces_positive
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.actualPieces_flatten
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.actualPieces_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.actualPieces_positive
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.coalesced_maximal_square_cover
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.MaximalSquareCover.related_maximal_square_cover
