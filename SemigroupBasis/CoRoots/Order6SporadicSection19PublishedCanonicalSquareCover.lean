import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedMaximalSquareCover

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalSquareCover

open BinaryPowers FactorContexts OccurrenceWitnesses MarkedZones
  SquareCoalescing MaximalFactors MaximalSquareCover

/-- The optional first boundary is structural data of an actual factor list. -/
def SeparatedHead (classify : Nat → Bool) (letter : Nat) : List (Word Nat) → Prop
  | [] => True
  | first :: _ => classify letter ≠ classify first.head

theorem decompose_append (classify : Nat → Bool) (left right : List Nat) :
    decompose classify (left ++ right) =
      left.foldr (insertLetter classify) (decompose classify right) := by
  induction left with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.cons_append, decompose, List.foldr, ih]

theorem foldr_run (classify : Nat → Bool) (first : Nat) (later : List Nat)
    (pieces : List (Word Nat))
    (uniform : ∀ letter ∈ later, classify letter = classify first)
    (boundary : SeparatedHead classify first pieces) :
    (first :: later).foldr (insertLetter classify) pieces =
      (⟨first, later⟩ : Word Nat) :: pieces := by
  revert first
  induction later with
  | nil =>
      intro first uniform boundary
      cases pieces with
      | nil => rfl
      | cons piece rest =>
          change insertLetter classify first (piece :: rest) = (⟨first, []⟩ : Word Nat) :: piece :: rest
          rw [insertLetter, if_neg boundary]
          rfl
  | cons second rest ih =>
      intro first uniform boundary
      have same : classify second = classify first := uniform second (List.mem_cons.mpr (Or.inl rfl))
      have restUniform : ∀ letter ∈ rest, classify letter = classify second := by
        intro letter member
        exact (uniform letter (List.mem_cons.mpr (Or.inr member))).trans same.symm
      have restBoundary : SeparatedHead classify second pieces := by
        cases pieces with
        | nil => trivial
        | cons next tail =>
            intro equal
            exact boundary (same.symm.trans equal)
      change insertLetter classify first
        ((second :: rest).foldr (insertLetter classify) pieces) =
        (⟨first, second :: rest⟩ : Word Nat) :: pieces
      rw [ih second restUniform restBoundary]
      rw [insertLetter, if_pos same.symm]
      rfl

theorem decompose_flatten_good (classify : Nat → Bool)
    (pieces : List (Word Nat)) (good : Good classify pieces) :
    decompose classify (flatten pieces) = pieces := by
  induction good with
  | nil => rfl
  | @last piece uniform =>
      change decompose classify (piece.toList ++ []) = [piece]
      rw [decompose_append]
      exact foldr_run classify piece.head piece.tail []
        (fun letter member => uniform letter (List.mem_cons.mpr (Or.inr member))) True.intro
  | @step first second rest uniform different tailGood ih =>
      change decompose classify (first.toList ++ flatten (second :: rest)) = first :: second :: rest
      rw [decompose_append, ih]
      exact foldr_run classify first.head first.tail (second :: rest)
        (fun letter member => uniform letter (List.mem_cons.mpr (Or.inr member))) different

theorem good_factorization_unique (classify : Nat → Bool)
    (left right : List (Word Nat)) (leftGood : Good classify left)
    (rightGood : Good classify right) (sameLetters : flatten left = flatten right) :
    left = right := by
  calc
    left = decompose classify (flatten left) := (decompose_flatten_good classify left leftGood).symm
    _ = decompose classify (flatten right) := congrArg (decompose classify) sameLetters
    _ = right := decompose_flatten_good classify right rightGood

theorem decompose_word_nonempty (classify : Nat → Bool) (word : Word Nat) :
    decompose classify word.toList ≠ [] := by
  intro empty
  have covered := flatten_decompose classify word.toList
  rw [empty] at covered
  exact piece_nonempty word covered.symm

theorem canonical_actualPieces (x y : Nat) (before middle after : List Nat) :
    decompose (binaryTag x y) (coalescedSquareBlocks x y before middle after).toList =
      actualPieces x y before middle after := by
  rw [← actualPieces_flatten x y before middle after]
  exact decompose_flatten_good (binaryTag x y) _ (actualPieces_good x y before middle after)

/-- Every binary component of the canonical maximal decomposition is the square. -/
def CanonicalSquareForm (x y : Nat) (word : Word Nat) : Prop :=
  ∀ piece ∈ decompose (binaryTag x y) word.toList,
    binaryTag x y piece.head = true →
      piece = square (Word.singleton x) (Word.singleton y)

theorem cover_canonical (x y : Nat) (word : Word Nat) (cover : SquareCover x y word) :
    CanonicalSquareForm x y word := by
  obtain ⟨pieces, letters, good, nonempty, squares⟩ := cover
  have canonical : decompose (binaryTag x y) word.toList = pieces := by
    rw [← letters]
    exact decompose_flatten_good (binaryTag x y) pieces good
  intro piece member positive
  rw [canonical] at member
  exact squares piece member positive

theorem coalesced_canonical (x y : Nat) (before middle after : List Nat) :
    CanonicalSquareForm x y (coalescedSquareBlocks x y before middle after) :=
  cover_canonical x y _ (coalesced_maximal_square_cover x y before middle after)

/-- Canonicality now follows from the actual occurrence witnesses and derivation.
This does not claim full Lemma19.2/19.3 completeness. -/
theorem related_canonical_square_form (x y : Nat) (word : Word Nat)
    (different : x ≠ y) (xRepeated : 2 ≤ word.toList.count x)
    (yRepeated : 2 ≤ word.toList.count y) (related : PairRelated x y word.toList) :
    (∃ normal : Word Nat, Derives basis word normal ∧ CanonicalSquareForm x y normal) ∨
    (∃ normal : Word Nat, Derives basis word normal ∧ CanonicalSquareForm y x normal) := by
  rcases related_maximal_square_cover x y word different xRepeated yRepeated related with forward | backward
  · obtain ⟨normal, step, cover⟩ := forward
    exact Or.inl ⟨normal, step, cover_canonical x y normal cover⟩
  · obtain ⟨normal, step, cover⟩ := backward
    exact Or.inr ⟨normal, step, cover_canonical y x normal cover⟩

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalSquareCover

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalSquareCover.decompose_append
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalSquareCover.foldr_run
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalSquareCover.decompose_flatten_good
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalSquareCover.good_factorization_unique
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalSquareCover.decompose_word_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalSquareCover.canonical_actualPieces
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalSquareCover.cover_canonical
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalSquareCover.coalesced_canonical
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.CanonicalSquareCover.related_canonical_square_form
