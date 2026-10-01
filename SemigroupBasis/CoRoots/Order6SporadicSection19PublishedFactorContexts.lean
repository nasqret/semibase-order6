import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedFactorBoundaries

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorContexts

open MaximalFactors FactorBoundaries

/-- Empty contexts stay optional; nonempty contexts are genuine semigroup words. -/
def contextWord : List Nat → Option (Word Nat)
  | [] => none
  | first :: rest => some ⟨first, rest⟩

def contextLetters : Option (Word Nat) → List Nat
  | none => []
  | some word => word.toList

theorem contextLetters_contextWord (letters : List Nat) :
    contextLetters (contextWord letters) = letters := by
  cases letters <;> rfl

theorem frame_toList (left right : Option (Word Nat)) (piece : Word Nat) :
    (Context.frame left right piece).toList =
      contextLetters left ++ (piece.toList ++ contextLetters right) := by
  cases left with
  | none =>
      cases right with
      | none => exact (List.append_nil piece.toList).symm
      | some suffix => exact Word.toList_append piece suffix
  | some beforeWord =>
      cases right with
      | none =>
          change (beforeWord ++ piece).toList = beforeWord.toList ++ (piece.toList ++ [])
          rw [Word.toList_append, List.append_nil]
      | some suffix =>
          change ((beforeWord ++ piece) ++ suffix).toList =
            beforeWord.toList ++ (piece.toList ++ suffix.toList)
          rw [Word.toList_append, Word.toList_append, List.append_assoc]

theorem frame_of_lists_toList (before after : List Nat) (piece : Word Nat) :
    (Context.frame (contextWord before) (contextWord after) piece).toList =
      before ++ (piece.toList ++ after) := by
  simpa only [contextLetters_contextWord] using
    frame_toList (contextWord before) (contextWord after) piece

theorem word_frame_of_split (before after : List Nat) (word piece : Word Nat)
    (split : word.toList = before ++ (piece.toList ++ after)) :
    word = Context.frame (contextWord before) (contextWord after) piece := by
  apply Word.toList_injective
  exact split.trans (frame_of_lists_toList before after piece).symm

/-- An actual run, not an assumed rendering, supplies the exact Word context. -/
theorem factor_as_frame (classify : Nat → Bool) (word piece : Word Nat)
    (member : piece ∈ decompose classify word.toList) :
    ∃ before after : List (Word Nat),
      decompose classify word.toList = before ++ piece :: after ∧
      word = Context.frame (contextWord (flatten before))
        (contextWord (flatten after)) piece ∧
      Constant classify piece := by
  obtain ⟨before, after, split, rendered, uniform, _, _⟩ :=
    factor_witness classify word.toList piece member
  exact ⟨before, after, split,
    word_frame_of_split (flatten before) (flatten after) word piece rendered, uniform⟩

/-- The typed context retains the original complementary run boundaries. -/
theorem maximal_binary_factor_as_frame (x y : Nat) (word piece : Word Nat)
    (member : piece ∈ decompose (binaryTag x y) word.toList)
    (binary : binaryTag x y piece.head = true) :
    ∃ before after : List (Word Nat),
      word = Context.frame (contextWord (flatten before))
        (contextWord (flatten after)) piece ∧
      (∀ value ∈ piece.toList, value = x ∨ value = y) ∧
      (∀ earlier last, before = earlier ++ [last] →
        ∀ value ∈ last.toList, value ≠ x ∧ value ≠ y) ∧
      (∀ next later, after = next :: later →
        ∀ value ∈ next.toList, value ≠ x ∧ value ≠ y) := by
  obtain ⟨before, after, rendered, uniform, leftOutside, rightOutside⟩ :=
    word_maximal_binary_factor_witness x y word piece member binary
  exact ⟨before, after,
    word_frame_of_split (flatten before) (flatten after) word piece rendered,
    uniform, leftOutside, rightOutside⟩

theorem replace_actual_factor (before after : List Nat)
    (word piece replacement : Word Nat)
    (split : word.toList = before ++ (piece.toList ++ after))
    (step : Derives basis piece replacement) :
    Derives basis word
      (Context.frame (contextWord before) (contextWord after) replacement) := by
  have framed : word = Context.frame (contextWord before) (contextWord after) piece :=
    word_frame_of_split before after word piece split
  rw [framed]
  exact Context.frame_derives step (contextWord before) (contextWord after)

/-- Any proved replacement of the selected binary factor lifts to the whole
word without changing either context or either complementary boundary.
This does not assume or prove the still-open C1/C2 witness extraction. -/
theorem maximal_binary_factor_replacement (x y : Nat) (word piece replacement : Word Nat)
    (member : piece ∈ decompose (binaryTag x y) word.toList)
    (binary : binaryTag x y piece.head = true)
    (step : Derives basis piece replacement) :
    ∃ before after : List (Word Nat),
      word = Context.frame (contextWord (flatten before))
        (contextWord (flatten after)) piece ∧
      Derives basis word (Context.frame (contextWord (flatten before))
        (contextWord (flatten after)) replacement) ∧
      (∀ value ∈ piece.toList, value = x ∨ value = y) ∧
      (∀ earlier last, before = earlier ++ [last] →
        ∀ value ∈ last.toList, value ≠ x ∧ value ≠ y) ∧
      (∀ next later, after = next :: later →
        ∀ value ∈ next.toList, value ≠ x ∧ value ≠ y) := by
  obtain ⟨before, after, framed, uniform, leftOutside, rightOutside⟩ :=
    maximal_binary_factor_as_frame x y word piece member binary
  refine ⟨before, after, framed, ?_, uniform, leftOutside, rightOutside⟩
  rw [framed]
  exact Context.frame_derives step (contextWord (flatten before)) (contextWord (flatten after))

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorContexts

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorContexts.contextLetters_contextWord
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorContexts.frame_toList
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorContexts.frame_of_lists_toList
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorContexts.word_frame_of_split
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorContexts.factor_as_frame
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorContexts.maximal_binary_factor_as_frame
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorContexts.replace_actual_factor
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FactorContexts.maximal_binary_factor_replacement
