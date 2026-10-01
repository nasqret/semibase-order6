import SemigroupBasis.CoRoots.Order6SporadicSection15Derivations

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis

/-- Convert a possibly empty list context into the optional nonempty word used
by the expanded Section 15 laws. -/
private def optionalWordOfList : List Nat → Option (Word Nat)
  | [] => none
  | head :: tail => some (S5_107.listWordOfCons head tail)

@[simp]
private theorem appendOptional_optionalWordOfList_toList
    (stem : Word Nat) (letters : List Nat) :
    (appendOptional stem (optionalWordOfList letters)).toList =
      stem.toList ++ letters := by
  cases letters with
  | nil =>
      simp [optionalWordOfList, appendOptional]
  | cons head tail =>
      simp [optionalWordOfList, appendOptional,
        S5_107.listWordOfCons, Word.toList]

@[simp]
private theorem appendOptional_optionalWordOfList_head_tail_append
    (stem : Word Nat) (letters after : List Nat) :
    (appendOptional stem (optionalWordOfList letters)).head ::
        ((appendOptional stem (optionalWordOfList letters)).tail ++ after) =
      stem.head :: (stem.tail ++ letters ++ after) := by
  cases letters with
  | nil =>
      simp [optionalWordOfList, appendOptional]
  | cons head tail =>
      simp [optionalWordOfList, appendOptional,
        S5_107.listWordOfCons, List.append_assoc]

/-! ## Typed expansion instances of (15.1a) -/

private theorem listDerives15_1aLeftExpand
    (before after : List Nat) (x : Nat) (h k : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [x] ++ k ++ [x] ++ after)
      (before ++ [x, x] ++ h ++ [x] ++ k ++ [x] ++ after) := by
  have core := S5_107.ListDerives.ofWord <|
    (derives15_1aLeft (Word.singleton x)
      (optionalWordOfList h) (optionalWordOfList k)).symm
  simpa [pattern15_1aLeft, pattern15_1aCore,
    Word.toList, Word.toList_append, List.append_assoc] using
      S5_107.ListDerives.context before after core

private theorem listDerives15_1aMiddleExpand
    (before after : List Nat) (x : Nat) (h k : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [x] ++ k ++ [x] ++ after)
      (before ++ [x] ++ h ++ [x, x] ++ k ++ [x] ++ after) := by
  have core := S5_107.ListDerives.ofWord <|
    (derives15_1aMiddle (Word.singleton x)
      (optionalWordOfList h) (optionalWordOfList k)).symm
  simpa [pattern15_1aMiddle, pattern15_1aCore,
    Word.toList_append, List.append_assoc] using
      S5_107.ListDerives.context before after core

private theorem listDerives15_1aRightExpand
    (before after : List Nat) (x : Nat) (h k : List Nat) :
    ListDerives
      (before ++ [x] ++ h ++ [x] ++ k ++ [x] ++ after)
      (before ++ [x] ++ h ++ [x] ++ k ++ [x, x] ++ after) := by
  have core := S5_107.ListDerives.ofWord <|
    (derives15_1aRight (Word.singleton x)
      (optionalWordOfList h) (optionalWordOfList k)).symm
  simpa [pattern15_1aRight, pattern15_1aCore,
    Word.toList_append, List.append_assoc] using
      S5_107.ListDerives.context before after core

/-! ## Occurrence extraction -/

/-- A list in which `x` occurs at least twice can be split at two selected
occurrences. Other occurrences of `x` may remain in any of the three pieces. -/
theorem exists_two_occurrence_split
    (x : Nat) :
    ∀ {letters : List Nat},
      2 ≤ letters.count x →
        ∃ before middle after,
          letters = before ++ x :: middle ++ x :: after
  | [], count => by
      simp at count
  | first :: rest, count => by
      by_cases equality : first = x
      · subst first
        have restPositive : 0 < rest.count x := by
          simp only [List.count_cons_self] at count
          omega
        obtain ⟨middle, after, split⟩ :=
          List.mem_iff_append.mp (List.count_pos_iff.mp restPositive)
        exact ⟨[], middle, after, by simp [split, List.append_assoc]⟩
      · have restCount : 2 ≤ rest.count x := by
          simpa [equality] using count
        obtain ⟨before, middle, after, split⟩ :=
          exists_two_occurrence_split x restCount
        exact
          ⟨first :: before, middle, after,
            by simp [split, List.append_assoc]⟩

/-! ## Selected high occurrence -/

/-- Duplicate one displayed occurrence of `x` when the complete word contains
at least three copies of `x`. The two supporting occurrences may both precede
the display, both follow it, or lie on opposite sides. These cases use the
right, left, and middle placements of (15.1a), respectively. -/
theorem listDerivesDuplicateSelectedHigh
    (x : Nat) (before after : List Nat)
    (high : 3 ≤ (before ++ [x] ++ after).count x) :
    ListDerives
      (before ++ [x] ++ after)
      (before ++ [x, x] ++ after) := by
  have totalReassociated :
      3 ≤ before.count x + (after.count x + 1) := by
    simpa [List.count_append] using high
  have total : 3 ≤ before.count x + 1 + after.count x := by
    omega
  by_cases beforeTwo : 2 ≤ before.count x
  · obtain ⟨stem, middle, suffix, split⟩ :=
      exists_two_occurrence_split x beforeTwo
    rw [split]
    simpa [List.append_assoc] using
      (listDerives15_1aRightExpand
        stem after x middle suffix)
  · by_cases afterTwo : 2 ≤ after.count x
    · obtain ⟨stem, middle, suffix, split⟩ :=
        exists_two_occurrence_split x afterTwo
      rw [split]
      simpa [List.append_assoc] using
        (listDerives15_1aLeftExpand
          before suffix x stem middle)
    · have beforePositive : 0 < before.count x := by
        omega
      have afterPositive : 0 < after.count x := by
        omega
      obtain ⟨beforePrefix, beforeSuffix, beforeSplit⟩ :=
        List.mem_iff_append.mp (List.count_pos_iff.mp beforePositive)
      obtain ⟨afterPrefix, afterSuffix, afterSplit⟩ :=
        List.mem_iff_append.mp (List.count_pos_iff.mp afterPositive)
      rw [beforeSplit, afterSplit]
      simpa [List.append_assoc] using
        (listDerives15_1aMiddleExpand
          beforePrefix afterSuffix x beforeSuffix afterPrefix)

/-- Contract the duplicated selected occurrence back to one copy. The high
hypothesis is stated for the contracted word, so this is exactly the symmetry
of `listDerivesDuplicateSelectedHigh`. -/
theorem listDerivesContractSelectedHigh
    (x : Nat) (before after : List Nat)
    (high : 3 ≤ (before ++ [x] ++ after).count x) :
    ListDerives
      (before ++ [x, x] ++ after)
      (before ++ [x] ++ after) :=
  (listDerivesDuplicateSelectedHigh x before after high).symm

end SemigroupBasis.CoRoots.Order6SporadicSection15
