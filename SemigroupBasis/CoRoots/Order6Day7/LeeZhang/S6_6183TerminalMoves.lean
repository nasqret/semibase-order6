import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183LowerProfiles

/-! Exact raw7 derivations for the marked terminal. All contexts are ordinary
nonempty words; empty list gaps are handled separately and never substituted
for a semigroup variable. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183

open SemigroupBasis
open S4_71Suffix

theorem mk_toList (first : Nat) (rest : List Nat) : (Word.mk first rest).toList = first :: rest := rfl

theorem derives_of_lists {left right left' right' : Word Nat}
    (derivation : Derives basis left right)
    (sameLeft : left'.toList = left.toList) (sameRight : right'.toList = right.toList) :
    Derives basis left' right' := by
  rw [Word.toList_injective sameLeft, Word.toList_injective sameRight]
  exact derivation

theorem derives_put (front : List Nat) {left right : Word Nat}
    (derivation : Derives basis left right) : Derives basis (put front left) (put front right) := by
  induction front with
  | nil => exact derivation
  | cons first rest ih => exact Derives.prepend (Word.singleton first) ih

theorem put_appendWord (front : List Nat) (middle suffix : Word Nat) :
    put front middle ++ suffix = put front (middle ++ suffix) := by
  apply Word.toList_injective
  simp only [Word.toList_append, put_toList, List.append_assoc]

def erase (selected : Nat) (word : List Nat) : List Nat := word.filter (fun letter => decide (letter ≠ selected))

theorem mem_erase (selected letter : Nat) (word : List Nat) :
    letter ∈ erase selected word ↔ letter ∈ word ∧ letter ≠ selected := by simp [erase]

theorem erased_absent (selected : Nat) (word : List Nat) : selected ∉ erase selected word := by simp [mem_erase]

theorem erase_before_double (before : List Nat) (selected : Nat) :
    Derives basis (put before (Word.singleton selected ++ Word.singleton selected))
      (put (erase selected before) (Word.singleton selected ++ Word.singleton selected)) := by
  induction before with
  | nil => exact Derives.refl _
  | cons first rest ih =>
      by_cases equal : first = selected
      · subst first
        have remove : Derives basis
            (put (selected :: rest) (Word.singleton selected ++ Word.singleton selected))
            (put rest (Word.singleton selected ++ Word.singleton selected)) := by
          cases rest with
          | nil =>
              apply derives_of_lists (derivesPower (Word.singleton selected)).symm
              all_goals simp only [put_toList, Word.toList_append, Word.toList_singleton,
                List.cons_append, List.nil_append]
          | cons head tail =>
              apply derives_of_lists (derivesDeleteBeforeSquare (Word.singleton selected) (Word.mk head tail))
              all_goals simp only [put_toList, Word.toList_append, Word.toList_singleton,
                mk_toList, List.cons_append, List.nil_append]
        simpa only [erase, List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
          ↓reduceIte] using remove.trans ih
      · have lifted := Derives.prepend (Word.singleton first) ih
        simpa [erase, equal, put] using lifted

theorem expand_terminal_repeat (selected : Nat) (middle : List Nat) :
    Derives basis (endWord (selected :: middle) selected)
      (endWord (selected :: selected :: middle) selected) := by
  cases middle with
  | nil =>
      apply derives_of_lists (derivesPower (Word.singleton selected))
      all_goals simp only [endWord, put_toList, Word.toList_append, Word.toList_singleton,
        List.cons_append, List.nil_append]
  | cons first rest =>
      apply derives_of_lists (derivesRepeatContraction (Word.singleton selected) (Word.mk first rest)).symm
      all_goals simp only [endWord, put_toList, Word.toList_append, Word.toList_singleton,
        mk_toList, List.cons_append, List.nil_append]

theorem remove_terminal_repetitions (before middle : List Nat) (selected : Nat) :
    Derives basis (endWord (before ++ selected :: middle) selected)
      (endWord (erase selected before ++ selected :: middle) selected) := by
  have expand := derives_put before (expand_terminal_repeat selected middle)
  have clear := Derives.appendRight (erase_before_double before selected) (endWord middle selected)
  have contract := derives_put (erase selected before) (expand_terminal_repeat selected middle).symm
  have first : Derives basis (endWord (before ++ selected :: middle) selected)
      (endWord (before ++ selected :: selected :: middle) selected) := by
    simpa only [endWord, put_append] using expand
  have second : Derives basis (endWord (before ++ selected :: selected :: middle) selected)
      (endWord (erase selected before ++ selected :: selected :: middle) selected) := by
    apply derives_of_lists clear
    all_goals simp only [endWord, put_toList, Word.toList_append, Word.toList_singleton,
      List.cons_append, List.nil_append, List.append_assoc]
  exact first.trans (second.trans (by simpa only [endWord, put_append] using contract))

theorem move_marked_across_doubles (selected : Nat) (middle : List Nat) (suffix : Word Nat) :
    Derives basis
      (Word.singleton selected ++ put (doubleLetters middle) (suffix ++ Word.singleton selected))
      (put (doubleLetters middle) (Word.singleton selected ++ (suffix ++ Word.singleton selected))) := by
  induction middle with
  | nil => exact Derives.refl _
  | cons first rest ih =>
      have swap := (derivesMarkedSquareSwap (Word.singleton first) (Word.singleton selected)
        (put (doubleLetters rest) suffix)).symm
      have step : Derives basis
          (Word.singleton selected ++ put (doubleLetters (first :: rest)) (suffix ++ Word.singleton selected))
          ((Word.singleton first ++ Word.singleton first) ++
            (Word.singleton selected ++ put (doubleLetters rest) (suffix ++ Word.singleton selected))) := by
        apply derives_of_lists swap
        all_goals simp only [doubleLetters, put_toList, Word.toList_append, Word.toList_singleton,
          List.cons_append, List.nil_append, List.append_assoc]
      have remaining := Derives.prepend (Word.singleton first ++ Word.singleton first) ih
      exact step.trans (by
        simpa only [doubleLetters, put, Word.append_assoc] using remaining)

def doubledWord (word : Word Nat) : Word Nat := ⟨word.head, word.head :: doubleLetters word.tail⟩

theorem doubledWord_toList (word : Word Nat) : (doubledWord word).toList = doubleLetters word.toList := rfl

theorem derives_word_square (word : Word Nat) : Derives basis (word ++ word) (doubledWord word) := by
  cases word with
  | mk first rest =>
      induction rest generalizing first with
      | nil => exact Derives.refl _
      | cons next tail ih =>
          have split := (derivesSquareInterleave (Word.singleton first) (Word.mk next tail)).symm
          have normalize := Derives.prepend (Word.singleton first ++ Word.singleton first) (ih next)
          have chain := split.trans normalize
          apply derives_of_lists chain
          all_goals simp only [doubledWord, doubleLetters, Word.toList_append, Word.toList_singleton,
            mk_toList, List.cons_append, List.nil_append, List.append_assoc]

theorem derives_square_middle_padding (selected middle : Word Nat) :
    Derives basis ((selected ++ (middle ++ middle)) ++ selected)
      (((selected ++ (middle ++ middle)) ++ selected) ++ selected) := by
  have first := (derivesSquareSandwich selected middle).symm
  have second := derivesSquareCommutation selected middle
  have third := (derivesDeleteBeforeSquare selected (middle ++ middle)).symm
  exact first.trans (second.trans (by simpa only [Word.append_assoc] using third))

theorem derives_saturated_gap_padding (selected : Nat) (middle : List Nat) :
    Derives basis (endWord (selected :: doubleLetters middle) selected)
      (endWord (selected :: doubleLetters middle) selected ++ Word.singleton selected) := by
  cases middle with
  | nil =>
      apply derives_of_lists (derivesPower (Word.singleton selected))
      all_goals simp only [endWord, doubleLetters, put_toList, Word.toList_append, Word.toList_singleton,
        List.cons_append, List.nil_append]
  | cons first rest =>
      let middle : Word Nat := ⟨first, rest⟩
      have normalized := Derives.appendRight (Derives.prepend (Word.singleton selected) (derives_word_square middle))
        (Word.singleton selected)
      have middleStep := derives_square_middle_padding (Word.singleton selected) middle
      have chain := normalized.symm.trans (middleStep.trans (Derives.appendRight normalized (Word.singleton selected)))
      apply derives_of_lists chain
      all_goals simp only [endWord, middle, doubledWord, doubleLetters, put_toList,
        Word.toList_append, Word.toList_singleton, mk_toList, List.cons_append,
        List.nil_append, List.append_assoc]

theorem terminal_stable_of_gap (before middle : List Nat) (selected : Nat)
    (repeated : ∀ letter, letter ∈ middle → 2 ≤ (before ++ selected :: middle).count letter) :
    Derives basis (endWord (before ++ selected :: middle) selected)
      (endWord (before ++ selected :: middle) selected ++ Word.singleton selected) := by
  have saturatedTheory := listTheory_doubleSegment (before ++ [selected]) middle [] (by
    intro letter member
    simpa only [List.append_nil, List.append_assoc, List.singleton_append] using repeated letter member)
  have normalize : Derives basis (endWord (before ++ selected :: middle) selected)
      (endWord (before ++ selected :: doubleLetters middle) selected) := by
    apply prefix_lower_replay
    simpa only [List.append_nil, List.append_assoc, List.singleton_append] using saturatedTheory
  have stable := derives_put before (derives_saturated_gap_padding selected middle)
  have middleStep : Derives basis (endWord (before ++ selected :: doubleLetters middle) selected)
      (endWord (before ++ selected :: doubleLetters middle) selected ++ Word.singleton selected) := by
    simpa only [endWord, put_append, put_appendWord] using stable
  exact normalize.trans (middleStep.trans (Derives.appendRight normalize (Word.singleton selected)).symm)

theorem move_marked_across_repeated (before middle : List Nat) (selected : Nat) (suffix : Word Nat)
    (repeated : ∀ letter, letter ∈ middle →
      2 ≤ (before ++ selected :: (middle ++ suffix.toList)).count letter) :
    Derives basis (put (before ++ selected :: middle) (suffix ++ Word.singleton selected))
      (put (before ++ middle ++ [selected]) (suffix ++ Word.singleton selected)) := by
  have initialTheory := listTheory_doubleSegment (before ++ [selected]) middle suffix.toList (by
    intro letter member
    simpa only [List.append_assoc, List.singleton_append] using repeated letter member)
  have finalRepeated : ∀ letter, letter ∈ middle →
      2 ≤ (before ++ middle ++ (selected :: suffix.toList)).count letter := by
    intro letter member
    have original := repeated letter member
    simp only [List.count_append, List.count_cons] at original ⊢
    omega
  have finalTheory := listTheory_doubleSegment before middle (selected :: suffix.toList) finalRepeated
  have first := prefix_lower_replay _ _ (Word.singleton selected) initialTheory
  have last := prefix_lower_replay _ _ (Word.singleton selected) finalTheory
  have middleStep := derives_put before (move_marked_across_doubles selected middle suffix)
  have first' : Derives basis (put (before ++ selected :: middle) (suffix ++ Word.singleton selected))
      (put before (Word.singleton selected ++ put (doubleLetters middle) (suffix ++ Word.singleton selected))) := by
    apply derives_of_lists first
    all_goals simp only [put_toList, Word.toList_append, Word.toList_singleton,
      List.cons_append, List.nil_append, List.append_assoc]
  have last' : Derives basis
      (put before (put (doubleLetters middle) (Word.singleton selected ++ (suffix ++ Word.singleton selected))))
      (put (before ++ middle ++ [selected]) (suffix ++ Word.singleton selected)) := by
    apply derives_of_lists last.symm
    all_goals simp only [put_toList, Word.toList_append, Word.toList_singleton,
      List.cons_append, List.nil_append, List.append_assoc]
  exact first'.trans (middleStep.trans last')

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_6183
