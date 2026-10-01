import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708Sigma12Derivations

/-! A concrete Word normal form, not a flat invariant key. List reduction and
sorting are terminating programs; all exceptional terminal forms are explicit. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708.Sigma12

open SemigroupBasis
open S4_71Suffix (put put_toList)

def framed (front : List Nat) (penultimate last : Nat) : Word Nat :=
  put front (Word.mk penultimate [last])

theorem framed_toList (front : List Nat) (penultimate last : Nat) :
    (framed front penultimate last).toList = front ++ [penultimate, last] := put_toList _ _

theorem framed_reverse (front : List Nat) (penultimate last : Nat) :
    (framed front penultimate last).reverse = Word.mk last (penultimate :: front.reverse) := by
  apply Word.toList_injective
  rw [Word.toList_reverse, framed_toList]
  simp [Word.toList]

inductive Input where
  | single : Nat → Input
  | frame : List Nat → Nat → Nat → Input
deriving DecidableEq, Repr

def Input.word : Input → Word Nat
  | .single letter => Word.singleton letter
  | .frame front penultimate last => framed front penultimate last

def decompose (word : Word Nat) : Input :=
  match word.reverse with
  | ⟨last, []⟩ => .single last
  | ⟨last, penultimate :: front⟩ => .frame front.reverse penultimate last

theorem decompose_single (letter : Nat) : decompose (Word.singleton letter) = .single letter := rfl

theorem decompose_frame (front : List Nat) (penultimate last : Nat) :
    decompose (framed front penultimate last) = .frame front penultimate last := by
  simp only [decompose, framed_reverse, List.reverse_reverse]

theorem word_decompose (word : Word Nat) : (decompose word).word = word := by
  apply Word.toList_injective
  calc
    (decompose word).word.toList = word.reverse.toList.reverse := by
      cases equal : word.reverse with
      | mk last rest =>
          cases rest with
          | nil => simp [decompose, equal, Input.word, Word.toList, Word.singleton]
          | cons penultimate front =>
              simp only [decompose, equal, Input.word]
              rw [framed_toList]
              simp [Word.toList, List.append_assoc]
    _ = word.toList := by rw [Word.toList_reverse, List.reverse_reverse]

theorem existsSingleOrFrame (word : Word Nat) :
    (∃ letter, word = Word.singleton letter) ∨
      ∃ front penultimate last, word = framed front penultimate last := by
  have representation := word_decompose word
  cases equation : decompose word with
  | single letter =>
      exact Or.inl ⟨letter, by simpa only [equation, Input.word] using representation.symm⟩
  | frame front penultimate last =>
      exact Or.inr ⟨front, penultimate, last, by simpa only [equation, Input.word] using representation.symm⟩

def SameCaps (left right : List Nat) : Prop :=
  ∀ letter, min (left.count letter) 2 = min (right.count letter) 2

theorem SameCaps.symm {left right : List Nat} (same : SameCaps left right) : SameCaps right left :=
  fun letter => (same letter).symm

theorem SameCaps.simple {left right : List Nat} (same : SameCaps left right) (letter : Nat) :
    left.count letter = 1 ↔ right.count letter = 1 := by
  have counts := same letter
  omega

theorem SameCaps.multiple {left right : List Nat} (same : SameCaps left right) (letter : Nat) :
    2 ≤ left.count letter ↔ 2 ≤ right.count letter := by
  have counts := same letter
  omega

def bag (word : List Nat) : List Nat := CappedList.normal capTwo word

theorem count_bag (word : List Nat) (letter : Nat) :
    (bag word).count letter = min (word.count letter) 2 := CappedList.count_normal _ _ _

theorem bag_eq_of_caps {left right : List Nat} (same : SameCaps left right) : bag left = bag right :=
  CappedList.normal_eq_of_counts capTwo capTwo left right same

def omitLetters (excluded word : List Nat) : List Nat :=
  word.filter (fun letter => decide (letter ∉ excluded))

theorem count_omit (excluded word : List Nat) (letter : Nat) :
    (omitLetters excluded word).count letter = if letter ∈ excluded then 0 else word.count letter := by
  by_cases member : letter ∈ excluded
  · rw [if_pos member]
    exact List.count_eq_zero.mpr (by simp [omitLetters, member])
  · rw [if_neg member]
    exact List.count_filter (by simpa using member)

def bulk (excluded word : List Nat) : List Nat := bag (omitLetters excluded word)

theorem bulk_eq_of_caps (excluded : List Nat) {left right : List Nat} (same : SameCaps left right) :
    bulk excluded left = bulk excluded right := by
  apply bag_eq_of_caps
  intro letter
  simp only [count_omit]
  split
  · rfl
  · exact same letter

theorem count_bulk (excluded word : List Nat) (letter : Nat) :
    (bulk excluded word).count letter =
      if letter ∈ excluded then 0 else min (word.count letter) 2 := by
  rw [bulk, count_bag, count_omit]
  split <;> simp

def multipleList (word : List Nat) : List Nat :=
  (bag word).filter (fun letter => decide ((bag word).count letter = 2))

def pivot (word : List Nat) : Nat := (multipleList word).headD 0

theorem pivot_eq_of_caps {left right : List Nat} (same : SameCaps left right) : pivot left = pivot right := by
  simp only [pivot, multipleList, bag_eq_of_caps same]

theorem pivot_multiple (word : List Nat) (existsMultiple : ∃ letter, 2 ≤ word.count letter) :
    2 ≤ word.count (pivot word) := by
  obtain ⟨letter, many⟩ := existsMultiple
  have count : (bag word).count letter = 2 := by rw [count_bag]; omega
  have member : letter ∈ multipleList word := by
    simp only [multipleList, List.mem_filter, decide_eq_true_eq]
    exact ⟨List.count_pos_iff.mp (by omega), count⟩
  cases equation : multipleList word with
  | nil => rw [equation] at member; cases member
  | cons first rest =>
      have firstMember : first ∈ multipleList word := by rw [equation]; exact List.Mem.head _
      have firstCount : (bag word).count first = 2 := of_decide_eq_true (List.mem_filter.mp firstMember).2
      rw [count_bag] at firstCount
      simp only [pivot, equation, List.headD_cons]
      omega

def normalFrame (front : List Nat) (penultimate last : Nat) : Word Nat :=
  let word := front ++ [penultimate, last]
  if word.count last = 1 then
    if word.count penultimate = 1 then
      put (bulk [penultimate, last] word) (Word.mk penultimate [last])
    else
      let selected := pivot word
      put (bulk [selected, last] word) (Word.mk selected [selected, last])
  else if word.count last = 2 then
    if penultimate = last then
      put (bulk [last] word) (Word.mk last [last])
    else
      Word.singleton last ++ put (bulk [last] word) (Word.singleton last)
  else
    let selected := pivot word
    put (bulk [selected] word) (Word.mk selected [selected, selected])

def normalForm (word : Word Nat) : Word Nat :=
  match decompose word with
  | .single letter => Word.singleton letter
  | .frame front penultimate last => normalFrame front penultimate last

theorem normalForm_single (letter : Nat) : normalForm (Word.singleton letter) = Word.singleton letter := rfl

theorem normalForm_frame (front : List Nat) (penultimate last : Nat) :
    normalForm (framed front penultimate last) = normalFrame front penultimate last := by
  simp only [normalForm, decompose_frame]

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708.Sigma12
