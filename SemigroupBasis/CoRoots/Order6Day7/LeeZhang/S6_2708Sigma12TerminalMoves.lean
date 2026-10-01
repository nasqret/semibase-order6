import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708Sigma12Probes

/-! Expose and retarget the actual terminal squares/cubes. All moves are
unrestricted consequences of the internal subset of approved Sigma12. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708.Sigma12

open SemigroupBasis

theorem caps_of_rel {left right : List Nat} (derivation : Rel left right) : SameCaps left right := by
  cases derivation with
  | empty => intro letter; rfl
  | words proof => exact caps_of_equivalent _ _ (Derives.sound core_models proof)

theorem perm_peel_one (word : List Nat) (letter : Nat) (positive : 0 < word.count letter) :
    word.Perm (word.erase letter ++ [letter]) := by
  have expose := List.perm_cons_erase (List.count_pos_iff.mp positive)
  have move := List.perm_append_comm (l₁ := [letter]) (l₂ := word.erase letter)
  simpa only [List.cons_append, List.nil_append] using expose.trans move

theorem perm_peel_two (word : List Nat) (letter : Nat) (many : 2 ≤ word.count letter) :
    word.Perm ((word.erase letter).erase letter ++ [letter, letter]) := by
  have first := perm_peel_one word letter (by omega)
  have remaining : 0 < (word.erase letter).count letter := by
    rw [List.count_erase_self]
    omega
  have second := (perm_peel_one (word.erase letter) letter remaining).append_right [letter]
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using first.trans second

theorem relSquareExpose (front : List Nat) (penultimate last : Nat)
    (different : last ≠ penultimate)
    (many : 2 ≤ (front ++ [penultimate, last]).count penultimate) :
    ∃ rest, Rel (front ++ [penultimate, last]) (rest ++ [penultimate, penultimate, last]) := by
  have positive : 0 < front.count penultimate := by
    simp only [List.count_append, List.count_cons_self, List.count_cons_of_ne different, List.count_nil] at many
    omega
  refine ⟨front.erase penultimate, ?_⟩
  simpa only [List.append_assoc, List.cons_append, List.nil_append] using
    relPrefixPermutation (perm_peel_one front penultimate positive) penultimate last

theorem relCubeExpose (front : List Nat) (penultimate last : Nat)
    (heavy : 3 ≤ (front ++ [penultimate, last]).count last) :
    ∃ rest, Rel (front ++ [penultimate, last]) (rest ++ [last, last, last]) := by
  by_cases adjacent : penultimate = last
  · subst penultimate
    have positive : 0 < front.count last := by
      simp only [List.count_append, List.count_cons_self, List.count_nil] at heavy
      omega
    refine ⟨front.erase last, ?_⟩
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using
      relPrefixPermutation (perm_peel_one front last positive) last last
  · have many : 2 ≤ front.count last := by
      simp only [List.count_append, List.count_cons_of_ne adjacent, List.count_cons_self, List.count_nil] at heavy
      omega
    let rest := (front.erase last).erase last
    have expose := relPrefixPermutation (perm_peel_two front last many) penultimate last
    have gather := (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesHeavyGather (Word.singleton last) (Word.singleton penultimate))).prepend rest
    refine ⟨rest ++ [penultimate], ?_⟩
    simp only [rest, Word.toList_append, Word.toList_singleton,
      List.append_assoc, List.cons_append, List.nil_append] at expose gather ⊢
    exact expose.trans gather

theorem relSquareRetarget (front : List Nat) (current selected last : Nat)
    (notLast : selected ≠ last)
    (many : 2 ≤ (front ++ [current, current, last]).count selected) :
    ∃ rest, Rel (front ++ [current, current, last]) (rest ++ [selected, selected, last]) := by
  by_cases already : selected = current
  · subst selected
    exact ⟨front, .refl _⟩
  · have prefixMany : 2 ≤ front.count selected := by
      simp only [List.count_append, List.count_cons_of_ne (Ne.symm already),
        List.count_cons_of_ne (Ne.symm notLast), List.count_nil] at many
      omega
    let rest := (front.erase selected).erase selected
    have expose := relPrefixPermutation ((perm_peel_two front selected prefixMany).append_right [current]) current last
    have switched := (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (derivesSquareCommute (Word.singleton selected) (Word.singleton current) (Word.singleton last))).prepend rest
    refine ⟨rest ++ [current, current], ?_⟩
    simp only [rest, Word.toList_append, Word.toList_singleton,
      List.append_assoc, List.cons_append, List.nil_append] at expose switched ⊢
    exact expose.trans switched

theorem relCubeRetarget (front : List Nat) (current selected : Nat)
    (many : 2 ≤ (front ++ [current, current, current]).count selected) :
    ∃ rest, Rel (front ++ [current, current, current]) (rest ++ [selected, selected, selected]) := by
  by_cases already : selected = current
  · subst selected
    exact ⟨front, .refl _⟩
  · have prefixMany : 2 ≤ front.count selected := by
      simp only [List.count_append, List.count_cons_of_ne (Ne.symm already), List.count_nil] at many
      omega
    let rest := (front.erase selected).erase selected
    have expose := relPrefixPermutation ((perm_peel_two front selected prefixMany).append_right [current]) current current
    have gather := (derivesHeavyGather (Word.singleton current)
      (Word.singleton selected ++ Word.singleton selected)).symm
    have switched := (SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
      (gather.trans (derivesHeavySwitch (Word.singleton current) (Word.singleton selected)))).prepend rest
    refine ⟨rest ++ [current, current], ?_⟩
    simp only [rest, Word.toList_append, Word.toList_singleton,
      List.append_assoc, List.cons_append, List.nil_append] at expose switched ⊢
    exact expose.trans switched

theorem middle_absent_of_simple (whole before middle after : List Nat) (letter : Nat)
    (same : SameCaps whole (before ++ middle ++ after)) (simple : whole.count letter = 1)
    (present : letter ∈ before ++ after) : middle.count letter = 0 := by
  have one := (same.simple letter).mp simple
  have positive : 0 < (before ++ after).count letter := List.count_pos_iff.mpr present
  simp only [List.count_append] at one positive
  omega

/-- Compare a normalized fixed window with the global canonical bulk. -/
theorem windowNormal_eq_bulk (limit : Nat → Nat) (whole before middle after excluded : List Nat)
    (same : SameCaps whole (before ++ middle ++ after))
    (support : ∀ letter, letter ∈ before ++ after → letter ∈ excluded)
    (outside : ∀ letter, letter ∉ excluded → limit letter = 2)
    (excludedGone : ∀ letter, letter ∈ excluded → min (middle.count letter) (limit letter) = 0) :
    CappedList.normal limit middle = bulk excluded whole := by
  change CappedList.normal limit middle = CappedList.normal capTwo (omitLetters excluded whole)
  apply CappedList.normal_eq_of_counts
  intro letter
  rw [count_omit]
  by_cases member : letter ∈ excluded
  · rw [if_pos member]
    simpa only [Nat.zero_min] using excludedGone letter member
  · rw [if_neg member, outside letter member]
    have contextZero : (before ++ after).count letter = 0 :=
      List.count_eq_zero.mpr (fun present => member (support letter present))
    have counts := same letter
    simp only [List.count_append] at contextZero counts
    have beforeZero : before.count letter = 0 := by omega
    have afterZero : after.count letter = 0 := by omega
    simpa only [beforeZero, afterZero, Nat.zero_add, Nat.add_zero, capTwo] using counts.symm

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708.Sigma12
