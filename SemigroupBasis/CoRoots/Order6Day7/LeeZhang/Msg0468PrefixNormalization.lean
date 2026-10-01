import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0468PrefixComparison
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0463TripleOccurrenceSplit

/-! A genuine unbounded cap-and-compare engine. Both algebraic hypotheses
are explicit: guarded swaps and insertion at three prior occurrences. A
concrete basis must discharge them before this theorem supplies derivations. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.PrefixCount

open SemigroupBasis

def GrowAtThree (basis : List (Identity Nat)) : Prop :=
  ∀ (letters : List Nat) (letter : Nat), 3 ≤ letters.count letter →
    S5_107.ListDerives basis letters (letters ++ [letter])

def TripleIntervalGrowth (basis : List (Identity Nat)) : Prop :=
  ∀ (letter : Nat) (firstGap secondGap : List Nat),
    S5_107.ListDerives basis ([letter] ++ firstGap ++ [letter] ++ secondGap ++ [letter])
      ([letter] ++ firstGap ++ [letter] ++ secondGap ++ [letter, letter])

theorem grow_at_three_of_interval {basis : List (Identity Nat)}
    (swaps : GuardedSwaps basis) (grow : TripleIntervalGrowth basis) : GrowAtThree basis := by
  intro letters letter triple
  obtain ⟨prefixWords, firstGap, secondGap, after, shape⟩ :=
    Msg0463NilZ2.exists_three_occurrence_split letter triple
  let interval := [letter] ++ firstGap ++ [letter] ++ secondGap ++ [letter]
  have expanded : S5_107.ListDerives basis (prefixWords ++ interval ++ after)
      ((prefixWords ++ interval) ++ letter :: after) := by
    simpa [interval, List.append_assoc] using (grow letter firstGap secondGap).context prefixWords after
  have twice : 2 ≤ (prefixWords ++ interval).count letter := by
    simp only [interval, List.count_append, List.count_cons_self, List.count_nil]
    omega
  have allowed : ∀ tested ∈ after, Crossable (prefixWords ++ interval) letter tested :=
    fun _ _ => Or.inl twice
  have moved := (move_head_left swaps (prefixWords ++ interval) after [] letter allowed).1.symm
  have combined := expanded.trans (by simpa using moved)
  simpa [shape, interval, List.append_assoc] using combined

def trim (prefixWords : List Nat) : List Nat → List Nat
  | [] => []
  | letter :: tail =>
      if 3 ≤ prefixWords.count letter then trim prefixWords tail
      else letter :: trim (prefixWords ++ [letter]) tail

theorem trim_count (prefixWords letters : List Nat) (tested : Nat) :
    (trim prefixWords letters).count tested =
      min (3 - prefixWords.count tested) (letters.count tested) := by
  induction letters generalizing prefixWords with
  | nil => simp [trim]
  | cons letter tail induction =>
      by_cases full : 3 ≤ prefixWords.count letter
      · rw [trim, if_pos full, induction]
        by_cases equal : letter = tested
        · subst tested
          simp only [List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne equal]
      · rw [trim, if_neg full]
        by_cases equal : letter = tested
        · subst tested
          simp only [List.count_cons_self, induction, List.count_append, List.count_nil]
          omega
        · simp only [List.count_cons_of_ne equal, induction, List.count_append, List.count_nil,
            Nat.add_zero]

theorem sameBeforeTwo_drop (prefixWords : List Nat) (letter : Nat) (tail : List Nat)
    (twice : 2 ≤ prefixWords.count letter) :
    SameBeforeTwo (prefixWords ++ letter :: tail) (prefixWords ++ tail) := by
  intro tested separator
  by_cases old : separator ∈ prefixWords
  · rw [before_append_of_mem separator prefixWords _ old,
      before_append_of_mem separator prefixWords _ old]
  · have different : letter ≠ separator := by
      intro equal
      subst separator
      have zero := List.count_eq_zero_of_not_mem old
      omega
    rw [before_append_of_not_mem separator prefixWords _ old,
      before_append_of_not_mem separator prefixWords _ old,
      before_cons_of_ne separator letter tail different]
    by_cases selected : letter = tested
    · subst tested
      simp only [List.count_append, List.count_cons_self]
      omega
    · simp only [List.count_append, List.count_cons_of_ne selected]

theorem trim_preserves_before (prefixWords letters : List Nat) :
    SameBeforeTwo (prefixWords ++ letters) (prefixWords ++ trim prefixWords letters) := by
  induction letters generalizing prefixWords with
  | nil => exact SameBeforeTwo.refl _
  | cons letter tail induction =>
      by_cases full : 3 ≤ prefixWords.count letter
      · rw [trim, if_pos full]
        exact (sameBeforeTwo_drop prefixWords letter tail (by omega)).trans (induction prefixWords)
      · rw [trim, if_neg full]
        simpa [List.append_assoc] using induction (prefixWords ++ [letter])

theorem trim_derives {basis : List (Identity Nat)} (grow : GrowAtThree basis)
    (prefixWords letters : List Nat) :
    S5_107.ListDerives basis (prefixWords ++ letters) (prefixWords ++ trim prefixWords letters) := by
  induction letters generalizing prefixWords with
  | nil => exact S5_107.ListDerives.refl _
  | cons letter tail induction =>
      by_cases full : 3 ≤ prefixWords.count letter
      · rw [trim, if_pos full]
        have deletion : S5_107.ListDerives basis (prefixWords ++ letter :: tail) (prefixWords ++ tail) := by
          simpa [List.append_assoc] using ((grow prefixWords letter full).append tail).symm
        exact deletion.trans (induction prefixWords)
      · rw [trim, if_neg full]
        simpa [List.append_assoc] using induction (prefixWords ++ [letter])

def SameCapsThree (left right : List Nat) : Prop :=
  ∀ tested, min 3 (left.count tested) = min 3 (right.count tested)

/-- The full unbounded derivation theorem for any basis with the two
proved capabilities. No quotient normalizer or finite test is used. -/
theorem compare_capped_counts {basis : List (Identity Nat)} (swaps : GuardedSwaps basis)
    (grow : GrowAtThree basis) (left right : List Nat)
    (counts : SameCapsThree left right) (same : SameBeforeTwo left right) :
    S5_107.ListDerives basis left right := by
  have leftDerivation : S5_107.ListDerives basis left (trim [] left) := by
    simpa using trim_derives grow [] left
  have rightDerivation : S5_107.ListDerives basis right (trim [] right) := by
    simpa using trim_derives grow [] right
  have exactCounts : ∀ tested, (trim [] left).count tested = (trim [] right).count tested := by
    intro tested
    simpa only [trim_count, List.count_nil, Nat.sub_zero] using counts tested
  have leftSame : SameBeforeTwo left (trim [] left) := by simpa using trim_preserves_before [] left
  have rightSame : SameBeforeTwo right (trim [] right) := by simpa using trim_preserves_before [] right
  have reducedSame := leftSame.symm.trans (same.trans rightSame)
  have middle : S5_107.ListDerives basis (trim [] left) (trim [] right) := by
    simpa using compare_exact_counts swaps [] (trim [] left) (trim [] right) exactCounts
      (by simpa using reducedSame)
  exact leftDerivation.trans (middle.trans rightDerivation.symm)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.PrefixCount
