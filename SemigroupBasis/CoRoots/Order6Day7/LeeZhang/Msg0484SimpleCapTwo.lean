import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0484SimpleComparison
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0468PrefixNormalization

/-! Keep the first two occurrences, then compare exact simple-prefix data.
Both algebraic capabilities remain explicit until a concrete basis proves
them. No bounded word window or assumed unrestricted completeness is used. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.SimplePrefix

open SemigroupBasis PrefixCount

def GrowAtTwo (basis : List (Identity Nat)) : Prop :=
  ∀ (letters : List Nat) (letter : Nat), 2 ≤ letters.count letter →
    S5_107.ListDerives basis letters (letters ++ [letter])

def trimTwo (prefixWords : List Nat) : List Nat → List Nat
  | [] => []
  | letter :: tail =>
      if 2 ≤ prefixWords.count letter then trimTwo prefixWords tail
      else letter :: trimTwo (prefixWords ++ [letter]) tail

theorem trimTwo_count (prefixWords letters : List Nat) (tested : Nat) :
    (trimTwo prefixWords letters).count tested =
      min (2 - prefixWords.count tested) (letters.count tested) := by
  induction letters generalizing prefixWords with
  | nil => simp [trimTwo]
  | cons letter tail induction =>
      by_cases full : 2 ≤ prefixWords.count letter
      · rw [trimTwo, if_pos full, induction]
        by_cases equal : letter = tested
        · subst tested
          simp only [List.count_cons_self]
          omega
        · rw [List.count_cons_of_ne equal]
      · rw [trimTwo, if_neg full]
        by_cases equal : letter = tested
        · subst tested
          simp only [List.count_cons_self, induction, List.count_append, List.count_nil]
          omega
        · simp only [List.count_cons_of_ne equal, induction, List.count_append, List.count_nil,
            Nat.add_zero]

theorem trimTwo_preserves_before (prefixWords letters : List Nat) :
    SameBeforeTwo (prefixWords ++ letters) (prefixWords ++ trimTwo prefixWords letters) := by
  induction letters generalizing prefixWords with
  | nil => exact SameBeforeTwo.refl _
  | cons letter tail induction =>
      by_cases full : 2 ≤ prefixWords.count letter
      · rw [trimTwo, if_pos full]
        exact (sameBeforeTwo_drop prefixWords letter tail full).trans (induction prefixWords)
      · rw [trimTwo, if_neg full]
        simpa [List.append_assoc] using induction (prefixWords ++ [letter])

theorem trimTwo_derives {basis : List (Identity Nat)} (grow : GrowAtTwo basis)
    (prefixWords letters : List Nat) :
    S5_107.ListDerives basis (prefixWords ++ letters) (prefixWords ++ trimTwo prefixWords letters) := by
  induction letters generalizing prefixWords with
  | nil => exact S5_107.ListDerives.refl _
  | cons letter tail induction =>
      by_cases full : 2 ≤ prefixWords.count letter
      · rw [trimTwo, if_pos full]
        have deletion : S5_107.ListDerives basis (prefixWords ++ letter :: tail) (prefixWords ++ tail) := by
          simpa [List.append_assoc] using ((grow prefixWords letter full).append tail).symm
        exact deletion.trans (induction prefixWords)
      · rw [trimTwo, if_neg full]
        simpa [List.append_assoc] using induction (prefixWords ++ [letter])

structure CappedSignature (left right : List Nat) : Prop where
  counts : ∀ tested, min 2 (left.count tested) = min 2 (right.count tested)
  prefixes : ∀ separator, left.count separator = 1 → ∀ tested,
    min 2 ((before separator left).count tested) = min 2 ((before separator right).count tested)

theorem CappedSignature.simple_count {left right : List Nat} (same : CappedSignature left right)
    (separator : Nat) (one : left.count separator = 1) : right.count separator = 1 := by
  have equal := same.counts separator
  omega

theorem CappedSignature.symm {left right : List Nat} (same : CappedSignature left right) :
    CappedSignature right left := by
  refine ⟨fun tested => (same.counts tested).symm, ?_⟩
  intro separator one tested
  have leftOne : left.count separator = 1 := by
    have equal := same.counts separator
    omega
  exact (same.prefixes separator leftOne tested).symm

theorem CappedSignature.trans {left middle right : List Nat}
    (first : CappedSignature left middle) (second : CappedSignature middle right) :
    CappedSignature left right := by
  refine ⟨fun tested => (first.counts tested).trans (second.counts tested), ?_⟩
  intro separator one tested
  exact (first.prefixes separator one tested).trans
    (second.prefixes separator (first.simple_count separator one) tested)

theorem trimTwo_exact_signature {left right : List Nat} (same : CappedSignature left right) :
    ExactSignature (trimTwo [] left) (trimTwo [] right) := by
  refine ⟨?_, ?_⟩
  · intro tested
    simpa only [trimTwo_count, List.count_nil, Nat.sub_zero] using same.counts tested
  · intro separator one tested
    have leftOne : left.count separator = 1 := by
      have count := trimTwo_count [] left separator
      simp only [List.count_nil, Nat.sub_zero] at count
      omega
    have original := same.prefixes separator leftOne tested
    have leftBefore : min 2 ((before separator left).count tested) =
        min 2 ((before separator (trimTwo [] left)).count tested) := by
      simpa using (trimTwo_preserves_before [] left) tested separator
    have rightBefore : min 2 ((before separator right).count tested) =
        min 2 ((before separator (trimTwo [] right)).count tested) := by
      simpa using (trimTwo_preserves_before [] right) tested separator
    have equal := leftBefore.symm.trans (original.trans rightBefore)
    have leftBound : (before separator (trimTwo [] left)).count tested ≤ 2 := by
      apply Nat.le_trans (before_count_le separator tested _)
      rw [trimTwo_count]
      simp only [List.count_nil, Nat.sub_zero]
      omega
    have rightBound : (before separator (trimTwo [] right)).count tested ≤ 2 := by
      apply Nat.le_trans (before_count_le separator tested _)
      rw [trimTwo_count]
      simp only [List.count_nil, Nat.sub_zero]
      omega
    simpa only [Nat.min_eq_right leftBound, Nat.min_eq_right rightBound] using equal

theorem compare_capped {basis : List (Identity Nat)} (swaps : GlobalSwaps basis)
    (grow : GrowAtTwo basis) (left right : List Nat) (same : CappedSignature left right) :
    S5_107.ListDerives basis left right := by
  have leftDerivation : S5_107.ListDerives basis left (trimTwo [] left) := by
    simpa using trimTwo_derives grow [] left
  have rightDerivation : S5_107.ListDerives basis right (trimTwo [] right) := by
    simpa using trimTwo_derives grow [] right
  have middle : S5_107.ListDerives basis (trimTwo [] left) (trimTwo [] right) := by
    simpa using compare_exact swaps [] (trimTwo [] left) (trimTwo [] right)
      (by simpa using trimTwo_exact_signature same)
  exact leftDerivation.trans (middle.trans rightDerivation.symm)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.SimplePrefix
