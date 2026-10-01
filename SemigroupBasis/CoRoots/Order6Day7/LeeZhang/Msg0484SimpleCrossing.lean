import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0484SimplePrefix

/-! Exact simple-separator data forbids crossing a globally simple letter.
This is a count argument on arbitrary lists, not a bounded-table assertion. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.SimplePrefix

open PrefixCount

theorem first_remaining_heavy (prefixWords gap leftTail rightTail : List Nat) (letter : Nat)
    (first : letter ∉ gap)
    (same : ExactSignature (prefixWords ++ letter :: leftTail)
      (prefixWords ++ gap ++ letter :: rightTail)) :
    ∀ tested ∈ gap,
      2 ≤ (prefixWords ++ gap ++ letter :: rightTail).count letter ∧
      2 ≤ (prefixWords ++ gap ++ letter :: rightTail).count tested := by
  intro tested member
  have different : letter ≠ tested := by
    intro equal
    subst tested
    exact first member
  have letterPositive : 1 ≤ (prefixWords ++ gap ++ letter :: rightTail).count letter := by
    simp only [List.count_append, List.count_cons_self]
    omega
  have gapPositive : 0 < gap.count tested := List.count_pos_iff.mpr member
  have testedPositive : 1 ≤ (prefixWords ++ gap ++ letter :: rightTail).count tested := by
    simp only [List.count_append]
    omega
  have letterHeavy : 2 ≤ (prefixWords ++ gap ++ letter :: rightTail).count letter := by
    by_cases failure : 2 ≤ (prefixWords ++ gap ++ letter :: rightTail).count letter
    · exact failure
    exfalso
    have one : (prefixWords ++ letter :: leftTail).count letter = 1 := by
      have equality := same.counts letter
      omega
    have absent : letter ∉ prefixWords := by
      apply List.not_mem_of_count_eq_zero
      simp only [List.count_append, List.count_cons_self] at one
      omega
    have extendedAbsent : letter ∉ prefixWords ++ gap := by simp [absent, first]
    have equality := same.prefixes letter one tested
    rw [before_append_of_not_mem letter prefixWords _ absent,
      before_append_of_not_mem letter (prefixWords ++ gap) _ extendedAbsent] at equality
    simp only [before_self, List.append_nil, List.count_append] at equality
    omega
  have testedHeavy : 2 ≤ (prefixWords ++ gap ++ letter :: rightTail).count tested := by
    by_cases failure : 2 ≤ (prefixWords ++ gap ++ letter :: rightTail).count tested
    · exact failure
    exfalso
    have one : (prefixWords ++ letter :: leftTail).count tested = 1 := by
      have equality := same.counts tested
      omega
    have absent : tested ∉ prefixWords := by
      apply List.not_mem_of_count_eq_zero
      have otherOne := (same.counts tested).symm.trans one
      simp only [List.count_append] at otherOne
      omega
    have gapBeforeZero : (before tested gap).count letter = 0 :=
      List.count_eq_zero_of_not_mem (fun inside => first (mem_before tested letter inside))
    have equality := same.prefixes tested one letter
    rw [before_append_of_not_mem tested prefixWords _ absent,
      before_cons_of_ne tested letter leftTail different] at equality
    have rightShape : before tested (prefixWords ++ gap ++ letter :: rightTail) =
        prefixWords ++ before tested gap := by
      rw [List.append_assoc, before_append_of_not_mem tested prefixWords _ absent,
        before_append_of_mem tested gap _ member]
    rw [rightShape] at equality
    simp only [List.count_append, List.count_cons_self, gapBeforeZero] at equality
    omega
  exact ⟨letterHeavy, testedHeavy⟩

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.SimplePrefix
