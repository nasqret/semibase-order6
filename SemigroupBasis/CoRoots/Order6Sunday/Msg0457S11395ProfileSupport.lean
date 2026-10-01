import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395GapParity

/-! Literal nonfirst-occurrence gap support. A positive gap coordinate
forces repetition in the whole word. Conversely, for a repeated target,
suffix membership is equivalent to positive gap support in that suffix. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ProfileSupport

open SemigroupBasis
open Msg0457S11395WordGaps Msg0457S11395ResolveLetter
open Msg0457S11395CoordinateSectors Msg0457S11395SectorSignature Msg0457S11395ScalarRender

theorem zero_profile_count (chain : Chain) (tested : Nat)
    (empty : positive (gapProfile tested chain) = false) :
    (flatten chain).count tested = (introductions chain).count tested := by
  induction chain with
  | stop gap =>
      have zero := positive_false_all_zero (gapProfile tested (.stop gap)) empty
        (gap.count tested) List.mem_cons_self
      exact zero
  | step gap fresh tail ih =>
      have zero := positive_false_all_zero (gapProfile tested (.step gap fresh tail)) empty
        (gap.count tested) List.mem_cons_self
      have tailEmpty : positive (gapProfile tested tail) = false := by
        simpa only [gapProfile, positive, zero] using empty
      simp only [flatten, introductions, List.count_append, List.count_cons, zero, Nat.zero_add, ih tailEmpty]

theorem positive_profile_repeated (prefixWords : List Nat) (chain : Chain) (tested : Nat)
    (good : WellFormed prefixWords chain) (active : positive (gapProfile tested chain) = true) :
    2 ≤ (prefixWords ++ flatten chain).count tested := by
  induction chain generalizing prefixWords with
  | stop gap =>
      have gapPositive : 0 < gap.count tested := by simpa [gapProfile, positive] using active
      have pastPositive := List.count_pos_iff.mpr (good tested (List.count_pos_iff.mp gapPositive))
      simp only [flatten, List.count_append]
      omega
  | step gap fresh tail ih =>
      by_cases gapPositive : 0 < gap.count tested
      · have pastPositive := List.count_pos_iff.mpr (good.1 tested (List.count_pos_iff.mp gapPositive))
        simp only [flatten, List.count_append, List.count_cons]
        omega
      · have later : positive (gapProfile tested tail) = true := by
          simpa [gapProfile, positive, gapPositive] using active
        simpa only [flatten, List.append_assoc, List.singleton_append] using
          ih (prefixWords ++ gap ++ [fresh]) good.2.2 later

theorem profile_zero_of_small (prefixWords : List Nat) (chain : Chain) (tested : Nat)
    (good : WellFormed prefixWords chain) (small : (prefixWords ++ flatten chain).count tested < 2) :
    positive (gapProfile tested chain) = false := by
  cases active : positive (gapProfile tested chain) with
  | false => rfl
  | true => have repeated := positive_profile_repeated prefixWords chain tested good active; omega

theorem repeated_profile_positive_iff (prefixWords : List Nat) (chain : Chain) (tested : Nat)
    (good : WellFormed prefixWords chain) (repeated : 2 ≤ (prefixWords ++ flatten chain).count tested) :
    positive (gapProfile tested chain) = true ↔ tested ∈ flatten chain := by
  constructor
  · exact positive_profile_mem chain tested
  · intro member
    cases active : positive (gapProfile tested chain) with
    | true => rfl
    | false =>
        have sameCount := zero_profile_count chain tested active
        have introPositive : 0 < (introductions chain).count tested := by
          rw [← sameCount]
          exact List.count_pos_iff.mpr member
        have pastAbsent := introductions_absent chain prefixWords good tested (List.count_pos_iff.mp introPositive)
        have pastZero := List.count_eq_zero.mpr pastAbsent
        have bound : (introductions chain).count tested ≤ 1 := by
          rw [(introductions_nodup chain prefixWords good).count]
          split <;> omega
        rw [List.count_append, pastZero, Nat.zero_add, sameCount] at repeated
        omega

theorem profile_positive_formula (prefixWords : List Nat) (chain : Chain) (tested : Nat)
    (good : WellFormed prefixWords chain) :
    positive (gapProfile tested chain) =
      decide (2 ≤ (prefixWords ++ flatten chain).count tested ∧ tested ∈ flatten chain) := by
  by_cases repeated : 2 ≤ (prefixWords ++ flatten chain).count tested
  · have equal := repeated_profile_positive_iff prefixWords chain tested good repeated
    cases active : positive (gapProfile tested chain) <;> simp_all
  · rw [profile_zero_of_small prefixWords chain tested good (by omega)]
    simp only [repeated, false_and, decide_false]

theorem singleton_profile_positive (head tested : Nat) (chain : Chain) (good : WellFormed [head] chain) :
    positive (gapProfile tested chain) = decide (2 ≤ (head :: flatten chain).count tested) := by
  rw [profile_positive_formula [head] chain tested good]
  by_cases repeated : 2 ≤ (head :: flatten chain).count tested
  · have member : tested ∈ flatten chain := by
      apply List.count_pos_iff.mp
      have equation : (head :: flatten chain).count tested =
          (flatten chain).count tested + (if head == tested then 1 else 0) := List.count_cons
      split at equation <;> omega
    simp [repeated, member]
  · simp [repeated]

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395ProfileSupport
