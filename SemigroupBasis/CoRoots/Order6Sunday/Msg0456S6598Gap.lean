import SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Rewrites

/-! B25 normalizes arbitrary globally repeated gaps to a sorted, reduced
support/parity renderer. All extracted pairs remain in an anchored bank;
the first introduction contributes one or two actual copies. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Gap

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Day7.LeeZhang
open Msg0456S6598Semantics Msg0456S6598Rewrites

theorem repeatedGapPermutation (prefixWords suffix : List Nat) {left right : List Nat}
    (permutation : left.Perm right) (repeated : AllRepeated prefixWords left suffix) :
    LD (prefixWords ++ left ++ suffix) (prefixWords ++ right ++ suffix) := by
  induction permutation generalizing prefixWords with
  | nil => exact S5_107.ListDerives.refl _
  | cons letter _ induction =>
      apply (show LD (prefixWords ++ _ ++ suffix) (prefixWords ++ _ ++ suffix) from ?_)
      simpa [List.append_assoc] using induction (prefixWords ++ [letter]) (by
        intro tested member
        have original := repeated tested (List.mem_cons_of_mem letter member)
        simpa [List.append_assoc] using original)
  | swap left right rest =>
      have first : 2 ≤ (prefixWords ++ [right,left] ++ (rest ++ suffix)).count right := by
        simpa [List.append_assoc] using repeated right (by simp)
      have second : 2 ≤ (prefixWords ++ [right,left] ++ (rest ++ suffix)).count left := by
        simpa [List.append_assoc] using repeated left (by simp)
      simpa [List.append_assoc] using swapRepeated prefixWords (rest ++ suffix) right left first second
  | trans firstPermutation _ first second =>
      apply (first prefixWords repeated).trans
      apply second prefixWords
      intro tested member
      have original := repeated tested (firstPermutation.mem_iff.mpr member)
      simp only [List.count_append] at original ⊢
      rw [← firstPermutation.count tested]
      exact original

/-- Exact multiplicities now suffice, without relative first-order data. -/
theorem compareRepeatedGaps (prefixWords left right suffix : List Nat)
    (counts : ∀ tested, left.count tested = right.count tested)
    (repeated : AllRepeated prefixWords left suffix) :
    LD (prefixWords ++ left ++ suffix) (prefixWords ++ right ++ suffix) :=
  repeatedGapPermutation prefixWords suffix (List.perm_iff_count.mpr counts) repeated

def canonicalGap (seen gap : List Nat) : List Nat :=
  S5_254.canonicalGapResidue (FordNil.canonicalGap seen gap)

theorem canonicalGap_count (seen gap : List Nat) (tested : Nat) :
    (canonicalGap seen gap).count tested =
      if tested ∈ seen then gap.count tested % 2
      else if tested ∈ gap then Msg0446TailBudget.firstCopies (gap.count tested % 2) else 0 := by
  rw [canonicalGap]
  change ((FordNil.canonicalGap seen gap).mergeSort _).count tested = _
  rw [(List.mergeSort_perm _ _).count tested, FordNil.canonicalGap_count]

theorem canonicalGap_parity (seen gap : List Nat) (tested : Nat) :
    (canonicalGap seen gap).count tested % 2 = gap.count tested % 2 := by
  change ((FordNil.canonicalGap seen gap).mergeSort _).count tested % 2 = _
  rw [(List.mergeSort_perm _ _).count tested, FordNil.canonicalGap_parity]

theorem canonicalGap_reduced (seen gap : List Nat) : FordNil.GapReduced seen (canonicalGap seen gap) := by
  intro tested
  have bound := FordNil.canonicalGap_reduced seen gap tested
  change ((FordNil.canonicalGap seen gap).mergeSort _).count tested ≤ _
  rw [(List.mergeSort_perm _ _).count tested]
  exact bound

theorem canonicalGap_pairwise (seen gap : List Nat) :
    (canonicalGap seen gap).Pairwise (· ≤ ·) :=
  S5_254.canonicalGapResidue_pairwise _

theorem canonicalGap_support (seen gap : List Nat) (tested : Nat) :
    tested ∈ seen ++ canonicalGap seen gap ↔ tested ∈ seen ++ gap := by
  have support := FordNil.mem_prefix_gap_iff_of_freshOrder (FordNil.canonicalGap_order seen gap) tested
  have sortedSupport : tested ∈ canonicalGap seen gap ↔ tested ∈ FordNil.canonicalGap seen gap :=
    (List.mergeSort_perm _ _).mem_iff
  simpa only [List.mem_append, sortedSupport] using support

/-- Prefix support and parity, not the order of new introductions, determine
the sorted gap literally. -/
theorem canonicalGap_eq (leftSeen rightSeen left right : List Nat)
    (seen : ∀ tested, tested ∈ leftSeen ↔ tested ∈ rightSeen)
    (support : ∀ tested, tested ∈ leftSeen ++ left ↔ tested ∈ rightSeen ++ right)
    (parity : ∀ tested, left.count tested % 2 = right.count tested % 2) :
    canonicalGap leftSeen left = canonicalGap rightSeen right := by
  have counts : ∀ tested, (canonicalGap leftSeen left).count tested =
      (canonicalGap rightSeen right).count tested := by
    intro tested
    rw [canonicalGap_count, canonicalGap_count]
    by_cases old : tested ∈ leftSeen
    · have oldRight := (seen tested).mp old
      simp [old, oldRight, parity tested]
    · have notRight : tested ∉ rightSeen := fun member => old ((seen tested).mpr member)
      have gapSupport : tested ∈ left ↔ tested ∈ right := by
        simpa [old, notRight] using support tested
      simp [old, notRight, gapSupport, parity tested]
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ first second => Nat.le_antisymm first second)
    (canonicalGap_pairwise leftSeen left) (canonicalGap_pairwise rightSeen right)
    (List.perm_iff_count.mpr counts)

/-- Unrestricted B25 reach of the sorted gap. No pair is discarded. -/
theorem normalizeRepeatedGap (prefixWords gap suffix : List Nat)
    (repeated : AllRepeated prefixWords gap suffix) :
    ∃ labels,
      LD (prefixWords ++ gap ++ suffix)
        (prefixWords ++ canonicalGap prefixWords gap ++ suffix ++ S5_254.renderSquareBank labels) ∧
      (∀ tested, gap.count tested =
        (canonicalGap prefixWords gap).count tested + 2 * labels.count tested) ∧
      (∀ tested ∈ labels, tested ∈ prefixWords ++ canonicalGap prefixWords gap) := by
  obtain ⟨labels, derived, counts, seen⟩ := FordNil.normalizeRepeatedGap prefixWords gap suffix repeated
  have sortedCounts : ∀ tested, (canonicalGap prefixWords gap).count tested =
      (FordNil.canonicalGap prefixWords gap).count tested := by
    intro tested
    exact (List.mergeSort_perm _ _).count tested
  have stillRepeated : AllRepeated prefixWords (FordNil.canonicalGap prefixWords gap)
      (suffix ++ S5_254.renderSquareBank labels) := by
    intro tested member
    have positive := List.count_pos_iff.mpr member
    have countEq := counts tested
    have original := repeated tested (List.count_pos_iff.mp (by omega))
    simp only [List.count_append, S5_254.count_renderSquareBank] at original ⊢
    omega
  have sorted := compareRepeatedGaps prefixWords (FordNil.canonicalGap prefixWords gap)
    (canonicalGap prefixWords gap) (suffix ++ S5_254.renderSquareBank labels)
    (fun tested => (sortedCounts tested).symm) stillRepeated
  refine ⟨labels, (transportFordList derived).trans ?_, ?_, ?_⟩
  · simpa [List.append_assoc] using sorted
  · intro tested
    rw [sortedCounts]
    exact counts tested
  · intro tested member
    have old := seen tested member
    have sameSupport : tested ∈ canonicalGap prefixWords gap ↔
        tested ∈ FordNil.canonicalGap prefixWords gap := (List.mergeSort_perm _ _).mem_iff
    simpa only [List.mem_append, sameSupport] using old

end SemigroupBasis.CoRoots.Order6Sunday.Msg0456S6598Gap
