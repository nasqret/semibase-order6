import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708Sigma12TerminalMoves
import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708Sigma12Semantics

/-! Every input word reaches its concrete canonical word by approved-law
derivations. Exposure, pivot retargeting, cap reduction, and sorting are separate
proved stages; no search bound appears in their statements. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708.Sigma12

open SemigroupBasis
open S4_71Suffix (put put_toList)

theorem relFreeNormal (front : List Nat) (penultimate last : Nat)
    (penultimateSimple : (front ++ [penultimate, last]).count penultimate = 1)
    (lastSimple : (front ++ [penultimate, last]).count last = 1) :
    Rel (front ++ [penultimate, last])
      (bulk [penultimate, last] (front ++ [penultimate, last]) ++ [penultimate, last]) := by
  let whole := front ++ [penultimate, last]
  have same : SameCaps whole ([] ++ front ++ [penultimate, last]) := fun _ => rfl
  have penultimateZero := middle_absent_of_simple whole [] front [penultimate, last] penultimate
    same penultimateSimple (by simp)
  have lastZero := middle_absent_of_simple whole [] front [penultimate, last] last
    same lastSimple (by simp)
  have canonical := windowNormal_eq_bulk capTwo whole [] front [penultimate, last] [penultimate, last]
    same (by intro letter member; simpa using member) (by intro letter _; rfl) (by
      intro letter member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simp only [penultimateZero, Nat.zero_min]
      · simp only [lastZero, Nat.zero_min])
  have normalized := relPrefixNormal front penultimate last
  rw [canonical] at normalized
  exact normalized

theorem relAdjacentNormal (front : List Nat) (last : Nat)
    (double : (front ++ [last, last]).count last = 2) :
    Rel (front ++ [last, last]) (bulk [last] (front ++ [last, last]) ++ [last, last]) := by
  let whole := front ++ [last, last]
  have absent : front.count last = 0 := by
    simp only [List.count_append, List.count_cons_self, List.count_nil] at double
    omega
  have canonical := windowNormal_eq_bulk capTwo whole [] front [last, last] [last]
    (fun _ => rfl) (by intro letter member; simpa using member) (by intro letter _; rfl) (by
      intro letter member
      have equal : letter = last := by simpa using member
      subst letter
      simp only [absent, Nat.zero_min])
  have normalized := relPrefixNormal front last last
  rw [canonical] at normalized
  exact normalized

theorem relSeparatedNormal (front : List Nat) (penultimate last : Nat)
    (different : penultimate ≠ last)
    (double : (front ++ [penultimate, last]).count last = 2) :
    Rel (front ++ [penultimate, last])
      ([last] ++ bulk [last] (front ++ [penultimate, last]) ++ [last]) := by
  let whole := front ++ [penultimate, last]
  have count : front.count last = 1 := by
    simp only [List.count_append, List.count_cons_of_ne different, List.count_cons_self, List.count_nil] at double
    omega
  let middle := front.erase last ++ [penultimate]
  have permutation := List.perm_cons_erase (List.count_pos_iff.mp (by omega : 0 < front.count last))
  have expose : Rel whole ([last] ++ middle ++ [last]) := by
    simpa only [whole, middle, List.append_assoc, List.cons_append, List.nil_append] using
      relPrefixPermutation permutation penultimate last
  have absent : middle.count last = 0 := by
    simp only [middle, List.count_append, List.count_erase_self, count,
      List.count_cons_of_ne different, List.count_nil]
  have canonical := windowNormal_eq_bulk capTwo whole [last] middle [last] [last]
    (caps_of_rel expose) (by intro letter member; simpa using member) (by intro letter _; rfl) (by
      intro letter member
      have equal : letter = last := by simpa using member
      subst letter
      simp only [absent, Nat.zero_min])
  have normalized := relMiddleNormal last middle
  rw [canonical] at normalized
  exact expose.trans normalized

theorem relBoundNormal (front : List Nat) (penultimate last : Nat)
    (penultimateMany : 2 ≤ (front ++ [penultimate, last]).count penultimate)
    (lastSimple : (front ++ [penultimate, last]).count last = 1) :
    Rel (front ++ [penultimate, last])
      (bulk [pivot (front ++ [penultimate, last]), last] (front ++ [penultimate, last]) ++
        [pivot (front ++ [penultimate, last]), pivot (front ++ [penultimate, last]), last]) := by
  let whole := front ++ [penultimate, last]
  let selected := pivot whole
  have different := Ne.symm (penultimate_ne_last front penultimate last lastSimple)
  obtain ⟨firstRest, expose⟩ := relSquareExpose front penultimate last different penultimateMany
  have selectedMany : 2 ≤ whole.count selected := pivot_multiple whole ⟨penultimate, penultimateMany⟩
  have selectedNotLast : selected ≠ last := by
    intro equal
    rw [equal] at selectedMany
    change 2 ≤ (front ++ [penultimate, last]).count last at selectedMany
    omega
  have intermediateMany := ((caps_of_rel expose).multiple selected).mp selectedMany
  obtain ⟨rest, retarget⟩ := relSquareRetarget firstRest penultimate selected last selectedNotLast intermediateMany
  have first : Rel whole (rest ++ [selected, selected, last]) := expose.trans retarget
  have same : SameCaps whole ([] ++ rest ++ [selected, selected, last]) := caps_of_rel first
  have lastZero := middle_absent_of_simple whole [] rest [selected, selected, last] last same lastSimple (by simp)
  have canonical := windowNormal_eq_bulk (exceptPivot selected) whole [] rest [selected, selected, last] [selected, last]
    same (by intro letter member; simpa using member) (by
      intro letter notMember
      have notSelected : letter ≠ selected := by
        intro equal
        subst letter
        exact notMember (by simp)
      simp only [exceptPivot, if_neg notSelected]) (by
      intro letter member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · simp [exceptPivot]
      · simp only [lastZero, Nat.zero_min])
  have normalized := relSquareNormal rest selected last
  rw [canonical] at normalized
  exact first.trans normalized

theorem relHeavyNormal (front : List Nat) (penultimate last : Nat)
    (heavy : 3 ≤ (front ++ [penultimate, last]).count last) :
    Rel (front ++ [penultimate, last])
      (bulk [pivot (front ++ [penultimate, last])] (front ++ [penultimate, last]) ++
        [pivot (front ++ [penultimate, last]), pivot (front ++ [penultimate, last]), pivot (front ++ [penultimate, last])]) := by
  let whole := front ++ [penultimate, last]
  let selected := pivot whole
  obtain ⟨firstRest, expose⟩ := relCubeExpose front penultimate last heavy
  have selectedMany : 2 ≤ whole.count selected := pivot_multiple whole ⟨last, by
    change 2 ≤ (front ++ [penultimate, last]).count last
    omega⟩
  have intermediateMany := ((caps_of_rel expose).multiple selected).mp selectedMany
  obtain ⟨rest, retarget⟩ := relCubeRetarget firstRest last selected intermediateMany
  have first : Rel whole (rest ++ [selected, selected, selected]) := expose.trans retarget
  have same : SameCaps whole ([] ++ rest ++ [selected, selected, selected]) := caps_of_rel first
  have canonical := windowNormal_eq_bulk (exceptPivot selected) whole [] rest [selected, selected, selected] [selected]
    same (by intro letter member; simpa using member) (by
      intro letter notMember
      have notSelected : letter ≠ selected := by simpa using notMember
      simp only [exceptPivot, if_neg notSelected]) (by
      intro letter member
      have equal : letter = selected := by simpa using member
      subst letter
      simp [exceptPivot])
  have normalized := relCubeNormal rest selected
  rw [canonical] at normalized
  exact first.trans normalized

theorem rel_normalFrame (front : List Nat) (penultimate last : Nat) :
    Rel (front ++ [penultimate, last]) (normalFrame front penultimate last).toList := by
  by_cases lastSimple : (front ++ [penultimate, last]).count last = 1
  · by_cases penultimateSimple : (front ++ [penultimate, last]).count penultimate = 1
    · simp only [normalFrame, if_pos lastSimple, if_pos penultimateSimple, put_toList]
      exact relFreeNormal front penultimate last penultimateSimple lastSimple
    · have positive : 0 < (front ++ [penultimate, last]).count penultimate :=
        List.count_pos_iff.mpr (by simp)
      have many : 2 ≤ (front ++ [penultimate, last]).count penultimate := by omega
      simp only [normalFrame, if_pos lastSimple, if_neg penultimateSimple, put_toList]
      exact relBoundNormal front penultimate last many lastSimple
  · by_cases lastDouble : (front ++ [penultimate, last]).count last = 2
    · by_cases adjacent : penultimate = last
      · subst penultimate
        simp only [normalFrame, if_neg lastSimple, if_pos lastDouble, ite_true, put_toList]
        exact relAdjacentNormal front last lastDouble
      · simp only [normalFrame, if_neg lastSimple, if_pos lastDouble, if_neg adjacent,
          Word.toList_append, Word.toList_singleton, put_toList]
        simpa only [List.append_assoc] using relSeparatedNormal front penultimate last adjacent lastDouble
    · have positive : 0 < (front ++ [penultimate, last]).count last := List.count_pos_iff.mpr (by simp)
      have heavy : 3 ≤ (front ++ [penultimate, last]).count last := by omega
      simp only [normalFrame, if_neg lastSimple, if_neg lastDouble, put_toList]
      exact relHeavyNormal front penultimate last heavy

theorem derives_normalForm (word : Word Nat) : Derives coreBasis word (normalForm word) := by
  rcases existsSingleOrFrame word with ⟨letter, rfl⟩ | ⟨front, penultimate, last, rfl⟩
  · rw [normalForm_single]
    exact Derives.refl _
  · rw [normalForm_frame]
    have listDerivation : Rel (framed front penultimate last).toList (normalFrame front penultimate last).toList := by
      rw [framed_toList]
      exact rel_normalFrame front penultimate last
    exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord listDerivation

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708.Sigma12
