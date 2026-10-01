import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708Sigma12Probes

/-! Unrestricted separation of the concrete Word normal forms by actual target
valuations. No finite screen or generic flat-key theorem is a premise. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708.Sigma12

open SemigroupBasis
open S4_71Suffix (put)

theorem eval_framed (valuation : Nat → Fin 6) (front : List Nat) (penultimate last : Nat) :
    table.semigroup.eval valuation (framed front penultimate last) =
      prefixEval valuation front (mul (valuation penultimate) (valuation last)) := by
  rw [framed, eval_put]
  rfl

theorem penultimate_ne_last (front : List Nat) (penultimate last : Nat)
    (simple : (front ++ [penultimate, last]).count last = 1) : penultimate ≠ last := by
  intro equal
  subst penultimate
  simp only [List.count_append, List.count_cons_self, List.count_nil] at simple
  omega

theorem doubleProbe (front : List Nat) (penultimate last : Nat)
    (double : (front ++ [penultimate, last]).count last = 2) :
    table.semigroup.eval (marked2 (fun letter => decide (letter = last))) (framed front penultimate last) =
      if penultimate = last then (0 : Fin 6) else (1 : Fin 6) := by
  rw [eval_framed]
  have lastValue : marked2 (fun letter => decide (letter = last)) last = 2 := by simp [marked2]
  rw [lastValue]
  by_cases adjacent : penultimate = last
  · subst penultimate
    rw [lastValue, if_pos rfl]
    change prefixEval _ front 0 = 0
    exact prefixEval_zero _ _
  · have penultimateValue : marked2 (fun letter => decide (letter = last)) penultimate = 5 := by
      simp [marked2, adjacent]
    rw [penultimateValue, if_neg adjacent]
    change prefixEval _ front 4 = 1
    rw [marked2_prefix_four, countP_single]
    have count : front.count last = 1 := by
      simp only [List.count_append, List.count_cons_of_ne adjacent, List.count_cons_self, List.count_nil] at double
      omega
    rw [count]
    rfl

theorem pairProbe (front : List Nat) (penultimate last selected : Nat)
    (different : last ≠ selected)
    (lastSimple : (front ++ [penultimate, last]).count last = 1)
    (selectedSimple : (front ++ [penultimate, last]).count selected = 1) :
    table.semigroup.eval (marked2 (fun letter => decide (letter = last ∨ letter = selected)))
      (framed front penultimate last) =
      if penultimate = selected then (0 : Fin 6) else (1 : Fin 6) := by
  rw [eval_framed]
  have lastValue : marked2 (fun letter => decide (letter = last ∨ letter = selected)) last = 2 := by
    simp [marked2]
  rw [lastValue]
  by_cases adjacent : penultimate = selected
  · subst penultimate
    have selectedValue : marked2 (fun letter => decide (letter = last ∨ letter = selected)) selected = 2 := by
      simp [marked2]
    rw [selectedValue, if_pos rfl]
    change prefixEval _ front 0 = 0
    exact prefixEval_zero _ _
  · have notLast := penultimate_ne_last front penultimate last lastSimple
    have penultimateValue : marked2 (fun letter => decide (letter = last ∨ letter = selected)) penultimate = 5 := by
      simp [marked2, notLast, adjacent]
    rw [penultimateValue, if_neg adjacent]
    change prefixEval _ front 4 = 1
    rw [marked2_prefix_four, countP_pair front last selected different]
    have lastCount : front.count last = 0 := by
      simp only [List.count_append, List.count_cons_of_ne notLast, List.count_cons_self, List.count_nil] at lastSimple
      omega
    have selectedCount : front.count selected = 1 := by
      simp only [List.count_append, List.count_cons_of_ne adjacent,
        List.count_cons_of_ne different, List.count_nil] at selectedSimple
      omega
    rw [lastCount, selectedCount]
    rfl

theorem simpleLast_preserved (leftFront rightFront : List Nat) (leftPenultimate rightPenultimate leftLast rightLast : Nat)
    (same : Equivalent (framed leftFront leftPenultimate leftLast) (framed rightFront rightPenultimate rightLast))
    (simple : (leftFront ++ [leftPenultimate, leftLast]).count leftLast = 1) :
    rightLast = leftLast ∧ (rightFront ++ [rightPenultimate, rightLast]).count rightLast = 1 := by
  have leftValue := (frame_probe4_eq_four_iff leftFront leftPenultimate leftLast leftLast).2 ⟨rfl, simple⟩
  have rightValue := (same (probe4 leftLast)).symm.trans leftValue
  obtain ⟨lastEqual, rightCount⟩ := (frame_probe4_eq_four_iff rightFront rightPenultimate rightLast leftLast).1 rightValue
  exact ⟨lastEqual, by simpa only [lastEqual] using rightCount⟩

theorem doubleLast_preserved (leftFront rightFront : List Nat) (leftPenultimate rightPenultimate leftLast rightLast : Nat)
    (same : Equivalent (framed leftFront leftPenultimate leftLast) (framed rightFront rightPenultimate rightLast))
    (double : (leftFront ++ [leftPenultimate, leftLast]).count leftLast = 2) :
    rightLast = leftLast ∧ (rightFront ++ [rightPenultimate, rightLast]).count rightLast = 2 := by
  have leftValue := (frame_probe4_eq_one_iff leftFront leftPenultimate leftLast leftLast).2 ⟨rfl, double⟩
  have rightValue := (same (probe4 leftLast)).symm.trans leftValue
  obtain ⟨lastEqual, rightCount⟩ := (frame_probe4_eq_one_iff rightFront rightPenultimate rightLast leftLast).1 rightValue
  exact ⟨lastEqual, by simpa only [lastEqual] using rightCount⟩

theorem simplePenultimate_preserved (leftFront rightFront : List Nat) (leftPenultimate rightPenultimate last : Nat)
    (same : Equivalent (framed leftFront leftPenultimate last) (framed rightFront rightPenultimate last))
    (lastSimple : (leftFront ++ [leftPenultimate, last]).count last = 1)
    (penultimateSimple : (leftFront ++ [leftPenultimate, last]).count leftPenultimate = 1) :
    rightPenultimate = leftPenultimate := by
  have caps : SameCaps (leftFront ++ [leftPenultimate, last]) (rightFront ++ [rightPenultimate, last]) := by
    simpa only [framed_toList] using caps_of_equivalent _ _ same
  have rightLastSimple := (caps.simple last).mp lastSimple
  have rightSelectedSimple := (caps.simple leftPenultimate).mp penultimateSimple
  have different := Ne.symm (penultimate_ne_last leftFront leftPenultimate last lastSimple)
  have values := same (marked2 (fun letter => decide (letter = last ∨ letter = leftPenultimate)))
  rw [pairProbe leftFront leftPenultimate last leftPenultimate different lastSimple penultimateSimple,
    pairProbe rightFront rightPenultimate last leftPenultimate different rightLastSimple rightSelectedSimple] at values
  by_cases equal : rightPenultimate = leftPenultimate
  · exact equal
  · simp only [if_neg equal] at values
    exact False.elim ((by decide : (0 : Fin 6) ≠ 1) values)

theorem doubleAdjacency_preserved (leftFront rightFront : List Nat) (leftPenultimate rightPenultimate last : Nat)
    (same : Equivalent (framed leftFront leftPenultimate last) (framed rightFront rightPenultimate last))
    (leftDouble : (leftFront ++ [leftPenultimate, last]).count last = 2)
    (rightDouble : (rightFront ++ [rightPenultimate, last]).count last = 2) :
    leftPenultimate = last ↔ rightPenultimate = last := by
  have values := same (marked2 (fun letter => decide (letter = last)))
  rw [doubleProbe leftFront leftPenultimate last leftDouble,
    doubleProbe rightFront rightPenultimate last rightDouble] at values
  by_cases leftAdjacent : leftPenultimate = last <;>
    by_cases rightAdjacent : rightPenultimate = last <;>
      simp [leftAdjacent, rightAdjacent] at values ⊢

theorem normalFrame_eq_of_equivalent (leftFront rightFront : List Nat)
    (leftPenultimate rightPenultimate leftLast rightLast : Nat)
    (same : Equivalent (framed leftFront leftPenultimate leftLast) (framed rightFront rightPenultimate rightLast)) :
    normalFrame leftFront leftPenultimate leftLast = normalFrame rightFront rightPenultimate rightLast := by
  have caps : SameCaps (leftFront ++ [leftPenultimate, leftLast]) (rightFront ++ [rightPenultimate, rightLast]) := by
    simpa only [framed_toList] using caps_of_equivalent _ _ same
  by_cases leftSimple : (leftFront ++ [leftPenultimate, leftLast]).count leftLast = 1
  · obtain ⟨lastEqual, rightSimple⟩ := simpleLast_preserved leftFront rightFront
      leftPenultimate rightPenultimate leftLast rightLast same leftSimple
    subst rightLast
    by_cases leftPenultimateSimple : (leftFront ++ [leftPenultimate, leftLast]).count leftPenultimate = 1
    · have penultimateEqual := simplePenultimate_preserved leftFront rightFront
        leftPenultimate rightPenultimate leftLast same leftSimple leftPenultimateSimple
      subst rightPenultimate
      have rightPenultimateSimple := (caps.simple leftPenultimate).mp leftPenultimateSimple
      simp only [normalFrame, if_pos leftSimple, if_pos rightSimple,
        if_pos leftPenultimateSimple, if_pos rightPenultimateSimple]
      rw [bulk_eq_of_caps [leftPenultimate, leftLast] caps]
    · have rightPenultimateNotSimple : (rightFront ++ [rightPenultimate, leftLast]).count rightPenultimate ≠ 1 := by
        intro rightPenultimateSimple
        have penultimateEqual := simplePenultimate_preserved rightFront leftFront
          rightPenultimate leftPenultimate leftLast same.symm rightSimple rightPenultimateSimple
        have leftCount := (caps.simple rightPenultimate).mpr rightPenultimateSimple
        exact leftPenultimateSimple (by simpa only [penultimateEqual] using leftCount)
      have pivotEqual := pivot_eq_of_caps caps
      simp only [normalFrame, if_pos leftSimple, if_pos rightSimple,
        if_neg leftPenultimateSimple, if_neg rightPenultimateNotSimple, pivotEqual]
      rw [bulk_eq_of_caps [pivot (rightFront ++ [rightPenultimate, leftLast]), leftLast] caps]
  · by_cases leftDouble : (leftFront ++ [leftPenultimate, leftLast]).count leftLast = 2
    · obtain ⟨lastEqual, rightDouble⟩ := doubleLast_preserved leftFront rightFront
        leftPenultimate rightPenultimate leftLast rightLast same leftDouble
      subst rightLast
      have rightNotSimple : (rightFront ++ [rightPenultimate, leftLast]).count leftLast ≠ 1 := by omega
      have adjacency := doubleAdjacency_preserved leftFront rightFront
        leftPenultimate rightPenultimate leftLast same leftDouble rightDouble
      by_cases leftAdjacent : leftPenultimate = leftLast
      · have rightAdjacent := adjacency.mp leftAdjacent
        simp only [normalFrame, if_neg leftSimple, if_neg rightNotSimple,
          if_pos leftDouble, if_pos rightDouble, if_pos leftAdjacent, if_pos rightAdjacent]
        rw [bulk_eq_of_caps [leftLast] caps]
      · have rightNotAdjacent : rightPenultimate ≠ leftLast := fun equal => leftAdjacent (adjacency.mpr equal)
        simp only [normalFrame, if_neg leftSimple, if_neg rightNotSimple,
          if_pos leftDouble, if_pos rightDouble, if_neg leftAdjacent, if_neg rightNotAdjacent]
        rw [bulk_eq_of_caps [leftLast] caps]
    · have rightNotSimple : (rightFront ++ [rightPenultimate, rightLast]).count rightLast ≠ 1 := by
        intro rightSimple
        exact leftSimple (simpleLast_preserved rightFront leftFront rightPenultimate leftPenultimate
          rightLast leftLast same.symm rightSimple).2
      have rightNotDouble : (rightFront ++ [rightPenultimate, rightLast]).count rightLast ≠ 2 := by
        intro rightDouble
        exact leftDouble (doubleLast_preserved rightFront leftFront rightPenultimate leftPenultimate
          rightLast leftLast same.symm rightDouble).2
      have pivotEqual := pivot_eq_of_caps caps
      simp only [normalFrame, if_neg leftSimple, if_neg rightNotSimple,
        if_neg leftDouble, if_neg rightNotDouble, pivotEqual]
      rw [bulk_eq_of_caps [pivot (rightFront ++ [rightPenultimate, rightLast])] caps]

theorem normalForm_eq_of_equivalent (left right : Word Nat) (same : Equivalent left right) :
    normalForm left = normalForm right := by
  rcases existsSingleOrFrame left with ⟨letter, rfl⟩ | ⟨leftFront, leftPenultimate, leftLast, rfl⟩
  · have caps : SameCaps [letter] right.toList := caps_of_equivalent _ _ same
    rw [singleton_of_caps right letter caps]
  · rcases existsSingleOrFrame right with ⟨letter, rfl⟩ | ⟨rightFront, rightPenultimate, rightLast, rfl⟩
    · have caps : SameCaps [letter] (framed leftFront leftPenultimate leftLast).toList :=
        caps_of_equivalent _ _ same.symm
      rw [singleton_of_caps _ letter caps]
    · rw [normalForm_frame, normalForm_frame]
      exact normalFrame_eq_of_equivalent leftFront rightFront leftPenultimate rightPenultimate leftLast rightLast same

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708.Sigma12
