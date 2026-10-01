import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14MarkerProbes

/-! A second concrete valuation separates the penultimate simple letter.
The proof is uniform in the finite-table parameters, including tables whose
unmarked pair value is zero. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14

open SemigroupBasis
open S6_2708.Sigma12

variable {G : Semigroup (Fin 6)} {swapping : Bool}

def pairVal (model : ProbeModel G swapping) (last selected letter : Nat) : Fin 6 :=
  if letter = last then model.pairLast else if letter = selected then model.pairMark else 5

theorem prefix_pair_killed (model : ProbeModel G swapping) (last selected : Nat)
    (different : last ≠ selected) (value : Fin 6)
    (neutral : G.mul 5 value = value) (killed : G.mul model.pairMark value = 0)
    (front : List Nat) (absent : front.count last = 0) :
    prefixEval G (pairVal model last selected) front value =
      if front.count selected = 0 then value else 0 := by
  revert absent
  induction front with
  | nil => intro _; simp [prefixEval]
  | cons letter rest ih =>
      intro absent
      have notLast : letter ≠ last := by
        intro equal
        subst letter
        simp only [List.count_cons_self] at absent
        omega
      have tailAbsent : rest.count last = 0 := by
        simpa only [List.count_cons_of_ne notLast] using absent
      rw [prefixEval, ih tailAbsent]
      by_cases selectedEqual : letter = selected
      · subst letter
        simp only [pairVal, if_neg (Ne.symm different), List.count_cons_self]
        by_cases noMore : rest.count selected = 0
        · simp [noMore, killed]
        · simp [noMore, model.mul_zero]
      · simp only [pairVal, if_neg notLast, if_neg selectedEqual,
          List.count_cons_of_ne selectedEqual]
        by_cases noMore : rest.count selected = 0
        · simp only [if_pos noMore, neutral]
        · simp only [if_neg noMore, model.mul_zero]

theorem pairProbe (model : ProbeModel G swapping) (front : List Nat) (penultimate last selected : Nat)
    (different : last ≠ selected)
    (lastSimple : (front ++ [penultimate, last]).count last = 1)
    (selectedSimple : (front ++ [penultimate, last]).count selected = 1) :
    G.eval (pairVal model last selected) (framed front penultimate last) =
      if penultimate = selected then (1 : Fin 6) else 0 := by
  rw [eval_framed]
  have notLast := penultimate_ne_last front penultimate last lastSimple
  have lastAbsent : front.count last = 0 := by
    simp only [List.count_append, List.count_cons_of_ne notLast,
      List.count_cons_self, List.count_nil] at lastSimple
    omega
  have lastValue : pairVal model last selected last = model.pairLast := by simp [pairVal]
  rw [lastValue]
  by_cases adjacent : penultimate = selected
  · subst penultimate
    have selectedValue : pairVal model last selected selected = model.pairMark := by
      simp [pairVal, Ne.symm different]
    have selectedAbsent : front.count selected = 0 := by
      simp only [List.count_append, List.count_cons_self,
        List.count_cons_of_ne different, List.count_nil] at selectedSimple
      omega
    rw [selectedValue, model.pair_mark_last,
      prefix_pair_killed model last selected different 1 model.neutral_one model.pair_mark_one front lastAbsent]
    simp [selectedAbsent]
  · have penultimateValue : pairVal model last selected penultimate = 5 := by
      simp [pairVal, notLast, adjacent]
    have selectedCount : front.count selected = 1 := by
      simp only [List.count_append, List.count_cons_of_ne adjacent,
        List.count_cons_of_ne different, List.count_nil] at selectedSimple
      omega
    rw [penultimateValue, model.pair_neutral_last,
      prefix_pair_killed model last selected different model.pairMiddle
        model.pair_neutral_middle model.pair_mark_middle front lastAbsent]
    simp [selectedCount, adjacent]

theorem simplePenultimate_preserved (model : ProbeModel G swapping)
    (leftFront rightFront : List Nat) (leftPenultimate rightPenultimate last : Nat)
    (same : Equivalent G (framed leftFront leftPenultimate last) (framed rightFront rightPenultimate last))
    (lastSimple : (leftFront ++ [leftPenultimate, last]).count last = 1)
    (penultimateSimple : (leftFront ++ [leftPenultimate, last]).count leftPenultimate = 1) :
    rightPenultimate = leftPenultimate := by
  have caps : SameCaps (leftFront ++ [leftPenultimate, last]) (rightFront ++ [rightPenultimate, last]) := by
    simpa only [framed_toList] using caps_of_equivalent model _ _ same
  have rightLastSimple := (caps.simple last).mp lastSimple
  have rightSelectedSimple := (caps.simple leftPenultimate).mp penultimateSimple
  have different := Ne.symm (penultimate_ne_last leftFront leftPenultimate last lastSimple)
  have values := same (pairVal model last leftPenultimate)
  rw [pairProbe model leftFront leftPenultimate last leftPenultimate different lastSimple penultimateSimple,
    pairProbe model rightFront rightPenultimate last leftPenultimate different rightLastSimple rightSelectedSimple] at values
  by_cases equal : rightPenultimate = leftPenultimate
  · exact equal
  · simp only [if_neg equal] at values
    exact False.elim ((by decide : (1 : Fin 6) ≠ 0) values)

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14
