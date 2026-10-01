import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14ProbeModel

/-! Actual-table marker evaluations detect a simple last letter and the exact
double-last stratum retained by each of the two approved normal forms. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14

open SemigroupBasis
open S6_2708.Sigma12
open S4_71Suffix (put)

variable {G : Semigroup (Fin 6)} {swapping : Bool}

theorem frame_marker_eq_simple_iff (model : ProbeModel G swapping)
    (front : List Nat) (penultimate last selected : Nat) :
    G.eval (marker selected) (framed front penultimate last) = model.simpleMarker ↔
      last = selected ∧ (front ++ [penultimate, last]).count selected = 1 := by
  by_cases lastEqual : last = selected
  · subst last
    rw [eval_framed]
    have selectedValue : marker selected selected = (4 : Fin 6) := by simp [marker]
    by_cases adjacent : penultimate = selected
    · subst penultimate
      rw [selectedValue, model.mark_mark, marker_prefix_one model]
      constructor
      · intro impossible
        exact False.elim (oneFall_ne_simple model _ impossible)
      · intro impossible
        simp only [List.count_append, List.count_cons_self, List.count_nil] at impossible
        omega
    · have penultimateValue : marker selected penultimate = (5 : Fin 6) := by simp [marker, adjacent]
      rw [selectedValue, penultimateValue, model.neutral_mark, marker_prefix_simple model,
        simpleFall_eq_simple_iff]
      simp only [List.count_append, List.count_cons_of_ne adjacent,
        List.count_cons_self, List.count_nil, true_and]
      omega
  · rw [framed_as_end, eval_put, Semigroup.eval_singleton]
    have lastValue : marker selected last = (5 : Fin 6) := by simp [marker, lastEqual]
    rw [lastValue, marker_prefix_neutral model]
    constructor
    · intro impossible
      exact False.elim (drift_ne_simple model _ impossible)
    · intro impossible
      exact False.elim (lastEqual impossible.1)

theorem frame_marker_eq_one_iff (model : ProbeModel G swapping)
    (front : List Nat) (penultimate last selected : Nat) :
    G.eval (marker selected) (framed front penultimate last) = (1 : Fin 6) ↔
      last = selected ∧ (front ++ [penultimate, last]).count selected = 2 ∧
        (swapping = true ∨ penultimate = last) := by
  by_cases lastEqual : last = selected
  · subst last
    rw [eval_framed]
    have selectedValue : marker selected selected = (4 : Fin 6) := by simp [marker]
    by_cases adjacent : penultimate = selected
    · subst penultimate
      rw [selectedValue, model.mark_mark, marker_prefix_one model, oneFall_eq_one_iff]
      simp only [List.count_append, List.count_cons_self, List.count_nil,
        or_true, and_true, true_and]
      omega
    · have penultimateValue : marker selected penultimate = (5 : Fin 6) := by simp [marker, adjacent]
      rw [selectedValue, penultimateValue, model.neutral_mark, marker_prefix_simple model,
        simpleFall_eq_one_iff]
      simp only [List.count_append, List.count_cons_of_ne adjacent, List.count_cons_self,
        List.count_nil, true_and, adjacent, or_false]
      constructor
      · intro hypothesis
        exact ⟨by omega, hypothesis.2⟩
      · intro hypothesis
        exact ⟨by omega, hypothesis.2⟩
  · rw [framed_as_end, eval_put, Semigroup.eval_singleton]
    have lastValue : marker selected last = (5 : Fin 6) := by simp [marker, lastEqual]
    rw [lastValue, marker_prefix_neutral model]
    constructor
    · intro impossible
      exact False.elim (drift_ne_one model _ impossible)
    · intro impossible
      exact False.elim (lastEqual impossible.1)

def GoodDouble (swapping : Bool) (front : List Nat) (penultimate last : Nat) : Prop :=
  (front ++ [penultimate, last]).count last = 2 ∧ (swapping = true ∨ penultimate = last)

theorem simpleLast_preserved (model : ProbeModel G swapping)
    (leftFront rightFront : List Nat) (leftPenultimate rightPenultimate leftLast rightLast : Nat)
    (same : Equivalent G (framed leftFront leftPenultimate leftLast) (framed rightFront rightPenultimate rightLast))
    (simple : (leftFront ++ [leftPenultimate, leftLast]).count leftLast = 1) :
    rightLast = leftLast ∧ (rightFront ++ [rightPenultimate, rightLast]).count rightLast = 1 := by
  have leftValue := (frame_marker_eq_simple_iff model leftFront leftPenultimate leftLast leftLast).2 ⟨rfl, simple⟩
  have rightValue := (same (marker leftLast)).symm.trans leftValue
  obtain ⟨lastEqual, rightCount⟩ :=
    (frame_marker_eq_simple_iff model rightFront rightPenultimate rightLast leftLast).1 rightValue
  exact ⟨lastEqual, by simpa only [lastEqual] using rightCount⟩

theorem goodDouble_preserved (model : ProbeModel G swapping)
    (leftFront rightFront : List Nat) (leftPenultimate rightPenultimate leftLast rightLast : Nat)
    (same : Equivalent G (framed leftFront leftPenultimate leftLast) (framed rightFront rightPenultimate rightLast))
    (double : GoodDouble swapping leftFront leftPenultimate leftLast) :
    rightLast = leftLast ∧ GoodDouble swapping rightFront rightPenultimate rightLast := by
  have leftValue := (frame_marker_eq_one_iff model leftFront leftPenultimate leftLast leftLast).2 ⟨rfl, double⟩
  have rightValue := (same (marker leftLast)).symm.trans leftValue
  obtain ⟨lastEqual, rightCount, rightMode⟩ :=
    (frame_marker_eq_one_iff model rightFront rightPenultimate rightLast leftLast).1 rightValue
  exact ⟨lastEqual, by simpa only [GoodDouble, lastEqual] using And.intro rightCount rightMode⟩

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Sigma14
