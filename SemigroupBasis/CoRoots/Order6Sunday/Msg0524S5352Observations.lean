import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5352Evaluator

/-! Necessary capped counts and the conditional final-letter observation.
The final letter is observable only below its third occurrence. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5352Observations

open SemigroupBasis
open Msg0524S5352Evaluator

def probe (marked : Bool) (x a : Nat) : Fin 6 :=
  if a = x then if marked then 4 else 3 else 5

theorem weight_probe (marked : Bool) (x a : Nat) :
    weight (probe marked x a) = if a = x then 1 else 0 := by
  cases marked <;> by_cases same : a = x <;> simp [probe, weight, same] <;> decide

theorem marker_probe (marked : Bool) (x a : Nat) :
    marker (probe marked x a) = (marked && decide (a = x)) := by
  cases marked <;> by_cases same : a = x <;> simp [probe, marker, same]

theorem cost_probe (marked : Bool) (x : Nat) (letters : List Nat) :
    cost (probe marked x) letters = letters.count x := by
  induction letters with
  | nil => rfl
  | cons a rest ih =>
      by_cases same : a = x <;> simp [cost, weight_probe, same, ih] <;> omega

theorem eval_probe (marked : Bool) (x : Nat) (word : Word Nat) :
    table.semigroup.eval (probe marked x) word =
      code (word.toList.count x) (marked && decide (last word = x)) := by
  rw [eval_formula, cost_probe, marker_probe]

theorem count_cap_of_valid (left right : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup) (x : Nat) :
    min (left.toList.count x) 3 = min (right.toList.count x) 3 := by
  have equal := congrArg weight (valid (probe false x))
  rw [eval_weight, eval_weight, cost_probe, cost_probe] at equal
  exact equal

theorem last_count_positive (word : Word Nat) : 0 < word.toList.count (last word) :=
  List.count_pos_iff.mpr (last_mem word)

theorem small_terminal_of_valid (left right : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup)
    (small : left.toList.count (last left) < 3) : last left = last right := by
  have equal := valid (probe true (last left))
  change table.semigroup.eval (probe true (last left)) left =
    table.semigroup.eval (probe true (last left)) right at equal
  rw [eval_probe, eval_probe] at equal
  simp only [Bool.true_and, decide_true] at equal
  have counts := count_cap_of_valid left right valid (last left)
  have exactCount : right.toList.count (last left) = left.toList.count (last left) := by omega
  rw [exactCount] at equal
  have bits := code_tag_injective (left.toList.count (last left))
    (last_count_positive left) small true (decide (last right = last left)) equal
  exact (of_decide_eq_true bits.symm).symm

def terminalTag (word : Word Nat) : Option Nat :=
  if word.toList.count (last word) < 3 then some (last word) else none

def SameKey (left right : Word Nat) : Prop :=
  (∀ x, min (left.toList.count x) 3 = min (right.toList.count x) 3) ∧
    terminalTag left = terminalTag right

theorem terminalTag_of_valid (left right : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup) :
    terminalTag left = terminalTag right := by
  by_cases lowLeft : left.toList.count (last left) < 3
  · have ends := small_terminal_of_valid left right valid lowLeft
    have counts := count_cap_of_valid left right valid (last left)
    have lowRight : right.toList.count (last right) < 3 := by
      rw [← ends]
      omega
    unfold terminalTag
    rw [if_pos lowLeft, if_pos lowRight, ends]
  · by_cases lowRight : right.toList.count (last right) < 3
    · have reverse : (Identity.mk right left).SatisfiedBy table.semigroup :=
        fun valuation => (valid valuation).symm
      have ends := small_terminal_of_valid right left reverse lowRight
      have counts := count_cap_of_valid left right valid (last left)
      rw [ends] at lowRight
      omega
    · simp only [terminalTag, if_neg lowLeft, if_neg lowRight]

theorem key_of_valid (left right : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup) : SameKey left right :=
  ⟨count_cap_of_valid left right valid, terminalTag_of_valid left right valid⟩

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5352Observations
