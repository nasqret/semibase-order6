import SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5369Evaluator

/-! Necessary head, length and capped-count observations, and the complete
long-word evaluator. No derivation, basis completeness, or short-word sufficiency. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5369Observations

open SemigroupBasis
open Msg0524S5369Evaluator

def lengthCap (word : Word α) : Nat := min word.toList.length 5

theorem nilValue_eq_iff (a b : Nat) : nilValue a = nilValue b ↔ min a 5 = min b 5 := by
  constructor
  · intro equal
    have values := congrArg Fin.val equal
    simp only [nilValue] at values
    omega
  · intro equal
    apply Fin.ext
    simp only [nilValue]
    omega

theorem cost_uniform (letters : List α) : cost (fun _ => (4 : Fin 6)) letters = letters.length := by
  induction letters with
  | nil => rfl
  | cons a rest ih =>
      simp only [cost, ih, List.length_cons]
      change 1 + rest.length = rest.length + 1
      omega

theorem eval_all_four (word : Word α) :
    table.semigroup.eval (fun _ => (4 : Fin 6)) word = nilValue word.toList.length := by
  rw [eval_of_no_marker _ _ (by intro a member; decide), cost_uniform]

theorem length_of_valid (left right : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup) :
    lengthCap left = lengthCap right := by
  have same := valid (fun _ => (4 : Fin 6))
  rw [eval_all_four, eval_all_four] at same
  exact (nilValue_eq_iff _ _).mp same

def headProbe (marker a : Nat) : Fin 6 := if a = marker then 5 else 0

theorem eval_head_probe (marker : Nat) (word : Word Nat) :
    table.semigroup.eval (headProbe marker) word = (5 : Fin 6) ↔ word.head = marker := by
  rw [eval_five_iff]
  by_cases same : word.head = marker <;> simp [headProbe, same]

theorem head_of_valid (left right : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup) : left.head = right.head := by
  have same := valid (headProbe left.head)
  have leftFive := (eval_head_probe left.head left).mpr rfl
  have rightFive := same.symm.trans leftFive
  exact ((eval_head_probe left.head right).mp rightFive).symm

def countProbe (marker a : Nat) : Fin 6 := if a = marker then 3 else 4

theorem cost_count_probe (marker : Nat) (letters : List Nat) :
    cost (countProbe marker) letters = letters.length + letters.count marker := by
  induction letters with
  | nil => rfl
  | cons a rest ih =>
      by_cases same : a = marker
      · simp [cost, countProbe, weight, same, ih] <;> omega
      · simp [cost, countProbe, weight, same, ih] <;> omega

theorem eval_count_probe (marker : Nat) (word : Word Nat) :
    table.semigroup.eval (countProbe marker) word =
      nilValue (word.toList.length + word.toList.count marker) := by
  rw [eval_of_no_marker _ _ (by
    intro a member
    unfold countProbe
    split <;> decide), cost_count_probe]

theorem count_cap_of_valid (left right : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup) (marker : Nat) :
    min (left.toList.count marker) (5-lengthCap left) =
      min (right.toList.count marker) (5-lengthCap right) := by
  have lengths := length_of_valid left right valid
  have same := valid (countProbe marker)
  rw [eval_count_probe, eval_count_probe] at same
  have amounts := (nilValue_eq_iff _ _).mp same
  change min (left.toList.length + left.toList.count marker) 5 =
    min (right.toList.length + right.toList.count marker) 5 at amounts
  unfold lengthCap at *
  omega

def SameKey (left right : Word Nat) : Prop :=
  left.head = right.head ∧ lengthCap left = lengthCap right ∧
    ∀ marker, min (left.toList.count marker) (5-lengthCap left) =
      min (right.toList.count marker) (5-lengthCap right)

theorem key_of_valid (left right : Word Nat)
    (valid : (Identity.mk left right).SatisfiedBy table.semigroup) : SameKey left right :=
  ⟨head_of_valid left right valid, length_of_valid left right valid,
    count_cap_of_valid left right valid⟩

theorem cost_ge_length (valuation : α → Fin 6) (letters : List α)
    (low : ∀ a ∈ letters, valuation a ≠ 5) : letters.length ≤ cost valuation letters := by
  induction letters with
  | nil => simp [cost]
  | cons a rest ih =>
      have first := weight_positive (valuation a) (low a (by simp))
      have tailBound := ih (fun b member => low b (List.mem_cons_of_mem a member))
      simp only [cost, List.length_cons]
      omega

theorem eval_long (valuation : α → Fin 6) (word : Word α) (long : 5 ≤ word.toList.length) :
    table.semigroup.eval valuation word = if valuation word.head=5 then (5 : Fin 6) else 0 := by
  classical
  by_cases head : valuation word.head=5
  · rw [if_pos head]
    exact (eval_five_iff valuation word).mpr head
  · rw [if_neg head]
    by_cases marked : ∃ a ∈ word.tail, valuation a=5
    · exact fold_zero_of_marker valuation word.tail (valuation word.head) head marked
    · have low : ∀ a ∈ word.toList, valuation a≠5 := by
        intro a member
        rcases List.mem_cons.mp member with same | tailMember
        · subst a
          exact head
        · intro yes
          exact marked ⟨a,tailMember,yes⟩
      rw [eval_of_no_marker valuation word low]
      have bound := cost_ge_length valuation word.toList low
      apply Fin.ext
      simp only [nilValue]
      omega

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524S5369Observations
