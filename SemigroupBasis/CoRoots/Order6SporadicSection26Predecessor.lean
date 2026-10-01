import SemigroupBasis.CoRoots.Order6SporadicSection26Tables

/-! A literal F7 probe detects the predecessor of the first separator.
If the separator is absent, the same observation returns the last letter.
All statements are unrestricted in word length and variable support. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection26.F7
open SemigroupBasis

def predecessorScan (separator previous : Nat) : List Nat → Nat
  | [] => previous
  | x :: xs => if x = separator then previous else predecessorScan separator x xs

def predecessorOrLast (separator : Nat) (word : Word Nat) : Option Nat :=
  if word.head = separator then none
  else some (predecessorScan separator word.head word.tail)

def predecessorProbe (selected separator letter : Nat) : Fin 6 :=
  if letter = separator then 2 else if letter = selected then 5 else 4

def decodePredecessor (state : Fin 6) : Option Bool :=
  if state = 2 then none else some (state == 3 || state == 5)

private theorem fold_zero (valuation : Nat → Fin 6) (xs : List Nat) :
    xs.foldl (fun state x => tableMul state (valuation x)) 0 = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldl_cons,mul_zero] using ih

private theorem fold_two (valuation : Nat → Fin 6) (xs : List Nat) :
    xs.foldl (fun state x => tableMul state (valuation x)) 2 = 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldl_cons,mul_two] using ih

private theorem fold_three (valuation : Nat → Fin 6) (xs : List Nat) :
    xs.foldl (fun state x => tableMul state (valuation x)) 3 = 3 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa only [List.foldl_cons,mul_three] using ih

private theorem probe_mul_nonseparator (selected separator previous x : Nat)
    (different : x ≠ separator) :
    tableMul (if previous = selected then 5 else 4)
      (predecessorProbe selected separator x) =
        (if x = selected then 5 else 4) := by
  unfold predecessorProbe
  rw [if_neg different]
  by_cases hp : previous = selected <;> by_cases hx : x = selected <;>
    simp only [hp,hx,ite_true,ite_false] <;> decide

private theorem probe_mul_separator (selected separator previous : Nat) :
    tableMul (if previous = selected then 5 else 4)
      (predecessorProbe selected separator separator) =
        (if previous = selected then 3 else 0) := by
  have initial : predecessorProbe selected separator separator = (2 : Fin 6) := by
    simp [predecessorProbe]
  rw [initial]
  by_cases hp : previous = selected <;>
    simp only [hp,ite_true,ite_false] <;> decide

theorem decode_predecessor_fold (selected separator previous : Nat) (xs : List Nat) :
    decodePredecessor
      (xs.foldl (fun state x => tableMul state (predecessorProbe selected separator x))
        (if previous = selected then 5 else 4)) =
      some (decide (predecessorScan separator previous xs = selected)) := by
  induction xs generalizing previous with
  | nil =>
      by_cases hp : previous = selected <;>
        simp [predecessorScan,hp,decodePredecessor]
  | cons x xs ih =>
      by_cases hx : x = separator
      · subst x
        rw [List.foldl_cons,probe_mul_separator]
        by_cases hp : previous = selected
        · rw [if_pos hp,fold_three]
          simp [predecessorScan,hp,decodePredecessor]
        · rw [if_neg hp,fold_zero]
          simp [predecessorScan,hp,decodePredecessor]
      · rw [List.foldl_cons,probe_mul_nonseparator selected separator previous x hx]
        simpa only [predecessorScan,if_neg hx] using ih x

theorem decode_predecessor_eval (selected separator : Nat) (word : Word Nat) :
    decodePredecessor (table.semigroup.eval (predecessorProbe selected separator) word) =
      (predecessorOrLast separator word).map (fun previous => decide (previous = selected)) := by
  cases word with
  | mk head tail =>
      by_cases hh : head = separator
      · subst head
        change decodePredecessor
          (tail.foldl (fun state x => tableMul state (predecessorProbe selected separator x))
            (predecessorProbe selected separator separator)) = _
        have initial : predecessorProbe selected separator separator = (2 : Fin 6) := by
          simp [predecessorProbe]
        rw [initial,fold_two]
        simp [decodePredecessor,predecessorOrLast]
      · change decodePredecessor
          (tail.foldl (fun state x => tableMul state (predecessorProbe selected separator x))
            (predecessorProbe selected separator head)) = _
        rw [show predecessorProbe selected separator head =
          (if head = selected then 5 else 4) from by simp only [predecessorProbe,if_neg hh]]
        rw [decode_predecessor_fold]
        simp [predecessorOrLast,hh]

theorem option_eq_of_all_indicators (left right : Option Nat)
    (same : ∀ selected, left.map (fun x => decide (x = selected)) =
      right.map (fun x => decide (x = selected))) : left = right := by
  cases left with
  | none =>
      cases right with
      | none => rfl
      | some b => have impossible := same b; simp at impossible
  | some a =>
      cases right with
      | none => have impossible := same a; simp at impossible
      | some b =>
          by_cases equal : a = b
          · exact congrArg some equal
          · have impossible := same a
            simp [Ne.symm equal] at impossible

theorem valid_predecessorOrLast (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) (separator : Nat) :
    predecessorOrLast separator identity.lhs = predecessorOrLast separator identity.rhs := by
  apply option_eq_of_all_indicators
  intro selected
  have observation := congrArg decodePredecessor (valid (predecessorProbe selected separator))
  simpa only [decode_predecessor_eval] using observation

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.decode_predecessor_fold
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.decode_predecessor_eval
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.option_eq_of_all_indicators
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection26.F7.valid_predecessorOrLast
end SemigroupBasis.CoRoots.Order6SporadicSection26.F7
