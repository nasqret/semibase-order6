import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Semantics

/-! Arbitrary-length observations behind S11395's postS and first-prefix
parity components. All context hypotheses are explicit; no bounded word
window or unproved signature converse is used. -/

namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Markers

open SemigroupBasis
open Msg0457S11395Semantics

def evalList (valuation : α → Fin 6) (xs : List α) : Fin 6 :=
  xs.foldl (fun a x => mul a (valuation x)) 2

theorem eval_eq_evalList (valuation : α → Fin 6) (word : Word α) :
    table.semigroup.eval valuation word = evalList valuation word.toList := by
  cases word with
  | mk head tail =>
      simp only [evalList, Word.toList, List.foldl_cons, left_identity]
      rfl

theorem evalList_append (valuation : α → Fin 6) (left right : List α) :
    evalList valuation (left ++ right) =
      right.foldl (fun a x => mul a (valuation x)) (evalList valuation left) :=
  List.foldl_append

theorem safe_mul : ∀ a b : Fin 6, 2 ≤ a.val → 2 ≤ b.val → 2 ≤ (mul a b).val := by decide
theorem safe_mul_nil : ∀ a : Fin 6, 2 ≤ a.val → mul a 1 = 1 := by decide

theorem fold_safe (valuation : α → Fin 6) (xs : List α) (initial : Fin 6)
    (initialSafe : 2 ≤ initial.val) (safe : ∀ x ∈ xs, 2 ≤ (valuation x).val) :
    2 ≤ (xs.foldl (fun a x => mul a (valuation x)) initial).val := by
  induction xs generalizing initial with
  | nil => exact initialSafe
  | cons x xs ih =>
      exact ih (mul initial (valuation x)) (safe_mul _ _ initialSafe (safe x (by simp)))
        (fun y member => safe y (List.mem_cons_of_mem x member))

theorem evalList_safe (valuation : α → Fin 6) (xs : List α)
    (safe : ∀ x ∈ xs, 2 ≤ (valuation x).val) : 2 ≤ (evalList valuation xs).val :=
  fold_safe valuation xs 2 (by decide) safe

def nilValue (blocked : Bool) : Fin 6 := if blocked then 0 else 1

theorem nilValue_step : ∀ (blocked : Bool) (a : Fin 6), 2 ≤ a.val →
    mul (nilValue blocked) a = nilValue (blocked || isLeft a) := by decide

theorem fold_nilValue (valuation : α → Fin 6) (xs : List α) (initial : Bool)
    (safe : ∀ x ∈ xs, 2 ≤ (valuation x).val) :
    xs.foldl (fun a x => mul a (valuation x)) (nilValue initial) =
      nilValue (initial || xs.any (fun x => isLeft (valuation x))) := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons, List.any_cons]
      rw [nilValue_step initial (valuation x) (safe x (by simp)),
        ih (initial || isLeft (valuation x))
          (fun y member => safe y (List.mem_cons_of_mem x member))]
      rw [Bool.or_assoc]

/-- One nilpotent survives precisely when its suffix has no left-zero
value. Values before it may include arbitrary units and left zeros. -/
theorem uniqueNil_split (valuation : α → Fin 6) (before after : List α) (separator : α)
    (nilSeparator : valuation separator = (1 : Fin 6))
    (beforeSafe : ∀ x ∈ before, 2 ≤ (valuation x).val)
    (afterSafe : ∀ x ∈ after, 2 ≤ (valuation x).val) :
    evalList valuation (before ++ separator :: after) =
      if after.any (fun x => isLeft (valuation x)) then 0 else 1 := by
  rw [evalList_append, List.foldl_cons, nilSeparator,
    safe_mul_nil _ (evalList_safe valuation before beforeSafe)]
  simpa [nilValue] using fold_nilValue valuation after false afterSafe

def groupValue (parity : Bool) : Fin 6 := if parity then 3 else 2
def leftValue (parity : Bool) : Fin 6 := if parity then 5 else 4

def groupBit (valuation : α → Fin 6) (xs : List α) : Bool :=
  xs.foldl (fun bit x => bit != (valuation x == (3 : Fin 6))) false

theorem groupValue_step : ∀ (parity : Bool) (a : Fin 6), a = 2 ∨ a = 3 →
    mul (groupValue parity) a = groupValue (parity != (a == 3)) := by decide

theorem groupValue_left : ∀ (parity : Bool) (a : Fin 6), isLeft a = true →
    mul (groupValue parity) a = leftValue ((a == 5) != parity) := by decide

theorem leftValue_safe : ∀ (parity : Bool) (a : Fin 6), 2 ≤ a.val →
    mul (leftValue parity) a = leftValue parity := by decide

theorem fold_units (valuation : α → Fin 6) (xs : List α) (initial : Bool)
    (units : ∀ x ∈ xs, valuation x = (2 : Fin 6) ∨ valuation x = (3 : Fin 6)) :
    xs.foldl (fun a x => mul a (valuation x)) (groupValue initial) =
      groupValue (xs.foldl (fun bit x => bit != (valuation x == (3 : Fin 6))) initial) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [groupValue_step initial (valuation x) (units x (by simp))]
      exact ih _ (fun y member => units y (List.mem_cons_of_mem x member))

theorem evalList_units (valuation : α → Fin 6) (xs : List α)
    (units : ∀ x ∈ xs, valuation x = (2 : Fin 6) ∨ valuation x = (3 : Fin 6)) :
    evalList valuation xs = groupValue (groupBit valuation xs) :=
  fold_units valuation xs false units

theorem fold_leftValue (valuation : α → Fin 6) (xs : List α) (parity : Bool)
    (safe : ∀ x ∈ xs, 2 ≤ (valuation x).val) :
    xs.foldl (fun a x => mul a (valuation x)) (leftValue parity) = leftValue parity := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [leftValue_safe parity (valuation x) (safe x (by simp))]
      exact ih (fun y member => safe y (List.mem_cons_of_mem x member))

/-- The first left-zero value is selected by first-occurrence order and
acted upon by the unit parity before it; all later safe values disappear. -/
theorem firstLeft_split (valuation : α → Fin 6) (before after : List α) (separator : α)
    (leftSeparator : isLeft (valuation separator) = true)
    (beforeUnits : ∀ x ∈ before, valuation x = (2 : Fin 6) ∨ valuation x = (3 : Fin 6))
    (afterSafe : ∀ x ∈ after, 2 ≤ (valuation x).val) :
    evalList valuation (before ++ separator :: after) =
      leftValue ((valuation separator == (5 : Fin 6)) != groupBit valuation before) := by
  rw [evalList_append, List.foldl_cons, evalList_units valuation before beforeUnits,
    groupValue_left _ _ leftSeparator]
  exact fold_leftValue valuation after _ afterSafe

theorem eval_zero_of_zero (valuation : α → Fin 6) (word : Word α)
    (zero : word.toList.any (fun x => valuation x == (0 : Fin 6)) = true) :
    table.semigroup.eval valuation word = (0 : Fin 6) := by
  rw [eval_eq_summary]
  have seen := summary_zeroSeen valuation word.toList
  rw [zero] at seen
  simp [decode, seen]

theorem eval_zero_of_two_nil (valuation : α → Fin 6) (word : Word α)
    (two : 2 ≤ word.toList.countP (fun x => isNil (valuation x))) :
    table.semigroup.eval valuation word = (0 : Fin 6) := by
  have count := summary_nilCount valuation word.toList
  have countTwo : (summaryList valuation word.toList).nilCount = (2 : Fin 3) := by
    apply Fin.ext
    omega
  rw [eval_eq_summary]
  simp [decode, countTwo]

end SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Markers
