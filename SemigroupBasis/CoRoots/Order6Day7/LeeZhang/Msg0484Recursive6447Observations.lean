import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0484Recursive6447Swaps

/-! Arbitrary-count observation codes and arbitrary-list evaluation.
Only the two requested three-case table controls remain explicit inputs.
The numerical separation lemmas quantify over every natural count. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive6447

open SemigroupBasis Order6Sunday

structure ObservationControls : Prop where
  highStep : ∀ n : Fin 3,
    RecursivePublishedFinite.S6_6447.mul
      (if n.val = 0 then (5 : Fin 6) else if n.val = 1 then 4 else 3) 4 =
      (if n.val = 0 then (4 : Fin 6) else 3)
  lowStep : ∀ n : Fin 3,
    RecursivePublishedFinite.S6_6447.mul
      (if n.val = 0 then (2 : Fin 6) else if n.val = 1 then 1 else 0) 4 =
      (if n.val = 0 then (1 : Fin 6) else 0)

def highValue (count : Nat) : Fin 6 := if count = 0 then 5 else if count = 1 then 4 else 3
def lowValue (count : Nat) : Fin 6 := if count = 0 then 2 else if count = 1 then 1 else 0

theorem highValue_cap (count : Nat) : highValue (min 2 count) = highValue count := by
  by_cases small : count ≤ 2
  · rw [Nat.min_eq_right small]
  have bound : 2 ≤ count := by omega
  have zero : count ≠ 0 := by omega
  have one : count ≠ 1 := by omega
  simp [Nat.min_eq_left bound, highValue, zero, one]

theorem lowValue_cap (count : Nat) : lowValue (min 2 count) = lowValue count := by
  by_cases small : count ≤ 2
  · rw [Nat.min_eq_right small]
  have bound : 2 ≤ count := by omega
  have zero : count ≠ 0 := by omega
  have one : count ≠ 1 := by omega
  simp [Nat.min_eq_left bound, lowValue, zero, one]

theorem highValue_separates {left right : Nat} (same : highValue left = highValue right) :
    min 2 left = min 2 right := by
  have finite : ∀ l r : Fin 3, highValue l.val = highValue r.val → l.val = r.val := by decide
  let l : Fin 3 := ⟨min 2 left, by omega⟩
  let r : Fin 3 := ⟨min 2 right, by omega⟩
  have equal : highValue l.val = highValue r.val :=
    (highValue_cap left).trans (same.trans (highValue_cap right).symm)
  exact finite l r equal

theorem lowValue_separates {left right : Nat} (same : lowValue left = lowValue right) :
    min 2 left = min 2 right := by
  have finite : ∀ l r : Fin 3, lowValue l.val = lowValue r.val → l.val = r.val := by decide
  let l : Fin 3 := ⟨min 2 left, by omega⟩
  let r : Fin 3 := ⟨min 2 right, by omega⟩
  have equal : lowValue l.val = lowValue r.val :=
    (lowValue_cap left).trans (same.trans (lowValue_cap right).symm)
  exact finite l r equal

theorem highValue_step (controls : ObservationControls) (count : Nat) :
    RecursivePublishedFinite.S6_6447.mul (highValue count) 4 = highValue (count + 1) := by
  by_cases zero : count = 0
  · subst count
    simpa [highValue] using controls.highStep 0
  by_cases one : count = 1
  · subst count
    simpa [highValue] using controls.highStep 1
  have nextZero : count + 1 ≠ 0 := by omega
  have nextOne : count + 1 ≠ 1 := by omega
  simpa [highValue, zero, one, nextZero, nextOne] using controls.highStep 2

theorem lowValue_step (controls : ObservationControls) (count : Nat) :
    RecursivePublishedFinite.S6_6447.mul (lowValue count) 4 = lowValue (count + 1) := by
  by_cases zero : count = 0
  · subst count
    simpa [lowValue] using controls.lowStep 0
  by_cases one : count = 1
  · subst count
    simpa [lowValue] using controls.lowStep 1
  have nextZero : count + 1 ≠ 0 := by omega
  have nextOne : count + 1 ≠ 1 := by omega
  simpa [lowValue, zero, one, nextZero, nextOne] using controls.lowStep 2

def run (valuation : Nat → Fin 6) (letters : List Nat) (initial : Fin 6) : Fin 6 :=
  letters.foldl (fun value letter => table.mul value (valuation letter)) initial

theorem run_cons (valuation : Nat → Fin 6) (head : Nat) (tail : List Nat) (initial : Fin 6) :
    run valuation (head :: tail) initial = run valuation tail (table.mul initial (valuation head)) := rfl

theorem run_append (valuation : Nat → Fin 6) (left right : List Nat) (initial : Fin 6) :
    run valuation (left ++ right) initial = run valuation right (run valuation left initial) := by
  simp only [run, List.foldl_append]

theorem run_congr (left right : Nat → Fin 6) (letters : List Nat) (initial : Fin 6)
    (agree : ∀ letter ∈ letters, left letter = right letter) :
    run left letters initial = run right letters initial := by
  induction letters generalizing initial with
  | nil => rfl
  | cons head tail induction =>
      simp only [run, List.foldl_cons]
      rw [agree head (by simp)]
      exact induction _ (fun letter member => agree letter (List.mem_cons_of_mem head member))

theorem run_word (valuation : Nat → Fin 6) (word : Word Nat) :
    run valuation word.toList 5 = table.semigroup.eval valuation word := by
  cases word with
  | mk head tail =>
      simp only [run, Word.toList, List.foldl_cons, Semigroup.eval]
      have unit := (RecursivePublishedFinite.S6_6447.identityControl (valuation head)).1
      change tail.foldl _ (RecursivePublishedFinite.S6_6447.mul 5 (valuation head)) = _
      rw [unit]
      rfl

def powerValuation (tested letter : Nat) : Fin 6 := if letter = tested then 4 else 5

theorem run_powers (value : Nat → Fin 6)
    (step : ∀ count, RecursivePublishedFinite.S6_6447.mul (value count) 4 = value (count + 1))
    (tested : Nat) (letters : List Nat) (initial : Nat) :
    run (powerValuation tested) letters (value initial) = value (initial + letters.count tested) := by
  induction letters generalizing initial with
  | nil => simp [run]
  | cons head tail induction =>
      by_cases equal : head = tested
      · subst head
        rw [run_cons, show powerValuation tested tested = 4 by simp [powerValuation]]
        change run (powerValuation tested) tail (RecursivePublishedFinite.S6_6447.mul (value initial) 4) = _
        rw [step, induction]
        simp only [List.count_cons_self]
        congr 1
        omega
      · change run (powerValuation tested) tail
            (RecursivePublishedFinite.S6_6447.mul (value initial) (powerValuation tested head)) = _
        rw [show powerValuation tested head = 5 by simp [powerValuation, equal],
          (RecursivePublishedFinite.S6_6447.identityControl (value initial)).2, induction,
          List.count_cons_of_ne equal]

theorem run_high_zero (controls : ObservationControls) (tested : Nat) (letters : List Nat) :
    run (powerValuation tested) letters 5 = highValue (letters.count tested) := by
  simpa only [highValue, if_pos rfl, Nat.zero_add] using
    run_powers highValue (highValue_step controls) tested letters 0

theorem run_low_zero (controls : ObservationControls) (tested : Nat) (letters : List Nat) :
    run (powerValuation tested) letters 2 = lowValue (letters.count tested) := by
  simpa only [lowValue, if_pos rfl, Nat.zero_add] using
    run_powers lowValue (lowValue_step controls) tested letters 0

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Recursive6447
