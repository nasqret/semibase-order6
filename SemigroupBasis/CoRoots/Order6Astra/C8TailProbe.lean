import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedSemanticSimpleAdjacency

namespace SemigroupBasis.CoRoots.Order6Astra.C8TailProbe

open Order6SporadicSection19
open Order6SporadicSection19.Published.SemanticSimpleAdjacency

/-- A binary assignment: `true` is d=5 and `false` is e=6 in the literal table. -/
def binary (d : Nat → Bool) (x : Nat) : Fin 6 := if d x then 4 else 5

/-- The unique simple marker is x=3; other letters are assigned d or e. -/
def probe (d : Nat → Bool) (t x : Nat) : Fin 6 :=
  if x = t then 2 else binary d x

def allE (d : Nat → Bool) (xs : List Nat) : Bool := xs.all (fun x => !(d x))
def allD (d : Nat → Bool) (xs : List Nat) : Bool := xs.all d

/-- No d-letter is followed by an e-letter. No bound on the input word. -/
def ordered (d : Nat → Bool) : List Nat → Bool
  | [] => true
  | x :: xs => if d x then allD d xs else ordered d xs

theorem zero_left : ∀ x : Fin 6, mul6 0 x = 0 := by decide

theorem run_zero (v : Nat → Fin 6) (xs : List Nat) : run v 0 xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [run_cons, zero_left, ih]

theorem run_congr_on (v w : Nat → Fin 6) (xs : List Nat)
    (same : ∀ x ∈ xs, v x = w x) (initial : Fin 6) :
    run v initial xs = run w initial xs := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
    rw [run_cons, run_cons, same x List.mem_cons_self]
    exact ih (fun y hy => same y (List.mem_cons_of_mem x hy)) _

theorem run_off_marker (d : Nat → Bool) (t : Nat) (xs : List Nat)
    (absent : t ∉ xs) (initial : Fin 6) :
    run (probe d t) initial xs = run (binary d) initial xs := by
  apply run_congr_on
  intro x hx
  have ne : x ≠ t := fun e => absent (e ▸ hx)
  exact if_neg ne

theorem run_three (d : Nat → Bool) (xs : List Nat) :
    run (binary d) 3 xs = if allD d xs then 3 else 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [run_cons]
    cases h : d x with
    | false =>
      have val : binary d x = 5 := by simp only [binary, h, Bool.false_eq_true, if_false]
      rw [val]
      have step : mul6 3 5 = 0 := by decide
      rw [step, run_zero]
      simp only [allD, List.all_cons, h, Bool.false_and, Bool.false_eq_true, if_false]
    | true =>
      have val : binary d x = 4 := by simp only [binary, h, if_true]
      rw [val]
      have step : mul6 3 4 = 3 := by decide
      rw [step, ih]
      simp only [allD, List.all_cons, h, Bool.true_and]

theorem run_five (d : Nat → Bool) (xs : List Nat) :
    run (binary d) 5 xs =
      if allE d xs then 5 else if ordered d xs then 3 else 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [run_cons]
    cases h : d x with
    | false =>
      have val : binary d x = 5 := by simp only [binary, h, Bool.false_eq_true, if_false]
      rw [val]
      have step : mul6 5 5 = 5 := by decide
      rw [step, ih]
      simp only [allE, List.all_cons, h, Bool.not_false, Bool.true_and, ordered,
        Bool.false_eq_true, if_false]
    | true =>
      have val : binary d x = 4 := by simp only [binary, h, if_true]
      rw [val]
      have step : mul6 5 4 = 3 := by decide
      rw [step, run_three]
      simp only [allE, List.all_cons, h, Bool.not_true, Bool.false_and, ordered,
        if_true, Bool.false_eq_true, if_false]

theorem allE_ordered (d : Nat → Bool) (xs : List Nat) (h : allE d xs = true) :
    ordered d xs = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have both : (Bool.not (d x) = true) ∧ allE d xs = true := by
      simpa only [allE, List.all_cons, Bool.and_eq_true] using h
    have dx : d x = false := by
      cases hx : d x <;> simp_all
    simp only [ordered, dx, Bool.false_eq_true, if_false]
    exact ih both.2

theorem prefix_marker (d : Nat → Bool) (xs : List Nat) :
    mul6 (run (binary d) 5 xs) 2 = if ordered d xs then 1 else 0 := by
  rw [run_five]
  cases he : allE d xs with
  | false =>
    simp only [Bool.false_eq_true, if_false]
    cases ordered d xs <;> decide
  | true =>
    simp only [allE_ordered d xs he]
    decide

theorem run_one (d : Nat → Bool) (xs : List Nat) :
    run (binary d) 1 xs = if allE d xs then 1 else 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [run_cons]
    cases h : d x with
    | false =>
      have val : binary d x = 5 := by simp only [binary, h, Bool.false_eq_true, if_false]
      rw [val]
      have step : mul6 1 5 = 1 := by decide
      rw [step, ih]
      simp only [allE, List.all_cons, h, Bool.not_false, Bool.true_and]
    | true =>
      have val : binary d x = 4 := by simp only [binary, h, if_true]
      rw [val]
      have step : mul6 1 4 = 0 := by decide
      rw [step, run_zero]
      simp only [allE, List.all_cons, h, Bool.not_true, Bool.false_and,
        Bool.false_eq_true, if_false]

/-- Exact evaluation of an arbitrary simple-marker cut, padded on the left by e.
The result is nonzero precisely for an e*d* prefix and an e* suffix. -/
theorem cut_value (d : Nat → Bool) (t : Nat) (p s : List Nat)
    (hp : t ∉ p) (hs : t ∉ s) :
    run (probe d t) 5 (p ++ t :: s) =
      if ordered d p && allE d s then 1 else 0 := by
  rw [run_append, run_cons, run_off_marker d t p hp]
  have marker : probe d t t = 2 := if_pos rfl
  rw [marker, prefix_marker]
  cases h : ordered d p with
  | false =>
    simp only [Bool.false_eq_true, if_false, Bool.false_and]
    exact run_zero _ _
  | true =>
    simp only [if_true, Bool.true_and]
    rw [run_off_marker d t s hs, run_one]

theorem word_cut_value (d : Nat → Bool) (t : Nat) (w : Word Nat) (p s : List Nat)
    (split : w.toList = p ++ t :: s) (simple : w.toList.count t = 1) :
    mul6 5 (table.semigroup.eval (probe d t) w) =
      if ordered d p && allE d s then 1 else 0 := by
  have counts : p.count t + (s.count t + 1) = 1 := by
    simpa only [split, List.count_append, List.count_cons_self] using simple
  have hp : t ∉ p := List.count_eq_zero.mp (by omega)
  have hs : t ∉ s := List.count_eq_zero.mp (by omega)
  rw [← run_word_left, split]
  exact cut_value d t p s hp hs

/-- Every admissible binary cut is invariant under actual C8 word-function
equality. This is not an assumed or bounded normal-form invariant. -/
theorem equal_eval_cut (u v : Word Nat) (eqv : EqualEval u v) (t : Nat)
    (p s q r : List Nat) (hu : u.toList = p ++ t :: s)
    (hv : v.toList = q ++ t :: r) (su : u.toList.count t = 1)
    (sv : v.toList.count t = 1) (d : Nat → Bool) :
    (ordered d p && allE d s) = (ordered d q && allE d r) := by
  have same :
      (if ordered d p && allE d s then (1 : Fin 6) else 0) =
      (if ordered d q && allE d r then (1 : Fin 6) else 0) :=
    (word_cut_value d t u p s hu su).symm.trans
      ((congrArg (mul6 5) (eqv (probe d t))).trans (word_cut_value d t v q r hv sv))
  have injective : Function.Injective (fun b : Bool => if b then (1 : Fin 6) else 0) := by
    intro a b
    cases a <;> cases b <;> decide
  exact injective same

end SemigroupBasis.CoRoots.Order6Astra.C8TailProbe

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8TailProbe.cut_value
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8TailProbe.word_cut_value
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8TailProbe.equal_eval_cut
