import SemigroupBasis.CoRoots.Order6SporadicSection22Models
import SemigroupBasis.CoRoots.Order6SporadicSection22E5Derivations

/-! E5 evaluation invariants. All finite computations use the literal
published table. The running accumulator permits empty list fragments;
the actual identity boundary remains a nonempty semigroup word. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection22.E5
open SemigroupBasis

def run (valuation : Nat → Fin 6) (acc : Fin 6) (letters : List Nat) : Fin 6 :=
  letters.foldl (fun current x => tableMul current (valuation x)) acc

theorem run_nil (valuation : Nat → Fin 6) (acc : Fin 6) : run valuation acc [] = acc := rfl
theorem run_cons (valuation : Nat → Fin 6) (acc : Fin 6) (x : Nat) (xs : List Nat) :
    run valuation acc (x :: xs) = run valuation (tableMul acc (valuation x)) xs := rfl
theorem run_append (valuation : Nat → Fin 6) (acc : Fin 6) (xs ys : List Nat) :
    run valuation acc (xs ++ ys) = run valuation (run valuation acc xs) ys := List.foldl_append

theorem run_mul (valuation : Nat → Fin 6) (letters : List Nat) (a b : Fin 6) :
    run valuation (tableMul a b) letters = tableMul a (run valuation b letters) := by
  induction letters generalizing b with
  | nil => rfl
  | cons x xs ih =>
      have associated : tableMul (tableMul a b) (valuation x) =
          tableMul a (tableMul b (valuation x)) := table.assoc a b (valuation x)
      rw [run_cons,associated,run_cons]
      exact ih _

def SameEval (left right : List Nat) : Prop :=
  ∀ (valuation : Nat → Fin 6) (acc : Fin 6), run valuation acc left = run valuation acc right

theorem SameEval.refl (letters : List Nat) : SameEval letters letters := fun _ _ => rfl
theorem SameEval.symm {left right : List Nat} (same : SameEval left right) : SameEval right left :=
  fun valuation acc => (same valuation acc).symm
theorem SameEval.trans {left middle right : List Nat} (first : SameEval left middle)
    (second : SameEval middle right) : SameEval left right :=
  fun valuation acc => (first valuation acc).trans (second valuation acc)

theorem sameEval_valid (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    SameEval identity.lhs.toList identity.rhs.toList := by
  intro valuation acc
  have boundary (word : Word Nat) :
      run valuation acc word.toList = tableMul acc (table.semigroup.eval valuation word) := by
    cases word with
    | mk head tail => exact run_mul valuation tail acc (valuation head)
  rw [boundary,boundary,valid valuation]

theorem derives_sameEval {left right : List Nat} (derivation : ListDerives left right) :
    SameEval left right := by
  cases derivation with
  | empty => exact SameEval.refl []
  | @words leftHead rightHead leftTail rightTail proof =>
      exact sameEval_valid ⟨S5_107.listWordOfCons leftHead leftTail,
        S5_107.listWordOfCons rightHead rightTail⟩ (proof.sound models)

theorem zeroRow (value : Fin 6) : tableMul 0 value = 0 := by revert value; decide

theorem run_zero (valuation : Nat → Fin 6) (letters : List Nat) : run valuation 0 letters = 0 := by
  induction letters with
  | nil => rfl
  | cons x xs ih => rw [run_cons,zeroRow]; exact ih

def headVal (marker x : Nat) : Fin 6 := if x = marker then 5 else 4

theorem headVal_stable (marker : Nat) (letters : List Nat) (acc : Fin 6)
    (stable : acc = 0 ∨ acc = 2) : run (headVal marker) acc letters = acc := by
  induction letters with
  | nil => rfl
  | cons x xs ih =>
      have fixed : tableMul acc (headVal marker x) = acc := by
        rcases stable with rfl | rfl
        · exact zeroRow _
        · by_cases same : x = marker
          · rw [headVal,if_pos same]
            decide
          · rw [headVal,if_neg same]
            decide
      rw [run_cons,fixed]
      exact ih

theorem headVal_cons (marker x : Nat) (xs : List Nat) :
    run (headVal marker) 1 (x :: xs) = if x = marker then 2 else 0 := by
  by_cases same : x = marker
  · rw [run_cons,headVal,if_pos same,show tableMul 1 5 = 2 by decide,
      headVal_stable marker xs 2 (Or.inr rfl),if_pos same]
  · rw [run_cons,headVal,if_neg same,show tableMul 1 4 = 0 by decide,
      headVal_stable marker xs 0 (Or.inl rfl),if_neg same]

theorem SameEval.head {left right : List Nat} (same : SameEval left right) : left.head? = right.head? := by
  cases left with
  | nil =>
      cases right with
      | nil => rfl
      | cons y ys =>
          have impossible : (1 : Fin 6) = 2 := by simpa [run_nil,headVal_cons] using same (headVal y) 1
          exact False.elim ((by decide : (1 : Fin 6) ≠ 2) impossible)
  | cons x xs =>
      cases right with
      | nil =>
          have impossible : (2 : Fin 6) = 1 := by simpa [run_nil,headVal_cons] using same (headVal x) 1
          exact False.elim ((by decide : (2 : Fin 6) ≠ 1) impossible)
      | cons y ys =>
          by_cases equal : x = y
          · simp [equal]
          · have impossible : (2 : Fin 6) = 0 := by
              simpa [headVal_cons,Ne.symm equal] using same (headVal x) 1
            exact False.elim ((by decide : (2 : Fin 6) ≠ 0) impossible)

def multiplicityValue : Nat → Fin 6
  | 0 => 4
  | 1 => 2
  | _ + 2 => 0

theorem multiplicityValue_add (m n : Nat) :
    tableMul (multiplicityValue m) (multiplicityValue n) = multiplicityValue (m + n) := by
  cases m with
  | zero =>
      cases n with
      | zero => rfl
      | succ n => cases n <;> rfl
  | succ m =>
      cases m with
      | zero =>
          cases n with
          | zero => rfl
          | succ n => cases n <;> rfl
      | succ m =>
          cases n with
          | zero => rfl
          | succ n => cases n <;> rfl

def countVal (marker x : Nat) : Fin 6 := if x = marker then 2 else 4

theorem countVal_run (marker : Nat) (letters : List Nat) (n : Nat) :
    run (countVal marker) (multiplicityValue n) letters = multiplicityValue (n + letters.count marker) := by
  induction letters generalizing n with
  | nil => rfl
  | cons x xs ih =>
      by_cases equal : x = marker
      · subst x
        rw [run_cons,countVal,if_pos rfl]
        change run (countVal marker) (tableMul (multiplicityValue n) (multiplicityValue 1)) xs = _
        rw [multiplicityValue_add,ih]
        simp [List.count_cons_self,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      · rw [run_cons,countVal,if_neg equal]
        change run (countVal marker) (tableMul (multiplicityValue n) (multiplicityValue 0)) xs = _
        rw [multiplicityValue_add,ih]
        simp [List.count_cons_of_ne equal]

theorem multiplicityValue_zero (n : Nat) : multiplicityValue n = 4 ↔ n = 0 := by
  cases n with
  | zero => decide
  | succ n => cases n <;> simp [multiplicityValue]

theorem multiplicityValue_one (n : Nat) : multiplicityValue n = 2 ↔ n = 1 := by
  cases n with
  | zero => decide
  | succ n => cases n <;> simp [multiplicityValue]

theorem SameEval.multiplicity {left right : List Nat} (same : SameEval left right) (x : Nat) :
    multiplicityValue (left.count x) = multiplicityValue (right.count x) := by
  have equal := same (countVal x) (multiplicityValue 0)
  simpa [countVal_run] using equal

theorem SameEval.countOne {left right : List Nat} (same : SameEval left right) (x : Nat) :
    left.count x = 1 ↔ right.count x = 1 := by
  rw [← multiplicityValue_one,← multiplicityValue_one,same.multiplicity x]

theorem SameEval.mem {left right : List Nat} (same : SameEval left right) (x : Nat) : x ∈ left ↔ x ∈ right := by
  have zeroEqual : left.count x = 0 ↔ right.count x = 0 := by
    rw [← multiplicityValue_zero,← multiplicityValue_zero,same.multiplicity x]
  constructor
  · intro member
    by_cases found : x ∈ right
    · exact found
    · exact False.elim ((List.count_eq_zero.mp (zeroEqual.mpr (List.count_eq_zero.mpr found))) member)
  · intro member
    by_cases found : x ∈ left
    · exact found
    · exact False.elim ((List.count_eq_zero.mp (zeroEqual.mp (List.count_eq_zero.mpr found))) member)

#print axioms sameEval_valid
#print axioms derives_sameEval
#print axioms SameEval.head
#print axioms SameEval.countOne
#print axioms SameEval.mem

end SemigroupBasis.CoRoots.Order6SporadicSection22.E5
