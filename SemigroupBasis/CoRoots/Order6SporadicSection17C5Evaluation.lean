import SemigroupBasis.CoRoots.Order6SporadicSection17S62778Tables
import SemigroupBasis.CoRoots.Order6SporadicSection17S62779Tables
import SemigroupBasis.CoRoots.Order6SporadicSection17C5Derivations

/-! Shared arbitrary-list evaluation for the two literal targets. The
Boolean selects C5/2778 or C6/2779; no relation between their theories is
assumed. The same elementary count detector works in both actual tables. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics
open SemigroupBasis

def mul (which : Bool) (a b : Fin 6) : Fin 6 :=
  if which then S6_2779.tableMul a b else S6_2778.tableMul a b

/-- Keep the carrier literally Fin6 across the selector boundary. -/
def table (which : Bool) : FiniteTable where
  order := 6
  mul := mul which
  assoc := by
    intro a b c
    cases which with
    | false => exact S6_2778.table.assoc a b c
    | true => exact S6_2779.table.assoc a b c

theorem models (which : Bool) : Models (table which).semigroup basis := by
  cases which with
  | false => exact S6_2778.models
  | true => exact S6_2779.models

def run (which : Bool) (valuation : Nat → Fin 6) (acc : Fin 6) (letters : List Nat) : Fin 6 :=
  letters.foldl (fun current x => mul which current (valuation x)) acc

theorem run_nil (which : Bool) (valuation : Nat → Fin 6) (acc : Fin 6) :
    run which valuation acc [] = acc := rfl
theorem run_cons (which : Bool) (valuation : Nat → Fin 6) (acc : Fin 6) (x : Nat) (xs : List Nat) :
    run which valuation acc (x :: xs) = run which valuation (mul which acc (valuation x)) xs := rfl
theorem run_append (which : Bool) (valuation : Nat → Fin 6) (acc : Fin 6) (xs ys : List Nat) :
    run which valuation acc (xs ++ ys) = run which valuation (run which valuation acc xs) ys := List.foldl_append

theorem run_mul (which : Bool) (valuation : Nat → Fin 6) (letters : List Nat) (a b : Fin 6) :
    run which valuation (mul which a b) letters = mul which a (run which valuation b letters) := by
  induction letters generalizing b with
  | nil => rfl
  | cons x xs ih =>
      have associated : mul which (mul which a b) (valuation x) =
          mul which a (mul which b (valuation x)) := (table which).assoc a b (valuation x)
      rw [run_cons,associated,run_cons]
      exact ih _

/-- None is the adjoined empty-word identity, not an extra semigroup element.
Using full nonempty evaluation retains the simple-head observation. -/
def evalList (which : Bool) (valuation : Nat → Fin 6) : List Nat → Option (Fin 6)
  | [] => none
  | x :: xs => some (run which valuation (valuation x) xs)

def SameEval (which : Bool) (left right : List Nat) : Prop :=
  ∀ valuation : Nat → Fin 6, evalList which valuation left = evalList which valuation right

theorem SameEval.refl (which : Bool) (letters : List Nat) : SameEval which letters letters := fun _ => rfl
theorem SameEval.symm {which : Bool} {left right : List Nat}
    (same : SameEval which left right) : SameEval which right left := fun valuation => (same valuation).symm
theorem SameEval.trans {which : Bool} {left middle right : List Nat}
    (first : SameEval which left middle) (second : SameEval which middle right) :
    SameEval which left right := fun valuation => (first valuation).trans (second valuation)

theorem SameEval.runEq {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (valuation : Nat → Fin 6) (acc : Fin 6) :
    run which valuation acc left = run which valuation acc right := by
  have boundary (letters : List Nat) : run which valuation acc letters =
      (evalList which valuation letters).elim acc (mul which acc) := by
    cases letters with
    | nil => rfl
    | cons x xs => exact run_mul which valuation xs acc (valuation x)
  rw [boundary,boundary,same valuation]

theorem sameEval_valid (which : Bool) (identity : Identity Nat)
    (valid : identity.SatisfiedBy (table which).semigroup) :
    SameEval which identity.lhs.toList identity.rhs.toList := by
  intro valuation
  change some ((table which).semigroup.eval valuation identity.lhs) =
    some ((table which).semigroup.eval valuation identity.rhs)
  exact congrArg some (valid valuation)

theorem derives_sameEval (which : Bool) {left right : List Nat} (derivation : ListDerives left right) :
    SameEval which left right := by
  cases derivation with
  | empty => exact SameEval.refl which []
  | @words leftHead rightHead leftTail rightTail proof =>
      exact sameEval_valid which ⟨S5_107.listWordOfCons leftHead leftTail,
        S5_107.listWordOfCons rightHead rightTail⟩ (proof.sound (models which))

theorem zeroRow (which : Bool) (value : Fin 6) : mul which 0 value = 0 := by
  revert which value
  decide

theorem run_zero (which : Bool) (valuation : Nat → Fin 6) (letters : List Nat) :
    run which valuation 0 letters = 0 := by
  induction letters with
  | nil => rfl
  | cons x xs ih => rw [run_cons,zeroRow]; exact ih

def multiplicityValue : Nat → Fin 6
  | 0 => 5
  | 1 => 1
  | _ + 2 => 0

theorem multiplicityValue_add (which : Bool) (m n : Nat) :
    mul which (multiplicityValue m) (multiplicityValue n) = multiplicityValue (m + n) := by
  cases m with
  | zero =>
      cases n with
      | zero => cases which <;> rfl
      | succ n => cases n <;> cases which <;> rfl
  | succ m =>
      cases m with
      | zero =>
          cases n with
          | zero => cases which <;> rfl
          | succ n => cases n <;> cases which <;> rfl
      | succ m =>
          cases n with
          | zero => cases which <;> rfl
          | succ n => cases n <;> cases which <;> rfl

def countVal (marker x : Nat) : Fin 6 := if x = marker then 1 else 5

theorem countVal_run (which : Bool) (marker : Nat) (letters : List Nat) (n : Nat) :
    run which (countVal marker) (multiplicityValue n) letters =
      multiplicityValue (n + letters.count marker) := by
  induction letters generalizing n with
  | nil => rfl
  | cons x xs ih =>
      by_cases equal : x = marker
      · subst x
        rw [run_cons,countVal,if_pos rfl]
        change run which (countVal marker) (mul which (multiplicityValue n) (multiplicityValue 1)) xs = _
        rw [multiplicityValue_add,ih]
        simp [List.count_cons_self,Nat.add_comm,Nat.add_left_comm]
      · rw [run_cons,countVal,if_neg equal]
        change run which (countVal marker) (mul which (multiplicityValue n) (multiplicityValue 0)) xs = _
        rw [multiplicityValue_add,ih]
        simp [List.count_cons_of_ne equal]

theorem multiplicityValue_zero (n : Nat) : multiplicityValue n = 5 ↔ n = 0 := by
  cases n with
  | zero => decide
  | succ n => cases n <;> simp [multiplicityValue]

theorem multiplicityValue_one (n : Nat) : multiplicityValue n = 1 ↔ n = 1 := by
  cases n with
  | zero => decide
  | succ n => cases n <;> simp [multiplicityValue]

theorem SameEval.multiplicity {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (x : Nat) :
    multiplicityValue (left.count x) = multiplicityValue (right.count x) := by
  have equal := same.runEq (countVal x) (multiplicityValue 0)
  simpa [countVal_run] using equal

theorem SameEval.countOne {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (x : Nat) : left.count x = 1 ↔ right.count x = 1 := by
  rw [← multiplicityValue_one,← multiplicityValue_one,same.multiplicity x]

theorem SameEval.mem {which : Bool} {left right : List Nat}
    (same : SameEval which left right) (x : Nat) : x ∈ left ↔ x ∈ right := by
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

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.models
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.sameEval_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.derives_sameEval
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.countOne
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics.SameEval.mem

end SemigroupBasis.CoRoots.Order6SporadicSection17.C5C6.Semantics
