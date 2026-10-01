import SemigroupBasis.CoRoots.Order6SporadicSection18ActualModel
import SemigroupBasis.CoRoots.Order6SporadicSection18Squares

/-! Actual-C7 arbitrary-word evaluation. Its local units separate values;
the nilpotent two-element generator with local identity detects content and
simple letters, without imposing a word-length or alphabet bound. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Actual
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

theorem run_word (valuation : Nat → Fin 6) (acc : Fin 6) (word : Word Nat) :
    run valuation acc word.toList = tableMul acc (table.semigroup.eval valuation word) := by
  cases word with
  | mk head tail => exact run_mul valuation tail acc (valuation head)

def SameEval (left right : List Nat) : Prop :=
  ∀ (valuation : Nat → Fin 6) (acc : Fin 6), run valuation acc left = run valuation acc right

theorem SameEval.refl (letters : List Nat) : SameEval letters letters := fun _ _ => rfl
theorem SameEval.symm {left right : List Nat} (same : SameEval left right) : SameEval right left :=
  fun valuation acc => (same valuation acc).symm
theorem SameEval.trans {left middle right : List Nat}
    (first : SameEval left middle) (second : SameEval middle right) : SameEval left right :=
  fun valuation acc => (first valuation acc).trans (second valuation acc)

theorem sameEval_valid (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) :
    SameEval identity.lhs.toList identity.rhs.toList := by
  intro valuation acc
  rw [run_word,run_word,valid valuation]

theorem sameEval_sound (identity : Identity Nat)
    (same : SameEval identity.lhs.toList identity.rhs.toList) :
    identity.SatisfiedBy table.semigroup := by
  intro valuation
  apply left_units_injective (table.semigroup.eval valuation identity.lhs)
    (table.semigroup.eval valuation identity.rhs)
  · simpa only [run_word] using same valuation 4
  · simpa only [run_word] using same valuation 5

theorem sameEval_iff_valid (identity : Identity Nat) :
    SameEval identity.lhs.toList identity.rhs.toList ↔ identity.SatisfiedBy table.semigroup :=
  ⟨sameEval_sound identity,sameEval_valid identity⟩

theorem derives_sameEval {left right : List Nat} (derivation : ListDerives left right) :
    SameEval left right := by
  cases derivation with
  | empty => exact SameEval.refl []
  | @words leftHead rightHead leftTail rightTail proof =>
      exact sameEval_valid ⟨S5_107.listWordOfCons leftHead leftTail,
        S5_107.listWordOfCons rightHead rightTail⟩ (proof.sound models)

theorem run_zero (valuation : Nat → Fin 6) (letters : List Nat) : run valuation 0 letters = 0 := by
  induction letters with
  | nil => rfl
  | cons x xs ih => rw [run_cons,(zero_absorbing (valuation x)).1]; exact ih

def multiplicityValue : Nat → Fin 6
  | 0 => 5
  | 1 => 1
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

def countVal (marker x : Nat) : Fin 6 := if x = marker then 1 else 5

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

theorem multiplicityValue_zero (n : Nat) : multiplicityValue n = 5 ↔ n = 0 := by
  cases n with
  | zero => decide
  | succ n =>
      cases n with
      | zero => decide
      | succ n =>
          constructor
          · intro impossible
            exact False.elim ((by decide : (0 : Fin 6) ≠ 5) impossible)
          · intro impossible
            omega

theorem multiplicityValue_one (n : Nat) : multiplicityValue n = 1 ↔ n = 1 := by
  cases n with
  | zero => decide
  | succ n =>
      cases n with
      | zero => decide
      | succ n =>
          constructor
          · intro impossible
            exact False.elim ((by decide : (0 : Fin 6) ≠ 1) impossible)
          · intro impossible
            omega

theorem SameEval.multiplicity {left right : List Nat} (same : SameEval left right) (x : Nat) :
    multiplicityValue (left.count x) = multiplicityValue (right.count x) := by
  have equal := same (countVal x) (multiplicityValue 0)
  simpa [countVal_run] using equal

theorem SameEval.countOne {left right : List Nat} (same : SameEval left right) (x : Nat) :
    left.count x = 1 ↔ right.count x = 1 := by
  rw [← multiplicityValue_one,← multiplicityValue_one,same.multiplicity x]

theorem SameEval.mem {left right : List Nat} (same : SameEval left right) (x : Nat) :
    x ∈ left ↔ x ∈ right := by
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

theorem identity_content (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) (x : Nat) :
    x ∈ identity.lhs.toList ↔ x ∈ identity.rhs.toList := (sameEval_valid identity valid).mem x

theorem identity_simple (identity : Identity Nat) (valid : identity.SatisfiedBy table.semigroup) (x : Nat) :
    identity.lhs.toList.count x = 1 ↔ identity.rhs.toList.count x = 1 :=
  (sameEval_valid identity valid).countOne x

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.run_word
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.sameEval_iff_valid
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.derives_sameEval
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.run_zero
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.countVal_run
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.SameEval.countOne
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.SameEval.mem
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.identity_content
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Actual.identity_simple

end SemigroupBasis.CoRoots.Order6SporadicSection18.Actual
