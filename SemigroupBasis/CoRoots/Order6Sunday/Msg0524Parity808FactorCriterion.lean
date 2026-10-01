import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808FactorEval
import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Counts

/-! Exact unrestricted identity criterion for the actual S3_10 factor.
The generic predicate-count aggregation is reused, not reproved or replayed. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808FactorCriterion

open SemigroupBasis
open Msg0524Parity808FactorEval
open Msg0457S11395Parity (parityBit parityBit_injective_mod)
open Msg0457S11395Counts (countP_mod_eq)

def SameSupportParity (left right : Word Nat) : Prop :=
  (∀ x, x ∈ left.toList ↔ x ∈ right.toList) ∧
    (∀ x, left.toList.count x % 2 = right.toList.count x % 2)

def supportProbe (letter x : Nat) : Fin 3 := if x = letter then 0 else 2
def parityProbe (letter x : Nat) : Fin 3 := if x = letter then 1 else 0

theorem supportProbe_all (xs : List Nat) (letter : Nat) :
    xs.all (fun x => supportProbe letter x == 2) = decide (letter ∉ xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases same : x = letter
    · subst x
      simp [supportProbe]
    · simp only [List.all_cons]
      rw [show (supportProbe letter x == 2) = true by simp [supportProbe,same],Bool.true_and,ih]
      simp [Ne.symm same]

theorem parityProbe_predicate (letter : Nat) :
    (fun x => parityProbe letter x == 1) = (fun x => x == letter) := by
  funext x
  by_cases same : x = letter <;> simp [parityProbe,same]

theorem support_of_valid (identity : Identity Nat) (valid : identity.SatisfiedBy factor) (letter : Nat) :
    letter ∈ identity.lhs.toList ↔ letter ∈ identity.rhs.toList := by
  have observed := congrArg (fun value : Fin 3 => value == 2) (valid (supportProbe letter))
  change (factor.eval (supportProbe letter) identity.lhs == 2) =
    (factor.eval (supportProbe letter) identity.rhs == 2) at observed
  rw [eval_identity,eval_identity,supportProbe_all,supportProbe_all] at observed
  by_cases left : letter ∈ identity.lhs.toList <;>
    by_cases right : letter ∈ identity.rhs.toList <;> simp_all

theorem parity_of_valid (identity : Identity Nat) (valid : identity.SatisfiedBy factor) (letter : Nat) :
    identity.lhs.toList.count letter % 2 = identity.rhs.toList.count letter % 2 := by
  have observed := congrArg (fun value : Fin 3 => value == 1) (valid (parityProbe letter))
  change (factor.eval (parityProbe letter) identity.lhs == 1) =
    (factor.eval (parityProbe letter) identity.rhs == 1) at observed
  rw [eval_odd,eval_odd,parityProbe_predicate] at observed
  exact parityBit_injective_mod observed

theorem all_eq_of_support (left right : List Nat) (predicate : Nat → Bool)
    (support : ∀ x, x ∈ left ↔ x ∈ right) : left.all predicate = right.all predicate := by
  have equivalent : left.all predicate = true ↔ right.all predicate = true := by
    constructor
    · intro h
      exact List.all_eq_true.mpr (fun x hx => List.all_eq_true.mp h x ((support x).mpr hx))
    · intro h
      exact List.all_eq_true.mpr (fun x hx => List.all_eq_true.mp h x ((support x).mp hx))
  cases hl : left.all predicate <;> cases hr : right.all predicate <;> simp_all

theorem valid_of_signature (identity : Identity Nat)
    (same : SameSupportParity identity.lhs identity.rhs) : identity.SatisfiedBy factor := by
  intro valuation
  have allEqual := all_eq_of_support identity.lhs.toList identity.rhs.toList
    (fun x => valuation x == 2) same.1
  have counts := countP_mod_eq identity.lhs.toList identity.rhs.toList
    (fun x => valuation x == 1) same.2
  have bits : parityBit (identity.lhs.toList.countP (fun x => valuation x == 1)) =
      parityBit (identity.rhs.toList.countP (fun x => valuation x == 1)) := by
    unfold parityBit
    rw [counts]
  rw [eval_formula,eval_formula,allEqual,bits]

theorem valid_iff_signature (identity : Identity Nat) :
    identity.SatisfiedBy factor ↔ SameSupportParity identity.lhs identity.rhs := by
  constructor
  · intro valid
    exact ⟨support_of_valid identity valid,parity_of_valid identity valid⟩
  · exact valid_of_signature identity

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808FactorCriterion
