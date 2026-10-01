import SemigroupBasis.Generated.CatalogueOrder3
import SemigroupBasis.CoRoots.Order6Sunday.Msg0457S11395Parity

/-! Arbitrary-word evaluation of the actual S3_10 support/parity factor.
No canonical adapter, target derivation, or completeness assumption is used. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808FactorEval

open SemigroupBasis
open Msg0457S11395Parity (parityBit xorFold_eq_parityBit)

abbrev table := Generated.Catalogue.S3_10.table
abbrev factor : Semigroup (Fin 3) := table.semigroup
abbrev mul := Generated.Catalogue.S3_10.mul

def evalList (valuation : α → Fin 3) (xs : List α) : Fin 3 :=
  xs.foldl (fun a x => mul a (valuation x)) 2

def decode (allIdentity odd : Bool) : Fin 3 := if allIdentity then 2 else if odd then 1 else 0

theorem left_identity : ∀ a : Fin 3, mul 2 a = a := by decide

theorem mul_identity (a b : Fin 3) :
    (mul a b == 2) = ((a == 2) && (b == 2)) := by revert a b; decide

theorem mul_odd (a b : Fin 3) :
    (mul a b == 1) = ((a == 1) != (b == 1)) := by revert a b; decide

theorem observations_injective : Function.Injective (fun a : Fin 3 => (a == 2,a == 1)) := by
  intro a b equal
  revert a b
  decide

theorem value_decode (a : Fin 3) : a = decode (a == 2) (a == 1) := by revert a; decide

theorem fold_identity (valuation : α → Fin 3) (xs : List α) (initial : Fin 3) :
    (xs.foldl (fun a x => mul a (valuation x)) initial == 2) =
      ((initial == 2) && xs.all (fun x => valuation x == 2)) := by
  induction xs generalizing initial with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons,List.all_cons,ih,mul_identity]
    exact Bool.and_assoc _ _ _

theorem fold_odd (valuation : α → Fin 3) (xs : List α) (initial : Fin 3) :
    (xs.foldl (fun a x => mul a (valuation x)) initial == 1) =
      xs.foldl (fun bit x => bit != (valuation x == 1)) (initial == 1) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,ih,mul_odd]

theorem eval_eq_evalList (valuation : α → Fin 3) (word : Word α) :
    factor.eval valuation word = evalList valuation word.toList := by
  cases word with
  | mk head tail =>
    simp only [evalList,Word.toList,List.foldl_cons,left_identity]
    rfl

theorem eval_identity (valuation : α → Fin 3) (word : Word α) :
    (factor.eval valuation word == 2) = word.toList.all (fun x => valuation x == 2) := by
  rw [eval_eq_evalList,evalList,fold_identity]
  rfl

theorem eval_odd (valuation : α → Fin 3) (word : Word α) :
    (factor.eval valuation word == 1) = parityBit (word.toList.countP (fun x => valuation x == 1)) := by
  rw [eval_eq_evalList,evalList,fold_odd]
  change word.toList.foldl (fun bit x => bit != (valuation x == 1)) (parityBit 0) = _
  simpa only [Nat.zero_add] using xorFold_eq_parityBit (fun x => valuation x == 1) word.toList 0

theorem eval_formula (valuation : α → Fin 3) (word : Word α) :
    factor.eval valuation word = decode (word.toList.all (fun x => valuation x == 2))
      (parityBit (word.toList.countP (fun x => valuation x == 1))) := by
  calc
    factor.eval valuation word = decode (factor.eval valuation word == 2)
      (factor.eval valuation word == 1) := value_decode _
    _ = _ := by rw [eval_identity,eval_odd]

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808FactorEval
