import SemigroupBasis.CoRoots.S5_848Normalization
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.Transfer
import SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808FactorCriterion

/-! Necessary last-block signature for actual S5_808. The block coordinate
is a genuine quotient; the leading-letter observation on the opposite is
from a genuine left-zero subsemigroup, NOT a head quotient. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808LastNecessary

open SemigroupBasis
open Msg0524Parity808FactorCriterion (SameSupportParity)

abbrev rightFactor : Semigroup (Fin 5) := Generated.Catalogue.S5_808.table.semigroup
abbrev oppositeFactor : Semigroup (Fin 5) := rightFactor.opposite

def blockQuotient : SplitSurjection oppositeFactor Generated.S4_71.table.semigroup.opposite where
  toFun := fun value =>
    if value = (0 : Fin 5) then (0 : Fin 4)
    else if value = (1 : Fin 5) then (1 : Fin 4)
    else if value = (2 : Fin 5) ∨ value = (3 : Fin 5) then (2 : Fin 4)
    else (3 : Fin 4)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  preimage := fun value =>
    if value = (0 : Fin 4) then (0 : Fin 5)
    else if value = (1 : Fin 4) then (1 : Fin 5)
    else if value = (2 : Fin 4) then (2 : Fin 5)
    else (4 : Fin 5)
  right_inverse := by
    intro value
    apply Fin.ext
    revert value
    decide

theorem leftZero_mul (a b : Fin 5) (ha : a = 2 ∨ a = 3) (hb : b = 2 ∨ b = 3) :
    oppositeFactor.mul a b = a := by
  revert a b
  decide

theorem leftZero_fold (valuation : α → Fin 5) (xs : List α) (initial : Fin 5)
    (hi : initial = 2 ∨ initial = 3) (range : ∀ x ∈ xs, valuation x = 2 ∨ valuation x = 3) :
    xs.foldl (fun a x => oppositeFactor.mul a (valuation x)) initial = initial := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons,leftZero_mul initial (valuation x) hi (range x (by simp))]
    exact ih (fun y hy => range y (List.mem_cons_of_mem x hy))

theorem leftZero_eval (valuation : α → Fin 5) (word : Word α)
    (range : ∀ x ∈ word.toList, valuation x = 2 ∨ valuation x = 3) :
    oppositeFactor.eval valuation word = valuation word.head := by
  cases word with
  | mk head tail =>
    change tail.foldl (fun a x => oppositeFactor.mul a (valuation x)) (valuation head) = valuation head
    exact leftZero_fold valuation tail (valuation head)
      (range head (by simp [Word.toList]))
      (fun x hx => range x (by simp [Word.toList,hx]))

def headProbe (letter x : Nat) : Fin 5 := if x = letter then 2 else 3

theorem headProbe_range (letter x : Nat) : headProbe letter x = 2 ∨ headProbe letter x = 3 := by
  by_cases same : x = letter <;> simp [headProbe,same]

theorem headProbe_eval (word : Word Nat) (letter : Nat) :
    oppositeFactor.eval (headProbe letter) word = headProbe letter word.head :=
  leftZero_eval (headProbe letter) word (fun x _ => headProbe_range letter x)

theorem valid_head (identity : Identity Nat) (valid : identity.SatisfiedBy oppositeFactor) :
    identity.lhs.head = identity.rhs.head := by
  by_cases same : identity.lhs.head = identity.rhs.head
  · exact same
  · have observed := valid (headProbe identity.lhs.head)
    rw [headProbe_eval,headProbe_eval] at observed
    simp [headProbe,Ne.symm same] at observed

theorem valid_sameSignature (identity : Identity Nat) (valid : identity.SatisfiedBy oppositeFactor) :
    S5_848.SameTailSquareSignature identity.lhs identity.rhs :=
  S5_848.sameSignature_of_block_valid_head_eq identity
    (blockQuotient.pushforwardIdentity identity valid) (valid_head identity valid)

theorem valid_lastSignature (identity : Identity Nat) (valid : identity.SatisfiedBy rightFactor) :
    S5_848.SameTailSquareSignature identity.reversed.lhs identity.reversed.rhs := by
  have reversedValid : identity.reversed.SatisfiedBy oppositeFactor :=
    (Identity.satisfiedBy_opposite_iff_reversed identity.reversed rightFactor).mpr
      (by simpa only [Identity.reversed_reversed] using valid)
  exact valid_sameSignature identity.reversed reversedValid

def JointSignature (left right : Word Nat) : Prop :=
  SameSupportParity left right ∧ S5_848.SameTailSquareSignature left.reverse right.reverse

theorem joint_signature_necessary (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Msg0524Parity808FactorEval.factor)
    (rightValid : identity.SatisfiedBy rightFactor) : JointSignature identity.lhs identity.rhs := by
  exact ⟨(Msg0524Parity808FactorCriterion.valid_iff_signature identity).mp leftValid,
    valid_lastSignature identity rightValid⟩

end SemigroupBasis.CoRoots.Order6Sunday.Msg0524Parity808LastNecessary
