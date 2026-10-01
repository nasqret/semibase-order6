import SemigroupBasis.CoRoots.Order6Sunday.Msg0534Parity808BarrierValidity
import SemigroupBasis.TransferPower

/-! The literal 11237/11389 tables share the established Parity808 basis.
The unrestricted bridge uses a separating pair of genuine homomorphisms,
an actual S4_71 embedding, and a right-zero probe. No finite screen is a
theorem premise. False selects 11237; true selects 11389. -/
namespace SemigroupBasis.CoRoots.Order6Sunday.Msg0534SingletonParityCompleteness

open SemigroupBasis
open Msg0524Parity808Gather (basis law0 law1 law2)

private def row (v0 v1 v2 v3 v4 v5 : Fin 6) (b : Fin 6) : Fin 6 :=
  if b = 0 then v0 else if b = 1 then v1 else if b = 2 then v2
  else if b = 3 then v3 else if b = 4 then v4 else v5

def mul (variant : Bool) (a b : Fin 6) : Fin 6 :=
  if variant then
    if a = 0 then row 0 0 0 0 0 0 b
    else if a = 1 then row 0 0 1 1 0 0 b
    else if a = 2 then row 0 1 2 3 4 5 b
    else if a = 3 then row 0 1 3 2 4 5 b
    else row 0 1 4 4 4 5 b
  else
    if a = 0 then row 0 0 0 0 0 0 b
    else if a = 1 then row 0 0 0 0 1 1 b
    else if a = 2 then row 0 1 2 3 2 2 b
    else if a = 3 then row 0 1 3 2 3 3 b
    else row 0 1 2 3 4 5 b

theorem associative : ∀ variant a b c, mul variant (mul variant a b) c =
    mul variant a (mul variant b c) := by decide

def table (variant : Bool) : FiniteTable where
  order := 6
  mul := mul variant
  assoc := associative variant

def parityMap (a : Fin 3) : Fin 6 := if a = 1 then 3 else 2
def supportMap (a : Fin 3) : Fin 6 := if a = 2 then 2 else 0

def parityHom (variant : Bool) : Hom Msg0524Parity808FactorEval.factor (table variant).semigroup where
  toFun := parityMap
  map_mul := by intro a b; revert a b; cases variant <;> decide

def supportHom (variant : Bool) : Hom Msg0524Parity808FactorEval.factor (table variant).semigroup where
  toFun := supportMap
  map_mul := by intro a b; revert a b; cases variant <;> decide

theorem maps_separate : ∀ a b : Fin 3,
    parityMap a = parityMap b → supportMap a = supportMap b → a = b := by decide

def factorEmbedding (variant : Bool) :
    Embedding Msg0524Parity808FactorEval.factor ((table variant).semigroup.pi Bool) :=
  Embedding.ofSeparatingHoms
    (fun coordinate : Bool => if coordinate then supportHom variant else parityHom variant)
    (by
      intro a b equal
      exact maps_separate a b (equal false) (equal true))

def blockMap (variant : Bool) (a : Fin 4) : Fin 6 :=
  if a = 0 then 0 else if a = 1 then 1
  else if a = 2 then (if variant then 4 else 2)
  else (if variant then 2 else 4)

def blockEmbedding (variant : Bool) :
    Embedding Generated.S4_71.table.semigroup (table variant).semigroup where
  toFun := blockMap variant
  map_mul := by intro a b; revert a b; cases variant <;> decide
  injective := by intro a b; revert a b; cases variant <;> decide

theorem opposite_marker_mul : ∀ variant a b,
    (a = (4 : Fin 6) ∨ a = 5) → (b = (4 : Fin 6) ∨ b = 5) →
    (table variant).semigroup.opposite.mul a b = a := by decide

theorem opposite_marker_fold (variant : Bool) (valuation : α → Fin 6)
    (xs : List α) (initial : Fin 6) (initialMarker : initial = 4 ∨ initial = 5)
    (markers : ∀ x ∈ xs, valuation x = 4 ∨ valuation x = 5) :
    xs.foldl (fun a x => (table variant).semigroup.opposite.mul a (valuation x)) initial = initial := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, opposite_marker_mul variant initial (valuation x)
      initialMarker (markers x (List.mem_cons_self))]
    exact ih (fun y hy => markers y (List.mem_cons_of_mem x hy))

def markerProbe (letter x : Nat) : Fin 6 := if x = letter then 4 else 5

theorem markerProbe_range (letter x : Nat) : markerProbe letter x = 4 ∨ markerProbe letter x = 5 := by
  by_cases same : x = letter <;> simp [markerProbe, same]

theorem opposite_marker_eval (variant : Bool) (letter : Nat) (word : Word Nat) :
    (table variant).semigroup.opposite.eval (markerProbe letter) word = markerProbe letter word.head :=
  opposite_marker_fold variant (markerProbe letter) word.tail (markerProbe letter word.head)
    (markerProbe_range letter word.head) (fun x _ => markerProbe_range letter x)

theorem valid_reverse_head (variant : Bool) (identity : Identity Nat)
    (valid : identity.SatisfiedBy (table variant).semigroup) :
    identity.reversed.lhs.head = identity.reversed.rhs.head := by
  have reverseValid : identity.reversed.SatisfiedBy (table variant).semigroup.opposite :=
    (Identity.satisfiedBy_opposite_iff_reversed identity.reversed (table variant).semigroup).mpr
      (by simpa only [Identity.reversed_reversed] using valid)
  by_cases same : identity.reversed.lhs.head = identity.reversed.rhs.head
  · exact same
  · have observed := reverseValid (markerProbe identity.reversed.lhs.head)
    rw [opposite_marker_eval, opposite_marker_eval] at observed
    simp [markerProbe, Ne.symm same] at observed

theorem factor_valid (variant : Bool) (identity : Identity Nat)
    (valid : identity.SatisfiedBy (table variant).semigroup) :
    identity.SatisfiedBy Msg0524Parity808FactorEval.factor :=
  (factorEmbedding variant).pullback_identity identity
    (identity.satisfiedByPi (table variant).semigroup Bool valid)

theorem joint_signature (variant : Bool) (identity : Identity Nat)
    (valid : identity.SatisfiedBy (table variant).semigroup) :
    Msg0524Parity808LastNecessary.JointSignature identity.lhs identity.rhs := by
  have blockValid := (blockEmbedding variant).pullback_identity identity valid
  have reverseBlock : identity.reversed.SatisfiedBy Generated.S4_71.table.semigroup.opposite :=
    (Identity.satisfiedBy_opposite_iff_reversed identity.reversed Generated.S4_71.table.semigroup).mpr
      (by simpa only [Identity.reversed_reversed] using blockValid)
  exact ⟨(Msg0524Parity808FactorCriterion.valid_iff_signature identity).mp
    (factor_valid variant identity valid),
    S5_848.sameSignature_of_block_valid_head_eq identity.reversed reverseBlock
      (valid_reverse_head variant identity valid)⟩

theorem power_law : ∀ variant x, mul variant x x =
    mul variant (mul variant (mul variant x x) x) x := by decide

theorem tail_square_law : ∀ variant x y z,
    mul variant (mul variant (mul variant (mul variant x x) y) y) z =
      mul variant (mul variant (mul variant (mul variant x y) y) x) z := by decide

theorem gather_law : ∀ variant x y, mul variant (mul variant x y) x =
    mul variant (mul variant y x) x := by decide

theorem models (variant : Bool) : Models (table variant).semigroup basis := by
  intro identity member
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · intro valuation
    exact power_law variant (valuation 0)
  · intro valuation
    exact tail_square_law variant (valuation 0) (valuation 1) (valuation 2)
  · intro valuation
    exact gather_law variant (valuation 0) (valuation 1)

theorem representative_basis (variant : Bool) : BasisFor (table variant).semigroup basis := by
  refine ⟨models variant, ?_⟩
  intro identity valid
  exact Msg0534Parity808BarrierValidity.joint_complete (joint_signature variant identity valid)

namespace S6_11237
abbrev table := Msg0534SingletonParityCompleteness.table false
theorem representative_basis : BasisFor table.semigroup basis :=
  Msg0534SingletonParityCompleteness.representative_basis false
theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed
end S6_11237

namespace S6_11389
abbrev table := Msg0534SingletonParityCompleteness.table true
theorem representative_basis : BasisFor table.semigroup basis :=
  Msg0534SingletonParityCompleteness.representative_basis true
theorem opposite_basis : BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed
end S6_11389

end SemigroupBasis.CoRoots.Order6Sunday.Msg0534SingletonParityCompleteness
