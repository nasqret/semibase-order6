import SemigroupBasis.Examples.LeftNormalBandThree
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Multiplication for the zero-based table
`[[1,1,1],[1,2,2],[1,3,3]]`. -/
def leftNormalBandFifteenMul (a b : Fin 3) : Fin 3 :=
  if b = 0 then 0 else a

/-- The exact Smallsemi representative `S3_15`. -/
def leftNormalBandFifteen : FiniteTable where
  order := 3
  mul := leftNormalBandFifteenMul
  assoc := by decide

private theorem leftNormalBandFifteenFold_eq_one_iff
    (valuation : Nat → Fin 3) (xs : List Nat) (acc : Fin 3) :
    xs.foldl
        (fun current x =>
          leftNormalBandFifteenMul current (valuation x)) acc = 1 ↔
      acc = 1 ∧ ∀ x, x ∈ xs → valuation x ≠ 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      by_cases hx : valuation x = 0
      · simp [leftNormalBandFifteenMul, hx]
      · simp [leftNormalBandFifteenMul, hx]

theorem leftNormalBandFifteenEval_eq_one_iff
    (valuation : Nat → Fin 3) (w : Word Nat) :
    leftNormalBandFifteen.semigroup.eval valuation w = (1 : Fin 3) ↔
      valuation w.head = (1 : Fin 3) ∧
        ∀ x, x ∈ w.tail → valuation x ≠ (0 : Fin 3) := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              leftNormalBandFifteenMul current (valuation x))
            (valuation head) = (1 : Fin 3) ↔
          valuation head = (1 : Fin 3) ∧
            ∀ x, x ∈ tail → valuation x ≠ (0 : Fin 3)
      exact leftNormalBandFifteenFold_eq_one_iff valuation tail _

private def leftNormalBandFifteenSupportSeparator
    (z : Nat) : Nat → Fin 3 :=
  fun x => if x = z then 0 else 1

theorem leftNormalBandFifteenSeparator_eq_one_iff
    (z : Nat) (w : Word Nat) :
    leftNormalBandFifteen.semigroup.eval
        (leftNormalBandFifteenSupportSeparator z) w = (1 : Fin 3) ↔
      z ∉ w.toList := by
  rw [leftNormalBandFifteenEval_eq_one_iff]
  constructor
  · rintro ⟨hhead, htail⟩ hz
    rcases List.mem_cons.mp hz with hz | hz
    · subst z
      simp [leftNormalBandFifteenSupportSeparator] at hhead
    · have := htail z hz
      simp [leftNormalBandFifteenSupportSeparator] at this
  · intro hz
    have hhead : w.head ≠ z := by
      intro h
      apply hz
      simpa [Word.toList, h] using List.Mem.head w.tail
    refine ⟨by
      simp [leftNormalBandFifteenSupportSeparator, hhead], ?_⟩
    intro x hx
    have hxz : x ≠ z := by
      intro h
      apply hz
      simpa [h] using List.Mem.tail w.head hx
    simp [leftNormalBandFifteenSupportSeparator, hxz]

theorem leftNormalBandFifteenValid_support_eq
    (e : Identity Nat)
    (valid : e.SatisfiedBy leftNormalBandFifteen.semigroup) :
    ∀ z, z ∈ e.lhs.toList ↔ z ∈ e.rhs.toList := by
  intro z
  have evaluated := valid (leftNormalBandFifteenSupportSeparator z)
  constructor
  · intro hl
    apply Decidable.byContradiction
    intro hr
    have rhsOne :
        leftNormalBandFifteen.semigroup.eval
            (leftNormalBandFifteenSupportSeparator z) e.rhs =
              (1 : Fin 3) :=
      (leftNormalBandFifteenSeparator_eq_one_iff z e.rhs).2 hr
    have lhsNotOne :
        leftNormalBandFifteen.semigroup.eval
            (leftNormalBandFifteenSupportSeparator z) e.lhs ≠
              (1 : Fin 3) := by
      intro lhsOne
      exact (leftNormalBandFifteenSeparator_eq_one_iff z e.lhs).1
        lhsOne hl
    exact lhsNotOne (evaluated.trans rhsOne)
  · intro hr
    apply Decidable.byContradiction
    intro hl
    have lhsOne :
        leftNormalBandFifteen.semigroup.eval
            (leftNormalBandFifteenSupportSeparator z) e.lhs =
              (1 : Fin 3) :=
      (leftNormalBandFifteenSeparator_eq_one_iff z e.lhs).2 hl
    have rhsNotOne :
        leftNormalBandFifteen.semigroup.eval
            (leftNormalBandFifteenSupportSeparator z) e.rhs ≠
              (1 : Fin 3) := by
      intro rhsOne
      exact (leftNormalBandFifteenSeparator_eq_one_iff z e.rhs).1
        rhsOne hr
    exact rhsNotOne (evaluated.symm.trans lhsOne)

private theorem leftNormalBandFifteenFold_of_nonzero
    (valuation : Nat → Fin 3) (xs : List Nat) (acc : Fin 3)
    (hall : ∀ x, x ∈ xs → valuation x ≠ 0) :
    xs.foldl
        (fun current x =>
          leftNormalBandFifteenMul current (valuation x)) acc = acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      rw [List.foldl_cons]
      have hx := hall x (List.Mem.head xs)
      rw [show leftNormalBandFifteenMul acc (valuation x) = acc by
        simp [leftNormalBandFifteenMul, hx]]
      exact ih acc (fun y hy => hall y (List.Mem.tail x hy))

theorem leftNormalBandFifteenEval_of_nonzero
    (valuation : Nat → Fin 3) (w : Word Nat)
    (hall : ∀ x, x ∈ w.toList → valuation x ≠ 0) :
    leftNormalBandFifteen.semigroup.eval valuation w =
      valuation w.head := by
  cases w with
  | mk head tail =>
      exact leftNormalBandFifteenFold_of_nonzero valuation tail
        (valuation head) (fun x hx => hall x (List.Mem.tail head hx))

private def leftNormalBandFifteenHeadSeparator
    (z : Nat) : Nat → Fin 3 :=
  fun x => if x = z then 1 else 2

theorem leftNormalBandFifteenValid_head_eq
    (e : Identity Nat)
    (valid : e.SatisfiedBy leftNormalBandFifteen.semigroup) :
    e.lhs.head = e.rhs.head := by
  apply Decidable.byContradiction
  intro headsNe
  let valuation := leftNormalBandFifteenHeadSeparator e.lhs.head
  have nonzero : ∀ x, valuation x ≠ (0 : Fin 3) := by
    intro x
    by_cases h : x = e.lhs.head <;>
      simp [valuation, leftNormalBandFifteenHeadSeparator, h]
  have evaluated := valid valuation
  rw [leftNormalBandFifteenEval_of_nonzero valuation e.lhs
      (fun x _ => nonzero x),
    leftNormalBandFifteenEval_of_nonzero valuation e.rhs
      (fun x _ => nonzero x)] at evaluated
  have lhsOne : valuation e.lhs.head = (1 : Fin 3) := by
    simp [valuation, leftNormalBandFifteenHeadSeparator]
  have rhsTwo : valuation e.rhs.head = (2 : Fin 3) := by
    simp [valuation, leftNormalBandFifteenHeadSeparator, Ne.symm headsNe]
  rw [lhsOne, rhsTwo] at evaluated
  exact (by decide : (1 : Fin 3) ≠ 2) evaluated

private theorem leftNormalBandFifteenMul_idempotent (a : Fin 3) :
    leftNormalBandFifteenMul a a = a := by
  decide +revert

private theorem leftNormalBandFifteenMul_left_normal
    (a b c : Fin 3) :
    leftNormalBandFifteenMul
        (leftNormalBandFifteenMul a b) c =
      leftNormalBandFifteenMul
        (leftNormalBandFifteenMul a c) b := by
  decide +revert

theorem leftNormalBandFifteenBasis_models :
    Models leftNormalBandFifteen.semigroup leftNormalBandThreeBasis := by
  intro e he
  simp only [leftNormalBandThreeBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change valuation 0 =
      leftNormalBandFifteenMul (valuation 0) (valuation 0)
    exact (leftNormalBandFifteenMul_idempotent (valuation 0)).symm
  · intro valuation
    change
      leftNormalBandFifteenMul
          (leftNormalBandFifteenMul (valuation 0) (valuation 1))
          (valuation 2) =
        leftNormalBandFifteenMul
          (leftNormalBandFifteenMul (valuation 0) (valuation 2))
          (valuation 1)
    exact leftNormalBandFifteenMul_left_normal
      (valuation 0) (valuation 1) (valuation 2)

theorem leftNormalBandFifteenBasis_complete :
    BasisFor leftNormalBandFifteen.semigroup leftNormalBandThreeBasis := by
  refine ⟨leftNormalBandFifteenBasis_models, ?_⟩
  intro e valid
  have heads := leftNormalBandFifteenValid_head_eq e valid
  have supportEq := leftNormalBandFifteenValid_support_eq e valid
  have lhsExpansion :
      Derives leftNormalBandThreeBasis e.lhs (e.lhs ++ e.rhs) :=
    leftNormalBandDerivesContentExpansion e.lhs e.rhs
      (fun x hx => (supportEq x).2 hx)
  have rhsExpansion :
      Derives leftNormalBandThreeBasis e.rhs (e.rhs ++ e.lhs) :=
    leftNormalBandDerivesContentExpansion e.rhs e.lhs
      (fun x hx => (supportEq x).1 hx)
  exact Derives.trans lhsExpansion <|
    Derives.trans
      (leftNormalBandDerivesConcatSwap e.lhs e.rhs heads)
      (Derives.symm rhsExpansion)

theorem leftNormalBandFifteenOppositeBasis_complete :
    BasisFor leftNormalBandFifteen.semigroup.opposite
      (reversedBasis leftNormalBandThreeBasis) :=
  leftNormalBandFifteenBasis_complete.oppositeReversed

end SemigroupBasis.Examples
