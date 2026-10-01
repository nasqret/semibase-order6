import SemigroupBasis.Examples.NormalBandFourSyntax
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- Exact zero-based multiplication for the catalogue table
`[[1,1,1,1],[1,2,1,4],[3,3,3,3],[1,2,1,4]]`. -/
def normalBandFourMul (a b : Fin 4) : Fin 4 :=
  if a = 0 then 0 else
    if a = 2 then 2 else
      if b = 0 then 0 else if b = 2 then 0 else b

/-- The root catalogue representative `S4_110`. -/
def normalBandFour : FiniteTable where
  order := 4
  mul := normalBandFourMul
  assoc := by decide

private theorem normalBandFourMul_idempotent (a : Fin 4) :
    normalBandFourMul a a = a := by
  decide +revert

private theorem normalBandFourMul_normal
    (a b c : Fin 4) :
    normalBandFourMul
        (normalBandFourMul
          (normalBandFourMul a b) c) a =
      normalBandFourMul
        (normalBandFourMul
          (normalBandFourMul a c) b) a := by
  decide +revert

theorem normalBandFourBasis_models :
    Models normalBandFour.semigroup normalBandBasis := by
  intro e he
  simp only [normalBandBasis, List.mem_cons,
    List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · intro valuation
    change
      valuation 0 =
        normalBandFourMul (valuation 0) (valuation 0)
    exact (normalBandFourMul_idempotent (valuation 0)).symm
  · intro valuation
    change
      normalBandFourMul
          (normalBandFourMul
            (normalBandFourMul (valuation 0) (valuation 1))
            (valuation 2))
          (valuation 0) =
        normalBandFourMul
          (normalBandFourMul
            (normalBandFourMul (valuation 0) (valuation 2))
            (valuation 1))
          (valuation 0)
    exact normalBandFourMul_normal
      (valuation 0) (valuation 1) (valuation 2)

private theorem normalBandFourFold_from_zero
    (valuation : Nat → Fin 4) (xs : List Nat) :
    xs.foldl
        (fun current x =>
          normalBandFourMul current (valuation x))
        (0 : Fin 4) = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simpa [List.foldl_cons, normalBandFourMul] using ih

private theorem normalBandFourFold_from_two
    (valuation : Nat → Fin 4) (xs : List Nat) :
    xs.foldl
        (fun current x =>
          normalBandFourMul current (valuation x))
        (2 : Fin 4) = 2 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simpa [List.foldl_cons, normalBandFourMul] using ih

private def normalBandSupportSeparator
    (tested : Nat) : Nat → Fin 4 :=
  fun x => if x = tested then 0 else 3

theorem normalBandSupportSeparator_eval_iff
    (tested : Nat) :
    ∀ w : Word Nat,
      normalBandFour.semigroup.eval
          (normalBandSupportSeparator tested) w = (3 : Fin 4) ↔
        tested ∉ w.toList
  | ⟨head, []⟩ => by
      simp [Semigroup.eval, Word.toList,
        normalBandSupportSeparator, eq_comm]
  | ⟨head, next :: rest⟩ => by
      by_cases hhead : head = tested
      · subst head
        change
          rest.foldl
              (fun current x =>
                normalBandFourMul current
                  (normalBandSupportSeparator tested x))
              (normalBandFourMul
                (normalBandSupportSeparator tested tested)
                (normalBandSupportSeparator tested next)) = 3 ↔
            tested ∉ tested :: next :: rest
        rw [show normalBandSupportSeparator tested tested =
            (0 : Fin 4) by
          simp [normalBandSupportSeparator]]
        rw [show normalBandFourMul 0
            (normalBandSupportSeparator tested next) = (0 : Fin 4) by
          simp [normalBandFourMul]]
        rw [normalBandFourFold_from_zero]
        simp
      · have firstStep :
            normalBandFourMul
                (normalBandSupportSeparator tested head)
                (normalBandSupportSeparator tested next) =
              normalBandSupportSeparator tested next := by
          by_cases hnext : next = tested <;>
            simp [normalBandSupportSeparator, normalBandFourMul,
              hhead, hnext]
        change
          rest.foldl
              (fun current x =>
                normalBandFourMul current
                  (normalBandSupportSeparator tested x))
              (normalBandFourMul
                (normalBandSupportSeparator tested head)
                (normalBandSupportSeparator tested next)) = 3 ↔
            tested ∉ head :: next :: rest
        rw [firstStep]
        change
          normalBandFour.semigroup.eval
              (normalBandSupportSeparator tested)
              (Word.mk next rest) = (3 : Fin 4) ↔
            tested ∉ head :: next :: rest
        rw [normalBandSupportSeparator_eval_iff tested
          (Word.mk next rest)]
        simp [Word.toList, Ne.symm hhead]

theorem normalBandValid_support_eq
    (e : Identity Nat)
    (valid : e.SatisfiedBy normalBandFour.semigroup) :
    ∀ tested, tested ∈ e.lhs.toList ↔ tested ∈ e.rhs.toList := by
  intro tested
  have evaluated := valid (normalBandSupportSeparator tested)
  constructor
  · intro lhsMem
    apply Decidable.byContradiction
    intro rhsNotMem
    have rhsThree :
        normalBandFour.semigroup.eval
            (normalBandSupportSeparator tested) e.rhs =
          (3 : Fin 4) :=
      (normalBandSupportSeparator_eval_iff tested e.rhs).2
        rhsNotMem
    have lhsNotThree :
        normalBandFour.semigroup.eval
            (normalBandSupportSeparator tested) e.lhs ≠
          (3 : Fin 4) := by
      intro lhsThree
      exact
        (normalBandSupportSeparator_eval_iff tested e.lhs).1
          lhsThree lhsMem
    exact lhsNotThree (evaluated.trans rhsThree)
  · intro rhsMem
    apply Decidable.byContradiction
    intro lhsNotMem
    have lhsThree :
        normalBandFour.semigroup.eval
            (normalBandSupportSeparator tested) e.lhs =
          (3 : Fin 4) :=
      (normalBandSupportSeparator_eval_iff tested e.lhs).2
        lhsNotMem
    have rhsNotThree :
        normalBandFour.semigroup.eval
            (normalBandSupportSeparator tested) e.rhs ≠
          (3 : Fin 4) := by
      intro rhsThree
      exact
        (normalBandSupportSeparator_eval_iff tested e.rhs).1
          rhsThree rhsMem
    exact rhsNotThree (evaluated.symm.trans lhsThree)

private def normalBandHeadSeparator
    (tested : Nat) : Nat → Fin 4 :=
  fun x => if x = tested then 2 else 0

theorem normalBandHeadSeparator_eval
    (tested : Nat) (w : Word Nat) :
    normalBandFour.semigroup.eval
        (normalBandHeadSeparator tested) w =
      normalBandHeadSeparator tested w.head := by
  cases w with
  | mk head tail =>
      change
        tail.foldl
            (fun current x =>
              normalBandFourMul current
                (normalBandHeadSeparator tested x))
            (normalBandHeadSeparator tested head) =
          normalBandHeadSeparator tested head
      by_cases hhead : head = tested
      · rw [show normalBandHeadSeparator tested head =
            (2 : Fin 4) by
          simp [normalBandHeadSeparator, hhead]]
        exact normalBandFourFold_from_two _ tail
      · rw [show normalBandHeadSeparator tested head =
            (0 : Fin 4) by
          simp [normalBandHeadSeparator, hhead]]
        exact normalBandFourFold_from_zero _ tail

theorem normalBandValid_head_eq
    (e : Identity Nat)
    (valid : e.SatisfiedBy normalBandFour.semigroup) :
    e.lhs.head = e.rhs.head := by
  apply Decidable.byContradiction
  intro headsNe
  have evaluated := valid (normalBandHeadSeparator e.lhs.head)
  rw [normalBandHeadSeparator_eval,
    normalBandHeadSeparator_eval] at evaluated
  have lhsTwo :
      normalBandHeadSeparator e.lhs.head e.lhs.head =
        (2 : Fin 4) := by
    simp [normalBandHeadSeparator]
  have rhsZero :
      normalBandHeadSeparator e.lhs.head e.rhs.head =
        (0 : Fin 4) := by
    simp [normalBandHeadSeparator, Ne.symm headsNe]
  rw [lhsTwo, rhsZero] at evaluated
  exact (by decide : (2 : Fin 4) ≠ 0) evaluated

private def normalBandFinalSeparator
    (tested : Nat) : Nat → Fin 4 :=
  fun x => if x = tested then 3 else 1

private theorem normalBandFinalSeparator_mul
    (tested x y : Nat) :
    normalBandFourMul
        (normalBandFinalSeparator tested x)
        (normalBandFinalSeparator tested y) =
      normalBandFinalSeparator tested y := by
  by_cases hx : x = tested <;>
    by_cases hy : y = tested <;>
      simp [normalBandFinalSeparator, normalBandFourMul, hx, hy]

theorem normalBandFinalSeparator_eval
    (tested : Nat) :
    ∀ w : Word Nat,
      normalBandFour.semigroup.eval
          (normalBandFinalSeparator tested) w =
        normalBandFinalSeparator tested
          (w.tail.getLastD w.head)
  | ⟨head, []⟩ => rfl
  | ⟨head, next :: rest⟩ => by
      change
        rest.foldl
            (fun current x =>
              normalBandFourMul current
                (normalBandFinalSeparator tested x))
            (normalBandFourMul
              (normalBandFinalSeparator tested head)
              (normalBandFinalSeparator tested next)) =
          normalBandFinalSeparator tested
            ((next :: rest).getLastD head)
      rw [normalBandFinalSeparator_mul]
      rw [List.getLastD_cons]
      change
        normalBandFour.semigroup.eval
            (normalBandFinalSeparator tested)
            (Word.mk next rest) =
          normalBandFinalSeparator tested
            (rest.getLastD next)
      exact normalBandFinalSeparator_eval tested (Word.mk next rest)

theorem normalBandValid_final_eq
    (e : Identity Nat)
    (valid : e.SatisfiedBy normalBandFour.semigroup) :
    e.lhs.tail.getLastD e.lhs.head =
      e.rhs.tail.getLastD e.rhs.head := by
  apply Decidable.byContradiction
  intro finalsNe
  let lhsFinal := e.lhs.tail.getLastD e.lhs.head
  have evaluated := valid (normalBandFinalSeparator lhsFinal)
  rw [normalBandFinalSeparator_eval,
    normalBandFinalSeparator_eval] at evaluated
  have lhsThree :
      normalBandFinalSeparator lhsFinal
          (e.lhs.tail.getLastD e.lhs.head) = (3 : Fin 4) := by
    simp [lhsFinal, normalBandFinalSeparator]
  have rhsOne :
      normalBandFinalSeparator lhsFinal
          (e.rhs.tail.getLastD e.rhs.head) = (1 : Fin 4) := by
    have rhsNe :
        e.rhs.tail.getLastD e.rhs.head ≠ lhsFinal := by
      simpa [lhsFinal] using Ne.symm finalsNe
    simp only [normalBandFinalSeparator, if_neg rhsNe]
  rw [lhsThree, rhsOne] at evaluated
  exact (by decide : (3 : Fin 4) ≠ 1) evaluated

/-- Unrestricted completeness over `Nat` variables. Valid identities preserve
exactly support, first variable, and final variable, and the syntactic
normal-band theorem derives every identity with those three invariants. -/
theorem normalBandFourBasis_complete :
    BasisFor normalBandFour.semigroup normalBandBasis := by
  refine ⟨normalBandFourBasis_models, ?_⟩
  intro e valid
  exact normalBandDerivesSameSignature e.lhs e.rhs
    (normalBandValid_head_eq e valid)
    (normalBandValid_final_eq e valid)
    (normalBandValid_support_eq e valid)

def normalBandFourOppositeBasis : List (Identity Nat) :=
  reversedBasis normalBandBasis

theorem normalBandFourOppositeBasis_complete :
    BasisFor normalBandFour.semigroup.opposite
      normalBandFourOppositeBasis := by
  simpa [normalBandFourOppositeBasis] using
    normalBandFourBasis_complete.oppositeReversed

end SemigroupBasis.Examples
