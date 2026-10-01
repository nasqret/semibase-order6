import SemigroupBasis.Examples.RectangularBandFourSyntax
import SemigroupBasis.Generated.CatalogueOrder4
import SemigroupBasis.Opposite

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- The exact catalogue table `S4_123`,
`[[1,1,3,3],[2,2,4,4],[1,1,3,3],[2,2,4,4]]`. -/
abbrev rectangularBandFour : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S4_123.table

private theorem rectangularBandFourMul_idempotent (a : Fin 4) :
    SemigroupBasis.Generated.Catalogue.S4_123.mul a a = a := by
  revert a
  decide

private theorem rectangularBandFourMul_sandwich
    (a b : Fin 4) :
    SemigroupBasis.Generated.Catalogue.S4_123.mul
        (SemigroupBasis.Generated.Catalogue.S4_123.mul a b) a =
      a := by
  revert a b
  decide

private theorem rectangularBandFourMul_drop_middle
    (a b c : Fin 4) :
    SemigroupBasis.Generated.Catalogue.S4_123.mul
        (SemigroupBasis.Generated.Catalogue.S4_123.mul a b) c =
      SemigroupBasis.Generated.Catalogue.S4_123.mul a c := by
  revert a b c
  decide

theorem rectangularBandFourBasis_models :
    Models rectangularBandFour.semigroup rectangularBandBasis := by
  intro identity member
  simp only [rectangularBandBasis, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · intro valuation
    change
      valuation 0 =
        SemigroupBasis.Generated.Catalogue.S4_123.mul
          (valuation 0) (valuation 0)
    exact (rectangularBandFourMul_idempotent (valuation 0)).symm
  · intro valuation
    change
      valuation 0 =
        SemigroupBasis.Generated.Catalogue.S4_123.mul
          (SemigroupBasis.Generated.Catalogue.S4_123.mul
            (valuation 0) (valuation 1))
          (valuation 0)
    exact
      (rectangularBandFourMul_sandwich
        (valuation 0) (valuation 1)).symm

private theorem rectangularBandFourFold_last
    (valuation : Nat → Fin 4) (initial : Fin 4) :
    ∀ (next : Nat) (rest : List Nat),
      rest.foldl
          (fun current letter =>
            SemigroupBasis.Generated.Catalogue.S4_123.mul
              current (valuation letter))
          (SemigroupBasis.Generated.Catalogue.S4_123.mul
            initial (valuation next)) =
        SemigroupBasis.Generated.Catalogue.S4_123.mul
          initial (valuation (rest.getLastD next))
  | next, [] => rfl
  | next, letter :: rest => by
      change
        rest.foldl
            (fun current z =>
              SemigroupBasis.Generated.Catalogue.S4_123.mul
                current (valuation z))
            (SemigroupBasis.Generated.Catalogue.S4_123.mul
              (SemigroupBasis.Generated.Catalogue.S4_123.mul
                initial (valuation next))
              (valuation letter)) =
          SemigroupBasis.Generated.Catalogue.S4_123.mul
            initial
            (valuation ((letter :: rest).getLastD next))
      rw [rectangularBandFourMul_drop_middle, List.getLastD_cons]
      exact rectangularBandFourFold_last valuation initial letter rest

/-- Evaluation in the exact catalogue table depends only on the ordered first
and last variables. -/
theorem rectangularBandFourEval_endpoints
    (valuation : Nat → Fin 4) :
    ∀ word : Word Nat,
      rectangularBandFour.semigroup.eval valuation word =
        SemigroupBasis.Generated.Catalogue.S4_123.mul
          (valuation word.head)
          (valuation (rectangularBandFinal word))
  | ⟨head, []⟩ => by
      change
        valuation head =
          SemigroupBasis.Generated.Catalogue.S4_123.mul
            (valuation head) (valuation head)
      exact (rectangularBandFourMul_idempotent (valuation head)).symm
  | ⟨head, next :: rest⟩ => by
      change
        rest.foldl
            (fun current letter =>
              SemigroupBasis.Generated.Catalogue.S4_123.mul
                current (valuation letter))
            (SemigroupBasis.Generated.Catalogue.S4_123.mul
              (valuation head) (valuation next)) =
          SemigroupBasis.Generated.Catalogue.S4_123.mul
            (valuation head)
            (valuation ((next :: rest).getLastD head))
      rw [List.getLastD_cons]
      exact
        rectangularBandFourFold_last
          valuation (valuation head) next rest

private def rectangularBandHeadSeparator
    (tested : Nat) : Nat → Fin 4 :=
  fun letter => if letter = tested then 1 else 0

private theorem rectangularBandHeadSeparator_mul
    (tested left right : Nat) :
    SemigroupBasis.Generated.Catalogue.S4_123.mul
        (rectangularBandHeadSeparator tested left)
        (rectangularBandHeadSeparator tested right) =
      rectangularBandHeadSeparator tested left := by
  by_cases hleft : left = tested <;>
    by_cases hright : right = tested <;>
      simp [rectangularBandHeadSeparator, hleft, hright,
        SemigroupBasis.Generated.Catalogue.S4_123.mul] <;>
      decide

theorem rectangularBandHeadSeparator_eval
    (tested : Nat) (word : Word Nat) :
    rectangularBandFour.semigroup.eval
        (rectangularBandHeadSeparator tested) word =
      rectangularBandHeadSeparator tested word.head := by
  rw [rectangularBandFourEval_endpoints]
  exact rectangularBandHeadSeparator_mul
    tested word.head (rectangularBandFinal word)

theorem rectangularBandFourValid_head_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rectangularBandFour.semigroup) :
    identity.lhs.head = identity.rhs.head := by
  apply Decidable.byContradiction
  intro headsNe
  have evaluated :=
    valid (rectangularBandHeadSeparator identity.lhs.head)
  rw [rectangularBandHeadSeparator_eval,
    rectangularBandHeadSeparator_eval] at evaluated
  simp [rectangularBandHeadSeparator, Ne.symm headsNe] at evaluated

private def rectangularBandFinalSeparator
    (tested : Nat) : Nat → Fin 4 :=
  fun letter => if letter = tested then 2 else 0

private theorem rectangularBandFinalSeparator_mul
    (tested left right : Nat) :
    SemigroupBasis.Generated.Catalogue.S4_123.mul
        (rectangularBandFinalSeparator tested left)
        (rectangularBandFinalSeparator tested right) =
      rectangularBandFinalSeparator tested right := by
  by_cases hleft : left = tested <;>
    by_cases hright : right = tested <;>
      simp [rectangularBandFinalSeparator, hleft, hright,
        SemigroupBasis.Generated.Catalogue.S4_123.mul] <;>
      decide

theorem rectangularBandFinalSeparator_eval
    (tested : Nat) (word : Word Nat) :
    rectangularBandFour.semigroup.eval
        (rectangularBandFinalSeparator tested) word =
      rectangularBandFinalSeparator tested
        (rectangularBandFinal word) := by
  rw [rectangularBandFourEval_endpoints]
  exact rectangularBandFinalSeparator_mul
    tested word.head (rectangularBandFinal word)

theorem rectangularBandFourValid_final_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rectangularBandFour.semigroup) :
    rectangularBandFinal identity.lhs =
      rectangularBandFinal identity.rhs := by
  apply Decidable.byContradiction
  intro finalsNe
  have evaluated :=
    valid (rectangularBandFinalSeparator
      (rectangularBandFinal identity.lhs))
  rw [rectangularBandFinalSeparator_eval,
    rectangularBandFinalSeparator_eval] at evaluated
  simp [rectangularBandFinalSeparator, Ne.symm finalsNe] at evaluated

/-- The exact `2 x 2` rectangular-band table separates every ordered
first/last pair. -/
theorem rectangularBandFourValid_endpoints_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rectangularBandFour.semigroup) :
    identity.lhs.head = identity.rhs.head ∧
      rectangularBandFinal identity.lhs =
        rectangularBandFinal identity.rhs :=
  ⟨rectangularBandFourValid_head_eq identity valid,
    rectangularBandFourValid_final_eq identity valid⟩

/-- Unrestricted completeness over `Nat` variables for the exact catalogue
table. -/
theorem rectangularBandFourBasis_complete :
    BasisFor rectangularBandFour.semigroup rectangularBandBasis := by
  refine ⟨rectangularBandFourBasis_models, ?_⟩
  intro identity valid
  have endpoints :=
    rectangularBandFourValid_endpoints_eq identity valid
  exact rectangularBandDerivesSameEndpoints
    identity.lhs identity.rhs endpoints.1 endpoints.2

theorem rectangularBandReversedBasis_eq :
    reversedBasis rectangularBandBasis = rectangularBandBasis := by
  decide

theorem rectangularBandFourOppositeBasis_complete :
    BasisFor rectangularBandFour.semigroup.opposite
      rectangularBandBasis := by
  have opposite := rectangularBandFourBasis_complete.oppositeReversed
  rw [rectangularBandReversedBasis_eq] at opposite
  exact opposite

end SemigroupBasis.Examples
