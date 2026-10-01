import SemigroupBasis.CoRoots.Order6SporadicSection18ActualModel
import SemigroupBasis.CoRoots.Order6SporadicSection18ReductionInterface

/-! The actual C7 hypotheses for the finite-support B0 separator reduction.
All finite facts are kernel-decided on the published table, not assumed from
the older S6_5625 specialization. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6SporadicSection12

def b0Embedding :
    Embedding uniqueSeparatorFour.semigroup Actual.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 6) else
    if a = 1 then (2 : Fin 6) else
    if a = 2 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide
  injective := by
    intro a b
    revert a b
    decide

theorem valid_b0 (identity : Identity Nat)
    (valid : identity.SatisfiedBy Actual.table.semigroup) :
    identity.SatisfiedBy uniqueSeparatorFour.semigroup :=
  b0Embedding.pullback_identity identity valid

theorem idempotentSeparable : IdempotentSeparable Actual.table := by
  intro x y different
  revert x y
  decide

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.b0Embedding
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.valid_b0
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.idempotentSeparable

end SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction
