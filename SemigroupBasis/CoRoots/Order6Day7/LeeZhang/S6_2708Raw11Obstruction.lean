import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708Raw11Presentation
import SemigroupBasis.NonlinearBasisObstruction
import SemigroupBasis.Order6.FactorPairJoin

/-!
# Unrestricted formal obstruction for the stopped S6_2708 raw11

This is a new exact-class formalization of the accepted finite counterexample,
not a repeat of the old raw248 screen. The generic nonlinear engine and the
explicit factorial-abcd model are reused unchanged. The sigma12 statement
is defined for fable review only; no positive completeness proof is begun.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708

open SemigroupBasis

theorem displayedBasis_nonlinear : AllSidesNonlinear basis := by
  unfold AllSidesNonlinear
  decide

theorem reversedBasis_nonlinear : AllSidesNonlinear (reversedBasis basis) := by
  unfold AllSidesNonlinear
  decide

theorem derives_squareFree_rigid {left right : Word Nat} (derivation : Derives basis left right) :
    (left.toList.Nodup → left = right) ∧ (right.toList.Nodup → left = right) :=
  derivation.squareFree_rigid_of_allSidesNonlinear displayedBasis_nonlinear

theorem missingPrefixSwap_not_derivable :
    ¬ Derives basis missingPrefixSwap.lhs missingPrefixSwap.rhs :=
  not_derivable_of_nonlinear_basis displayedBasis_nonlinear (by decide) (by decide)

/-- Independent semantic proof from the already formalized explicit model. -/
theorem missingPrefixSwap_not_derivable_by_countermodel :
    ¬ Derives basis missingPrefixSwap.lhs missingPrefixSwap.rhs := by
  intro derivation
  exact DualC4Raw6.Countermodel.missingPrefixSwap_fails
    (Derives.sound countermodel_models_raw derivation DualC4Raw6.Countermodel.valuation)

theorem reversed_missingPrefixSwap_not_derivable :
    ¬ Derives (reversedBasis basis) missingPrefixSwap.reversed.lhs missingPrefixSwap.reversed.rhs :=
  not_derivable_of_nonlinear_basis reversedBasis_nonlinear (by decide) (by decide)

theorem raw_basis_isFalse : ¬ BasisFor table.semigroup basis := by
  intro complete
  exact missingPrefixSwap_not_derivable (complete.2 missingPrefixSwap missingPrefixSwap_valid)

theorem opposite_raw_basis_isFalse : ¬ BasisFor table.semigroup.opposite (reversedBasis basis) := by
  intro complete
  have valid : missingPrefixSwap.reversed.SatisfiedBy table.semigroup.opposite := by
    apply (Identity.satisfiedBy_opposite_iff_reversed missingPrefixSwap.reversed table.semigroup).2
    simpa using missingPrefixSwap_valid
  exact reversed_missingPrefixSwap_not_derivable (complete.2 missingPrefixSwap.reversed valid)

/-- Diagonal on the actual table twice; no factorization is asserted. -/
theorem raw_normalizer_isFalse :
    ¬ Nonempty (IntersectionNormalizer table.semigroup table.semigroup basis) := by
  rintro ⟨normalizer⟩
  have intersection := normalizer.toIntersectionBasis models_raw models_raw
  exact missingPrefixSwap_not_derivable
    (intersection.complete missingPrefixSwap missingPrefixSwap_valid missingPrefixSwap_valid)

/-- Exact candidate statement for fable review ONLY, not a theorem. -/
def ProposedSigma12Completeness : Prop :=
  ∀ identity : Identity Nat, identity.SatisfiedBy table.semigroup →
    Derives sigma12 identity.lhs identity.rhs

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.S6_2708
