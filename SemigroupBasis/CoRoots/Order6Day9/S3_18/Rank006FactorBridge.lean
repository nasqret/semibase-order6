import SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SquaredReplay

/-!
# Rank006: the C3 and zero-adjoined-C3 routes have exactly the same joint theory

S4_69 already separates support. Therefore replacing C3 by S4_124 adds no
new constraint to the intersection: S4_124 records precisely support and
multiplicity modulo three. This unrestricted semantic bridge lets the
same eventual Sigma+ owner proof serve codex-0's S6_14914 route. No class
table, finite map, endpoint, or completeness proof is asserted here.
-/

namespace SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006FactorBridge

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SigmaPlus
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Semantics
open SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006SquaredReplay

abbrev expandedLeft : FiniteTable := Generated.Catalogue.S4_124.table

theorem expandedLeft_eq_positiveModThree : expandedLeft = commutativePositiveModThreeFour := by
  unfold expandedLeft Generated.Catalogue.S4_124.table commutativePositiveModThreeFour
  rw [FiniteTable.mk.injEq]
  refine ⟨rfl, heq_of_eq ?_⟩
  funext first second
  decide +revert

theorem expandedLeftValid_iff_support_mod (identity : Identity Nat) :
    identity.SatisfiedBy expandedLeft.semigroup ↔
      (∀ letter, letter ∈ identity.lhs.toList ↔ letter ∈ identity.rhs.toList) ∧
      (∀ letter, identity.lhs.toList.count letter % 3 = identity.rhs.toList.count letter % 3) := by
  rw [expandedLeft_eq_positiveModThree]
  constructor
  · intro valid
    exact ⟨positiveModThreeValid_support identity valid,
      positiveModThreeValid_count_mod_three identity valid⟩
  · rintro ⟨support, residues⟩
    exact (positiveDerivesOfSupportMod identity.lhs identity.rhs support residues).sound
      commutativePositiveModThreeFourBasis_models

/-- Equality of the two ACTUAL factor theories, not of bounded term tables. -/
theorem factor_theory_iff (identity : Identity Nat) :
    (identity.SatisfiedBy leftTable.semigroup ∧ identity.SatisfiedBy rightTable.semigroup) ↔
      (identity.SatisfiedBy expandedLeft.semigroup ∧ identity.SatisfiedBy rightTable.semigroup) := by
  constructor
  · rintro ⟨leftValid, rightValid⟩
    exact ⟨(expandedLeftValid_iff_support_mod identity).mpr
      ⟨rightValid_support identity rightValid, (leftValid_iff_mod_eq identity).mp leftValid⟩,
      rightValid⟩
  · rintro ⟨expandedValid, rightValid⟩
    exact ⟨(leftValid_iff_mod_eq identity).mpr
      ((expandedLeftValid_iff_support_mod identity).mp expandedValid).2, rightValid⟩

theorem expandedLeft_models : Models expandedLeft.semigroup sigmaPlus := by
  intro identity member
  exact ((factor_theory_iff identity).mp
    ⟨modelsLeft identity member, modelsRight identity member⟩).1

/-- Exact equivalence of the two outstanding unrestricted obligations. -/
theorem complete_iff_expanded : Complete ↔
    ∀ identity : Identity Nat,
      identity.SatisfiedBy expandedLeft.semigroup →
      identity.SatisfiedBy rightTable.semigroup →
      Derives sigmaPlus identity.lhs identity.rhs := by
  constructor
  · intro complete identity expandedValid rightValid
    have valid := (factor_theory_iff identity).mpr ⟨expandedValid, rightValid⟩
    exact complete identity valid.1 valid.2
  · intro expandedComplete identity leftValid rightValid
    have valid := (factor_theory_iff identity).mp ⟨leftValid, rightValid⟩
    exact expandedComplete identity valid.1 valid.2

/-- Conditional only. The full S1 Complete proof is still required. -/
def intersectionBasisExpandedOfComplete (complete : Complete) :
    IntersectionBasis expandedLeft.semigroup rightTable.semigroup sigmaPlus where
  leftModels := expandedLeft_models
  rightModels := modelsRight
  complete := complete_iff_expanded.mp complete

end SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006FactorBridge
