import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Pair2675Rules

/-! Complete exact B10 endpoints for the two actual tables. The nontrivial
length stratum is proved before long-word mixing; no false square expansion. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Pair2675

open SemigroupBasis

theorem complete (identity : Identity Nat)
    (markerValid : identity.SatisfiedBy markerTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) : Derives basis identity.lhs identity.rhs :=
  rules.complete rightTable.semigroup rightModels S5_203Family.S5_203.basisFor
    rightLeftReductive identity markerValid rightValid (shortOrLong identity rightValid)

def intersection : IntersectionBasis markerTable.semigroup rightTable.semigroup basis where
  leftModels := markerModels
  rightModels := rightModels
  complete := complete

noncomputable def quotientNormalizer : IntersectionNormalizer markerTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer intersection

noncomputable def normalizer : IntersectionNormalizer markerTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer quotientNormalizer
    (fun _ member => Derives.fromBasis member) (fun _ valid => valid) (fun _ valid => valid)

noncomputable def oppositeNormalizer :
    IntersectionNormalizer markerTable.semigroup.opposite rightTable.semigroup.opposite (reversedBasis basis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer intersection.oppositeReversed

theorem pair2675_representative_basis : BasisFor table2675.semigroup basis :=
  normalizer.basisFor markerModels rightModels subdirect2675
theorem pair2677_representative_basis : BasisFor table2677.semigroup basis :=
  normalizer.basisFor markerModels rightModels subdirect2677
theorem pair2675_opposite_basis : BasisFor table2675.semigroup.opposite (reversedBasis basis) :=
  pair2675_representative_basis.oppositeReversed
theorem pair2677_opposite_basis : BasisFor table2677.semigroup.opposite (reversedBasis basis) :=
  pair2677_representative_basis.oppositeReversed

theorem pair2675_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table2675.semigroup) :
    Derives basis identity.lhs identity.rhs := pair2675_representative_basis.2 identity valid
theorem pair2677_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table2677.semigroup) :
    Derives basis identity.lhs identity.rhs := pair2677_representative_basis.2 identity valid

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Pair2675
