import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Single9095Bridges
import SemigroupBasis.CoRoots.Order6FactorPairS3_18S4_20Normal

/-! The exact approved B14 is complete via the established C3/simple-endpoints
normalizer. The literal target uses a C3 embedding and an S4_20 quotient;
no nonexistent surjection from the target onto C3 is asserted. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Single9095

open SemigroupBasis

noncomputable def cyclicNormalizer : IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    (SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
      Order6FactorPairS3_18S4_20.intersectionBasis)
    oldBasisDerivable (fun _ valid => valid) (fun _ valid => valid)

noncomputable def normalizer : IntersectionNormalizer expandedTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer cyclicNormalizer
    (fun _ member => Derives.fromBasis member)
    (fun identity valid => cyclicCoreEmbedding.pullback_identity identity valid) (fun _ valid => valid)

noncomputable def intersection : IntersectionBasis expandedTable.semigroup rightTable.semigroup basis :=
  normalizer.toIntersectionBasis expandedModels rightModels

noncomputable def oppositeNormalizer :
    IntersectionNormalizer expandedTable.semigroup.opposite rightTable.semigroup.opposite (reversedBasis basis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer intersection.oppositeReversed

theorem singleton9095_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table9095.semigroup) :
    Derives basis identity.lhs identity.rhs :=
  intersection.complete identity (expandedQuotient.pushforwardIdentity identity valid)
    (endpointQuotient.pushforwardIdentity identity valid)

theorem singleton9095_representative_basis : BasisFor table9095.semigroup basis :=
  normalizer.basisFor expandedModels rightModels subdirect9095
theorem singleton9095_opposite_basis : BasisFor table9095.semigroup.opposite (reversedBasis basis) :=
  singleton9095_representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Single9095
