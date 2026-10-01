import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Group14914Bridges

/-! Genuine basis transport from S1's unrestricted canonical-tile proof.
The old B13 record is preserved; the new exact B13 serves three actual tables. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Group14914

open SemigroupBasis

noncomputable def normalizer3 : IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    (SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
      SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Intersection.intersectionBasis)
    oldBasisDerivable (fun _ valid => valid) (fun _ valid => valid)

noncomputable def normalizer4 : IntersectionNormalizer expandedTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    (SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
      SemigroupBasis.CoRoots.Order6Day9.S3_18.Rank006Intersection.expandedIntersectionBasis)
    oldBasisDerivable (fun _ valid => valid) (fun _ valid => valid)

noncomputable def intersection3 : IntersectionBasis leftTable.semigroup rightTable.semigroup basis :=
  normalizer3.toIntersectionBasis leftModels rightModels
noncomputable def intersection4 : IntersectionBasis expandedTable.semigroup rightTable.semigroup basis :=
  normalizer4.toIntersectionBasis expandedModels rightModels

noncomputable def oppositeNormalizer3 :
    IntersectionNormalizer leftTable.semigroup.opposite rightTable.semigroup.opposite (reversedBasis basis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer intersection3.oppositeReversed
noncomputable def oppositeNormalizer4 :
    IntersectionNormalizer expandedTable.semigroup.opposite rightTable.semigroup.opposite (reversedBasis basis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer intersection4.oppositeReversed

theorem group14914_representative_basis : BasisFor table14914.semigroup basis :=
  normalizer4.basisFor expandedModels rightModels subdirect14914
theorem group14937_representative_basis : BasisFor table14937.semigroup basis :=
  normalizer3.basisFor leftModels rightModels subdirect14937
theorem group15924_representative_basis : BasisFor table15924.semigroup basis :=
  normalizer3.basisFor leftModels rightModels subdirect15924
theorem group14914_opposite_basis : BasisFor table14914.semigroup.opposite (reversedBasis basis) :=
  group14914_representative_basis.oppositeReversed
theorem group14937_opposite_basis : BasisFor table14937.semigroup.opposite (reversedBasis basis) :=
  group14937_representative_basis.oppositeReversed
theorem group15924_opposite_basis : BasisFor table15924.semigroup.opposite (reversedBasis basis) :=
  group15924_representative_basis.oppositeReversed

theorem group14914_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table14914.semigroup) :
    Derives basis identity.lhs identity.rhs := group14914_representative_basis.2 identity valid
theorem group14937_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table14937.semigroup) :
    Derives basis identity.lhs identity.rhs := group14937_representative_basis.2 identity valid
theorem group15924_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table15924.semigroup) :
    Derives basis identity.lhs identity.rhs := group15924_representative_basis.2 identity valid

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0443Group14914
