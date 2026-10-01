import SemigroupBasis.CoRoots.Order6HeadSupportCap
import SemigroupBasis.Generated.S3_15

namespace SemigroupBasis.Generated.Order6FactorIntersectionEndpointsV1.Common

open SemigroupBasis

private theorem sameIdentityTheoryOverOfCommonBasis
    {A : Type u} {B : Type v} {X : Type w}
    {G : Semigroup A} {H : Semigroup B}
    {commonBasis : List (Identity X)}
    (basisForG : BasisFor G commonBasis)
    (basisForH : BasisFor H commonBasis) :
    SameIdentityTheoryOver G H X := by
  intro identity
  constructor
  · intro validInG valuation
    exact Derives.sound basisForH.1
      (basisForG.2 identity validInG) valuation
  · intro validInH valuation
    exact Derives.sound basisForG.1
      (basisForH.2 identity validInH) valuation

private theorem leftNormalBandThree_s3_15_sameTheory :
    SameIdentityTheoryOver
      SemigroupBasis.Examples.leftNormalBandThree.semigroup
      SemigroupBasis.Generated.S3_15.table.semigroup Nat :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.Examples.leftNormalBandThreeBasis_complete
    SemigroupBasis.Generated.S3_15.representative_basis

/-- The `S3_13 x S5_201` intersection theorem transported to the
identity-equivalent `S3_15 x S5_201` factor pair. -/
def s3_15S5_201IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Examples.commutativeCappedSupportFive.semigroup
      SemigroupBasis.CoRoots.Order6HeadSupportCap.basis :=
  SemigroupBasis.CoRoots.Order6HeadSupportCap.intersectionBasis.transferTheories
    leftNormalBandThree_s3_15_sameTheory (fun _ => Iff.rfl)

end SemigroupBasis.Generated.Order6FactorIntersectionEndpointsV1.Common
