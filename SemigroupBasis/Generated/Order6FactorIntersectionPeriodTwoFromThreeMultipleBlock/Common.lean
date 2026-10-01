import SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock
import SemigroupBasis.Generated.CommutativePeriodTwoFromThreeFamily
import SemigroupBasis.Generated.DualMultipleBlockFiveTransfersLayer2
import SemigroupBasis.Generated.S5_121

namespace SemigroupBasis.Generated.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.Common

open SemigroupBasis
open SemigroupBasis.Examples

private theorem sameIdentityTheoryOverOfCommonBasis
    {A : Type u} {B : Type v}
    {G : Semigroup A} {H : Semigroup B}
    {commonBasis : List (Identity Nat)}
    (basisForG : BasisFor G commonBasis)
    (basisForH : BasisFor H commonBasis) :
    SameIdentityTheoryOver G H Nat := by
  intro identity
  constructor
  · intro valid valuation
    exact Derives.sound basisForH.1
      (basisForG.2 identity valid) valuation
  · intro valid valuation
    exact Derives.sound basisForG.1
      (basisForH.2 identity valid) valuation

private def transportIntersection
    {A : Type u} {B : Type v}
    {left : Semigroup A} {right : Semigroup B}
    (leftBasis : BasisFor left dualMultipleBlockFiveStoredBasis)
    (rightBasis :
      BasisFor right commutativePeriodTwoFromThreeBasis) :
    IntersectionBasis left right
      SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.representativeBasis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.representativeIntersectionBasis.transferTheories
    (sameIdentityTheoryOverOfCommonBasis
      dualMultipleBlockFiveStoredBasis_complete leftBasis)
    (sameIdentityTheoryOverOfCommonBasis s5_223Basis rightBasis)

def s5_121_s5_223_intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S5_121.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_223.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.representativeBasis :=
  transportIntersection
    SemigroupBasis.Generated.S5_121.representative_basis
    SemigroupBasis.Generated.CommutativePeriodTwoFromThreeFamily.S5_223.representative_basis

def s5_132_s5_226_intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.Catalogue.S5_132.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_226.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.representativeBasis :=
  transportIntersection
    SemigroupBasis.Generated.DualMultipleBlockFiveTransfers.S5_132.representative_basis
    SemigroupBasis.Generated.CommutativePeriodTwoFromThreeFamily.S5_226.representative_basis

def s5_134_s5_223_intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.Catalogue.S5_134.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_223.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.representativeBasis :=
  transportIntersection
    SemigroupBasis.Generated.DualMultipleBlockFiveTransfers.S5_134.representative_basis
    SemigroupBasis.Generated.CommutativePeriodTwoFromThreeFamily.S5_223.representative_basis

def s5_143_s5_226_intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.Catalogue.S5_143.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_226.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.representativeBasis :=
  transportIntersection
    SemigroupBasis.Generated.DualMultipleBlockFiveTransfers.S5_143.representative_basis
    SemigroupBasis.Generated.CommutativePeriodTwoFromThreeFamily.S5_226.representative_basis

def s5_123_s5_223_intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.Catalogue.S5_123.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_223.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.representativeBasis :=
  transportIntersection
    SemigroupBasis.Generated.DualMultipleBlockFiveTransfers.S5_123.representative_basis
    SemigroupBasis.Generated.CommutativePeriodTwoFromThreeFamily.S5_223.representative_basis

def s5_145_s5_226_intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.Catalogue.S5_145.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_226.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.representativeBasis :=
  transportIntersection
    SemigroupBasis.Generated.DualMultipleBlockFiveTransfers.S5_145.representative_basis
    SemigroupBasis.Generated.CommutativePeriodTwoFromThreeFamily.S5_226.representative_basis

def s5_247_s5_514_intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.Catalogue.S5_247.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_514.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.representativeBasis :=
  transportIntersection
    SemigroupBasis.Generated.DualMultipleBlockFiveTransfers.S5_247.representative_basis
    SemigroupBasis.Generated.CommutativePeriodTwoFromThreeFamily.S5_514.representative_basis

def s5_251_s5_514_intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.Catalogue.S5_251.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_514.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.representativeBasis :=
  transportIntersection
    SemigroupBasis.Generated.DualMultipleBlockFiveTransfers.S5_251.representative_basis
    SemigroupBasis.Generated.CommutativePeriodTwoFromThreeFamily.S5_514.representative_basis

end SemigroupBasis.Generated.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.Common
