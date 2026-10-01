import SemigroupBasis.CoRoots.Order6FactorIntersectionFinalMarkerShortLong
import SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort
import SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots
import SemigroupBasis.CoRoots.S5_1007Family
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.Generated.CommutativePeriodThreeFromTwoFamily
import SemigroupBasis.Generated.FinalMarkerTransfers
import SemigroupBasis.Generated.S3_10
import SemigroupBasis.Generated.S3_11
import SemigroupBasis.Normalization.OneLocalFordLord
import SemigroupBasis.Order6Subdirect.Common

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace SemigroupBasis.Generated.Order6FactorIntersectionResidual59.Common

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

private theorem s3_10_s3_11_sameTheory :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.S3_10.table.semigroup
      SemigroupBasis.Generated.S3_11.table.semigroup Nat :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.Generated.S3_10.representative_basis
    SemigroupBasis.Generated.S3_11.representative_basis

private theorem s5_1001_s5_1004_sameTheory :
    SameIdentityTheoryOver
      SemigroupBasis.Examples.s5_1001.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1004.table.semigroup Nat :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.Examples.s5_1001Basis
    SemigroupBasis.Generated.CommutativePeriodThreeFromTwoFamily.S5_1004.representative_basis

private theorem s5_1001_s5_1156_sameTheory :
    SameIdentityTheoryOver
      SemigroupBasis.Examples.s5_1001.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1156.table.semigroup Nat :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.Examples.s5_1001Basis
    SemigroupBasis.Generated.CommutativePeriodThreeFromTwoFamily.S5_1156.representative_basis

private theorem s5_1007_s5_1008_sameTheory :
    SameIdentityTheoryOver
      SemigroupBasis.CoRoots.S5_1007Family.S5_1007.table.semigroup
      SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup Nat :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.CoRoots.S5_1007Family.S5_1007.basis_complete
    SemigroupBasis.CoRoots.S5_1007Family.S5_1008.basis_complete

def positiveParityS3_11S4_9IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.S4_9.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.s3_10_s4_9_intersectionBasis.transferTheories
    s3_10_s3_11_sameTheory (fun _ => Iff.rfl)

def positiveParityS3_11S4_35IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.S4_35.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.s3_10_s4_35_intersectionBasis.transferTheories
    s3_10_s3_11_sameTheory (fun _ => Iff.rfl)

def indexTwoPeriodThreeS3_6S5_1004IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Examples.finalMarkerThree.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1004.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.IndexTwoPeriodThree.basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.IndexTwoPeriodThree.intersectionBasis.transferTheories
    (fun _ => Iff.rfl) s5_1001_s5_1004_sameTheory

def indexTwoPeriodThreeS3_6S5_1156IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Examples.finalMarkerThree.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1156.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.IndexTwoPeriodThree.basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.IndexTwoPeriodThree.intersectionBasis.transferTheories
    (fun _ => Iff.rfl) s5_1001_s5_1156_sameTheory

def prefixResidueSixS3_6S5_1008IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Examples.finalMarkerThree.semigroup
      SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.PrefixResidueSix.basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.PrefixResidueSix.intersectionBasis.transferTheories
    (fun _ => Iff.rfl) s5_1007_s5_1008_sameTheory

private def toFinThree : Nat -> Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

def s3_6IntoS4_44Map (value : Fin 3) : Fin 4 :=
  if value = 0 then (0 : Fin 4) else
  if value = 1 then (1 : Fin 4) else
  (2 : Fin 4)

def s3_6IntoS4_44 :
    Embedding
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_44.table.semigroup where
  toFun := s3_6IntoS4_44Map
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    revert left right
    decide

private theorem s4_44ModelsFinalMarkerThreeBasis :
    Models
      SemigroupBasis.Generated.Catalogue.S4_44.table.semigroup
      SemigroupBasis.Examples.finalMarkerThreeBasis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.Catalogue.S4_44.table
    SemigroupBasis.Examples.finalMarkerThreeBasis
    toFinThree
    (by decide)

private theorem s4_44FinalMarkerThreeBasis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S4_44.table.semigroup
      SemigroupBasis.Examples.finalMarkerThreeBasis :=
  SemigroupBasis.Generated.S3_6.representative_basis.inheritAlongEmbedding
    s3_6IntoS4_44 s4_44ModelsFinalMarkerThreeBasis

private theorem s3_6_s4_44_sameTheory :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.S3_6.table.semigroup
      SemigroupBasis.Generated.Catalogue.S4_44.table.semigroup Nat :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.Generated.S3_6.representative_basis
    s4_44FinalMarkerThreeBasis

def finalMarkerS4_44S4_2IntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.Catalogue.S4_44.table.semigroup
      SemigroupBasis.Generated.S4_2.table.semigroup
      SemigroupBasis.CoRoots.Order6FactorIntersectionFinalMarkerShortLong.basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionFinalMarkerShortLong.s3_6_s4_2_intersectionBasis.transferTheories
    s3_6_s4_44_sameTheory (fun _ => Iff.rfl)

private def s3_10OppositeTable : FiniteTable :=
  SemigroupBasis.Order6Subdirect.oppositeTable
    SemigroupBasis.Generated.S3_10.table

private def s4_9OppositeTable : FiniteTable :=
  SemigroupBasis.Order6Subdirect.oppositeTable
    SemigroupBasis.Generated.S4_9.table

private theorem s3_10OppositeModelsPositiveParityBasis :
    Models
      SemigroupBasis.Generated.S3_10.table.semigroup.opposite
      SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis := by
  simpa only [s3_10OppositeTable,
    SemigroupBasis.Order6Subdirect.oppositeTable_semigroup] using
    FiniteCertificate.checkModels_sound
      s3_10OppositeTable
      SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis
      toFinThree
      (by decide)

private theorem s4_9OppositeModelsPositiveParityBasis :
    Models
      SemigroupBasis.Generated.S4_9.table.semigroup.opposite
      SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis := by
  simpa only [s4_9OppositeTable,
    SemigroupBasis.Order6Subdirect.oppositeTable_semigroup] using
    FiniteCertificate.checkModels_sound
      s4_9OppositeTable
      SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis
      toFinThree
      (by decide)

private theorem s3_10ModelsReversedPositiveParityBasis :
    Models
      SemigroupBasis.Generated.S3_10.table.semigroup
      (reversedBasis
        SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis) :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S3_10.table
    (reversedBasis
      SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis)
    toFinThree
    (by decide)

private theorem s4_9ModelsReversedPositiveParityBasis :
    Models
      SemigroupBasis.Generated.S4_9.table.semigroup
      (reversedBasis
        SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis) :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.Generated.S4_9.table
    (reversedBasis
      SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis)
    toFinThree
    (by decide)

private theorem reversedPositiveParityAxiomsDerive
    (identity : Identity Nat)
    (member :
      identity ∈
        reversedBasis
          SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis) :
    Derives
      SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis
      identity.lhs identity.rhs :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.s3_10_s4_9_intersectionBasis.complete
    identity
    (s3_10ModelsReversedPositiveParityBasis identity member)
    (s4_9ModelsReversedPositiveParityBasis identity member)

private def positiveParityS3_10OppositeS4_9OppositeRetargeted :
    IntersectionBasis
      SemigroupBasis.Generated.S3_10.table.semigroup.opposite
      SemigroupBasis.Generated.S4_9.table.semigroup.opposite
      SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis :=
  SemigroupBasis.OneLocalFordLord.retargetIntersectionBasis
    SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.s3_10_s4_9_intersectionBasis.oppositeReversed
    s3_10OppositeModelsPositiveParityBasis
    s4_9OppositeModelsPositiveParityBasis
    reversedPositiveParityAxiomsDerive

private theorem s3_10Opposite_s3_10_sameTheory :
    SameIdentityTheoryOver
      SemigroupBasis.Generated.S3_10.table.semigroup.opposite
      SemigroupBasis.Generated.S3_10.table.semigroup Nat :=
  sameIdentityTheoryOverOfCommonBasis
    SemigroupBasis.Generated.S3_10.opposite_basis
    SemigroupBasis.Generated.S3_10.representative_basis

def positiveParityS3_10S4_9OppositeIntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_10.table.semigroup
      SemigroupBasis.Generated.S4_9.table.semigroup.opposite
      SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis :=
  positiveParityS3_10OppositeS4_9OppositeRetargeted.transferTheories
    s3_10Opposite_s3_10_sameTheory (fun _ => Iff.rfl)

end SemigroupBasis.Generated.Order6FactorIntersectionResidual59.Common
