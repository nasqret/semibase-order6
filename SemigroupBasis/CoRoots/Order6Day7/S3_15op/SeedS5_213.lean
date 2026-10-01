import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opProfile
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_213ReversedLift
import SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_213M2Transfers

/-!
# Independent unrestricted S3_15op × S5_213 rank-083 seed

The existing S3_15/S5_213 intersection is genuinely unrestricted. Reversal of
the target's actual S3_15 opposite factor gives direct left validity. The
separately proved unrestricted M2 opposite-theory theorem converts reversed
S5_213 validity into the exact direct right-factor validity. Reversal of the
complete source derivation, followed by three explicit source-law witnesses,
proves the immutable three-law rank-083 intersection BEFORE its quotient
normalizer and both authenticated S6_5676 orientations.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_213

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank083.basis

private abbrev sourceBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_213M2.sigma

private abbrev leftFactor :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable.semigroup

private abbrev rightFactor :=
  SemigroupBasis.Generated.Catalogue.S5_213.table.semigroup

private theorem rank083_leftTable_eq :
    Rank083.leftTable =
      SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable := by
  change
    SemigroupBasis.Order6Subdirect.oppositeTable
        SemigroupBasis.Generated.Catalogue.S3_15.table =
      SemigroupBasis.Order6Subdirect.oppositeTable
        SemigroupBasis.Generated.S3_15.table
  rw [SemigroupBasis.Generated.S3_15.table_eq_canonical_catalogue]

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

/-- Every exact frozen rank-083 law is valid in its canonical left factor. -/
theorem modelsLeft : Models leftFactor targetBasis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable
    Rank083.basis toFinThree (by decide)

/-- Reuse the immutable frozen right-factor validity witnesses. -/
theorem modelsRight : Models rightFactor targetBasis :=
  Rank083.rightModels

/-- Reversal converts actual opposite-factor validity into direct validity. -/
theorem reversedLeftValidity
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftFactor) :
    identity.reversed.SatisfiedBy
      SemigroupBasis.Generated.S3_15.table.semigroup := by
  have oppositeValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_15.table.semigroup.opposite := by
    simpa only
      [SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable_semigroup]
      using valid
  exact
    (Identity.satisfiedBy_opposite_iff_reversed identity
      SemigroupBasis.Generated.S3_15.table.semigroup).mp oppositeValid

/-- Use the previously PROVED unrestricted M2 opposite-theory implication. -/
theorem reversedRightValidity
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightFactor) :
    identity.reversed.SatisfiedBy rightFactor := by
  have oppositeValid :
      identity.reversed.SatisfiedBy rightFactor.opposite := by
    apply
      (Identity.satisfiedBy_opposite_iff_reversed
        identity.reversed rightFactor).mpr
    simpa only [Identity.reversed_reversed] using valid
  exact
    SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_213M2.s5_213_valid_of_opposite_valid
      identity.reversed oppositeValid

/-- Invoke actual unrestricted completeness of the existing direct pair. -/
theorem sourceIntersectionDerivation
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives sourceBasis
      identity.reversed.lhs identity.reversed.rhs :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_13S5_213M2.intersectionBasisS3_15S5_213.complete
    identity.reversed
    (reversedLeftValidity identity leftValid)
    (reversedRightValidity identity rightValid)

/-- Reverse the genuine source derivation into its target orientation. -/
theorem reversedIntersectionDerivation
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives (reversedBasis sourceBasis)
      identity.lhs identity.rhs := by
  have reversed :=
    (sourceIntersectionDerivation identity leftValid rightValid).reverse
  simpa [Identity.reversed] using reversed

/-- Independent unrestricted completeness for the exact three-law block. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives targetBasis identity.lhs identity.rhs :=
  transportReversedSourceDerivation
    (reversedIntersectionDerivation identity leftValid rightValid)

def displayedIntersectionBasis :
    IntersectionBasis leftFactor rightFactor targetBasis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

/-- Exact unrestricted intersection for the authenticated rank-083 envelope. -/
def intersectionBasis :
    IntersectionBasis
      Rank083.leftTable.semigroup
      Rank083.rightTable.semigroup
      Rank083.basis := by
  rw [rank083_leftTable_eq]
  exact displayedIntersectionBasis

/-- Quotient normalization is downstream of proved unrestricted completeness. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank083.leftTable.semigroup
      Rank083.rightTable.semigroup
      Rank083.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- The authenticated S6_5676 representative. -/
theorem representative_basis_S6_5676 :
    BasisFor Rank083.S6_5676.table.semigroup Rank083.basis :=
  Rank083.S6_5676.representative_basis_of_normalizer intersectionNormalizer

/-- The authenticated exact reversed-basis opposite orientation. -/
theorem opposite_basis_S6_5676 :
    BasisFor Rank083.S6_5676.table.semigroup.opposite
      (reversedBasis Rank083.basis) :=
  Rank083.S6_5676.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_213
