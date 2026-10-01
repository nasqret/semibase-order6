import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opProfile
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_108ReversedLift
import SemigroupBasis.CoRoots.Order6S5_108OppositeInitialIntersection

/-!
# Independent unrestricted S3_15op × S5_108 rank-075 seed

The earlier initial-intersection theorem is genuinely complete for the direct
S3_15/S5_107 pair. Word reversal converts validity in the exact S3_15 opposite
factor into direct validity. The separately proved unrestricted S5_107 versus
S5_108-opposite identity-theory equivalence converts reversed right validity
into its source-factor validity. Reversal of the resulting unrestricted
derivation, followed by fifteen exact one-step or two-step displayed witnesses,
proves the frozen rank-075 intersection BEFORE quotient normalization.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_108

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank075.basis

private abbrev initialBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6S5_107InitialIntersection.basis

private abbrev leftFactor :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable.semigroup

private abbrev rightFactor :=
  SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup

private theorem rank075_leftTable_eq :
    Rank075.leftTable =
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

set_option maxRecDepth 100000 in
/-- Every exact frozen rank-075 law is valid in its opposite S3_15 factor. -/
theorem modelsLeft : Models leftFactor targetBasis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable
    Rank075.basis toFinThree (by decide)

/-- Reuse the hash-authenticated exact frozen right-factor model proofs. -/
theorem modelsRight : Models rightFactor targetBasis :=
  Rank075.rightModels

/-- Opposite-factor validity is EXACTLY validity of the reversed identity in
the direct, previously proved S3_15 intersection factor. -/
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

/-- The independently COMPLETE S5_107/S5_108-opposite theory equivalence
transports reversed validity without any finite-table semantic shortcut. -/
theorem reversedRightValidity
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightFactor) :
    identity.reversed.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup := by
  have oppositeValid :
      identity.reversed.SatisfiedBy rightFactor.opposite := by
    apply
      (Identity.satisfiedBy_opposite_iff_reversed
        identity.reversed rightFactor).mpr
    simpa only [Identity.reversed_reversed] using valid
  exact
    (SemigroupBasis.CoRoots.Order6S5_108OppositeInitialIntersection.s5_107_s5_108Opposite_sameTheory
      identity.reversed).mpr oppositeValid

/-- Invoke actual unrestricted completeness of the older initial intersection. -/
theorem sourceInitialIntersectionDerivation
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives initialBasis identity.reversed.lhs identity.reversed.rhs :=
  SemigroupBasis.CoRoots.Order6S5_107InitialIntersectionFamilies.intersectionS3_15S5_107.complete
    identity.reversed
    (reversedLeftValidity identity leftValid)
    (reversedRightValidity identity rightValid)

/-- Reverse the unrestricted source derivation back to target orientation. -/
theorem reversedInitialIntersectionDerivation
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives (reversedBasis initialBasis) identity.lhs identity.rhs := by
  have reversed :=
    (sourceInitialIntersectionDerivation identity leftValid rightValid).reverse
  simpa [Identity.reversed] using reversed

/-- Independent unrestricted completeness for the exact frozen fifteen-law
S3_15op/S5_108 intersection. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives targetBasis identity.lhs identity.rhs :=
  transportReversedInitialDerivation
    (reversedInitialIntersectionDerivation identity leftValid rightValid)

def displayedIntersectionBasis :
    IntersectionBasis leftFactor rightFactor targetBasis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

/-- Exact unrestricted intersection basis for the frozen rank-075 block. -/
def intersectionBasis :
    IntersectionBasis
      Rank075.leftTable.semigroup
      Rank075.rightTable.semigroup
      Rank075.basis := by
  rw [rank075_leftTable_eq]
  exact displayedIntersectionBasis

/-- Quotient normalization is downstream of proved intersection completeness. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank075.leftTable.semigroup
      Rank075.rightTable.semigroup
      Rank075.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- The exact authenticated rank-075 representative. -/
theorem representative_basis_S6_3942 :
    BasisFor Rank075.S6_3942.table.semigroup Rank075.basis :=
  Rank075.S6_3942.representative_basis_of_normalizer intersectionNormalizer

/-- Its exact reversed-basis opposite orientation. -/
theorem opposite_basis_S6_3942 :
    BasisFor Rank075.S6_3942.table.semigroup.opposite
      (reversedBasis Rank075.basis) :=
  Rank075.S6_3942.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_108
