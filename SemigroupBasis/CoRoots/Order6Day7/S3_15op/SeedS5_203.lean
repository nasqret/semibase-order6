import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opProfile
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_203ReversedLift
import SemigroupBasis.CoRoots.Order6Day7.S2_4.SeedS5_203Opposite

/-!
# Independent unrestricted S3_15op × S5_203 rank-080 seed

The independently kernel-green S2 rank-046 intersection is complete for the
actual left-zero factor and the opposite of the actual S5_203 factor. Word
reversal therefore gives a genuine unrestricted right-zero/S5_203 source.
The right-zero factor embeds into the exact S3_15 opposite table on catalogue
states 1 and 2. Pullback along that concrete embedding supplies the required
source left validity without a fabricated semantic implication.

All eighteen reversed source laws have independently explicit derivations
from the twelve frozen rank-080 laws. Structural equational transport thus
proves the exact unrestricted intersection before quotient normalization and
both authenticated S6_5580 orientation endpoints.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_203

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank080.basis

private abbrev sourceBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank046.basis

private abbrev leftFactor :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable.semigroup

private abbrev rightFactor :=
  SemigroupBasis.Generated.Catalogue.S5_203.table.semigroup

private theorem rank080_leftTable_eq :
    Rank080.leftTable =
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
/-- Check every exact frozen law on the canonical opposite left factor. -/
theorem modelsLeft : Models leftFactor targetBasis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable
    Rank080.basis toFinThree (by decide)

/-- Reuse the hash-authenticated frozen right-factor model proofs. -/
theorem modelsRight : Models rightFactor targetBasis :=
  Rank080.rightModels

/-- The actual right-zero factor occupies states 1 and 2 in S3_15 opposite. -/
def rightZeroIntoS3_15Opposite (value : Fin 2) : Fin 3 :=
  if value = 0 then (1 : Fin 3) else (2 : Fin 3)

/-- Concrete multiplicative and injective embedding; no theory is assumed. -/
def rightZeroEmbedding :
    Embedding
      SemigroupBasis.Generated.S2_4.table.semigroup.opposite
      leftFactor where
  toFun := rightZeroIntoS3_15Opposite
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equality
    revert left right
    decide

/-- Reverse the existing independently kernel-green S2 factor intersection. -/
def reversedS2Intersection :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup.opposite
      rightFactor
      (reversedBasis sourceBasis) :=
  SemigroupBasis.IntersectionBasis.oppositeLeftOfOppositeRight
    SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank046.Seed.intersectionBasis

/-- Actual source-factor validity follows by pulling back the embedding. -/
theorem rightZeroValidity_of_leftValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftFactor) :
    identity.SatisfiedBy
      SemigroupBasis.Generated.S2_4.table.semigroup.opposite :=
  rightZeroEmbedding.pullback_identity identity valid

/-- Apply unrestricted completeness of the already proved reversed S2 pair. -/
theorem sourceReversedIntersectionDerivation
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives (reversedBasis sourceBasis)
      identity.lhs identity.rhs :=
  reversedS2Intersection.complete identity
    (rightZeroValidity_of_leftValid identity leftValid) rightValid

/-- Genuine unrestricted completeness for the frozen twelve-law rank block. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives targetBasis identity.lhs identity.rhs :=
  transportReversedS2Derivation
    (sourceReversedIntersectionDerivation identity leftValid rightValid)

def displayedIntersectionBasis :
    IntersectionBasis leftFactor rightFactor targetBasis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

/-- Exact unrestricted intersection for the immutable rank-080 envelope. -/
def intersectionBasis :
    IntersectionBasis
      Rank080.leftTable.semigroup
      Rank080.rightTable.semigroup
      Rank080.basis := by
  rw [rank080_leftTable_eq]
  exact displayedIntersectionBasis

/-- Quotient normalization is strictly downstream of the unrestricted proof. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank080.leftTable.semigroup
      Rank080.rightTable.semigroup
      Rank080.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- The exact authenticated rank-080 representative. -/
theorem representative_basis_S6_5580 :
    BasisFor Rank080.S6_5580.table.semigroup Rank080.basis :=
  Rank080.S6_5580.representative_basis_of_normalizer intersectionNormalizer

/-- The exact literal reversed-basis opposite orientation. -/
theorem opposite_basis_S6_5580 :
    BasisFor Rank080.S6_5580.table.semigroup.opposite
      (reversedBasis Rank080.basis) :=
  Rank080.S6_5580.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_203
