import SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_203
import SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_240ReversedLift
import SemigroupBasis.CoRoots.Order6Day7.S2_4.SeedS5_240Opposite

/-!
# Independent unrestricted S3_15op × S5_240 rank-086 seed

The independently kernel-green S2 rank-051 source is complete for the actual
left-zero factor and opposite S5_240. Reversing the intersection yields a
genuine unrestricted right-zero/S5_240 pair. The earlier independently
kernel-green rank-080 proof already provides the concrete multiplicative
embedding of that right-zero factor into S3_15 opposite on states 1 and 2.

All fourteen reversed source laws have explicit frozen rank-086 derivations,
so structural rebase constructs the exact unrestricted intersection BEFORE
quotient normalization and both authenticated S6_6169 orientations.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_240

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank086.basis

private abbrev sourceBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank051.basis

private abbrev leftFactor :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable.semigroup

private abbrev rightFactor :=
  SemigroupBasis.Generated.Catalogue.S5_240.table.semigroup

private theorem rank086_leftTable_eq :
    Rank086.leftTable =
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

/-- All eight exact frozen laws hold in the canonical opposite left factor. -/
theorem modelsLeft : Models leftFactor targetBasis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable
    Rank086.basis toFinThree (by decide)

/-- Reuse the hash-authenticated frozen right-factor proofs. -/
theorem modelsRight : Models rightFactor targetBasis :=
  Rank086.rightModels

/-- Reuse the already kernel-green explicit right-zero embedding. -/
def rightZeroEmbedding :
    Embedding
      SemigroupBasis.Generated.S2_4.table.semigroup.opposite
      leftFactor :=
  SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_203.rightZeroEmbedding

/-- The exact injective image is catalogue states 1 and 2. -/
theorem rightZeroEmbedding_values :
    List.ofFn
      (fun value : Fin 2 => (rightZeroEmbedding.toFun value).val) =
      [1, 2] := by
  decide

/-- Reverse the independently kernel-green rank-051 S2 intersection. -/
def reversedS2Intersection :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup.opposite
      rightFactor
      (reversedBasis sourceBasis) :=
  SemigroupBasis.IntersectionBasis.oppositeLeftOfOppositeRight
    SemigroupBasis.CoRoots.Order6Day7.S2_4.Rank051.Seed.intersectionBasis

/-- Pull actual left validity back along the concrete embedding. -/
theorem rightZeroValidity_of_leftValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftFactor) :
    identity.SatisfiedBy
      SemigroupBasis.Generated.S2_4.table.semigroup.opposite :=
  rightZeroEmbedding.pullback_identity identity valid

/-- Apply the complete reversed S2 pair without a finite-theory shortcut. -/
theorem sourceReversedIntersectionDerivation
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives (reversedBasis sourceBasis)
      identity.lhs identity.rhs :=
  reversedS2Intersection.complete identity
    (rightZeroValidity_of_leftValid identity leftValid) rightValid

/-- Exact unrestricted completeness for the immutable rank-086 basis. -/
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

/-- Exact intersection structure for the frozen rank-086 factors and laws. -/
def intersectionBasis :
    IntersectionBasis
      Rank086.leftTable.semigroup
      Rank086.rightTable.semigroup
      Rank086.basis := by
  rw [rank086_leftTable_eq]
  exact displayedIntersectionBasis

/-- Introduce quotient normalization only after unrestricted completeness. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank086.leftTable.semigroup
      Rank086.rightTable.semigroup
      Rank086.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- The exact authenticated S6_6169 representative. -/
theorem representative_basis_S6_6169 :
    BasisFor Rank086.S6_6169.table.semigroup Rank086.basis :=
  Rank086.S6_6169.representative_basis_of_normalizer intersectionNormalizer

/-- The exact literal reversed-basis opposite orientation. -/
theorem opposite_basis_S6_6169 :
    BasisFor Rank086.S6_6169.table.semigroup.opposite
      (reversedBasis Rank086.basis) :=
  Rank086.S6_6169.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_240
