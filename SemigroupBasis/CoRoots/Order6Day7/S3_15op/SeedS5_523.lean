import SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_523SuffixLift
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opProfile
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.S5_523

/-!
# Independent unrestricted S3_15op × S5_523 rank-100 seed

The already certified common `S3_15op` profile gives actual final-letter
equality. The independently complete `S5_523` factor supplies its exact
five-law derivation and separates literal words from words of length at least
three. Explicit suffix-lifting transports that unrestricted lower derivation
through the seven immutable rank-100 displayed laws; the three-step terminal
duplication chain removes the temporary common final letter on both sides.

The resulting genuine factor-intersection completeness strictly precedes
quotient normalization and both authenticated S6_9689 orientations.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_523

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank100.basis

private abbrev leftFactor :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable.semigroup

private abbrev rightFactor :=
  SemigroupBasis.Generated.Catalogue.S5_523.table.semigroup

private theorem rank100_leftTable_eq :
    Rank100.leftTable =
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
/-- Kernel-check all seven exact frozen laws in the canonical left factor. -/
theorem modelsLeft : Models leftFactor targetBasis :=
  FiniteCertificate.checkModels_sound
    SemigroupBasis.CoRoots.Order6L3HeavyRank2.s3_15OppositeTable
    Rank100.basis toFinThree (by decide)

/-- Reuse all seven separately authenticated frozen right-factor witnesses. -/
theorem modelsRight : Models rightFactor targetBasis :=
  Rank100.rightModels

/-- Actual unrestricted left-factor validity fixes the final variable. -/
theorem commonFinal_of_leftValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftFactor) :
    identity.lhs.final = identity.rhs.final :=
  (SemigroupBasis.CoRoots.Order6L3HeavyRank2.sameLastSupport_of_s3_15Opposite_valid
    identity valid).final_eq

/-- Invoke the independently unconditional five-law lower-factor endpoint. -/
theorem lowerDerivation_of_rightValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightFactor) :
    Derives SemigroupBasis.CoRoots.S5_523.basis
      identity.lhs identity.rhs :=
  SemigroupBasis.CoRoots.S5_523.representative_basis.2 identity valid

/-- Use actual certified lower semantics, never a bounded-table implication. -/
theorem lowerSignature_of_rightValid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightFactor) :
    SemigroupBasis.CoRoots.S5_523.SameLongFirstOccurrenceSignature
      identity.lhs identity.rhs :=
  SemigroupBasis.CoRoots.S5_523.s5_523SemanticSeparation
    identity.lhs identity.rhs valid

/-- Independent unrestricted completeness for the immutable seven-law block. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives targetBasis identity.lhs identity.rhs := by
  have lower := lowerDerivation_of_rightValid identity rightValid
  have signature := lowerSignature_of_rightValid identity rightValid
  rcases signatureShortOrLong identity.lhs identity.rhs signature with
    literal | ⟨leftLong, rightLong⟩
  · rw [literal]
    exact Derives.refl _
  · have finalEq := commonFinal_of_leftValid identity leftValid
    let final : Word Nat := Word.singleton identity.lhs.final
    have lifted := liftLowerWithSuffix lower final Word.singleton
    rw [bind_singleton, bind_singleton] at lifted
    have leftDuplicate :=
      derivesWordFinalDuplication identity.lhs leftLong
    have rightDuplicate :=
      derivesWordFinalDuplication identity.rhs rightLong
    have rightAligned :
        Derives targetBasis
          identity.rhs (identity.rhs ++ final) := by
      simpa [final, finalEq] using rightDuplicate
    exact leftDuplicate.trans (lifted.trans rightAligned.symm)

/-- The exact unrestricted factor intersection, before any quotient object. -/
def displayedIntersectionBasis :
    IntersectionBasis leftFactor rightFactor targetBasis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

/-- Re-identify the immutable frozen canonical left table explicitly. -/
def intersectionBasis :
    IntersectionBasis
      Rank100.leftTable.semigroup
      Rank100.rightTable.semigroup
      Rank100.basis := by
  rw [rank100_leftTable_eq]
  exact displayedIntersectionBasis

/-- Introduce quotient normalization strictly after unrestricted completeness. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank100.leftTable.semigroup
      Rank100.rightTable.semigroup
      Rank100.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- The exact authenticated rank-100 S6_9689 representative. -/
theorem representative_basis_S6_9689 :
    BasisFor Rank100.S6_9689.table.semigroup Rank100.basis :=
  Rank100.S6_9689.representative_basis_of_normalizer intersectionNormalizer

/-- The exact literal reversed-basis opposite orientation. -/
theorem opposite_basis_S6_9689 :
    BasisFor Rank100.S6_9689.table.semigroup.opposite
      (reversedBasis Rank100.basis) :=
  Rank100.S6_9689.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_523
