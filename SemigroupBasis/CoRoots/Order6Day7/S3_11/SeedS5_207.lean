import SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_207ParityMarkerNormal
import SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal

/-!
# Authenticated unrestricted D009 cyclic root and S3_11 owner widening

The independently frozen S2_2 and S3_11 envelopes expose the same exact
eight-law parity-marker basis.  The fresh cyclic root uses the COMPLETE
S5_207 marker signature plus pointwise cyclic parity.  Only the explicit
one-way subgroup embedding widens that root to the S1 owner factor.

S6_5449 alone belongs to S1.  The public auxiliary cyclic root is available
to S2, but its S6_2854 and S6_2892 classes are neither instantiated nor
claimed here.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_207

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank009.basis

/-- The two independently immutable envelopes share the exact ordered B8. -/
theorem frozenCyclicBasis_eq :
    SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.basis = Rank009.basis := by
  decide

/-- Genuine catalogue C2 validity implies unrestricted pointwise parity. -/
theorem cyclicOccurrenceParity
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.leftTable.semigroup) :
    ∀ letter,
      identity.lhs.toList.count letter % 2 =
        identity.rhs.toList.count letter % 2 :=
  SemigroupBasis.CoRoots.S5_441Invariant.sameOccurrenceParity_of_s2_2_valid
    identity valid

/-- Exact fresh unrestricted cyclic/parity-marker B8 completeness. -/
theorem derivesOfCyclicFactorValid
    (identity : Identity Nat)
    (cyclicValid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.leftTable.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.rightTable.semigroup) :
    Derives targetBasis identity.lhs identity.rhs := by
  have markerSignature :=
    SemigroupBasis.CoRoots.S5_207.valid_sameMarkerSignature
      identity rightValid
  exact derivesOfSameMarkerParitySignature
    identity.lhs identity.rhs markerSignature
      (cyclicOccurrenceParity identity cyclicValid)

/-- Complete exact auxiliary root for S2's separately owned cyclic shell. -/
def cyclicIntersectionBasis :
    IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.basis where
  leftModels :=
    SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.leftModels
  rightModels :=
    SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.rightModels
  complete := by
    intro identity cyclicValid rightValid
    rw [frozenCyclicBasis_eq]
    exact derivesOfCyclicFactorValid identity cyclicValid rightValid

/-- Reuse the actual explicit C2 subgroup embedding, never theory equality. -/
def cyclicEmbeddingIntoS3_11 :
    Embedding
      SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup := by
  rw [SemigroupBasis.CoRoots.S5_441Invariant.catalogueS2_2_table_eq_cyclicTwo]
  rw [← SemigroupBasis.Generated.S3_11.table_eq_canonical_catalogue]
  exact
    SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening.cyclicEmbeddingS3_11

/-- Actual S3_11 validity pulls back one way to the catalogue cyclic factor. -/
theorem cyclicValid_of_s3_11Valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy Rank009.leftTable.semigroup) :
    identity.SatisfiedBy
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.leftTable.semigroup :=
  cyclicEmbeddingIntoS3_11.pullback_identity identity valid

/-- Preserve all exact displayed S3_11 frozen-law witnesses. -/
theorem modelsLeft : Models Rank009.leftTable.semigroup targetBasis :=
  Rank009.leftModels

/-- Preserve all exact displayed S5_207 frozen-law witnesses. -/
theorem modelsRight : Models Rank009.rightTable.semigroup targetBasis :=
  Rank009.rightModels

/-- Independent owner completeness comes after its fresh auxiliary root. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Rank009.leftTable.semigroup)
    (rightValid : identity.SatisfiedBy Rank009.rightTable.semigroup) :
    Derives targetBasis identity.lhs identity.rhs := by
  exact derivesOfCyclicFactorValid identity
    (cyclicValid_of_s3_11Valid identity leftValid) rightValid

/-- Actual unrestricted pair completeness precedes quotient normalization. -/
def intersectionBasis :
    IntersectionBasis
      Rank009.leftTable.semigroup
      Rank009.rightTable.semigroup
      Rank009.basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

/-- Quotient normalization is strictly downstream of both actual roots. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank009.leftTable.semigroup
      Rank009.rightTable.semigroup
      Rank009.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- Authenticated S1-owned unrestricted representative orientation. -/
theorem representative_basis_S6_5449 :
    BasisFor Rank009.S6_5449.table.semigroup Rank009.basis :=
  Rank009.S6_5449.representative_basis_of_normalizer intersectionNormalizer

/-- Authenticated S1-owned literal reversed-basis opposite orientation. -/
theorem opposite_basis_S6_5449 :
    BasisFor Rank009.S6_5449.table.semigroup.opposite
      (reversedBasis Rank009.basis) :=
  Rank009.S6_5449.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_207
