import SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_796OppositeFixedHead
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.S5_787Family

/-!
# First independent unrestricted authenticated S3_11 owner seed

The exact right factor is `S5_796ᵒᵖ`.  Reversal supplies its COMPLETE
separator/first signature; the S3_11 factor supplies unrestricted occurrence
parity.  The frozen seventeen-law basis is proved complete by the protected
twenty-five-law S5_441 normalizer before quotient normalization is formed.

Both S6_11228 orientations are unconditional at source level.  Independent
kernel recording, acceptance, and sealing remain outside this source proof.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_796Opposite

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank001.basis

private abbrev leftFactor := Rank001.leftTable.semigroup

private abbrev rightFactor := Rank001.rightTable.semigroup

/-- Reuse every exact frozen S3_11 displayed-law witness. -/
theorem modelsLeft : Models leftFactor targetBasis :=
  Rank001.leftModels

/-- Reuse every exact frozen S5_796-opposite displayed-law witness. -/
theorem modelsRight : Models rightFactor targetBasis :=
  Rank001.rightModels

/-- Unrestricted reversal into the genuine ordinary S5_796 factor. -/
theorem rightValidReversed
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy rightFactor) :
    identity.reversed.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_796.table.semigroup := by
  change
    identity.SatisfiedBy
      SemigroupBasis.Generated.Catalogue.S5_796.table.semigroup.opposite
    at valid
  exact
    (Identity.satisfiedBy_opposite_iff_reversed identity
      SemigroupBasis.Generated.Catalogue.S5_796.table.semigroup).mp valid

/-- The exact full joint invariant: parity, exact cuts, and first marker. -/
theorem reversedFixedHeadSignature
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    SameFixedHeadParitySeparatorSignature
      identity.lhs.reverse identity.rhs.reverse := by
  have rightSignature :=
    SemigroupBasis.CoRoots.S5_787FamilyInvariant.S5_796.valid_sameSignature
      identity.reversed (rightValidReversed identity rightValid)
  have originalParity :=
    SemigroupBasis.CoRoots.S5_441Invariant.sameOccurrenceParity_of_s3_11_valid
      identity leftValid
  have reversedParity :
      SemigroupBasis.CoRoots.S5_441Invariant.SameOccurrenceParity
        identity.lhs.reverse identity.rhs.reverse := by
    intro letter
    simpa [Word.toList_reverse, List.count_reverse] using
      originalParity letter
  exact
    ⟨⟨rightSignature.support, rightSignature.exactCuts, reversedParity⟩,
      rightSignature.first⟩

/-- Independent, unrestricted pair completeness for the EXACT frozen basis. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives targetBasis identity.lhs identity.rhs := by
  have reversedDerivation :=
    derivesOfSameFixedHeadParitySeparatorSignature
      (reversedFixedHeadSignature identity leftValid rightValid)
  simpa using reversedDerivation.reverse

/-- Actual pair completeness is proved before any quotient normalization. -/
def intersectionBasis :
    IntersectionBasis
      Rank001.leftTable.semigroup
      Rank001.rightTable.semigroup
      Rank001.basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

/-- Quotient normalization is strictly downstream of unrestricted completeness. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank001.leftTable.semigroup
      Rank001.rightTable.semigroup
      Rank001.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- Authenticated unrestricted representative orientation. -/
theorem representative_basis_S6_11228 :
    BasisFor Rank001.S6_11228.table.semigroup Rank001.basis :=
  Rank001.S6_11228.representative_basis_of_normalizer intersectionNormalizer

/-- Authenticated unrestricted literal reversed-basis opposite orientation. -/
theorem opposite_basis_S6_11228 :
    BasisFor Rank001.S6_11228.table.semigroup.opposite
      (reversedBasis Rank001.basis) :=
  Rank001.S6_11228.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_796Opposite
