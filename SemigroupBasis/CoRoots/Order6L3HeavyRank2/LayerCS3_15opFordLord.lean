import SemigroupBasis.CoRoots.Order6FordLord1ccaRelativeTransfer
import SemigroupBasis.CoRoots.Order6FordLordAe8DualTransfer
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.Blocks
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal

/-!
# Layer-C normalizers for the two Ford--Lord `S3_15^op` pairs

The two displayed bases are kept separate.  Their unrestricted completeness
engines are the existing `1cca` and corrected `ae8` structural transfers;
this file only binds those engines to the exact rank-two basis blocks and
refines each one to the public `IntersectionNormalizer` interface.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon

/-! ## `S3_15^op x S5_788` -/

theorem basisS3_15opS5_788_eq_displayed :
    basisS3_15opS5_788 =
      SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_1ccaef90de83de0a.basis := by
  decide

private def intersectionS3_15opS5_788 :
    IntersectionBasis
      s3_15OppositeTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup
      basisS3_15opS5_788 := by
  change IntersectionBasis
    SemigroupBasis.Generated.S3_15.table.semigroup.opposite
    SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup
    basisS3_15opS5_788
  rw [basisS3_15opS5_788_eq_displayed]
  exact
    SemigroupBasis.CoRoots.Order6FordLord1ccaRelativeTransfer.intersectionBasisS5_788

/-- Unrestricted proof-producing normalizer for the exact fourteen-law
`S3_15^op x S5_788` block. -/
noncomputable def normalizerS3_15opS5_788 :
    IntersectionNormalizer
      s3_15OppositeTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup
      basisS3_15opS5_788 :=
  LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionS3_15opS5_788

/-! ## `S3_15^op x S5_794` -/

theorem basisS3_15opS5_794_eq_displayed :
    basisS3_15opS5_794 =
      SemigroupBasis.Generated.Order6OneLocalFordLord.DisplayedSigma.Sigma_ae8f21b57d380dc3.basis := by
  decide

private def intersectionS3_15opS5_794 :
    IntersectionBasis
      s3_15OppositeTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup
      basisS3_15opS5_794 := by
  change IntersectionBasis
    SemigroupBasis.Generated.S3_15.table.semigroup.opposite
    SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup
    basisS3_15opS5_794
  rw [basisS3_15opS5_794_eq_displayed]
  exact
    SemigroupBasis.CoRoots.Order6FordLordAe8DualTransfer.intersectionBasisS5_794

/-- Unrestricted proof-producing normalizer for the exact eight-law
`S3_15^op x S5_794` block. -/
noncomputable def normalizerS3_15opS5_794 :
    IntersectionNormalizer
      s3_15OppositeTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup
      basisS3_15opS5_794 :=
  LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionS3_15opS5_794

end SemigroupBasis.CoRoots.Order6L3HeavyRank2
