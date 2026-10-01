import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opFordLord
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opS5_381Transfer
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15opS5_791Transfer

/-!
# Layer-C closure for the four `S3_15^op` pairs

The shared left profile stops before each right-factor-specific proof.  This
module only exposes the two remaining public quotient normalizers; the 788
and 794 normalizers retain their separate Ford--Lord constructions.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon

/-- Unrestricted proof-producing normalizer for the exact ten-law
`S3_15^op x S5_381` block. -/
noncomputable def normalizerS3_15opS5_381 :
    IntersectionNormalizer
      s3_15OppositeTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_381.table.semigroup
      basisS3_15opS5_381 :=
  LayerCCommon.IntersectionBasis.toQuotientNormalizer
    S3_15opS5_381.intersectionBasisS5_381

/-- Unrestricted proof-producing normalizer for the exact eleven-law
`S3_15^op x S5_791` block. -/
noncomputable def normalizerS3_15opS5_791 :
    IntersectionNormalizer
      s3_15OppositeTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_791.table.semigroup
      basisS3_15opS5_791 :=
  LayerCCommon.IntersectionBasis.toQuotientNormalizer
    S3_15opS5_791.intersectionBasisS5_791

end SemigroupBasis.CoRoots.Order6L3HeavyRank2
