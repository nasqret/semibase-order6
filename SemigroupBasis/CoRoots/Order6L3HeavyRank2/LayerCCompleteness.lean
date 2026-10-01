import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_11S5_788Completeness
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15S4_96Completeness
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_15op

/-!
# Six unrestricted heavy rank-two intersection completeness values

Each declaration binds the exact immutable Layer-A displayed basis, its two
already certified finite-factor model theorems, and an independently proved
arbitrary-word `IntersectionNormalizer`. No oracle window, fixed alphabet,
bounded derivation, or factor-separation assumption is used.

The five-class `S3_15 × S4_96` family retains its isolated seven-law bridge;
the four opposite-left families retain their four independent right-factor
proof engines; and `S3_11 × S5_788` retains the anchored exact-cut normal.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2

open SemigroupBasis

/-- Public alias for the unrestricted anchored C2 normalizer. -/
def normalizerS3_11S5_788 :
    IntersectionNormalizer
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup
      basisS3_11S5_788 :=
  S3_11S5_788.intersectionNormalizer

/-- The exact eighteen-law C2 factor-intersection basis. -/
def intersectionBasisS3_11S5_788 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup
      basisS3_11S5_788 :=
  normalizerS3_11S5_788.toIntersectionBasis
    basisS3_11S5_788_left_models basisS3_11S5_788_right_models

/-- The exact fourteen-law first opposite-left factor-intersection basis. -/
noncomputable def intersectionBasisS3_15opS5_788 :
    IntersectionBasis
      s3_15OppositeTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup
      basisS3_15opS5_788 :=
  normalizerS3_15opS5_788.toIntersectionBasis
    basisS3_15opS5_788_left_models basisS3_15opS5_788_right_models

/-- The exact bridge-patched seven-law isolated factor-intersection basis. -/
noncomputable def intersectionBasisS3_15S4_96 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Generated.S4_96.table.semigroup
      basisS3_15S4_96 :=
  normalizerS3_15S4_96.toIntersectionBasis
    basisS3_15S4_96_left_models basisS3_15S4_96_right_models

/-- The exact eight-law second opposite-left factor-intersection basis. -/
noncomputable def intersectionBasisS3_15opS5_794 :
    IntersectionBasis
      s3_15OppositeTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup
      basisS3_15opS5_794 :=
  normalizerS3_15opS5_794.toIntersectionBasis
    basisS3_15opS5_794_left_models basisS3_15opS5_794_right_models

/-- The exact ten-law third opposite-left factor-intersection basis. -/
noncomputable def intersectionBasisS3_15opS5_381 :
    IntersectionBasis
      s3_15OppositeTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_381.table.semigroup
      basisS3_15opS5_381 :=
  normalizerS3_15opS5_381.toIntersectionBasis
    basisS3_15opS5_381_left_models basisS3_15opS5_381_right_models

/-- The exact eleven-law fourth opposite-left factor-intersection basis. -/
noncomputable def intersectionBasisS3_15opS5_791 :
    IntersectionBasis
      s3_15OppositeTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_791.table.semigroup
      basisS3_15opS5_791 :=
  normalizerS3_15opS5_791.toIntersectionBasis
    basisS3_15opS5_791_left_models basisS3_15opS5_791_right_models

/-- Every authenticated subdirect representative of the C2 factors inherits
the literal eighteen-law unrestricted basis. -/
theorem basisForS3_11S5_788
    {A : Type u} {G : Semigroup A}
    (pair : SubdirectPair G
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup) :
    BasisFor G basisS3_11S5_788 :=
  intersectionBasisS3_11S5_788.basisFor pair

/-- Every authenticated first opposite-left representative inherits the
literal fourteen-law unrestricted basis. -/
theorem basisForS3_15opS5_788
    {A : Type u} {G : Semigroup A}
    (pair : SubdirectPair G
      s3_15OppositeTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup) :
    BasisFor G basisS3_15opS5_788 :=
  intersectionBasisS3_15opS5_788.basisFor pair

/-- Every authenticated isolated representative inherits all seven laws,
including the explicit `xxyzxy = xyxzxy` bridge. -/
theorem basisForS3_15S4_96
    {A : Type u} {G : Semigroup A}
    (pair : SubdirectPair G
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Generated.S4_96.table.semigroup) :
    BasisFor G basisS3_15S4_96 :=
  intersectionBasisS3_15S4_96.basisFor pair

/-- Every authenticated second opposite-left representative inherits the
literal eight-law unrestricted basis. -/
theorem basisForS3_15opS5_794
    {A : Type u} {G : Semigroup A}
    (pair : SubdirectPair G
      s3_15OppositeTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup) :
    BasisFor G basisS3_15opS5_794 :=
  intersectionBasisS3_15opS5_794.basisFor pair

/-- Every authenticated third opposite-left representative inherits the
literal ten-law unrestricted basis. -/
theorem basisForS3_15opS5_381
    {A : Type u} {G : Semigroup A}
    (pair : SubdirectPair G
      s3_15OppositeTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_381.table.semigroup) :
    BasisFor G basisS3_15opS5_381 :=
  intersectionBasisS3_15opS5_381.basisFor pair

/-- Every authenticated fourth opposite-left representative inherits the
literal eleven-law unrestricted basis. -/
theorem basisForS3_15opS5_791
    {A : Type u} {G : Semigroup A}
    (pair : SubdirectPair G
      s3_15OppositeTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_791.table.semigroup) :
    BasisFor G basisS3_15opS5_791 :=
  intersectionBasisS3_15opS5_791.basisFor pair

end SemigroupBasis.CoRoots.Order6L3HeavyRank2
