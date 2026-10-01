import SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Completeness

namespace SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Completeness

open SemigroupBasis

/- The completeness module develops its declarations in the
`Order6FactorPairS2_4S5_209Normal` namespace. Keep the generated endpoints on
the module-named surface without changing that shared source file. -/

abbrev correctedBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Normal.correctedBasis

def intersectionS2_4S5_209 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.S5_209.table.semigroup
      correctedBasis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Normal.intersectionS2_4S5_209

def intersectionS2_4S5_211 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_211.table.semigroup
      correctedBasis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Normal.intersectionS2_4S5_211

def intersectionS2_4S5_500 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_4.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_500.table.semigroup
      correctedBasis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Normal.intersectionS2_4S5_500

def intersectionS3_15S5_209 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Generated.S5_209.table.semigroup
      correctedBasis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Normal.intersectionS3_15S5_209

def intersectionS3_15S5_211 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_211.table.semigroup
      correctedBasis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Normal.intersectionS3_15S5_211

def intersectionS3_15S5_500 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_15.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_500.table.semigroup
      correctedBasis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Normal.intersectionS3_15S5_500

end SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_209Completeness
