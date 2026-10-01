import SemigroupBasis.Generated.Order6S5_107ParityKernel.Shared

namespace SemigroupBasis.Generated.Order6Level2TierBHash86393.Shared

open SemigroupBasis

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.Generated.Order6S5_107ParityKernel.Shared.basis

theorem basis_length : basis.length = 19 :=
  SemigroupBasis.Generated.Order6S5_107ParityKernel.Shared.basis_length

def intersectionBasisS2_2S5_107 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup basis :=
  SemigroupBasis.Generated.Order6S5_107ParityKernel.Shared.s2S5IntersectionBasis

def intersectionBasisS2_2S5_108 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.intersectionBasisOfSameRightTheory
    intersectionBasisS2_2S5_107
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.sameTheoryS5_107S5_108

def intersectionBasisS2_2S5_108Opposite :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup.opposite
      basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.intersectionBasisOfSameRightTheory
    intersectionBasisS2_2S5_107
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.sameTheoryS5_107S5_108Opposite

def intersectionBasisS2_2S5_109 :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_109.table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.intersectionBasisOfSameRightTheory
    intersectionBasisS2_2S5_107
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.sameTheoryS5_107S5_109

def intersectionBasisS3_11S5_107 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_107.table.semigroup basis :=
  SemigroupBasis.Generated.Order6S5_107ParityKernel.Shared.s3S5IntersectionBasis

def intersectionBasisS3_11S5_108 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.intersectionBasisOfSameRightTheory
    intersectionBasisS3_11S5_107
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.sameTheoryS5_107S5_108

def intersectionBasisS3_11S5_109 :
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_109.table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.intersectionBasisOfSameRightTheory
    intersectionBasisS3_11S5_107
    SemigroupBasis.CoRoots.Order6FactorPairS2S5107Prelude.sameTheoryS5_107S5_109

end SemigroupBasis.Generated.Order6Level2TierBHash86393.Shared
