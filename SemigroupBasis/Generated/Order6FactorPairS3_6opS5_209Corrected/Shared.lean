import SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Completeness

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Completeness

open SemigroupBasis

/- The completeness module currently develops its public declarations in the
`Order6FactorPairS3_6opS5_209Normal` namespace.  Keep the generated endpoints
on the module-named surface without changing that shared source file. -/

abbrev correctedBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Normal.correctedBasis

/-- Module-named bridge to the repaired thirteen-law intersection basis. -/
def correctedIntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_6.table.semigroup.opposite
      SemigroupBasis.Generated.S5_209.table.semigroup
      correctedBasis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Normal.correctedIntersectionBasis

end SemigroupBasis.CoRoots.Order6FactorPairS3_6opS5_209Completeness
