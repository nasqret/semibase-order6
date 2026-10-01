import SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_207
import SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.CyclicRecordedSplice

open SemigroupBasis

abbrev targetBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.basis

/-- Consume S1's independently kernel-recorded auxiliary cyclic intersection. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.rightTable.semigroup
      targetBasis :=
  SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_207.cyclicIntersectionBasis

/-- Quotient normalization is downstream of the exact unrestricted intersection. -/
noncomputable def normalizer :
    IntersectionNormalizer
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.rightTable.semigroup
      targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_2854_representative_basis :
    BasisFor
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.S6_2854.table.semigroup
      targetBasis :=
  SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.S6_2854.representative_basis_of_normalizer
    normalizer

theorem s6_2854_opposite_basis :
    BasisFor
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.S6_2854.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.S6_2854.opposite_basis_of_normalizer
    normalizer

theorem s6_2892_representative_basis :
    BasisFor
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.S6_2892.table.semigroup
      targetBasis :=
  SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.S6_2892.representative_basis_of_normalizer
    normalizer

theorem s6_2892_opposite_basis :
    BasisFor
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.S6_2892.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.S6_2892.opposite_basis_of_normalizer
    normalizer

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank009.CyclicRecordedSplice
