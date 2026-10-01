import SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_203
import SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.CyclicRecordedSplice

open SemigroupBasis

abbrev targetBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.basis

/-- Consume the separately kernel-recorded owner proof at its exact factor boundary. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.rightTable.semigroup
      targetBasis :=
  SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_203.cyclicIntersectionBasis

/-- Quotient normalization remains strictly downstream of unrestricted completeness. -/
noncomputable def normalizer :
    IntersectionNormalizer
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.rightTable.semigroup
      targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_2852_representative_basis :
    BasisFor
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.S6_2852.table.semigroup
      targetBasis :=
  SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.S6_2852.representative_basis_of_normalizer
    normalizer

theorem s6_2852_opposite_basis :
    BasisFor
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.S6_2852.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.S6_2852.opposite_basis_of_normalizer
    normalizer

theorem s6_2890_representative_basis :
    BasisFor
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.S6_2890.table.semigroup
      targetBasis :=
  SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.S6_2890.representative_basis_of_normalizer
    normalizer

theorem s6_2890_opposite_basis :
    BasisFor
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.S6_2890.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.S6_2890.opposite_basis_of_normalizer
    normalizer

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.CyclicRecordedSplice
