import SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_798OppositeCore
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6Level2TierBHashE2c5e460

/-!
# Unrestricted authenticated D020 owner root by opposite-source transport

The existing e2c root is unrestricted for the ACTUAL ordinary pair
`S2_2 × S5_798`.  Its exact ordered law list agrees with the independently
checked adapter list.  Discharging that sole explicit conditional premise
instantiates the proven opposite transport and yields frozen owner B13.

Only the S1-owned S6_11233 class and its literal opposite are instantiated;
the separately owned S2_2 rank-020 S6_8865 class is not claimed.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_798Opposite

open SemigroupBasis

/-- All thirteen literal historical source laws agree in their exact order. -/
theorem sourceBasis_eq_historical :
    SeedS5_798OppositeAdapter.sourceBasis =
      SemigroupBasis.CoRoots.Order6Level2TierBHashE2c5e460.basis := by
  decide

/-- The exact unrestricted historical e2c pair supplies the sole premise of
the independently checked owner transport; no factor-theory equality. -/
def authenticatedSourceIntersection :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_798.table.semigroup
      SeedS5_798OppositeAdapter.sourceBasis := by
  rw [sourceBasis_eq_historical]
  exact
    SemigroupBasis.CoRoots.Order6Level2TierBHashE2c5e460.intersectionBasisS2_2S5_798

/-- Actual pair completeness is established before quotient normalization. -/
def intersectionBasis :
    IntersectionBasis
      Rank020.leftTable.semigroup
      Rank020.rightTable.semigroup
      Rank020.basis :=
  SeedS5_798OppositeCore.intersectionBasis_of_source
    authenticatedSourceIntersection

/-- Quotient normalization is strictly downstream of unrestricted proof. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank020.leftTable.semigroup
      Rank020.rightTable.semigroup
      Rank020.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- Authenticated exact S1-owned representative orientation. -/
theorem representative_basis_S6_11233 :
    BasisFor Rank020.S6_11233.table.semigroup Rank020.basis :=
  Rank020.S6_11233.representative_basis_of_normalizer intersectionNormalizer

/-- Authenticated exact S1-owned opposite with literal reversed B13. -/
theorem opposite_basis_S6_11233 :
    BasisFor Rank020.S6_11233.table.semigroup.opposite
      (reversedBasis Rank020.basis) :=
  Rank020.S6_11233.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_798Opposite
