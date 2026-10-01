import SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_516DualCore
import SemigroupBasis.CoRoots.Order6FactorPairS2S5196Intersection
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal

/-!
# Actual unrestricted S3_11 × S5_516 rank-043 owner intersection

The ten-law historical `C2 × S5_196` root is a genuine unrestricted
intersection basis, not a finite witness.  S5_516 validity is transported
through its exact semantic classification and reverse-word duality; all ten
reversed root axioms are independently replayed by sixteen frozen displayed
edges.  Only after the resulting owner intersection is complete is its
quotient normalizer constructed and the four exact owner endpoints exported.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_516

open SemigroupBasis

/-- The independently materialized adapter list is the literal historical B10. -/
theorem historicalSourceBasis_eq :
    SeedS5_516DualAdapter.sourceBasis =
      SemigroupBasis.CoRoots.Order6FactorPairS2S5196Intersection.basis := by
  decide

/-- Discharge the one explicit unrestricted cyclic/196 root premise. -/
def historicalSourceIntersection :
    IntersectionBasis
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup
      SeedS5_516DualAdapter.sourceBasis := by
  rw [historicalSourceBasis_eq]
  exact
    SemigroupBasis.CoRoots.Order6FactorPairS2S5196Intersection.intersectionBasis

/-- Genuine unrestricted owner-factor completeness for the exact frozen B10. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Rank043.leftTable.semigroup)
    (rightValid : identity.SatisfiedBy Rank043.rightTable.semigroup) :
    Derives Rank043.basis identity.lhs identity.rhs :=
  SeedS5_516DualCore.derivesOfFactorValid
    historicalSourceIntersection identity leftValid rightValid

/-- The owner intersection is proved before any quotient normalizer. -/
def intersectionBasis :
    IntersectionBasis
      Rank043.leftTable.semigroup
      Rank043.rightTable.semigroup
      Rank043.basis where
  leftModels := Rank043.leftModels
  rightModels := Rank043.rightModels
  complete := derivesOfFactorValid

/-- Quotient normalization is strictly downstream of actual completeness. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank043.leftTable.semigroup
      Rank043.rightTable.semigroup
      Rank043.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- First authenticated owner representative orientation. -/
theorem representative_basis_S6_5498 :
    BasisFor Rank043.S6_5498.table.semigroup Rank043.basis :=
  Rank043.S6_5498.representative_basis_of_normalizer intersectionNormalizer

/-- First authenticated owner literal reversed-basis opposite orientation. -/
theorem opposite_basis_S6_5498 :
    BasisFor Rank043.S6_5498.table.semigroup.opposite
      (reversedBasis Rank043.basis) :=
  Rank043.S6_5498.opposite_basis_of_normalizer intersectionNormalizer

/-- Second authenticated owner representative orientation. -/
theorem representative_basis_S6_5509 :
    BasisFor Rank043.S6_5509.table.semigroup Rank043.basis :=
  Rank043.S6_5509.representative_basis_of_normalizer intersectionNormalizer

/-- Second authenticated owner literal reversed-basis opposite orientation. -/
theorem opposite_basis_S6_5509 :
    BasisFor Rank043.S6_5509.table.semigroup.opposite
      (reversedBasis Rank043.basis) :=
  Rank043.S6_5509.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_516
