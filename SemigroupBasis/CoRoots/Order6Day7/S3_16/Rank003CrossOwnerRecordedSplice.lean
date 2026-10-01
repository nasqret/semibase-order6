import SemigroupBasis.CoRoots.Order6Day7.S3_16.SeedS5_994OppositeTheoryBridge
import SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_1144

/-!
# Consume the independently recorded S1 intersection in S2's Rank003 bridge

S1 job 20964479 independently recorded the exact unrestricted
S3_11 x S5_1144 intersection. S2 already proved the actual unrestricted
cross-family factor-theory transfer for S3_16 x S5_994-op, with both
target classes conditional on precisely that owner premise.

The representation boundary is explicit: Generated.S3_11.table is not
definitionally the catalogue table, so its independently proved table
equality is rewritten before the concrete frozen-basis equality. This module
constructs the actual intersection before its quotient normalizer and then
instantiates the four owner-authored endpoint theorems.

Independent S1/S2 owner review is still required before any class recording.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.CrossOwnerRecordedSplice

open SemigroupBasis

abbrev targetBasis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.basis

/-- The two independently authenticated frozen eleven-law lists are exact. -/
theorem displayedBases_eq :
    SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank003.basis = targetBasis := by
  decide

/-- Transport the separately kernel-green owner intersection across the
named S3_11 representation boundary and the exact displayed-basis equality. -/
def recordedCharteredIntersection :
    IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.TheoryBridge.sourceParity
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.TheoryBridge.charteredBand
      targetBasis := by
  change
    IntersectionBasis
      SemigroupBasis.Generated.S3_11.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup
      targetBasis
  rw [SemigroupBasis.Generated.S3_11.table_eq_canonical_catalogue]
  rw [← displayedBases_eq]
  exact SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_1144.intersectionBasis

/-- Genuine unrestricted target completeness consumes the recorded owner
premise; no finite factor or conditional assumption is substituted. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.rightTable.semigroup
      targetBasis :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.TheoryBridge.targetIntersection_of_charteredSource
    recordedCharteredIntersection

/-- Quotient normalization is strictly downstream of target completeness. -/
noncomputable def normalizer :
    IntersectionNormalizer
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.rightTable.semigroup
      targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_14872_representative_basis :
    BasisFor
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.S6_14872.table.semigroup
      targetBasis :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.TheoryBridge.s6_14872_representative_basis_of_charteredSource
    recordedCharteredIntersection

theorem s6_14872_opposite_basis :
    BasisFor
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.S6_14872.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.TheoryBridge.s6_14872_opposite_basis_of_charteredSource
    recordedCharteredIntersection

theorem s6_14883_representative_basis :
    BasisFor
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.S6_14883.table.semigroup
      targetBasis :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.TheoryBridge.s6_14883_representative_basis_of_charteredSource
    recordedCharteredIntersection

theorem s6_14883_opposite_basis :
    BasisFor
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.S6_14883.table.semigroup.opposite
      (reversedBasis targetBasis) :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.TheoryBridge.s6_14883_opposite_basis_of_charteredSource
    recordedCharteredIntersection

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank003.CrossOwnerRecordedSplice
