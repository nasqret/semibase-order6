import SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered
import SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030
import SemigroupBasis.CoRoots.S5_83Family
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal

/-!
# Conditional proof-valued collision twin: S3_4 x S5_83 / S5_84

The shared lower-order basis is already COMPLETE for both right factors.
This module proves their actual unrestricted semantic equivalence and both
directions of intersection-basis transport. Every endpoint retains an explicit
OWNER-PROVED unrestricted intersection basis as a premise; this source does
not invent a seed, assert an unconditional endpoint, or claim class closure.
The quotient normalizer is constructed only after intersection completeness.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004SiblingTransport

open SemigroupBasis

/-- Genuine two-way unrestricted right-factor identity equivalence, proved
from the existing COMPLETE common lower-order basis. -/
theorem rightIdentityTheory (identity : Identity Nat) :
    identity.SatisfiedBy SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.rightTable.semigroup ↔
      identity.SatisfiedBy SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.rightTable.semigroup := by
  constructor
  · intro valid
    exact Derives.sound SemigroupBasis.CoRoots.S5_83Family.S5_84.basis_complete.1
      (SemigroupBasis.CoRoots.S5_83Family.S5_83.basis_complete.2 identity valid)
  · intro valid
    exact Derives.sound SemigroupBasis.CoRoots.S5_83Family.S5_83.basis_complete.1
      (SemigroupBasis.CoRoots.S5_83Family.S5_84.basis_complete.2 identity valid)

/-- Transport an ACTUALLY PROVED surviving unrestricted owner seed into the
recovered namespace; no proof is obtained without that explicit premise. -/
def recoveredIntersectionBasis
    (sourceBasis : IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.basis) :
    IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.basis where
  leftModels := SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.leftModels
  rightModels := SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.rightModels
  complete := by
    intro identity leftValid rightValid
    have sourceLeft :
        identity.SatisfiedBy SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.leftTable.semigroup :=
      leftValid
    have sourceRight :
        identity.SatisfiedBy SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.rightTable.semigroup :=
      (rightIdentityTheory identity).mp rightValid
    have sourceDerivation :=
      sourceBasis.complete identity sourceLeft sourceRight
    have sameBasis :
        SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.basis = SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.basis := by
      decide
    rw [sameBasis]
    exact sourceDerivation

/-- The reverse transport is equally genuine and retains an independently
proved recovered owner intersection basis as its explicit premise. -/
def survivingIntersectionBasis
    (sourceBasis : IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.basis) :
    IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.basis where
  leftModels := SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.leftModels
  rightModels := SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.rightModels
  complete := by
    intro identity leftValid rightValid
    have targetLeft :
        identity.SatisfiedBy SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.leftTable.semigroup :=
      leftValid
    have targetRight :
        identity.SatisfiedBy SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.rightTable.semigroup :=
      (rightIdentityTheory identity).mpr rightValid
    have targetDerivation :=
      sourceBasis.complete identity targetLeft targetRight
    have sameBasis :
        SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.basis = SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.basis := by
      decide
    rw [← sameBasis]
    exact targetDerivation

noncomputable def recoveredIntersectionNormalizer
    (sourceBasis : IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.basis) :
    IntersectionNormalizer
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    (recoveredIntersectionBasis sourceBasis)

noncomputable def survivingIntersectionNormalizer
    (sourceBasis : IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.basis) :
    IntersectionNormalizer
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    (survivingIntersectionBasis sourceBasis)


theorem recovered_representative_basis_S6_2638
    (sourceBasis : IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.basis) :
    BasisFor SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.S6_2638.table.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.basis :=
  SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.S6_2638.representative_basis_of_normalizer
    (recoveredIntersectionNormalizer sourceBasis)

theorem recovered_opposite_basis_S6_2638
    (sourceBasis : IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.basis) :
    BasisFor SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.S6_2638.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.basis) :=
  SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.S6_2638.opposite_basis_of_normalizer
    (recoveredIntersectionNormalizer sourceBasis)

theorem surviving_representative_basis_S6_2639
    (sourceBasis : IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.basis) :
    BasisFor SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.S6_2639.table.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.basis :=
  SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.S6_2639.representative_basis_of_normalizer
    (survivingIntersectionNormalizer sourceBasis)

theorem surviving_opposite_basis_S6_2639
    (sourceBasis : IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004Recovered.basis) :
    BasisFor SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.S6_2639.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.basis) :=
  SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030.S6_2639.opposite_basis_of_normalizer
    (survivingIntersectionNormalizer sourceBasis)

end SemigroupBasis.CoRoots.Order6Day7.S3_4.Rank030Pair004SiblingTransport
