import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered
import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004
import SemigroupBasis.Generated.S4_96TransfersLayer1
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal

/-!
# Owner-conditional proof-valued S3_16 collision twin, rank 004

This module proves actual two-way unrestricted right-factor identity-theory
equivalence using independently COMPLETE released lower-order bases. Every
intersection-basis transport and endpoint requires an EXPLICIT independently
proved S2 owner seed; no finite table alone establishes completeness.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002SiblingTransport

open SemigroupBasis


theorem rightIdentityTheory (identity : Identity Nat) :
    identity.SatisfiedBy SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.rightTable.semigroup ↔
      identity.SatisfiedBy SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.rightTable.semigroup := by
  constructor
  · intro valid
    have targetDerivation :
        Derives SemigroupBasis.Generated.S4_96Transfers.S5_997.transferBasis
          identity.lhs identity.rhs :=
      SemigroupBasis.Generated.S4_96Transfers.S5_997.transferred_basis.2
        identity valid
    have sourceModels :
        Models SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.rightTable.semigroup
          SemigroupBasis.Generated.S4_96Transfers.S5_997.transferBasis :=
      SemigroupBasis.Generated.S4_96.representative_basis.1
    exact Derives.sound sourceModels targetDerivation
  · intro valid
    have sourceDerivation :
        Derives SemigroupBasis.Examples.affineParityFourBasis
          identity.lhs identity.rhs :=
      SemigroupBasis.Generated.S4_96.representative_basis.2 identity valid
    have targetModels :
        Models SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.rightTable.semigroup
          SemigroupBasis.Examples.affineParityFourBasis :=
      SemigroupBasis.Generated.S4_96Transfers.S5_997.transferred_basis.1
    exact Derives.sound targetModels sourceDerivation

def recoveredIntersectionBasis
    (sourceBasis : IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.basis) :
    IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.basis where
  leftModels := SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.leftModels
  rightModels := SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.rightModels
  complete := by
    intro identity leftValid rightValid
    have sourceLeft :
        identity.SatisfiedBy SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.leftTable.semigroup := leftValid
    have sourceRight :
        identity.SatisfiedBy SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.rightTable.semigroup :=
      (rightIdentityTheory identity).mp rightValid
    have sourceDerivation := sourceBasis.complete identity sourceLeft sourceRight
    have sameBasis : SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.basis = SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.basis := by decide
    rw [sameBasis]
    exact sourceDerivation

def survivingIntersectionBasis
    (sourceBasis : IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.basis) :
    IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.basis where
  leftModels := SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.leftModels
  rightModels := SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.rightModels
  complete := by
    intro identity leftValid rightValid
    have targetLeft :
        identity.SatisfiedBy SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.leftTable.semigroup := leftValid
    have targetRight :
        identity.SatisfiedBy SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.rightTable.semigroup :=
      (rightIdentityTheory identity).mpr rightValid
    have targetDerivation := sourceBasis.complete identity targetLeft targetRight
    have sameBasis : SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.basis = SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.basis := by decide
    rw [← sameBasis]
    exact targetDerivation

noncomputable def recoveredIntersectionNormalizer
    (sourceBasis : IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.basis) :
    IntersectionNormalizer
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    (recoveredIntersectionBasis sourceBasis)

noncomputable def survivingIntersectionNormalizer
    (sourceBasis : IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.basis) :
    IntersectionNormalizer
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    (survivingIntersectionBasis sourceBasis)


theorem recovered_representative_basis_S6_14887
    (sourceBasis : IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.basis) :
    BasisFor SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.S6_14887.table.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.basis :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.S6_14887.representative_basis_of_normalizer
    (recoveredIntersectionNormalizer sourceBasis)

theorem recovered_opposite_basis_S6_14887
    (sourceBasis : IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.basis) :
    BasisFor SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.S6_14887.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.basis) :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.S6_14887.opposite_basis_of_normalizer
    (recoveredIntersectionNormalizer sourceBasis)

theorem recovered_representative_basis_S6_14888
    (sourceBasis : IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.basis) :
    BasisFor SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.S6_14888.table.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.basis :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.S6_14888.representative_basis_of_normalizer
    (recoveredIntersectionNormalizer sourceBasis)

theorem recovered_opposite_basis_S6_14888
    (sourceBasis : IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.basis) :
    BasisFor SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.S6_14888.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.basis) :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.S6_14888.opposite_basis_of_normalizer
    (recoveredIntersectionNormalizer sourceBasis)

theorem surviving_representative_basis_S6_14895
    (sourceBasis : IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.basis) :
    BasisFor SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.S6_14895.table.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.basis :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.S6_14895.representative_basis_of_normalizer
    (survivingIntersectionNormalizer sourceBasis)

theorem surviving_opposite_basis_S6_14895
    (sourceBasis : IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002Recovered.basis) :
    BasisFor SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.S6_14895.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.basis) :=
  SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004.S6_14895.opposite_basis_of_normalizer
    (survivingIntersectionNormalizer sourceBasis)

end SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004Pair002SiblingTransport
