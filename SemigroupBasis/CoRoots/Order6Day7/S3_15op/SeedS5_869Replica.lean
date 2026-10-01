import SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered
import SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_871
import SemigroupBasis.CoRoots.S5_869Family

/-!
# Proof-valued collision replica: S3_15op x S5_869

The source and target right factors have the SAME independently kernel-green,
complete lower-order basis. The actual unrestricted identity-theory
equivalence is proved below before transporting the existing intersection
completeness. The quotient normalizer is introduced only AFTER the new
intersection basis is complete. No finite table check is used as a theory
implication, and the frozen rank namespace is never overwritten.
-/

namespace SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_869Replica

open SemigroupBasis

/-- Both semantic directions follow from the sealed common COMPLETE lower
factor basis; this is an actual unrestricted theory transport. -/
theorem rightIdentityTheory (identity : Identity Nat) :
    identity.SatisfiedBy SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.rightTable.semigroup ↔
      identity.SatisfiedBy SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028.rightTable.semigroup := by
  constructor
  · intro valid
    exact Derives.sound SemigroupBasis.CoRoots.S5_869Family.S5_871.basis_complete.1
      (SemigroupBasis.CoRoots.S5_869Family.S5_869.basis_complete.2 identity valid)
  · intro valid
    exact Derives.sound SemigroupBasis.CoRoots.S5_869Family.S5_869.basis_complete.1
      (SemigroupBasis.CoRoots.S5_869Family.S5_871.basis_complete.2 identity valid)

/-- The recovered displayed basis is syntactically the same frozen rank
basis, and completeness is transported through the PROVED semantic field. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.leftTable.semigroup)
    (rightValid : identity.SatisfiedBy SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.rightTable.semigroup) :
    Derives SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.basis identity.lhs identity.rhs := by
  have sourceLeft :
      identity.SatisfiedBy SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028.leftTable.semigroup :=
    leftValid
  have sourceRight :
      identity.SatisfiedBy SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028.rightTable.semigroup :=
    (rightIdentityTheory identity).mp rightValid
  have sourceDerivation :=
    SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_871.intersectionBasis.complete
      identity sourceLeft sourceRight
  have sameBasis : SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.basis = SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028.basis := by
    decide
  rw [sameBasis]
  exact sourceDerivation

/-- Independent unrestricted intersection basis, assembled BEFORE any
quotient normalizer is introduced. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.basis where
  leftModels := SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.leftModels
  rightModels := SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.rightModels
  complete := derivesOfFactorValid

/-- Quotient normalization is downstream of independently proved exact
intersection completeness; it cannot be a premise of that proof. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem representative_basis_S6_13752 :
    BasisFor SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.S6_13752.table.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.basis :=
  SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.S6_13752.representative_basis_of_normalizer
    intersectionNormalizer

theorem opposite_basis_S6_13752 :
    BasisFor SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.S6_13752.table.semigroup.opposite
      (reversedBasis SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.basis) :=
  SemigroupBasis.CoRoots.Order6Day7.S3_15op.Rank028Pair004Recovered.S6_13752.opposite_basis_of_normalizer
    intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_15op.SeedS5_869Replica
