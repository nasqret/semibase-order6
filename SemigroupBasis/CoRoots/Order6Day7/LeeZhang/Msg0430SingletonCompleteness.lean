import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0430FixedHead

/-! Unrestricted completeness of the approved corrected S6_5603 six-law list.
The actual S3_15 factor fixes the full initial letter. The explicit law bridge
then reuses the kernel-green S2_4 x S5_207 seed and its reviewed transport.
The historical S6_5596 endpoint is not asserted to be S6_5603: the latter's
own literal split-subdirect maps were proved in Msg0430Presentation. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0430

open SemigroupBasis Examples

theorem singletonLeft_head (identity : Identity Nat)
    (valid : identity.SatisfiedBy singletonLeft.semigroup) :
    identity.lhs.head = identity.rhs.head :=
  leftNormalBandFifteenValid_head_eq identity valid

theorem singletonLeft_to_seed (identity : Identity Nat)
    (valid : identity.SatisfiedBy singletonLeft.semigroup) :
    identity.SatisfiedBy S2_4.Rank045.leftTable.semigroup := by
  have heads := singletonLeft_head identity valid
  change identity.SatisfiedBy leftZeroTwo.semigroup
  intro valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval, heads]

/-- Actual unrestricted proof, before constructing any endpoint interface. -/
theorem singleton_complete (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy singletonLeft.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives singletonBasis identity.lhs identity.rhs :=
  singletonFixedHeadRules.complete identity (singletonLeft_head identity leftValid) rightValid

def singletonIntersection : IntersectionBasis singletonLeft.semigroup rightTable.semigroup singletonBasis where
  leftModels := singletonLeftModels
  rightModels := singletonRightModels
  complete := singleton_complete

/-- Genuine source-to-target transport of the already-certified family seed. -/
noncomputable def singletonNormalizer : IntersectionNormalizer singletonLeft.semigroup rightTable.semigroup singletonBasis :=
  S2_4.Rank045.Seed.transportedNormalizer singletonFixedHeadRules.oldSeedLaw
    singletonLeft_to_seed (fun _ valid => valid)

theorem singleton5603_representative_basis : BasisFor table5603.semigroup singletonBasis :=
  singletonNormalizer.basisFor singletonLeftModels singletonRightModels subdirect5603

theorem singleton5603_opposite_basis : BasisFor table5603.semigroup.opposite (reversedBasis singletonBasis) :=
  singleton5603_representative_basis.oppositeReversed

theorem singleton5603_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table5603.semigroup) :
    Derives singletonBasis identity.lhs identity.rhs := singleton5603_representative_basis.2 identity valid

theorem singleton5603_opposite_complete (identity : Identity Nat) (valid : identity.SatisfiedBy table5603.semigroup.opposite) :
    Derives (reversedBasis singletonBasis) identity.lhs identity.rhs := singleton5603_opposite_basis.2 identity valid

def singletonOppositeIntersection :
    IntersectionBasis singletonLeft.semigroup.opposite rightTable.semigroup.opposite (reversedBasis singletonBasis) :=
  singletonIntersection.oppositeReversed

noncomputable def singletonOppositeNormalizer :
    IntersectionNormalizer singletonLeft.semigroup.opposite rightTable.semigroup.opposite (reversedBasis singletonBasis) :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer singletonOppositeIntersection

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0430
