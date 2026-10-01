import SemigroupBasis.CoRoots.Order6Day7.LeeZhang.Msg0490FordOnlyNormalization
import SemigroupBasis.CoRoots.Order6Day7.S3_16.Rank004AffineOwnerDiagnostic
import SemigroupBasis.Generated.S5_201
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer

/-! Genuine unbounded semantic necessity, a certified C1 intersection seed,
and unconditional endpoints for the two already supplied split pairs.
All fixed table proofs and factor-separation results are imported unchanged. -/

namespace SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordOnly

open SemigroupBasis Examples Order6Sunday

theorem signature_of_example_valid (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftRegularBandThree.semigroup)
    (rightValid : identity.SatisfiedBy commutativeCappedSupportFive.semigroup) :
    Signature identity.lhs.toList identity.rhs.toList where
  order := S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq identity leftValid
  counts := cappedSupportValid_cappedCountTwo identity rightValid
  length := cappedSupportValid_cappedLengthThree identity rightValid

def exampleNormalizer :
    IntersectionNormalizer leftRegularBandThree.semigroup commutativeCappedSupportFive.semigroup basis where
  normal := normal
  derives_normal := derives_normal
  normal_eq_of_factor_valid := fun identity leftValid rightValid =>
    normal_eq_of_signature (signature_of_example_valid identity leftValid rightValid)

theorem exampleLeft_of_catalogue (identity : Identity Nat)
    (valid : identity.SatisfiedBy Generated.Catalogue.S3_16.table.semigroup) :
    identity.SatisfiedBy leftRegularBandThree.semigroup :=
  S3_16.Rank004.AffineOwnerDiagnostic.canonicalLeftIntoActual.pullback_identity identity valid

theorem exampleRight_of_catalogue (identity : Identity Nat)
    (valid : identity.SatisfiedBy Generated.Catalogue.S5_201.table.semigroup) :
    identity.SatisfiedBy commutativeCappedSupportFive.semigroup := by
  change identity.SatisfiedBy Generated.S5_201.table.semigroup
  rw [Generated.S5_201.table_eq_canonical_catalogue]
  exact valid

/-- Use the shared kernel-green transport on actual unrestricted implications. -/
def catalogueNormalizer :
    IntersectionNormalizer Generated.Catalogue.S3_16.table.semigroup
      Generated.Catalogue.S5_201.table.semigroup basis :=
  Order6L3HeavyRank2.LayerCCommon.transportNormalizer exampleNormalizer
    (fun _ member => Derives.fromBasis member)
    exampleLeft_of_catalogue exampleRight_of_catalogue

theorem leftModels : Models Generated.Catalogue.S3_16.table.semigroup basis := by
  intro identity member
  exact L6FordOnly.Sigma09a2Finite.S6_5553.ontoLeft.pushforwardIdentity identity
    (FordOnlyExactFinite.S6_5553.models identity member)

theorem rightModels : Models Generated.Catalogue.S5_201.table.semigroup basis := by
  intro identity member
  exact L6FordOnly.Sigma09a2Finite.S6_5553.ontoRight.pushforwardIdentity identity
    (FordOnlyExactFinite.S6_5553.models identity member)

def intersectionBasis :
    IntersectionBasis Generated.Catalogue.S3_16.table.semigroup
      Generated.Catalogue.S5_201.table.semigroup basis :=
  catalogueNormalizer.toIntersectionBasis leftModels rightModels

theorem representative_basis5553 :
    BasisFor L6FordOnly.Sigma09a2Finite.S6_5553.table.semigroup basis :=
  intersectionBasis.basisFor L6FordOnly.Sigma09a2Finite.S6_5553.pair

theorem opposite_basis5553 :
    BasisFor L6FordOnly.Sigma09a2Finite.S6_5553.table.semigroup.opposite (reversedBasis basis) :=
  representative_basis5553.oppositeReversed

theorem representative_basis9546 :
    BasisFor L6FordOnly.Sigma09a2Finite.S6_9546.table.semigroup basis :=
  intersectionBasis.basisFor L6FordOnly.Sigma09a2Finite.S6_9546.pair

theorem opposite_basis9546 :
    BasisFor L6FordOnly.Sigma09a2Finite.S6_9546.table.semigroup.opposite (reversedBasis basis) :=
  representative_basis9546.oppositeReversed

theorem signature_of_factor_valid (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Generated.Catalogue.S3_16.table.semigroup)
    (rightValid : identity.SatisfiedBy Generated.Catalogue.S5_201.table.semigroup) :
    Signature identity.lhs.toList identity.rhs.toList :=
  signature_of_example_valid identity (exampleLeft_of_catalogue identity leftValid)
    (exampleRight_of_catalogue identity rightValid)

theorem signature_of_valid5553 (identity : Identity Nat)
    (valid : identity.SatisfiedBy L6FordOnly.Sigma09a2Finite.S6_5553.table.semigroup) :
    Signature identity.lhs.toList identity.rhs.toList :=
  signature_of_factor_valid identity
    (L6FordOnly.Sigma09a2Finite.S6_5553.ontoLeft.pushforwardIdentity identity valid)
    (L6FordOnly.Sigma09a2Finite.S6_5553.ontoRight.pushforwardIdentity identity valid)

theorem signature_of_valid9546 (identity : Identity Nat)
    (valid : identity.SatisfiedBy L6FordOnly.Sigma09a2Finite.S6_9546.table.semigroup) :
    Signature identity.lhs.toList identity.rhs.toList :=
  signature_of_factor_valid identity
    (L6FordOnly.Sigma09a2Finite.S6_9546.ontoLeft.pushforwardIdentity identity valid)
    (L6FordOnly.Sigma09a2Finite.S6_9546.ontoRight.pushforwardIdentity identity valid)

theorem valid_iff_signature5553 (identity : Identity Nat) :
    identity.SatisfiedBy L6FordOnly.Sigma09a2Finite.S6_5553.table.semigroup ↔
      Signature identity.lhs.toList identity.rhs.toList :=
  ⟨signature_of_valid5553 identity,
    fun same => Derives.sound representative_basis5553.1 (derives_of_signature same)⟩

theorem valid_iff_signature9546 (identity : Identity Nat) :
    identity.SatisfiedBy L6FordOnly.Sigma09a2Finite.S6_9546.table.semigroup ↔
      Signature identity.lhs.toList identity.rhs.toList :=
  ⟨signature_of_valid9546 identity,
    fun same => Derives.sound representative_basis9546.1 (derives_of_signature same)⟩

end SemigroupBasis.CoRoots.Order6Day7.LeeZhang.FordOnly
