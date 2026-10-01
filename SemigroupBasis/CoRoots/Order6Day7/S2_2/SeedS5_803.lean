import SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank001
import SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_796Opposite
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCTransportNormalizer
import SemigroupBasis.CoRoots.S5_803

/-!
# First unrestricted authenticated `S2_2` family seed

The independently kernel-green `S3_11 × S5_796ᵒᵖ` owner proof establishes
unrestricted completeness for the same literal seventeen-law list whenever
the reversed words share support, exact separator cuts, occurrence parity,
and their initial variable.  The actual `S2_2` factor independently supplies
occurrence parity, while the actual `S5_803` factor independently supplies
the reversed separator/first signature.  No equality or inclusion of the two
factor-pair theories is asserted.

The exact frozen rank-001 pair is completed before quotient normalization.
Both orientations of both authenticated six-element classes are then
unconditional. Independent class-kernel recording, acceptance, and sealing
remain outside this source-level proof.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank001.Seed

open SemigroupBasis

universe u v

/-- The protected S1 owner basis and the frozen S2 target basis are literally
the same ordered list of seventeen displayed identities. -/
theorem ownerDisplayedBasis_eq_target :
    SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank001.basis = basis := by
  decide

/-- The actual cyclic two-element left factor supplies unrestricted
occurrence parity; reversing words preserves every individual count. -/
theorem reversedOccurrenceParity
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftTable.semigroup) :
    SemigroupBasis.CoRoots.S5_441Invariant.SameOccurrenceParity
      identity.lhs.reverse identity.rhs.reverse := by
  have originalParity :=
    SemigroupBasis.CoRoots.S5_441Invariant.sameOccurrenceParity_of_s2_2_valid
      identity valid
  intro letter
  simpa [Word.toList_reverse, List.count_reverse] using
    originalParity letter

/-- Combine the independently obtained ACTUAL cyclic-factor parity and
ACTUAL `S5_803` separator/first signature at exactly the shared S1 proof
interface; no factor-theory identification is used. -/
theorem reversedFixedHeadParitySeparatorSignature
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_796Opposite.SameFixedHeadParitySeparatorSignature
      identity.lhs.reverse identity.rhs.reverse := by
  have rightSignature :=
    SemigroupBasis.CoRoots.S5_803.valid_reversed_signature
      identity rightValid
  exact
    ⟨⟨rightSignature.support, rightSignature.exactCuts,
        reversedOccurrenceParity identity leftValid⟩,
      rightSignature.first⟩

/-- The independently kernel-green protected-prefix normalizer proves the
actual frozen seventeen-law target on every alphabet. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftTable.semigroup)
    (rightValid : identity.SatisfiedBy rightTable.semigroup) :
    Derives basis identity.lhs identity.rhs := by
  have reversedDerivation :=
    SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_796Opposite.derivesOfSameFixedHeadParitySeparatorSignature
      (reversedFixedHeadParitySeparatorSignature
        identity leftValid rightValid)
  have ownerForward :
      Derives SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank001.basis
        identity.lhs identity.rhs := by
    simpa using reversedDerivation.reverse
  rw [ownerDisplayedBasis_eq_target] at ownerForward
  exact ownerForward

/-- Genuine unrestricted target completeness precedes quotient packaging. -/
def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis where
  leftModels := leftModels
  rightModels := rightModels
  complete := derivesOfFactorValid

/-- The reviewed quotient normalizer is used only after pair completeness. -/
noncomputable def normalizer :
    IntersectionNormalizer leftTable.semigroup rightTable.semigroup basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

theorem s6_8863_representative_basis :
    BasisFor S6_8863.table.semigroup basis :=
  S6_8863.representative_basis_of_normalizer normalizer

theorem s6_8863_opposite_basis :
    BasisFor S6_8863.table.semigroup.opposite (reversedBasis basis) :=
  S6_8863.opposite_basis_of_normalizer normalizer

theorem s6_9009_representative_basis :
    BasisFor S6_9009.table.semigroup basis :=
  S6_9009.representative_basis_of_normalizer normalizer

theorem s6_9009_opposite_basis :
    BasisFor S6_9009.table.semigroup.opposite (reversedBasis basis) :=
  S6_9009.opposite_basis_of_normalizer normalizer

/-- Expose the already kernel-reviewed generic family transport with every
displayed-law derivation and each factor implication explicit. -/
noncomputable def transportedNormalizer
    {A : Type u} {B : Type v}
    {targetLeft : Semigroup A} {targetRight : Semigroup B}
    {targetBasis : List (Identity Nat)}
    (lawDerivations :
      ∀ law : Identity Nat,
        law ∈ basis → Derives targetBasis law.lhs law.rhs)
    (leftTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetLeft →
          identity.SatisfiedBy leftTable.semigroup)
    (rightTheory :
      ∀ identity : Identity Nat,
        identity.SatisfiedBy targetRight →
          identity.SatisfiedBy rightTable.semigroup) :
    IntersectionNormalizer targetLeft targetRight targetBasis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.transportNormalizer
    normalizer lawDerivations leftTheory rightTheory

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank001.Seed
