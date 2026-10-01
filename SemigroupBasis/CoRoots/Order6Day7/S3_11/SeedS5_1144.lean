import SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_1144ParityNormal
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal

/-!
# Authenticated unrestricted `S3_11 × S5_1144` owner seed

The exact right factor supplies complete first- and last-occurrence order;
the exact left factor supplies per-variable parity.  Their unrestricted joint
signature is proved complete by parity-preserving whole-square transport of
the regular-band calculus and transported two-sided guarded parity reduction.

Both authenticated S6_14891 orientations are unconditional at source level.
Independent kernel recording, acceptance, and sealing remain outside this
proof.  The separate S2 theory bridge can consume the intersection basis only
after the independently recorded owner carrier is green.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_1144

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank003.basis

private abbrev leftFactor := Rank003.leftTable.semigroup

private abbrev rightFactor := Rank003.rightTable.semigroup

/-- Reuse all exact frozen S3_11 displayed-law witnesses. -/
theorem modelsLeft : Models leftFactor targetBasis :=
  Rank003.leftModels

/-- Reuse all exact frozen S5_1144 displayed-law witnesses. -/
theorem modelsRight : Models rightFactor targetBasis :=
  Rank003.rightModels

/-- Independent, unrestricted completeness for the EXACT frozen owner pair. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    Derives targetBasis identity.lhs identity.rhs := by
  have firstEqual :=
    SemigroupBasis.CoRoots.S5_1092Factors.S5_1144.valid_firstOccurrenceSequence_eq
      identity rightValid
  have lastEqual :=
    SemigroupBasis.CoRoots.S5_1092Factors.S5_1144.valid_lastOccurrenceSequence_eq
      identity rightValid
  have parity :=
    SemigroupBasis.CoRoots.S5_441Invariant.sameOccurrenceParity_of_s3_11_valid
      identity leftValid
  exact derivesOfBandParitySignature
    identity.lhs identity.rhs firstEqual lastEqual parity

/-- Actual pair completeness is established before quotient normalization. -/
def intersectionBasis :
    IntersectionBasis
      Rank003.leftTable.semigroup
      Rank003.rightTable.semigroup
      Rank003.basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

/-- Quotient normalization is downstream of unrestricted pair completeness. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank003.leftTable.semigroup
      Rank003.rightTable.semigroup
      Rank003.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- Authenticated unrestricted representative orientation. -/
theorem representative_basis_S6_14891 :
    BasisFor Rank003.S6_14891.table.semigroup Rank003.basis :=
  Rank003.S6_14891.representative_basis_of_normalizer intersectionNormalizer

/-- Authenticated unrestricted literal reversed-basis opposite orientation. -/
theorem opposite_basis_S6_14891 :
    BasisFor Rank003.S6_14891.table.semigroup.opposite
      (reversedBasis Rank003.basis) :=
  Rank003.S6_14891.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_1144
