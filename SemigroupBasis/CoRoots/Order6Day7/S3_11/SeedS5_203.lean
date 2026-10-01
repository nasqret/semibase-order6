import SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_203TerminalParityNormal
import SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCQuotientNormal

/-!
# Authenticated unrestricted D008 cyclic root and S3_11 owner widening

The exact 26-law displayed basis is shared by the independently frozen
`S2_2 × S5_203` and `S3_11 × S5_203` rank-008 envelopes.  Its fresh cyclic
root is proved from the COMPLETE S5_203 terminal-state signature together
with pointwise cyclic parity.  The explicit cyclic embedding into S3_11 then
widens that root in one direction only; factor-theory equality is neither
true nor asserted.

Only the S1-owned authenticated S6_5427 endpoints are instantiated here.
The separately owned S2_2/S6_2852/S6_2890 shells can later consume the
public cyclic root without crossing ownership boundaries.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_203

open SemigroupBasis

private abbrev targetBasis : List (Identity Nat) := Rank008.basis

/-- Both immutable D008 envelopes carry exactly the same ordered 26 laws. -/
theorem frozenCyclicBasis_eq :
    SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.basis = Rank008.basis := by
  decide

/-- Reuse the genuine catalogue cyclic-group parity separator. -/
theorem cyclicOccurrenceParity
    (identity : Identity Nat)
    (valid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.leftTable.semigroup) :
    ∀ letter,
      identity.lhs.toList.count letter % 2 =
        identity.rhs.toList.count letter % 2 :=
  SemigroupBasis.CoRoots.S5_441Invariant.sameOccurrenceParity_of_s2_2_valid
    identity valid

/-- Fresh unrestricted D008 cyclic-factor proof; the lower ten-law factor
basis is used only for its proved concrete terminal-state separator. -/
theorem derivesOfCyclicFactorValid
    (identity : Identity Nat)
    (cyclicValid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.leftTable.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.rightTable.semigroup) :
    Derives targetBasis identity.lhs identity.rhs := by
  have terminalSignature :=
    SemigroupBasis.CoRoots.S5_203.valid_sameSupportTerminalStateSignature
      identity rightValid
  exact derivesOfSameTerminalParitySignature
    identity.lhs identity.rhs terminalSignature
      (cyclicOccurrenceParity identity cyclicValid)

/-- Complete exact auxiliary root for S2's separately owned frozen shell. -/
def cyclicIntersectionBasis :
    IntersectionBasis
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.leftTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.rightTable.semigroup
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.basis where
  leftModels :=
    SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.leftModels
  rightModels :=
    SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.rightModels
  complete := by
    intro identity cyclicValid rightValid
    rw [frozenCyclicBasis_eq]
    exact derivesOfCyclicFactorValid identity cyclicValid rightValid

/-- Reuse the already proved concrete cyclic subgroup embedding, rewritten
to the actual raw catalogue factor tables; no factor-theory equality. -/
def cyclicEmbeddingIntoS3_11 :
    Embedding
      SemigroupBasis.Generated.Catalogue.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup := by
  rw [SemigroupBasis.CoRoots.S5_441Invariant.catalogueS2_2_table_eq_cyclicTwo]
  rw [← SemigroupBasis.Generated.S3_11.table_eq_canonical_catalogue]
  exact
    SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening.cyclicEmbeddingS3_11

/-- Exact one-way widening supplies genuine cyclic validity from S3_11. -/
theorem cyclicValid_of_s3_11Valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy Rank008.leftTable.semigroup) :
    identity.SatisfiedBy
      SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank008.leftTable.semigroup :=
  cyclicEmbeddingIntoS3_11.pullback_identity identity valid

/-- Reuse all exact frozen S3_11 displayed-law witnesses. -/
theorem modelsLeft : Models Rank008.leftTable.semigroup targetBasis :=
  Rank008.leftModels

/-- Reuse all exact frozen S5_203 displayed-law witnesses. -/
theorem modelsRight : Models Rank008.rightTable.semigroup targetBasis :=
  Rank008.rightModels

/-- Independent unrestricted S1 owner completeness follows from its fresh
auxiliary cyclic root and the explicit ONE-WAY subgroup embedding. -/
theorem derivesOfFactorValid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Rank008.leftTable.semigroup)
    (rightValid : identity.SatisfiedBy Rank008.rightTable.semigroup) :
    Derives targetBasis identity.lhs identity.rhs := by
  exact derivesOfCyclicFactorValid identity
    (cyclicValid_of_s3_11Valid identity leftValid) rightValid

/-- Actual pair completeness is proved strictly before quotient normalization. -/
def intersectionBasis :
    IntersectionBasis
      Rank008.leftTable.semigroup
      Rank008.rightTable.semigroup
      Rank008.basis where
  leftModels := modelsLeft
  rightModels := modelsRight
  complete := derivesOfFactorValid

/-- Quotient normalization is downstream of both unrestricted roots. -/
noncomputable def intersectionNormalizer :
    IntersectionNormalizer
      Rank008.leftTable.semigroup
      Rank008.rightTable.semigroup
      Rank008.basis :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCCommon.IntersectionBasis.toQuotientNormalizer
    intersectionBasis

/-- Authenticated S1-owned unrestricted representative orientation. -/
theorem representative_basis_S6_5427 :
    BasisFor Rank008.S6_5427.table.semigroup Rank008.basis :=
  Rank008.S6_5427.representative_basis_of_normalizer intersectionNormalizer

/-- Authenticated S1-owned literal reversed-basis opposite orientation. -/
theorem opposite_basis_S6_5427 :
    BasisFor Rank008.S6_5427.table.semigroup.opposite
      (reversedBasis Rank008.basis) :=
  Rank008.S6_5427.opposite_basis_of_normalizer intersectionNormalizer

end SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_203
