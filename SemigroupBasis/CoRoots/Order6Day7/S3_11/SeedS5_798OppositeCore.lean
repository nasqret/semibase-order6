import SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_798OppositeAdapter
import SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening
import SemigroupBasis.Generated.S2_2

/-!
# Conditional D020 opposite transport, with the exact source root explicit

Every semantic step here is unconditional EXCEPT the one explicitly named
`IntersectionBasis S2_2 S5_798 sourceBasis` premise.  That premise is the
literal already-authored historical e2c root and is discharged in the final
owner module.  No finite factor-theory equality, quotient normalization, or
bounded descriptor is used.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_798OppositeCore

open SemigroupBasis

private abbrev sourceLeft :=
  SemigroupBasis.Generated.S2_2.table.semigroup

private abbrev sourceRight :=
  SemigroupBasis.Generated.Catalogue.S5_798.table.semigroup

/-- The actual two-element cyclic semigroup is its own opposite. -/
theorem cyclicSelfDual : sourceLeft.opposite = sourceLeft := by
  unfold sourceLeft SemigroupBasis.Generated.S2_2.table
    FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext left right
  apply Fin.ext
  decide +revert

/-- Actual cyclic subgroup embedding into the actual frozen owner factor. -/
def cyclicEmbeddingIntoS3_11 :
    Embedding sourceLeft Rank020.leftTable.semigroup := by
  change
    Embedding SemigroupBasis.Examples.cyclicTwo.semigroup
      SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup
  rw [← SemigroupBasis.Generated.S3_11.table_eq_canonical_catalogue]
  exact
    SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening.cyclicEmbeddingS3_11

/-- Left-owner validity pulls back one way, then self-opposition reverses it. -/
theorem reversedCyclicValidity
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Rank020.leftTable.semigroup) :
    identity.reversed.SatisfiedBy sourceLeft := by
  have cyclicValid :=
    cyclicEmbeddingIntoS3_11.pullback_identity identity leftValid
  have oppositeValid : identity.SatisfiedBy sourceLeft.opposite := by
    rw [cyclicSelfDual]
    exact cyclicValid
  exact
    (Identity.satisfiedBy_opposite_iff_reversed identity sourceLeft).mp
      oppositeValid

/-- Exact owner right-opposite validity becomes ordinary source validity. -/
theorem reversedRightValidity
    (identity : Identity Nat)
    (rightValid : identity.SatisfiedBy Rank020.rightTable.semigroup) :
    identity.reversed.SatisfiedBy sourceRight := by
  change identity.SatisfiedBy sourceRight.opposite at rightValid
  exact
    (Identity.satisfiedBy_opposite_iff_reversed identity sourceRight).mp
      rightValid

/-- The sole conditional input is the ACTUAL unrestricted source-pair root. -/
theorem historicalReversedDerivation
    (sourceIntersection :
      IntersectionBasis sourceLeft sourceRight
        SeedS5_798OppositeAdapter.sourceBasis)
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Rank020.leftTable.semigroup)
    (rightValid : identity.SatisfiedBy Rank020.rightTable.semigroup) :
    Derives SeedS5_798OppositeAdapter.sourceBasis
      identity.reversed.lhs identity.reversed.rhs :=
  sourceIntersection.complete identity.reversed
    (reversedCyclicValidity identity leftValid)
    (reversedRightValidity identity rightValid)

/-- Return to the original word orientation under literal reversed source. -/
theorem reversedSourceDerivation
    (sourceIntersection :
      IntersectionBasis sourceLeft sourceRight
        SeedS5_798OppositeAdapter.sourceBasis)
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Rank020.leftTable.semigroup)
    (rightValid : identity.SatisfiedBy Rank020.rightTable.semigroup) :
    Derives (reversedBasis SeedS5_798OppositeAdapter.sourceBasis)
      identity.lhs identity.rhs := by
  have historical :=
    (historicalReversedDerivation sourceIntersection identity
      leftValid rightValid).reverse
  simpa [Identity.reversed] using historical

/-- Each source axiom is discharged by its explicit frozen-B13 certificate. -/
theorem derivesOfFactorValid
    (sourceIntersection :
      IntersectionBasis sourceLeft sourceRight
        SeedS5_798OppositeAdapter.sourceBasis)
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Rank020.leftTable.semigroup)
    (rightValid : identity.SatisfiedBy Rank020.rightTable.semigroup) :
    Derives Rank020.basis identity.lhs identity.rhs :=
  (reversedSourceDerivation sourceIntersection identity
    leftValid rightValid).transport
      SeedS5_798OppositeAdapter.reversedSourceAxiomsDeriveFrozen

/-- Conditional exact-owner root; its sole hypothesis is discharged by the
actual e2c theorem in the importing owner module. -/
def intersectionBasis_of_source
    (sourceIntersection :
      IntersectionBasis sourceLeft sourceRight
        SeedS5_798OppositeAdapter.sourceBasis) :
    IntersectionBasis
      Rank020.leftTable.semigroup
      Rank020.rightTable.semigroup
      Rank020.basis where
  leftModels := Rank020.leftModels
  rightModels := Rank020.rightModels
  complete := derivesOfFactorValid sourceIntersection

end SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_798OppositeCore
