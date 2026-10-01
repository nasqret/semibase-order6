import SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_516DualAdapter
import SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening
import SemigroupBasis.CoRoots.S5_196Family
import SemigroupBasis.CoRoots.S5_516Completeness
import SemigroupBasis.Generated.S2_2

/-!
# Conditional D043 dual semantic transport, with its exact root explicit

The catalogue semigroups `S5_196` and `S5_516` are neither isomorphic nor
anti-isomorphic.  Right validity is instead transported in one explicit
direction through the already proved exact initial-marker classification,
its named reverse-word duality, the complete S5_196 syntax theorem, and the
actual S5_196 finite models.  The sole completeness hypothesis is the genuine
unrestricted `IntersectionBasis C2 S5_196 sourceBasis` root.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_516DualCore

open SemigroupBasis

private abbrev sourceLeft :=
  SemigroupBasis.Generated.S2_2.table.semigroup

private abbrev sourceRight :=
  SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup

/-- The actual two-element cyclic semigroup is its own opposite. -/
theorem cyclicSelfDual : sourceLeft.opposite = sourceLeft := by
  unfold sourceLeft SemigroupBasis.Generated.S2_2.table
    FiniteTable.semigroup Semigroup.opposite
  congr 1
  funext left right
  apply Fin.ext
  decide +revert

/-- Actual one-way cyclic subgroup embedding into the frozen S3_11 factor. -/
def cyclicEmbeddingIntoS3_11 :
    Embedding sourceLeft Rank043.leftTable.semigroup := by
  change
    Embedding SemigroupBasis.Examples.cyclicTwo.semigroup
      SemigroupBasis.Generated.Catalogue.S3_11.table.semigroup
  rw [← SemigroupBasis.Generated.S3_11.table_eq_canonical_catalogue]
  exact
    SemigroupBasis.CoRoots.Order6FactorPairS3_11Widening.cyclicEmbeddingS3_11

/-- Frozen owner-left validity pulls back and then genuinely reverses. -/
theorem reversedCyclicValidity
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Rank043.leftTable.semigroup) :
    identity.reversed.SatisfiedBy sourceLeft := by
  have cyclicValid :=
    cyclicEmbeddingIntoS3_11.pullback_identity identity leftValid
  have oppositeValid : identity.SatisfiedBy sourceLeft.opposite := by
    rw [cyclicSelfDual]
    exact cyclicValid
  exact
    (Identity.satisfiedBy_opposite_iff_reversed identity sourceLeft).mp
      oppositeValid

/-- Exact S5_516 validity gives the actual unrestricted dual class, not an
unproved factor-theory equality or a nonexistent anti-isomorphism. -/
theorem reversedRightExactClass
    (identity : Identity Nat)
    (rightValid : identity.SatisfiedBy Rank043.rightTable.semigroup) :
    SemigroupBasis.CoRoots.S5_196.ExactBasisClass
      identity.reversed.lhs identity.reversed.rhs := by
  have rightValid' :
      identity.SatisfiedBy SemigroupBasis.CoRoots.S5_516.table.semigroup := by
    change
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_516.table.semigroup
    exact rightValid
  have exactClass :=
    SemigroupBasis.CoRoots.S5_516.valid_exactBasisClass identity rightValid'
  have dual :=
    (SemigroupBasis.CoRoots.S5_516.exactBasisClass_iff_dual
      identity.lhs identity.rhs).mp exactClass
  simpa [Identity.reversed] using dual

/-- Complete S5_196 syntax and its independently checked models yield genuine
validity of the reversed identity on the actual source factor. -/
theorem reversedRightValidity
    (identity : Identity Nat)
    (rightValid : identity.SatisfiedBy Rank043.rightTable.semigroup) :
    identity.reversed.SatisfiedBy sourceRight := by
  have derived :=
    SemigroupBasis.CoRoots.S5_196.derives_iff_exactBasisClass.mpr
      (reversedRightExactClass identity rightValid)
  intro valuation
  exact derived.sound
    SemigroupBasis.CoRoots.S5_196Family.S5_196.models valuation

/-- The sole conditional input is the actual unrestricted cyclic/196 root. -/
theorem historicalReversedDerivation
    (sourceIntersection :
      IntersectionBasis sourceLeft sourceRight
        SeedS5_516DualAdapter.sourceBasis)
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Rank043.leftTable.semigroup)
    (rightValid : identity.SatisfiedBy Rank043.rightTable.semigroup) :
    Derives SeedS5_516DualAdapter.sourceBasis
      identity.reversed.lhs identity.reversed.rhs :=
  sourceIntersection.complete identity.reversed
    (reversedCyclicValidity identity leftValid)
    (reversedRightValidity identity rightValid)

/-- Reverse the genuine historical derivation back to the owner orientation. -/
theorem reversedSourceDerivation
    (sourceIntersection :
      IntersectionBasis sourceLeft sourceRight
        SeedS5_516DualAdapter.sourceBasis)
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Rank043.leftTable.semigroup)
    (rightValid : identity.SatisfiedBy Rank043.rightTable.semigroup) :
    Derives (reversedBasis SeedS5_516DualAdapter.sourceBasis)
      identity.lhs identity.rhs := by
  have historical :=
    (historicalReversedDerivation sourceIntersection identity
      leftValid rightValid).reverse
  simpa [Identity.reversed] using historical

/-- Retarget by all sixteen individually checked frozen-basis edges. -/
theorem derivesOfFactorValid
    (sourceIntersection :
      IntersectionBasis sourceLeft sourceRight
        SeedS5_516DualAdapter.sourceBasis)
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy Rank043.leftTable.semigroup)
    (rightValid : identity.SatisfiedBy Rank043.rightTable.semigroup) :
    Derives Rank043.basis identity.lhs identity.rhs :=
  (reversedSourceDerivation sourceIntersection identity
    leftValid rightValid).transport
      SeedS5_516DualAdapter.reversedSourceAxiomsDeriveFrozen

/-- Conditional exact-owner root with its sole unrestricted premise explicit. -/
def intersectionBasis_of_source
    (sourceIntersection :
      IntersectionBasis sourceLeft sourceRight
        SeedS5_516DualAdapter.sourceBasis) :
    IntersectionBasis
      Rank043.leftTable.semigroup
      Rank043.rightTable.semigroup
      Rank043.basis where
  leftModels := Rank043.leftModels
  rightModels := Rank043.rightModels
  complete := derivesOfFactorValid sourceIntersection

end SemigroupBasis.CoRoots.Order6Day7.S3_11.SeedS5_516DualCore
