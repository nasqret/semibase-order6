import SemigroupBasis.CoRoots.S5_1089Normalization
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.Examples.LeftZeroTwo
import SemigroupBasis.Generated.CatalogueOrder5Part09
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_1089Semantics

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_1089

private theorem valid_head_eq_of_embedding
    {carrier : Type}
    (target : Semigroup carrier)
    (embedding : Embedding leftZeroTwo.semigroup target)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy target) :
    identity.lhs.head = identity.rhs.head := by
  have pulled :=
    embedding.pullback_identity identity valid
  apply Decidable.byContradiction
  intro different
  let valuation : Nat → Fin 2 :=
    fun letter => if letter = identity.lhs.head then 0 else 1
  have evaluated := pulled valuation
  rw [leftZeroTwo_eval, leftZeroTwo_eval] at evaluated
  simp [valuation, Ne.symm different] at evaluated

private theorem valid_lastOccurrenceSequence_eq_of_embedding
    {carrier : Type}
    (target : Semigroup carrier)
    (embedding :
      Embedding leftRegularBandThree.semigroup.opposite target)
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy target) :
    lastOccurrenceSequence identity.lhs.toList =
      lastOccurrenceSequence identity.rhs.toList := by
  have validRight :=
    embedding.pullback_identity identity valid
  have validReversed :
      identity.reversed.SatisfiedBy
        leftRegularBandThree.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity leftRegularBandThree.semigroup).mp validRight
  have firstReversed :=
    SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      identity.reversed validReversed
  have reversedEquality := congrArg List.reverse firstReversed
  simpa [Identity.reversed,
    lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence] using
      reversedEquality

namespace S5_1089

abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_1089.table

set_option maxRecDepth 100000 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

/-- Zero-based left-zero embedding `[0, 2]`. -/
def headEmbedding :
    Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then (0 : Fin 5) else (2 : Fin 5)
  injective := by
    intro left right
    revert left right
    decide
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide

/-- Zero-based opposite-`S3_16` embedding `[1, 3, 4]`. -/
def lastOccurrenceEmbedding :
    Embedding
      leftRegularBandThree.semigroup.opposite table.semigroup where
  toFun := fun value =>
    if value.val = 0 then (1 : Fin 5)
    else if value.val = 1 then (3 : Fin 5)
    else (4 : Fin 5)
  injective := by
    intro left right
    revert left right
    decide
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide

theorem valid_head_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.lhs.head = identity.rhs.head :=
  valid_head_eq_of_embedding
    table.semigroup headEmbedding identity valid

theorem valid_lastOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    lastOccurrenceSequence identity.lhs.toList =
      lastOccurrenceSequence identity.rhs.toList :=
  valid_lastOccurrenceSequence_eq_of_embedding
    table.semigroup lastOccurrenceEmbedding identity valid

end S5_1089

namespace S5_1143

abbrev table : FiniteTable :=
  SemigroupBasis.Generated.Catalogue.S5_1143.table

set_option maxRecDepth 100000 in
theorem models : Models table.semigroup basis :=
  models_of_finite_checks table (by decide)

/-- Zero-based left-zero embedding `[0, 2]`. -/
def headEmbedding :
    Embedding leftZeroTwo.semigroup table.semigroup where
  toFun := fun value =>
    if value.val = 0 then (0 : Fin 5) else (2 : Fin 5)
  injective := by
    intro left right
    revert left right
    decide
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide

/-- Zero-based opposite-`S3_16` embedding `[0, 1, 3]`. -/
def lastOccurrenceEmbedding :
    Embedding
      leftRegularBandThree.semigroup.opposite table.semigroup where
  toFun := fun value =>
    if value.val = 0 then (0 : Fin 5)
    else if value.val = 1 then (1 : Fin 5)
    else (3 : Fin 5)
  injective := by
    intro left right
    revert left right
    decide
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide

theorem valid_head_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.lhs.head = identity.rhs.head :=
  valid_head_eq_of_embedding
    table.semigroup headEmbedding identity valid

theorem valid_lastOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    lastOccurrenceSequence identity.lhs.toList =
      lastOccurrenceSequence identity.rhs.toList :=
  valid_lastOccurrenceSequence_eq_of_embedding
    table.semigroup lastOccurrenceEmbedding identity valid

end S5_1143

end SemigroupBasis.CoRoots.S5_1089Semantics
