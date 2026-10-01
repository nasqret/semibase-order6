import SemigroupBasis.CoRoots.S5_1092Normalization
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.Generated.CatalogueOrder5Part09
import SemigroupBasis.Transfer

namespace SemigroupBasis.CoRoots.S5_1092Factors

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.S5_1092

private theorem valid_firstOccurrenceSequence_eq_of_embedding
    {carrier : Type}
    (target : Semigroup carrier)
    (embedding :
      Embedding
        SemigroupBasis.Examples.leftRegularBandThree.semigroup target)
    (e : Identity Nat)
    (valid : e.SatisfiedBy target) :
    firstOccurrenceSequence e.lhs.toList =
      firstOccurrenceSequence e.rhs.toList := by
  exact
    SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      e (embedding.pullback_identity e valid)

private theorem valid_lastOccurrenceSequence_eq_of_embedding
    {carrier : Type}
    (target : Semigroup carrier)
    (embedding :
      Embedding
        SemigroupBasis.Examples.leftRegularBandThree.semigroup.opposite
        target)
    (e : Identity Nat)
    (valid : e.SatisfiedBy target) :
    lastOccurrenceSequence e.lhs.toList =
      lastOccurrenceSequence e.rhs.toList := by
  have validRight :=
    embedding.pullback_identity e valid
  have validReversed :
      e.reversed.SatisfiedBy
        SemigroupBasis.Examples.leftRegularBandThree.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      e SemigroupBasis.Examples.leftRegularBandThree.semigroup).mp validRight
  have firstReversed :=
    SemigroupBasis.CoRoots.S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      e.reversed validReversed
  have reversedEquality := congrArg List.reverse firstReversed
  simpa [Identity.reversed,
    lastOccurrenceSequence_eq_reverse_firstOccurrenceSequence] using reversedEquality

namespace S5_1092

def initialEmbedding :
    Embedding
      SemigroupBasis.Examples.leftRegularBandThree.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then (0 : Fin 5)
    else if a.val = 1 then (3 : Fin 5)
    else (2 : Fin 5)
  injective := by
    intro a b
    revert a b
    decide
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide

def finalEmbedding :
    Embedding
      SemigroupBasis.Examples.leftRegularBandThree.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then (1 : Fin 5)
    else if a.val = 1 then (3 : Fin 5)
    else (4 : Fin 5)
  injective := by
    intro a b
    revert a b
    decide
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide

theorem valid_firstOccurrenceSequence_eq
    (e : Identity Nat)
    (valid :
      e.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup) :
    firstOccurrenceSequence e.lhs.toList =
      firstOccurrenceSequence e.rhs.toList :=
  valid_firstOccurrenceSequence_eq_of_embedding
    SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup
    initialEmbedding e valid

theorem valid_lastOccurrenceSequence_eq
    (e : Identity Nat)
    (valid :
      e.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup) :
    lastOccurrenceSequence e.lhs.toList =
      lastOccurrenceSequence e.rhs.toList :=
  valid_lastOccurrenceSequence_eq_of_embedding
    SemigroupBasis.Generated.Catalogue.S5_1092.table.semigroup
    finalEmbedding e valid

end S5_1092

namespace S5_1135

def initialEmbedding :
    Embedding
      SemigroupBasis.Examples.leftRegularBandThree.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then (0 : Fin 5)
    else if a.val = 1 then (1 : Fin 5)
    else (4 : Fin 5)
  injective := by
    intro a b
    revert a b
    decide
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide

def finalEmbedding :
    Embedding
      SemigroupBasis.Examples.leftRegularBandThree.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then (1 : Fin 5)
    else if a.val = 1 then (2 : Fin 5)
    else (3 : Fin 5)
  injective := by
    intro a b
    revert a b
    decide
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide

theorem valid_firstOccurrenceSequence_eq
    (e : Identity Nat)
    (valid :
      e.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup) :
    firstOccurrenceSequence e.lhs.toList =
      firstOccurrenceSequence e.rhs.toList :=
  valid_firstOccurrenceSequence_eq_of_embedding
    SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup
    initialEmbedding e valid

theorem valid_lastOccurrenceSequence_eq
    (e : Identity Nat)
    (valid :
      e.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup) :
    lastOccurrenceSequence e.lhs.toList =
      lastOccurrenceSequence e.rhs.toList :=
  valid_lastOccurrenceSequence_eq_of_embedding
    SemigroupBasis.Generated.Catalogue.S5_1135.table.semigroup
    finalEmbedding e valid

end S5_1135

namespace S5_1144

def initialEmbedding :
    Embedding
      SemigroupBasis.Examples.leftRegularBandThree.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then (0 : Fin 5)
    else if a.val = 1 then (1 : Fin 5)
    else (2 : Fin 5)
  injective := by
    intro a b
    revert a b
    decide
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide

def finalEmbedding :
    Embedding
      SemigroupBasis.Examples.leftRegularBandThree.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup where
  toFun := fun a =>
    if a.val = 0 then (0 : Fin 5)
    else if a.val = 1 then (1 : Fin 5)
    else (3 : Fin 5)
  injective := by
    intro a b
    revert a b
    decide
  map_mul := by
    intro a b
    apply Fin.ext
    revert a b
    decide

theorem valid_firstOccurrenceSequence_eq
    (e : Identity Nat)
    (valid :
      e.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup) :
    firstOccurrenceSequence e.lhs.toList =
      firstOccurrenceSequence e.rhs.toList :=
  valid_firstOccurrenceSequence_eq_of_embedding
    SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup
    initialEmbedding e valid

theorem valid_lastOccurrenceSequence_eq
    (e : Identity Nat)
    (valid :
      e.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup) :
    lastOccurrenceSequence e.lhs.toList =
      lastOccurrenceSequence e.rhs.toList :=
  valid_lastOccurrenceSequence_eq_of_embedding
    SemigroupBasis.Generated.Catalogue.S5_1144.table.semigroup
    finalEmbedding e valid

end S5_1144

end SemigroupBasis.CoRoots.S5_1092Factors
