import SemigroupBasis.CoRoots.Order6L3HeavyRank2.Blocks
import SemigroupBasis.CoRoots.S5_788Invariant
import SemigroupBasis.CoRoots.S5_1089Normalization
import SemigroupBasis.Examples.CommutativeParityThree

/-!
# Exact C2 semantic profile for `S3_11 x S5_788`

The left factor supplies support and pointwise occurrence parity.  The right
factor supplies support, every exact unique-separator cut with its side
supports, and first-occurrence order.  Their unrestricted conjunction is the
descriptor consumed by the C2 syntactic normalizer; no last-occurrence or
finite-window coordinate is assumed.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_11S5_788

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev leftFactor :=
  SemigroupBasis.Generated.S3_11.table.semigroup

private abbrev rightFactor :=
  SemigroupBasis.Generated.Catalogue.S5_788.table.semigroup

/-- Exact semantic relation jointly detected by the two C2 factors. -/
structure SameParitySeparatorInitialSignature
    (left right : Word Nat) : Prop where
  support :
    SemigroupBasis.CoRoots.S5_441Invariant.SameSupport left right
  exactCuts :
    SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature left right
  initials :
    firstOccurrenceSequence left.toList =
      firstOccurrenceSequence right.toList
  parity :
    SemigroupBasis.CoRoots.S5_441Invariant.SameOccurrenceParity left right

namespace SameParitySeparatorInitialSignature

theorem refl (word : Word Nat) :
    SameParitySeparatorInitialSignature word word :=
  ⟨SemigroupBasis.CoRoots.S5_441Invariant.SameSupport.refl word,
    SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature.refl word,
    rfl,
    SemigroupBasis.CoRoots.S5_441Invariant.SameOccurrenceParity.refl word⟩

theorem symm {left right : Word Nat}
    (same : SameParitySeparatorInitialSignature left right) :
    SameParitySeparatorInitialSignature right left :=
  ⟨SemigroupBasis.CoRoots.S5_441Invariant.SameSupport.symm same.support,
    SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature.symm
      same.exactCuts,
    same.initials.symm,
    SemigroupBasis.CoRoots.S5_441Invariant.SameOccurrenceParity.symm
      same.parity⟩

theorem trans {left middle right : Word Nat}
    (first : SameParitySeparatorInitialSignature left middle)
    (second : SameParitySeparatorInitialSignature middle right) :
    SameParitySeparatorInitialSignature left right :=
  ⟨SemigroupBasis.CoRoots.S5_441Invariant.SameSupport.trans
      first.support second.support,
    SemigroupBasis.CoRoots.S5_441Invariant.SameExactCutSignature.trans
      first.exactCuts second.exactCuts,
    first.initials.trans second.initials,
    SemigroupBasis.CoRoots.S5_441Invariant.SameOccurrenceParity.trans
      first.parity second.parity⟩

end SameParitySeparatorInitialSignature

private theorem sameSupport_of_left_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftFactor) :
    SemigroupBasis.CoRoots.S5_441Invariant.SameSupport
      identity.lhs identity.rhs := by
  simpa [SemigroupBasis.Generated.S3_11.table,
    parityZeroThree] using
      parityZeroValid_support identity valid

private theorem sameParity_of_left_valid
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy leftFactor) :
    SemigroupBasis.CoRoots.S5_441Invariant.SameOccurrenceParity
      identity.lhs identity.rhs := by
  simpa [SemigroupBasis.Generated.S3_11.table,
    parityZeroThree] using
      parityZeroValid_parity identity valid

/-- Unrestricted factor validity implies exactly the C2 descriptor. -/
theorem sameSignature_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy leftFactor)
    (rightValid : identity.SatisfiedBy rightFactor) :
    SameParitySeparatorInitialSignature identity.lhs identity.rhs := by
  have rightSignature :=
    SemigroupBasis.CoRoots.S5_788FamilyInvariant.S5_788.valid_sameSignature
      identity rightValid
  exact
    ⟨sameSupport_of_left_valid identity leftValid,
      rightSignature.exactCuts,
      rightSignature.initials,
      sameParity_of_left_valid identity leftValid⟩

/-! ## Excluding the stronger Ford/Lord descriptor

The exact factor intersection does not determine last-occurrence order.
Keeping this closed witness beside the semantic profile prevents a later
reachability proof from accidentally assuming the strictly stronger generic
`OneLocalFordLord.Profile 2 2` contract.
-/

private def counterexampleFinite : Identity (Fin 2) :=
  Identity.mk (Word.mk 0 [1, 0, 1]) (Word.mk 0 [1, 1, 0])

def counterexample : Identity Nat :=
  Identity.mk (Word.mk 0 [1, 0, 1]) (Word.mk 0 [1, 1, 0])

private theorem counterexample_left_valid :
    counterexample.SatisfiedBy leftFactor := by
  have checked :=
    SemigroupBasis.Generated.S3_11.table.checkIdentityNat_sound
      counterexampleFinite (by decide)
  simpa [counterexample, counterexampleFinite, Identity.map,
    Word.map] using checked

private theorem counterexample_right_valid :
    counterexample.SatisfiedBy rightFactor := by
  have checked :=
    SemigroupBasis.Generated.Catalogue.S5_788.table.checkIdentityNat_sound
      counterexampleFinite (by decide)
  simpa [counterexample, counterexampleFinite, Identity.map,
    Word.map] using checked

/-- The C2 descriptor is strictly weaker than adding last-occurrence order. -/
theorem exists_sameSignature_lastOccurrenceSequence_ne :
    ∃ left right : Word Nat,
      SameParitySeparatorInitialSignature left right ∧
        SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence left.toList ≠
          SemigroupBasis.CoRoots.S5_1089.lastOccurrenceSequence right.toList := by
  refine ⟨counterexample.lhs, counterexample.rhs, ?_, ?_⟩
  · exact sameSignature_of_factor_valid counterexample
      counterexample_left_valid counterexample_right_valid
  · decide

theorem targetModelsLeft :
    Models leftFactor
      SemigroupBasis.CoRoots.Order6L3HeavyRank2.basisS3_11S5_788 :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.basisS3_11S5_788_left_models

theorem targetModelsRight :
    Models rightFactor
      SemigroupBasis.CoRoots.Order6L3HeavyRank2.basisS3_11S5_788 :=
  SemigroupBasis.CoRoots.Order6L3HeavyRank2.basisS3_11S5_788_right_models

end SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_11S5_788
