import SemigroupBasis.CoRoots.S5_381Invariant

namespace SemigroupBasis.Examples.SimpleSequenceFirstGap

open SemigroupBasis
open SemigroupBasis.CoRoots
open SemigroupBasis.Examples

/-- Two globally simple variables occur in this order. This is expressed
as the reversed simple-order relation from the established `S4_71`
scanner. -/
def SimplePrecedes (word : Word Nat) (x y : Nat) : Prop :=
  S5_793Invariant.SimplePrecedes word.reverse y x

/-- The globally simple variable `simple` occurs before the first
occurrence of the multiple variable `multiple`. The truth vector over all
simple variables records the first-occurrence gap of `multiple`. -/
def SimpleBeforeMultipleFirst
    (word : Word Nat) (simple multiple : Nat) : Prop :=
  S5_793Invariant.MultipleLastBeforeSimple
    word.reverse multiple simple

/-- The optional globally simple final marker, represented as the simple
initial marker of the reversed word. -/
def SimpleFinal (word : Word Nat) (letter : Nat) : Prop :=
  S5_107.SimpleInitial word.reverse letter

@[simp]
theorem cappedMultiplicity_reverse
    (word : Word Nat) (letter : Nat) :
    S5_107.cappedMultiplicity word.reverse letter =
      S5_107.cappedMultiplicity word letter := by
  simp [S5_107.cappedMultiplicity, List.count_reverse]

/-- The exact first-gap/final signature. `blockTheory` is the complete
opposite-`S4_71` semantic component; the remaining fields expose its
capped multiplicities, ordered globally simple variables, all first-gap
cuts, and the optional globally simple final marker. -/
structure SameSignature (left right : Word Nat) : Prop where
  blockTheory :
    (Identity.mk left right).SatisfiedBy
      Generated.S4_71.table.semigroup.opposite
  capped :
    ∀ letter,
      S5_107.cappedMultiplicity left letter =
        S5_107.cappedMultiplicity right letter
  simpleSequence :
    ∀ x y,
      SimplePrecedes left x y ↔ SimplePrecedes right x y
  firstGap :
    ∀ simple multiple,
      SimpleBeforeMultipleFirst left simple multiple ↔
        SimpleBeforeMultipleFirst right simple multiple
  final :
    ∀ letter, SimpleFinal left letter ↔ SimpleFinal right letter

/-- Convert the first-gap/final signature into the established
last-gap/initial signature on reversed words. -/
theorem SameSignature.toDual
    {left right : Word Nat}
    (same : SameSignature left right) :
    S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
      left.reverse right.reverse := by
  have reversedBlock :
      (Identity.mk left right).reversed.SatisfiedBy
        Generated.S4_71.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      (Identity.mk left right)
      Generated.S4_71.table.semigroup).mp same.blockTheory
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [Identity.reversed] using reversedBlock
  · intro letter
    simpa using same.capped letter
  · intro x y
    simpa [SimplePrecedes] using same.simpleSequence y x
  · intro x y
    simpa [SimpleBeforeMultipleFirst] using same.firstGap y x
  · intro letter
    simpa [SimpleFinal] using same.final letter

/-- Reflect the established dual signature back to the explicit
first-gap/final fields. -/
theorem SameSignature.ofDual
    {left right : Word Nat}
    (same :
      S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
        left.reverse right.reverse) :
    SameSignature left right := by
  have reversedBlock :
      (Identity.mk left right).reversed.SatisfiedBy
        Generated.S4_71.table.semigroup := by
    simpa [Identity.reversed] using same.blockTheory
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact
      (Identity.satisfiedBy_opposite_iff_reversed
        (Identity.mk left right)
        Generated.S4_71.table.semigroup).mpr reversedBlock
  · intro letter
    simpa using same.capped letter
  · intro x y
    simpa [SimplePrecedes] using same.simpleSequence y x
  · intro simple multiple
    simpa [SimpleBeforeMultipleFirst] using
      same.lastGap multiple simple
  · intro letter
    simpa [SimpleFinal] using same.initial letter

/-- The two signature presentations are definitionally inverse up to word
reversal. -/
theorem sameSignature_iff_dual
    (left right : Word Nat) :
    SameSignature left right ↔
      S5_381Invariant.SameSimpleSequenceLastGapInitialSignature
        left.reverse right.reverse :=
  ⟨SameSignature.toDual, SameSignature.ofDual⟩

/-- Factor validity supplies the complete explicit signature. -/
theorem sameSignature_of_factor_valid
    (identity : Identity Nat)
    (blockValid :
      identity.SatisfiedBy
        Generated.S4_71.table.semigroup.opposite)
    (finalValid :
      identity.SatisfiedBy finalMarkerThree.semigroup) :
    SameSignature identity.lhs identity.rhs := by
  have reversedBlock :
      identity.reversed.SatisfiedBy
        Generated.S4_71.table.semigroup :=
    (Identity.satisfiedBy_opposite_iff_reversed
      identity Generated.S4_71.table.semigroup).mp blockValid
  have reversedFinal :
      identity.reversed.SatisfiedBy
        finalMarkerThree.semigroup.opposite := by
    apply
      (Identity.satisfiedBy_opposite_iff_reversed
        identity.reversed finalMarkerThree.semigroup).mpr
    simpa using finalValid
  have dual :=
    S5_381Invariant.sameSignature_of_factor_valid
      identity.reversed reversedBlock reversedFinal
  apply SameSignature.ofDual (left := identity.lhs) (right := identity.rhs)
  simpa [Identity.reversed] using dual

namespace SameSignature

theorem refl (word : Word Nat) : SameSignature word word :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ => Iff.rfl⟩

theorem symm {left right : Word Nat}
    (same : SameSignature left right) :
    SameSignature right left :=
  ⟨fun valuation => (same.blockTheory valuation).symm,
    fun letter => (same.capped letter).symm,
    fun x y => (same.simpleSequence x y).symm,
    fun simple multiple => (same.firstGap simple multiple).symm,
    fun letter => (same.final letter).symm⟩

theorem trans {left middle right : Word Nat}
    (first : SameSignature left middle)
    (second : SameSignature middle right) :
    SameSignature left right :=
  ⟨fun valuation =>
      (first.blockTheory valuation).trans
        (second.blockTheory valuation),
    fun letter =>
      (first.capped letter).trans (second.capped letter),
    fun x y =>
      (first.simpleSequence x y).trans
        (second.simpleSequence x y),
    fun simple multiple =>
      (first.firstGap simple multiple).trans
        (second.firstGap simple multiple),
    fun letter =>
      (first.final letter).trans (second.final letter)⟩

theorem absent {left right : Word Nat}
    (same : SameSignature left right) (letter : Nat) :
    letter ∉ left.toList ↔ letter ∉ right.toList := by
  rw [← List.count_eq_zero, ← List.count_eq_zero,
    ← S5_107.cappedMultiplicity_eq_zero_iff,
    ← S5_107.cappedMultiplicity_eq_zero_iff,
    same.capped letter]

theorem support {left right : Word Nat}
    (same : SameSignature left right) (letter : Nat) :
    letter ∈ left.toList ↔ letter ∈ right.toList := by
  simpa using not_congr (same.absent letter)

theorem simple {left right : Word Nat}
    (same : SameSignature left right) (letter : Nat) :
    S5_107.SimpleIn left letter ↔
      S5_107.SimpleIn right letter := by
  unfold S5_107.SimpleIn
  rw [← S5_107.cappedMultiplicity_eq_one_iff,
    ← S5_107.cappedMultiplicity_eq_one_iff,
    same.capped letter]

end SameSignature

end SemigroupBasis.Examples.SimpleSequenceFirstGap
