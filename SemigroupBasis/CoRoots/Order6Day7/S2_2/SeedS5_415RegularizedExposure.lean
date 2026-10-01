import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415EvenCoverage

/-!
# Rank040: product closure at every exposure of an actually regular word

Let r be a genuine two-sided inverse of w, and write w = P Q at an
arbitrary raw-list cut. The derivational representative w r w r w has
regular flanks L = w r P and R = Q r w. Their actual inverses are Q r
and r P, including when either original raw flank is empty.

The existing tagged-insertion theorem transports each insertion to this
representative and back. Thus the old two-regular-flank product theorem
now applies to EVERY endpoint exposure of a regular word. No prefix is
cancelled, no common inverse is inferred from factor semantics, and no
BrandtParityLift or DiagonalParityLift field is assumed.

This discharges the product-closure sub-obligation, not the remaining
unrestricted generation or diagonal-comparison obligation.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.RegularizedExposure

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_415 (BrandtEndpoint BrandtEndpointSide RepeatedWord)
open ExposureReplay CutConnectivity TaggedExposure NormalizedInverse DiagonalComparison EvenCoverage

private theorem derives_of_toList_eq {source target source' target' : Word Nat}
    (derivation : Derives Rank040.basis source target)
    (sourceEq : source.toList = source'.toList)
    (targetEq : target.toList = target'.toList) : Derives Rank040.basis source' target' := by
  have sourceWordEq := Word.toList_injective sourceEq
  have targetWordEq := Word.toList_injective targetEq
  simpa only [sourceWordEq, targetWordEq] using derivation

theorem inverseRangeContracts {word : Word Nat} (witness : InverseWitness word) :
    Derives Rank040.basis
      ((word ++ witness.inverse) ++ (word ++ witness.inverse)) (word ++ witness.inverse) := by
  simpa only [Word.append_assoc] using
    Derives.appendRight witness.word_inverse_word witness.inverse

theorem inverseSourceContracts {word : Word Nat} (witness : InverseWitness word) :
    Derives Rank040.basis
      ((witness.inverse ++ word) ++ (witness.inverse ++ word)) (witness.inverse ++ word) := by
  simpa only [Word.append_assoc] using Derives.appendRight witness.inverse_word_inverse word

private theorem cubicContracts {word : Word Nat}
    (contract : Derives Rank040.basis (word ++ word) word) :
    Derives Rank040.basis ((word ++ word) ++ word) word :=
  (Derives.appendRight contract word).trans contract

theorem inverseAlternationContracts {word : Word Nat} (witness : InverseWitness word) :
    Derives Rank040.basis
      (((witness.inverse ++ word) ++ witness.inverse) ++ (word ++ witness.inverse))
      witness.inverse := by
  have first := Derives.appendRight witness.inverse_word_inverse (word ++ witness.inverse)
  have second : Derives Rank040.basis
      (witness.inverse ++ (word ++ witness.inverse)) witness.inverse := by
    simpa only [Word.append_assoc] using witness.inverse_word_inverse
  exact first.trans second

def leftFlank {word : Word Nat} (witness : InverseWitness word) (cut : Exposure word) : Word Nat :=
  ChainReplay.Context.wrap [] (word ++ witness.inverse) cut.before

def rightFlank {word : Word Nat} (witness : InverseWitness word) (cut : Exposure word) : Word Nat :=
  ChainReplay.Context.wrap cut.after (witness.inverse ++ word) []

def leftFlankInverse {word : Word Nat} (witness : InverseWitness word) (cut : Exposure word) : Word Nat :=
  ChainReplay.Context.wrap cut.after witness.inverse []

def rightFlankInverse {word : Word Nat} (witness : InverseWitness word) (cut : Exposure word) : Word Nat :=
  ChainReplay.Context.wrap [] witness.inverse cut.before

/-- The flanks are regular because of the supplied inverse of the WHOLE
word, not because the original raw factors were assumed regular. -/
def leftFlankWitness {word : Word Nat} (witness : InverseWitness word) (cut : Exposure word) :
    InverseWitness (leftFlank witness cut) where
  inverse := leftFlankInverse witness cut
  word_inverse_word := by
    apply derives_of_toList_eq
      (ChainReplay.Context.derives_wrap (cubicContracts (inverseRangeContracts witness)) [] cut.before)
    all_goals simp only [leftFlank, leftFlankInverse, ChainReplay.Context.wrap_toList,
      Word.toList_append, cut.partition, List.append_assoc, List.nil_append, List.append_nil]
  inverse_word_inverse := by
    apply derives_of_toList_eq
      (ChainReplay.Context.derives_wrap (inverseAlternationContracts witness) cut.after [])
    all_goals simp only [leftFlank, leftFlankInverse, ChainReplay.Context.wrap_toList,
      Word.toList_append, cut.partition, List.append_assoc, List.nil_append, List.append_nil]

def rightFlankWitness {word : Word Nat} (witness : InverseWitness word) (cut : Exposure word) :
    InverseWitness (rightFlank witness cut) where
  inverse := rightFlankInverse witness cut
  word_inverse_word := by
    apply derives_of_toList_eq
      (ChainReplay.Context.derives_wrap (cubicContracts (inverseSourceContracts witness)) cut.after [])
    all_goals simp only [rightFlank, rightFlankInverse, ChainReplay.Context.wrap_toList,
      Word.toList_append, cut.partition, List.append_assoc, List.nil_append, List.append_nil]
  inverse_word_inverse := by
    apply derives_of_toList_eq
      (ChainReplay.Context.derives_wrap (inverseAlternationContracts witness) [] cut.before)
    all_goals simp only [rightFlank, rightFlankInverse, ChainReplay.Context.wrap_toList,
      Word.toList_append, cut.partition, List.append_assoc, List.nil_append, List.append_nil]

theorem regularizedSourceDerives {word : Word Nat}
    (witness : InverseWitness word) (cut : Exposure word) :
    Derives Rank040.basis word (leftFlank witness cut ++ rightFlank witness cut) := by
  have first := Derives.appendRight witness.word_inverse_word (witness.inverse ++ word)
  have second : Derives Rank040.basis (word ++ (witness.inverse ++ word)) word := by
    simpa only [Word.append_assoc] using witness.word_inverse_word
  apply derives_of_toList_eq (first.trans second).symm
  · rfl
  · simp only [leftFlank, rightFlank, ChainReplay.Context.wrap_toList, Word.toList_append,
      cut.partition, List.append_assoc, List.nil_append, List.append_nil]

/-- The middle occurrence survives in the padded representative. -/
def regularizedOccurrence {word : Word Nat} {letter : Nat}
    (witness : InverseWitness word) (occurrence : Occurrence word letter) (side : BrandtEndpointSide) :
    Occurrence (leftFlank witness (occurrence.cut side) ++ rightFlank witness (occurrence.cut side))
      letter where
  before := (word ++ witness.inverse).toList ++ occurrence.before
  after := occurrence.after ++ (witness.inverse ++ word).toList
  partition := by
    cases side <;>
      simp only [leftFlank, rightFlank, ChainReplay.Context.wrap_toList, Word.toList_append,
        Occurrence.cut, occurrence.partition, List.append_assoc, List.nil_append,
        List.append_nil, List.cons_append]

theorem regularizedInsertion_eq {word : Word Nat} {letter : Nat}
    (witness : InverseWitness word) (occurrence : Occurrence word letter)
    (side : BrandtEndpointSide) (loop : Word Nat) :
    ((regularizedOccurrence witness occurrence side).cut side).insert loop =
      (leftFlank witness (occurrence.cut side) ++ (loop ++ loop)) ++
        rightFlank witness (occurrence.cut side) := by
  apply Word.toList_injective
  cases side <;>
    simp only [regularizedOccurrence, Occurrence.cut, Exposure.insert,
      leftFlank, rightFlank, ChainReplay.Context.wrap_toList, Word.toList_append,
      List.append_assoc, List.nil_append, List.append_nil, List.cons_append]

/-- The old and new insertions are equivalent by actual tagged rewriting.
This step is what makes transport BACK sound; padding is not cancellative. -/
theorem regularizedInsertionDerives {word : Word Nat} {letter : Nat}
    (witness : InverseWitness word) (occurrence : Occurrence word letter)
    (side : BrandtEndpointSide) (loop : Word Nat) :
    Derives Rank040.basis ((occurrence.cut side).insert loop)
      ((leftFlank witness (occurrence.cut side) ++ (loop ++ loop)) ++
        rightFlank witness (occurrence.cut side)) := by
  have transported := insertionDerivesAcrossRepresentatives
    (regularizedSourceDerives witness (occurrence.cut side)) letter side loop occurrence
    (regularizedOccurrence witness occurrence side)
  simpa only [regularizedInsertion_eq] using transported

/-- Product closure at EACH displayed endpoint cut, with only whole-word
regularity. Raw before/after lists are allowed to be empty. -/
theorem occurrenceAbsorbsProduct {word : Word Nat} {letter : Nat} {first second : Word Nat}
    (witness : InverseWitness word) (occurrence : Occurrence word letter) (side : BrandtEndpointSide)
    (firstAbsorbs : (occurrence.cut side).Absorbs first)
    (secondAbsorbs : (occurrence.cut side).Absorbs second) :
    (occurrence.cut side).Absorbs (first ++ second) := by
  have equivalent := regularizedSourceDerives witness (occurrence.cut side)
  have firstCut : CutAbsorbs (leftFlank witness (occurrence.cut side))
      (rightFlank witness (occurrence.cut side)) first :=
    equivalent.symm.trans
      (firstAbsorbs.trans (regularizedInsertionDerives witness occurrence side first))
  have secondCut : CutAbsorbs (leftFlank witness (occurrence.cut side))
      (rightFlank witness (occurrence.cut side)) second :=
    equivalent.symm.trans
      (secondAbsorbs.trans (regularizedInsertionDerives witness occurrence side second))
  have productCut := cutAbsorbsProduct
    (leftFlankWitness witness (occurrence.cut side))
    (rightFlankWitness witness (occurrence.cut side)) firstCut secondCut
  exact equivalent.trans
    (productCut.trans (regularizedInsertionDerives witness occurrence side (first ++ second)).symm)

theorem endpointAbsorbsProduct {word : Word Nat} {endpoint : BrandtEndpoint} {first second : Word Nat}
    (witness : InverseWitness word)
    (firstAbsorbs : EndpointAbsorbs word endpoint first)
    (secondAbsorbs : EndpointAbsorbs word endpoint second) :
    EndpointAbsorbs word endpoint (first ++ second) := fun occurrence =>
  occurrenceAbsorbsProduct witness occurrence endpoint.side
    (firstAbsorbs occurrence) (secondAbsorbs occurrence)

/-- Quantification over all genuinely derived representatives is inherited
from the existing tag transport theorem; no new regularity premise there. -/
theorem derivationalExposureAbsorbsProduct
    {word : Word Nat} {endpoint : BrandtEndpoint} {first second : Word Nat}
    (witness : InverseWitness word)
    (firstAbsorbs : DerivationalExposureAbsorbs word endpoint first)
    (secondAbsorbs : DerivationalExposureAbsorbs word endpoint second) :
    DerivationalExposureAbsorbs word endpoint (first ++ second) :=
  (derivationalExposureAbsorbs_iff word endpoint (first ++ second)).mpr
    (endpointAbsorbsProduct witness (firstAbsorbs word (Derives.refl word))
      (secondAbsorbs word (Derives.refl word)))

/-- The previous repeated-word regularity theorem supplies the witness
without an additional owner field or finite-model assumption. -/
theorem repeatedEndpointAbsorbsProduct
    {word : Word Nat} {endpoint : BrandtEndpoint} {first second : Word Nat}
    (repeated : RepeatedWord word)
    (firstAbsorbs : EndpointAbsorbs word endpoint first)
    (secondAbsorbs : EndpointAbsorbs word endpoint second) :
    EndpointAbsorbs word endpoint (first ++ second) :=
  endpointAbsorbsProduct (RepeatedCellRegularity.repeatedWordInverseWitness word repeated)
    firstAbsorbs secondAbsorbs

theorem repeatedDerivationalExposureAbsorbsProduct
    {word : Word Nat} {endpoint : BrandtEndpoint} {first second : Word Nat}
    (repeated : RepeatedWord word)
    (firstAbsorbs : DerivationalExposureAbsorbs word endpoint first)
    (secondAbsorbs : DerivationalExposureAbsorbs word endpoint second) :
    DerivationalExposureAbsorbs word endpoint (first ++ second) :=
  derivationalExposureAbsorbsProduct (RepeatedCellRegularity.repeatedWordInverseWitness word repeated)
    firstAbsorbs secondAbsorbs

structure EvenEndpointAbsorbs (word : Word Nat) (endpoint : BrandtEndpoint) (loop : Word Nat) : Prop where
  even : ZeroParity loop
  absorbs : EndpointAbsorbs word endpoint loop

theorem evenEndpointSquare_iff (word : Word Nat) (endpoint : BrandtEndpoint) (loop : Word Nat) :
    EvenEndpointAbsorbs word endpoint (loop ++ loop) ↔ EndpointAbsorbs word endpoint loop :=
  ⟨fun witness => (endpointAbsorbsSquare_iff word endpoint loop).mp witness.absorbs,
    fun witness => ⟨zeroParitySquare loop, (endpointAbsorbsSquare_iff word endpoint loop).mpr witness⟩⟩

theorem EvenEndpointAbsorbs.product
    {word : Word Nat} {endpoint : BrandtEndpoint} {first second : Word Nat}
    (witness : InverseWitness word)
    (left : EvenEndpointAbsorbs word endpoint first) (right : EvenEndpointAbsorbs word endpoint second) :
    EvenEndpointAbsorbs word endpoint (first ++ second) :=
  ⟨zeroParityAppend left.even right.even, endpointAbsorbsProduct witness left.absorbs right.absorbs⟩

theorem zeroParityRotation {first second : Word Nat} (even : ZeroParity (first ++ second)) :
    ZeroParity (second ++ first) := by
  intro letter
  have parity := even letter
  simpa only [Word.toList_append, List.count_append, Nat.add_comm] using parity

/-- Rotation retains the actual moving-cut exposure condition. -/
theorem evenEndpointRotation
    (word first second remainder : Word Nat) (before after : List Nat)
    (partition : word.toList = before ++ first.toList ++ remainder.toList ++ after)
    (absorbed : EvenEndpointAbsorbs word (BrandtEndpoint.incoming first.head) (first ++ second)) :
    EvenEndpointAbsorbs word (BrandtEndpoint.incoming remainder.head) (second ++ first) :=
  ⟨zeroParityRotation absorbed.even,
    endpointAbsorbs_rotation word first second remainder before after partition absorbed.absorbs⟩

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.RegularizedExposure
