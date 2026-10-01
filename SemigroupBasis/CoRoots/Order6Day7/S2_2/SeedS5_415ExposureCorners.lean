import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415RegularizedExposure

/-!
# Rank040: actual idempotent corners of a regular source word

For an ACTUAL inverse r of w=P Q, the corner is Q r P. It is idempotent
in the frozen-law term quotient. Tagged insertion and the regularized-cut
criterion identify these specific corners along endpoint connectivity.
This is NOT the refuted assertion that arbitrary ambient closed loops
of zero parity are equal. Every equality here uses the supplied inverse.

The corner also gives explicit regularized letter arrows and prefix
transporters. No graph-completeness or diagonal-lift field is assumed.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.ExposureCorners

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_415 (BrandtEndpoint BrandtEndpointSide BrandtEndpointConnected)
open ExposureReplay CutConnectivity RegularizedExposure

abbrev Carrier := TermSemigroup Rank040.basis
abbrev G : Semigroup Carrier := termSemigroup Rank040.basis
abbrev value (word : Word Nat) : Carrier := termClass Rank040.basis word

theorem value_of_derives {left right : Word Nat} (derived : Derives Rank040.basis left right) :
    value left = value right := (termClass_eq_iff_derives Rank040.basis).mpr derived

private theorem derives_of_toList_eq {source target source' target' : Word Nat}
    (derivation : Derives Rank040.basis source target)
    (sourceEq : source.toList = source'.toList)
    (targetEq : target.toList = target'.toList) : Derives Rank040.basis source' target' := by
  have sourceWordEq := Word.toList_injective sourceEq
  have targetWordEq := Word.toList_injective targetEq
  simpa only [sourceWordEq, targetWordEq] using derivation

def cornerWord {word : Word Nat} (witness : InverseWitness word) (cut : Exposure word) : Word Nat :=
  ChainReplay.Context.wrap cut.after witness.inverse cut.before

theorem cornerIdempotentDerives {word : Word Nat} (witness : InverseWitness word) (cut : Exposure word) :
    Derives Rank040.basis (cornerWord witness cut ++ cornerWord witness cut) (cornerWord witness cut) := by
  apply derives_of_toList_eq
    (ChainReplay.Context.derives_wrap witness.inverse_word_inverse cut.after cut.before)
  all_goals simp only [cornerWord, ChainReplay.Context.wrap_toList, Word.toList_append,
    cut.partition, List.append_assoc]

theorem cornerIdempotent {word : Word Nat} (witness : InverseWitness word) (cut : Exposure word) :
    G.IsIdempotent (value (cornerWord witness cut)) :=
  value_of_derives (cornerIdempotentDerives witness cut)

theorem leftFlankSourceDerives {word : Word Nat} (witness : InverseWitness word) (cut : Exposure word) :
    Derives Rank040.basis (leftFlankInverse witness cut ++ leftFlank witness cut) (cornerWord witness cut) := by
  apply derives_of_toList_eq
    (ChainReplay.Context.derives_wrap witness.inverse_word_inverse cut.after cut.before)
  all_goals simp only [cornerWord, leftFlank, leftFlankInverse, ChainReplay.Context.wrap_toList,
    Word.toList_append, cut.partition, List.append_assoc, List.nil_append, List.append_nil]

theorem rightFlankRangeDerives {word : Word Nat} (witness : InverseWitness word) (cut : Exposure word) :
    Derives Rank040.basis (rightFlank witness cut ++ rightFlankInverse witness cut) (cornerWord witness cut) := by
  apply derives_of_toList_eq
    (ChainReplay.Context.derives_wrap witness.inverse_word_inverse cut.after cut.before)
  all_goals simp only [cornerWord, rightFlank, rightFlankInverse, ChainReplay.Context.wrap_toList,
    Word.toList_append, cut.partition, List.append_assoc, List.nil_append, List.append_nil]

theorem leftFlankRangeDerives {word : Word Nat} (witness : InverseWitness word) (cut : Exposure word) :
    Derives Rank040.basis (leftFlank witness cut ++ leftFlankInverse witness cut) (word ++ witness.inverse) := by
  apply derives_of_toList_eq (Derives.appendRight witness.word_inverse_word witness.inverse)
  all_goals simp only [leftFlank, leftFlankInverse, ChainReplay.Context.wrap_toList,
    Word.toList_append, cut.partition, List.append_assoc, List.nil_append, List.append_nil]

theorem regularizedCornerValue {word : Word Nat} (witness : InverseWitness word) (cut : Exposure word) :
    G.mul (G.mul (value (leftFlankInverse witness cut)) (value (leftFlank witness cut)))
      (G.mul (value (rightFlank witness cut)) (value (rightFlankInverse witness cut))) =
        value (cornerWord witness cut) := by
  have first := value_of_derives (leftFlankSourceDerives witness cut)
  have second := value_of_derives (rightFlankRangeDerives witness cut)
  change G.mul (value (leftFlankInverse witness cut ++ leftFlank witness cut))
    (value (rightFlank witness cut ++ rightFlankInverse witness cut)) = _
  rw [first, second]
  exact cornerIdempotent witness cut

/-- The exact quotient criterion for an original endpoint cut. Transport
to and from the regularized source is by actual tagged derivations. -/
theorem occurrenceAbsorbs_iff_corner {word : Word Nat} {letter : Nat}
    (witness : InverseWitness word) (occurrence : Occurrence word letter)
    (side : BrandtEndpointSide) (loop : Word Nat) :
    (occurrence.cut side).Absorbs loop ↔
      value (cornerWord witness (occurrence.cut side)) =
        G.mul (value (cornerWord witness (occurrence.cut side))) (G.mul (value loop) (value loop)) := by
  let cut := occurrence.cut side
  have source := regularizedSourceDerives witness cut
  have inserted := regularizedInsertionDerives witness occurrence side loop
  have cutIff : (occurrence.cut side).Absorbs loop ↔
      CutAbsorbs (leftFlank witness cut) (rightFlank witness cut) loop :=
    ⟨fun absorbed => source.symm.trans (absorbed.trans inserted),
      fun absorbed => source.trans (absorbed.trans inserted.symm)⟩
  have valueIff : CutAbsorbs (leftFlank witness cut) (rightFlank witness cut) loop ↔
      G.mul (value (leftFlank witness cut)) (value (rightFlank witness cut)) =
        G.mul (G.mul (value (leftFlank witness cut)) (G.mul (value loop) (value loop)))
          (value (rightFlank witness cut)) :=
    (termClass_eq_iff_derives Rank040.basis).symm
  have criterion := regularSandwichInsertionIff G (termSemigroup_models Rank040.basis)
    (leftFlankWitness witness cut).termInverse (rightFlankWitness witness cut).termInverse
    (modelSquareIdempotent G (termSemigroup_models Rank040.basis) (value loop))
  have combined := cutIff.trans (valueIff.trans criterion)
  simpa only [leftFlankWitness, rightFlankWitness, regularizedCornerValue] using combined

theorem occurrenceAbsorbsOwnCorner {word : Word Nat} {letter : Nat}
    (witness : InverseWitness word) (occurrence : Occurrence word letter) (side : BrandtEndpointSide) :
    (occurrence.cut side).Absorbs (cornerWord witness (occurrence.cut side)) := by
  apply (occurrenceAbsorbs_iff_corner witness occurrence side _).mpr
  have idempotent := cornerIdempotent witness (occurrence.cut side)
  change G.mul (value (cornerWord witness (occurrence.cut side)))
    (value (cornerWord witness (occurrence.cut side))) = _ at idempotent
  simp only [idempotent]

/-- Connected endpoints have equal ACTUAL corner idempotents, not equal
arbitrary ambient loop words. The inverse witness is essential data. -/
theorem connectedCornerValues {word : Word Nat} {source target : BrandtEndpoint}
    (witness : InverseWitness word) (connected : BrandtEndpointConnected word source target)
    (first : Occurrence word source.letter) (second : Occurrence word target.letter) :
    value (cornerWord witness (first.cut source.side)) =
      value (cornerWord witness (second.cut target.side)) := by
  have firstIdempotent := cornerIdempotent witness (first.cut source.side)
  have secondIdempotent := cornerIdempotent witness (second.cut target.side)
  have firstAtSecond := (occurrenceAbsorbsOwnCorner witness first source.side).trans
    (connectedEndpointInsertions connected (cornerWord witness (first.cut source.side)) first second)
  have secondAtFirst := (occurrenceAbsorbsOwnCorner witness second target.side).trans
    (connectedEndpointInsertions connected.symm (cornerWord witness (second.cut target.side)) second first)
  have secondBelow := (occurrenceAbsorbs_iff_corner witness second target.side _).mp firstAtSecond
  have firstBelow := (occurrenceAbsorbs_iff_corner witness first source.side _).mp secondAtFirst
  change G.mul (value (cornerWord witness (first.cut source.side)))
    (value (cornerWord witness (first.cut source.side))) = _ at firstIdempotent
  change G.mul (value (cornerWord witness (second.cut target.side)))
    (value (cornerWord witness (second.cut target.side))) = _ at secondIdempotent
  rw [firstIdempotent] at secondBelow
  rw [secondIdempotent] at firstBelow
  exact firstBelow.trans
    ((modelIdempotentsCommute G (termSemigroup_models Rank040.basis)
      firstIdempotent secondIdempotent).trans secondBelow.symm)

theorem connectedCornersDerives {word : Word Nat} {source target : BrandtEndpoint}
    (witness : InverseWitness word) (connected : BrandtEndpointConnected word source target)
    (first : Occurrence word source.letter) (second : Occurrence word target.letter) :
    Derives Rank040.basis (cornerWord witness (first.cut source.side))
      (cornerWord witness (second.cut target.side)) :=
  (termClass_eq_iff_derives Rank040.basis).mp (connectedCornerValues witness connected first second)

def backWord {word : Word Nat} {letter : Nat}
    (witness : InverseWitness word) (occurrence : Occurrence word letter) : Word Nat :=
  ChainReplay.Context.wrap occurrence.after witness.inverse occurrence.before

theorem incomingCorner_eq {word : Word Nat} {letter : Nat}
    (witness : InverseWitness word) (occurrence : Occurrence word letter) :
    cornerWord witness (occurrence.cut .incoming) = Word.singleton letter ++ backWord witness occurrence := by
  apply Word.toList_injective
  simp only [cornerWord, backWord, Occurrence.cut, ChainReplay.Context.wrap_toList,
    Word.toList_append, Word.toList_singleton, List.cons_append, List.nil_append]

theorem outgoingCorner_eq {word : Word Nat} {letter : Nat}
    (witness : InverseWitness word) (occurrence : Occurrence word letter) :
    cornerWord witness (occurrence.cut .outgoing) = backWord witness occurrence ++ Word.singleton letter := by
  apply Word.toList_injective
  simp only [cornerWord, backWord, Occurrence.cut, ChainReplay.Context.wrap_toList,
    Word.toList_append, Word.toList_singleton, List.append_assoc]

theorem backInnerInverseDerives {word : Word Nat} {letter : Nat}
    (witness : InverseWitness word) (occurrence : Occurrence word letter) :
    Derives Rank040.basis
      ((backWord witness occurrence ++ Word.singleton letter) ++ backWord witness occurrence)
      (backWord witness occurrence) := by
  apply derives_of_toList_eq
    (ChainReplay.Context.derives_wrap witness.inverse_word_inverse occurrence.after occurrence.before)
  all_goals simp only [backWord, ChainReplay.Context.wrap_toList, Word.toList_append,
    Word.toList_singleton, occurrence.partition, List.append_assoc, List.cons_append, List.nil_append]

def regularizedLetter {word : Word Nat} {letter : Nat}
    (witness : InverseWitness word) (occurrence : Occurrence word letter) : Word Nat :=
  (Word.singleton letter ++ backWord witness occurrence) ++ Word.singleton letter

def regularizedLetterWitness {word : Word Nat} {letter : Nat}
    (witness : InverseWitness word) (occurrence : Occurrence word letter) :
    InverseWitness (regularizedLetter witness occurrence) :=
  NormalizedInverse.reverseWitness (inverseWitnessOfInner (backWord witness occurrence)
    (Word.singleton letter) (backInnerInverseDerives witness occurrence))

theorem regularizedLetterRangeDerives {word : Word Nat} {letter : Nat}
    (witness : InverseWitness word) (occurrence : Occurrence word letter) :
    Derives Rank040.basis (regularizedLetter witness occurrence ++ backWord witness occurrence)
      (cornerWord witness (occurrence.cut .incoming)) := by
  rw [incomingCorner_eq]
  simpa only [regularizedLetter, Word.append_assoc] using
    Derives.prepend (Word.singleton letter) (backInnerInverseDerives witness occurrence)

theorem regularizedLetterSourceDerives {word : Word Nat} {letter : Nat}
    (witness : InverseWitness word) (occurrence : Occurrence word letter) :
    Derives Rank040.basis (backWord witness occurrence ++ regularizedLetter witness occurrence)
      (cornerWord witness (occurrence.cut .outgoing)) := by
  rw [outgoingCorner_eq]
  simpa only [regularizedLetter, Word.append_assoc] using
    Derives.appendRight (backInnerInverseDerives witness occurrence) (Word.singleton letter)

theorem regularizedLetterValue {word : Word Nat} {letter : Nat}
    (witness : InverseWitness word) (occurrence : Occurrence word letter) :
    value (regularizedLetter witness occurrence) =
      G.mul (value (cornerWord witness (occurrence.cut .incoming))) (value (Word.singleton letter)) ∧
    value (regularizedLetter witness occurrence) =
      G.mul (value (Word.singleton letter)) (value (cornerWord witness (occurrence.cut .outgoing))) := by
  rw [incomingCorner_eq, outgoingCorner_eq]
  constructor
  · rfl
  · exact congrArg value (Word.append_assoc _ _ _)

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.ExposureCorners
