import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415DiagonalParityLift

/-!
# Rank040: even absorption, and the exact boundary of an even-loop screen

All constructors below require actual frozen-basis absorption witnesses.
The relation x² = x⁴ reflects absorption of a squared loop back to the
original loop, at the head and at every literal endpoint exposure. Hence
the even-only ClosedReturnDerivation obligation is equivalent to the old
all-loop obligation; the parity restriction alone does not discharge it.

The concrete four-letter grammar gap is nevertheless genuinely absorbed
by its square bank. A literal grammar miss is not a basis countermodel.
The finite screen is evidence outside this module, not a proof premise.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.EvenCoverage

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_415
open BrandtParityBridge HeadRetargetBoundary ClosedReturnReplay ExposureReplay
open CutConnectivity NormalizedInverse DiagonalComparison RepeatedCellRegularity

theorem closedReturnAppend {word first second : Word Nat}
    (left : ClosedReturnWord word first) (right : ClosedReturnWord word second) :
    ClosedReturnWord word (first ++ second) where
  support := by
    intro letter member
    rw [Word.toList_append] at member
    rcases List.mem_append.mp member with member | member
    · exact left.support letter member
    · exact right.support letter member
  initial := left.initial
  internal := by
    intro source target member
    rw [Word.adjacentPairs_append] at member
    rcases List.mem_append.mp member with member | member
    · exact left.internal source target member
    · rcases List.mem_cons.mp member with same | member
      · cases same
        exact left.returns.trans right.initial.symm
      · exact right.internal source target member
  returns := by simpa only [Word.final_append] using right.returns

theorem closedReturnSquare {word loop : Word Nat} (closed : ClosedReturnWord word loop) :
    ClosedReturnWord word (loop ++ loop) := closedReturnAppend closed closed

/-- Square-root reflection uses x² = x⁴, never cancellation. -/
theorem squareAbsorbsSquare_iff (word loop : Word Nat) :
    SquareAbsorbs word (loop ++ loop) ↔ SquareAbsorbs word loop := by
  have expansion : Derives Rank040.basis ((loop ++ loop) ++ word)
      (((loop ++ loop) ++ (loop ++ loop)) ++ word) := by
    simpa only [Word.append_assoc] using Derives.appendRight (derivesPairExpansion loop) word
  exact ⟨fun absorbed => absorbed.trans expansion.symm,
    fun absorbed => absorbed.trans expansion⟩

theorem exposureAbsorbsSquare_iff {word : Word Nat} (cut : Exposure word) (loop : Word Nat) :
    cut.Absorbs (loop ++ loop) ↔ cut.Absorbs loop := by
  have expansion : Derives Rank040.basis (cut.insert loop) (cut.insert (loop ++ loop)) := by
    have pair : Derives Rank040.basis (loop ++ loop) ((loop ++ loop) ++ (loop ++ loop)) := by
      simpa only [Word.append_assoc] using derivesPairExpansion loop
    exact ChainReplay.Context.derives_wrap pair cut.before cut.after
  exact ⟨fun absorbed => absorbed.trans expansion.symm,
    fun absorbed => absorbed.trans expansion⟩

theorem endpointAbsorbsSquare_iff (word : Word Nat) (endpoint : BrandtEndpoint) (loop : Word Nat) :
    EndpointAbsorbs word endpoint (loop ++ loop) ↔ EndpointAbsorbs word endpoint loop := by
  constructor
  · intro absorbed occurrence
    exact (exposureAbsorbsSquare_iff (occurrence.cut endpoint.side) loop).mp (absorbed occurrence)
  · intro absorbed occurrence
    exact (exposureAbsorbsSquare_iff (occurrence.cut endpoint.side) loop).mpr (absorbed occurrence)

/-- OPEN, and not weaker than the all-loop obligation. -/
def EvenClosedReturnDerivation : Prop :=
  ∀ word loop : Word Nat, ClosedReturnWord word loop → ZeroParity loop → SquareAbsorbs word loop

theorem evenClosedReturnDerivation_iff : EvenClosedReturnDerivation ↔ ClosedReturnDerivation := by
  constructor
  · intro owner word loop closed
    exact (squareAbsorbsSquare_iff word loop).mp
      (owner word (loop ++ loop) (closedReturnSquare closed) (zeroParitySquare loop))
  · intro owner word loop closed _
    exact owner word loop closed

structure EvenAbsorbs (word loop : Word Nat) : Prop where
  even : ZeroParity loop
  absorbs : SquareAbsorbs word loop

theorem EvenAbsorbs.closed {word loop : Word Nat} (witness : EvenAbsorbs word loop) :
    ClosedReturnWord word loop := witness.absorbs.closedReturnWord

theorem evenAbsorbsSquare_iff (word loop : Word Nat) :
    EvenAbsorbs word (loop ++ loop) ↔ SquareAbsorbs word loop :=
  ⟨fun witness => (squareAbsorbsSquare_iff word loop).mp witness.absorbs,
    fun witness => ⟨zeroParitySquare loop, (squareAbsorbsSquare_iff word loop).mpr witness⟩⟩

theorem EvenAbsorbs.product {word first second : Word Nat}
    (left : EvenAbsorbs word first) (right : EvenAbsorbs word second) :
    EvenAbsorbs word (first ++ second) :=
  ⟨zeroParityAppend left.even right.even, left.absorbs.product right.absorbs⟩

theorem EvenAbsorbs.sourceDerives {source target loop : Word Nat}
    (witness : EvenAbsorbs source loop) (equivalent : Derives Rank040.basis source target) :
    EvenAbsorbs target loop :=
  ⟨witness.even, SquareAbsorbs.ofDerives equivalent.symm witness.absorbs⟩

theorem EvenAbsorbs.loopDerives {word first second : Word Nat}
    (witness : EvenAbsorbs word first) (equivalent : Derives Rank040.basis first second) :
    EvenAbsorbs word second :=
  ⟨zeroParityOfSignature (signature_of_derives equivalent) witness.even,
    witness.absorbs.loopCongruence equivalent⟩

theorem evenDoubleSandwich (first second : Word Nat) :
    ZeroParity (((first ++ second) ++ second) ++ first) := by
  intro letter
  simp only [Word.toList_append, List.count_append]
  omega

theorem evenTriangle (first second third : Word Nat) :
    ZeroParity (triangleWord first second third) := by
  intro letter
  simp only [triangleWord, Word.toList_append, List.count_append]
  omega

theorem absorbedDoubleSandwich {word first second : Word Nat}
    (left : SquareAbsorbs word first) (right : SquareAbsorbs word second) :
    EvenAbsorbs word (((first ++ second) ++ second) ++ first) :=
  ⟨evenDoubleSandwich first second, ((left.product right).product right).product left⟩

theorem absorbedTriangle {word first second third : Word Nat}
    (left : SquareAbsorbs word first) (middle : SquareAbsorbs word second)
    (right : SquareAbsorbs word third) : EvenAbsorbs word (triangleWord first second third) :=
  ⟨evenTriangle first second third,
    ((((left.product middle).product left).product right).product middle).product right⟩

def literalGapSource : Word Nat := Word.mk 0 [1, 1, 0]
def exposedGapSource : Word Nat := Word.mk 0 [0, 1, 1]
def literalGapLoop : Word Nat := Word.mk 0 [0]

/-- The source-representative repair found by the screen is exactly law04
backward, with singleton block substitution and empty outer contexts. -/
theorem literalGapSourceDerives : Derives Rank040.basis literalGapSource exposedGapSource :=
  (Derives.fromBasis (e := law04) (by simp [Rank040.basis])).symm

theorem literalGapEvenAbsorbed : EvenAbsorbs literalGapSource literalGapLoop := by
  apply (evenAbsorbsSquare_iff literalGapSource (Word.singleton 0)).mpr
  exact SquareAbsorbs.ofDerives literalGapSourceDerives
    ((SquareAbsorbs.square (Word.singleton 0)).appendRight (Word.mk 1 [1]))

def grammarGap : Word Nat := Word.mk 0 [1, 0, 2, 1, 3, 2, 3]
def grammarGapBank : Word Nat := squareLetterBank 0 [1, 2, 3]

theorem grammarGapZeroParity : ZeroParity grammarGap := by
  intro letter
  simp only [grammarGap, Word.toList, List.count_cons, List.count_nil]
  omega

/-- The actual absorption of abacbdcd needs neither a claimed grammar
coverage theorem nor an equality between the loop and its ambient bank. -/
theorem grammarGapAbsorbed : SquareAbsorbs grammarGapBank grammarGap := by
  apply squareLetterBankWordAbsorbs 0 [1, 2, 3] grammarGap
  intro letter member
  simpa [grammarGap, Word.toList, or_assoc, or_left_comm, or_comm] using member

theorem grammarGapEvenAbsorbed : EvenAbsorbs grammarGapBank grammarGap :=
  ⟨grammarGapZeroParity, grammarGapAbsorbed⟩

theorem grammarGapClosed : ClosedReturnWord grammarGapBank grammarGap :=
  grammarGapEvenAbsorbed.closed

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.EvenCoverage
