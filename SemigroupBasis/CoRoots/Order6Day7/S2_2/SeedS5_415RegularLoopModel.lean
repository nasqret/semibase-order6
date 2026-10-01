import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415ExposureCorners

/-!
# Rank040: graph-closed paths act in actual local groups

The source has a supplied frozen-basis inverse. Actual exposure corners
give a groupoid of regularized letters, and the already-proved endpoint
connections identify its objects. Every graph-closed positive path is a
local-group element. The frozen square law makes its square the corner
identity, which yields an ACTUAL closed-return derivation.

No finite coverage result or unproved generator induction is imported.
The subsequent zero-parity comparison is still a separate proof task.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.RegularLoopModel

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_415 (BrandtEndpoint BrandtEndpointSide BrandtEndpointConnected)
open ExposureReplay CutConnectivity RegularizedExposure ExposureCorners
open HeadRetargetBoundary ClosedReturnReplay

/-- An actual regular element with its specified range and source
idempotents. No global regularity assumption is made on the semigroup. -/
structure Arrow {S : Type u} (H : Semigroup S) (start finish element : S) where
  inverse : S
  inverse_laws : H.IsInverse element inverse
  range_eq : H.mul element inverse = start
  source_eq : H.mul inverse element = finish

theorem Arrow.startIdempotent {H : Semigroup S} {start finish element : S}
    (arrow : Arrow H start finish element) : H.IsIdempotent start := by
  rw [← arrow.range_eq]
  exact arrow.inverse_laws.mul_idempotent

theorem Arrow.finishIdempotent {H : Semigroup S} {start finish element : S}
    (arrow : Arrow H start finish element) : H.IsIdempotent finish := by
  rw [← arrow.source_eq]
  exact arrow.inverse_laws.reverse_mul_idempotent

theorem Arrow.leftUnit {H : Semigroup S} {start finish element : S}
    (arrow : Arrow H start finish element) : H.mul start element = element := by
  rw [← arrow.range_eq]
  exact arrow.inverse_laws.1

theorem Arrow.rightUnit {H : Semigroup S} {start finish element : S}
    (arrow : Arrow H start finish element) : H.mul element finish = element := by
  rw [← arrow.source_eq, ← H.assoc]
  exact arrow.inverse_laws.1

theorem Arrow.inverseLeftUnit {H : Semigroup S} {start finish element : S}
    (arrow : Arrow H start finish element) : H.mul finish arrow.inverse = arrow.inverse := by
  exact (congrArg (fun middle => H.mul middle arrow.inverse) arrow.source_eq.symm).trans
    arrow.inverse_laws.2

theorem Arrow.inverseRightUnit {H : Semigroup S} {start finish element : S}
    (arrow : Arrow H start finish element) : H.mul arrow.inverse start = arrow.inverse := by
  exact (congrArg (H.mul arrow.inverse) arrow.range_eq.symm).trans
    ((H.assoc _ _ _).symm.trans arrow.inverse_laws.2)

def Arrow.reverse {H : Semigroup S} {start finish element : S}
    (arrow : Arrow H start finish element) : Arrow H finish start arrow.inverse :=
  ⟨element, arrow.inverse_laws.symm, arrow.source_eq, arrow.range_eq⟩

def Arrow.identity {H : Semigroup S} {anchor : S} (idempotent : H.IsIdempotent anchor) :
    Arrow H anchor anchor anchor where
  inverse := anchor
  inverse_laws := by
    change H.mul anchor anchor = anchor at idempotent
    constructor <;> change H.mul (H.mul anchor anchor) anchor = anchor <;>
      simp only [idempotent]
  range_eq := idempotent
  source_eq := idempotent

/-- Exact matching-corner composition. This uses actual inverse equations,
not an assumed representation theorem for an ambient graph. -/
def Arrow.comp {H : Semigroup S} {start middle finish first second : S}
    (left : Arrow H start middle first) (right : Arrow H middle finish second) :
    Arrow H start finish (H.mul first second) := by
  have rangeEq : H.mul (H.mul first second) (H.mul right.inverse left.inverse) = start := by
    calc
      H.mul (H.mul first second) (H.mul right.inverse left.inverse) =
          H.mul (H.mul first (H.mul second right.inverse)) left.inverse := by simp only [H.assoc]
      _ = H.mul (H.mul first middle) left.inverse := by rw [right.range_eq]
      _ = H.mul first left.inverse := by rw [left.rightUnit]
      _ = start := left.range_eq
  have sourceEq : H.mul (H.mul right.inverse left.inverse) (H.mul first second) = finish := by
    calc
      H.mul (H.mul right.inverse left.inverse) (H.mul first second) =
          H.mul right.inverse (H.mul (H.mul left.inverse first) second) := by simp only [H.assoc]
      _ = H.mul right.inverse (H.mul middle second) := by rw [left.source_eq]
      _ = H.mul right.inverse second := by rw [right.leftUnit]
      _ = finish := right.source_eq
  refine ⟨H.mul right.inverse left.inverse, ⟨?_, ?_⟩, rangeEq, sourceEq⟩
  · rw [rangeEq, ← H.assoc, left.leftUnit]
  · rw [sourceEq, ← H.assoc, right.inverseLeftUnit]

theorem Arrow.cycleSquare {H : Semigroup S} {anchor element : S}
    (arrow : Arrow H anchor anchor element) (commute : H.IdempotentsCommute)
    (square : H.IsIdempotent (H.mul element element)) : H.mul element element = anchor := by
  change H.mul (H.mul element element) (H.mul element element) = H.mul element element at square
  let doubled := arrow.comp arrow
  have selfInverse : H.IsInverse (H.mul element element) (H.mul element element) := by
    constructor <;> change H.mul (H.mul (H.mul element element) (H.mul element element))
      (H.mul element element) = H.mul element element <;> simp only [square]
  have inverseEq := commute.inverse_unique doubled.inverse_laws selfInverse
  have range := doubled.range_eq
  rw [inverseEq] at range
  exact square.symm.trans range

theorem Arrow.cycleInverse_self {H : Semigroup S} {anchor element : S}
    (arrow : Arrow H anchor anchor element) (commute : H.IdempotentsCommute)
    (square : H.IsIdempotent (H.mul element element)) : arrow.inverse = element := by
  have squareEq := arrow.cycleSquare commute square
  have selfInverse : H.IsInverse element element := by
    constructor <;> change H.mul (H.mul element element) element = element <;>
      rw [squareEq, arrow.leftUnit]
  exact commute.inverse_unique arrow.inverse_laws selfInverse

theorem cycleSquare {anchor element : Carrier} (arrow : Arrow G anchor anchor element) :
    G.mul element element = anchor :=
  arrow.cycleSquare (modelIdempotentsCommute G (termSemigroup_models Rank040.basis))
    (modelSquareIdempotent G (termSemigroup_models Rank040.basis) element)

theorem cycleInverse_self {anchor element : Carrier} (arrow : Arrow G anchor anchor element) :
    arrow.inverse = element :=
  arrow.cycleInverse_self (modelIdempotentsCommute G (termSemigroup_models Rank040.basis))
    (modelSquareIdempotent G (termSemigroup_models Rank040.basis) element)

theorem cycleArrowsCommute {anchor first second : Carrier}
    (left : Arrow G anchor anchor first) (right : Arrow G anchor anchor second) :
    G.mul first second = G.mul second first := by
  have reverseProduct := cycleInverse_self (left.comp right)
  change G.mul right.inverse left.inverse = G.mul first second at reverseProduct
  rw [cycleInverse_self left, cycleInverse_self right] at reverseProduct
  exact reverseProduct.symm

noncomputable def chosenOccurrence (word : Word Nat) (letter : Nat) (member : letter ∈ word.toList) :
    Occurrence word letter := Classical.choice (occurrence_exists member)

/-- A total corner assignment. Absent endpoints use the actual head
anchor; all supported endpoints use a chosen genuine occurrence. -/
noncomputable def endpointCorner {word : Word Nat} (witness : InverseWitness word)
    (endpoint : BrandtEndpoint) : Carrier := by
  classical
  exact if member : endpoint.letter ∈ word.toList then
    value (cornerWord witness ((chosenOccurrence word endpoint.letter member).cut endpoint.side))
  else value (word ++ witness.inverse)

theorem endpointCorner_atOccurrence {word : Word Nat} (witness : InverseWitness word)
    (endpoint : BrandtEndpoint) (occurrence : Occurrence word endpoint.letter) :
    endpointCorner witness endpoint = value (cornerWord witness (occurrence.cut endpoint.side)) := by
  classical
  simp only [endpointCorner, dif_pos occurrence.member]
  exact connectedCornerValues witness (BrandtEndpointConnected.refl endpoint)
    (chosenOccurrence word endpoint.letter occurrence.member) occurrence

theorem endpointCorner_connected {word : Word Nat} (witness : InverseWitness word)
    {source target : BrandtEndpoint} (connected : BrandtEndpointConnected word source target) :
    endpointCorner witness source = endpointCorner witness target := by
  classical
  by_cases sourceMember : source.letter ∈ word.toList
  · have targetMember := (connectedEndpointMembership connected).mp sourceMember
    simp only [endpointCorner, dif_pos sourceMember, dif_pos targetMember]
    exact connectedCornerValues witness connected (chosenOccurrence word source.letter sourceMember)
      (chosenOccurrence word target.letter targetMember)
  · have targetAbsent : ¬ target.letter ∈ word.toList :=
      fun member => sourceMember ((connectedEndpointMembership connected).mpr member)
    simp only [endpointCorner, dif_neg sourceMember, dif_neg targetAbsent]

theorem endpointCorner_idempotent {word : Word Nat} (witness : InverseWitness word)
    (endpoint : BrandtEndpoint) : G.IsIdempotent (endpointCorner witness endpoint) := by
  classical
  by_cases member : endpoint.letter ∈ word.toList
  · simp only [endpointCorner, dif_pos member]
    exact cornerIdempotent witness _
  · simp only [endpointCorner, dif_neg member]
    exact witness.termInverse.mul_idempotent

def occurrenceArrow {word : Word Nat} {letter : Nat}
    (witness : InverseWitness word) (occurrence : Occurrence word letter) :
    Arrow G (value (cornerWord witness (occurrence.cut .incoming)))
      (value (cornerWord witness (occurrence.cut .outgoing))) (value (regularizedLetter witness occurrence)) where
  inverse := value (backWord witness occurrence)
  inverse_laws := (regularizedLetterWitness witness occurrence).termInverse
  range_eq := value_of_derives (regularizedLetterRangeDerives witness occurrence)
  source_eq := value_of_derives (regularizedLetterSourceDerives witness occurrence)

noncomputable def letterArrow {word : Word Nat} (witness : InverseWitness word)
    (letter : Nat) (member : letter ∈ word.toList) :
    Arrow G (endpointCorner witness (BrandtEndpoint.incoming letter))
      (endpointCorner witness (BrandtEndpoint.outgoing letter))
      (G.mul (endpointCorner witness (BrandtEndpoint.incoming letter)) (value (Word.singleton letter))) := by
  let occurrence := chosenOccurrence word letter member
  rw [endpointCorner_atOccurrence witness (BrandtEndpoint.incoming letter) occurrence,
    endpointCorner_atOccurrence witness (BrandtEndpoint.outgoing letter) occurrence]
  simp only [BrandtEndpoint.incoming, BrandtEndpoint.outgoing]
  rw [← (regularizedLetterValue witness occurrence).1]
  exact occurrenceArrow witness occurrence

/-- Every supported directed word path is an ACTUAL arrow between its
endpoint corners. This is a structural induction with no word bound. -/
theorem wordPathArrow {word : Word Nat} (witness : InverseWitness word) (path : Word Nat)
    (support : ∀ letter, letter ∈ path.toList → letter ∈ word.toList)
    (internal : ∀ first second, (first, second) ∈ path.adjacentPairs →
      BrandtEndpointConnected word (BrandtEndpoint.outgoing first) (BrandtEndpoint.incoming second)) :
    Nonempty (Arrow G (endpointCorner witness (BrandtEndpoint.incoming path.head))
      (endpointCorner witness (BrandtEndpoint.outgoing path.final))
      (G.mul (endpointCorner witness (BrandtEndpoint.incoming path.head)) (value path))) := by
  cases path with
  | mk head tail =>
    induction tail generalizing head with
    | nil =>
      exact ⟨letterArrow witness head (support head (by simp [Word.toList]))⟩
    | cons next rest ih =>
      let suffix := Word.mk next rest
      have suffixSupport : ∀ letter, letter ∈ suffix.toList → letter ∈ word.toList :=
        fun letter member => support letter (List.mem_cons_of_mem head member)
      have suffixInternal : ∀ first second, (first, second) ∈ suffix.adjacentPairs →
          BrandtEndpointConnected word (BrandtEndpoint.outgoing first) (BrandtEndpoint.incoming second) :=
        fun first second member => internal first second (List.mem_cons_of_mem (head, next) member)
      obtain ⟨tailArrow⟩ := ih next suffixSupport suffixInternal
      have headArrow := letterArrow witness head (support head (by simp [Word.toList]))
      have connected := internal head next (by simp [Word.adjacentPairs, Word.adjacentPairsFrom])
      have endpoints := endpointCorner_connected witness connected
      have aligned : Arrow G (endpointCorner witness (BrandtEndpoint.outgoing head))
          (endpointCorner witness (BrandtEndpoint.outgoing suffix.final))
          (G.mul (endpointCorner witness (BrandtEndpoint.outgoing head)) (value suffix)) := by
        simpa only [endpoints] using tailArrow
      have assembled := headArrow.comp aligned
      have valueEq :
          G.mul (G.mul (endpointCorner witness (BrandtEndpoint.incoming head)) (value (Word.singleton head)))
            (G.mul (endpointCorner witness (BrandtEndpoint.outgoing head)) (value suffix)) =
          G.mul (endpointCorner witness (BrandtEndpoint.incoming head)) (value (Word.mk head (next :: rest))) := by
        calc
          _ = G.mul
              (G.mul (G.mul (endpointCorner witness (BrandtEndpoint.incoming head)) (value (Word.singleton head)))
                (endpointCorner witness (BrandtEndpoint.outgoing head))) (value suffix) := (G.assoc _ _ _).symm
          _ = G.mul (G.mul (endpointCorner witness (BrandtEndpoint.incoming head)) (value (Word.singleton head)))
              (value suffix) := by rw [headArrow.rightUnit]
          _ = G.mul (endpointCorner witness (BrandtEndpoint.incoming head))
              (G.mul (value (Word.singleton head)) (value suffix)) := G.assoc _ _ _
          _ = _ := rfl
      rw [valueEq] at assembled
      simpa only [suffix, Word.final, List.getLastD_cons] using Nonempty.intro assembled

theorem endpointHeadCorner {word : Word Nat} (witness : InverseWitness word) :
    endpointCorner witness (BrandtEndpoint.incoming word.head) = value (word ++ witness.inverse) := by
  let occurrence : Occurrence word word.head := ⟨[], word.tail, rfl⟩
  rw [endpointCorner_atOccurrence witness (BrandtEndpoint.incoming word.head) occurrence]
  apply congrArg value
  apply Word.toList_injective
  simp only [cornerWord, occurrence, BrandtEndpoint.incoming, Occurrence.cut,
    ChainReplay.Context.wrap_toList, Word.toList_append, List.append_nil]
  cases word <;> rfl

/-- The unrestricted regular-source closed-return theorem. This is an
actual frozen-basis derivation; no generator-coverage premise remains. -/
theorem regularClosedReturnDerivation {word loop : Word Nat} (witness : InverseWitness word)
    (closed : ClosedReturnWord word loop) : SquareAbsorbs word loop := by
  let anchor := endpointCorner witness (BrandtEndpoint.incoming word.head)
  have initial := endpointCorner_connected witness closed.initial
  have final := endpointCorner_connected witness closed.returns
  obtain ⟨pathArrow⟩ := wordPathArrow witness loop closed.support closed.internal
  have cycle : Arrow G anchor anchor (G.mul anchor (value loop)) := by
    simpa only [initial, final] using pathArrow
  have square := cycleSquare cycle
  have absorbsCorner : anchor = G.mul anchor (G.mul (value loop) (value loop)) := by
    calc
      anchor = G.mul (G.mul anchor (value loop)) (G.mul anchor (value loop)) := square.symm
      _ = G.mul (G.mul (G.mul anchor (value loop)) anchor) (value loop) := (G.assoc _ _ _).symm
      _ = G.mul (G.mul anchor (value loop)) (value loop) := by rw [cycle.rightUnit]
      _ = G.mul anchor (G.mul (value loop) (value loop)) := G.assoc _ _ _
  let occurrence : Occurrence word word.head := ⟨[], word.tail, rfl⟩
  have cornerEq := endpointCorner_atOccurrence witness (BrandtEndpoint.incoming word.head) occurrence
  have actual : (occurrence.cut .incoming).Absorbs loop :=
    (occurrenceAbsorbs_iff_corner witness occurrence .incoming loop).mpr (by
      simpa only [anchor, cornerEq] using absorbsCorner)
  exact actual

theorem repeatedClosedReturnDerivation {word loop : Word Nat}
    (repeated : SemigroupBasis.CoRoots.S5_415.RepeatedWord word) (closed : ClosedReturnWord word loop) :
    SquareAbsorbs word loop :=
  regularClosedReturnDerivation (RepeatedCellRegularity.repeatedWordInverseWitness word repeated) closed

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.RegularLoopModel
