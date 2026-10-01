import SemigroupBasis.CoRoots.Order6Day7.S2_2.SeedS5_415ExposureReplay

/-!
# Rank040: square insertions transport along actual endpoint connectivity

The four frozen laws 04/05/06/09 move an arbitrary square between repeated
incoming or outgoing occurrences. Literal adjacency joins the two kinds
of cuts. Consequently any two actual cuts representing connected Brandt
endpoints have derivably equivalent square insertions, with no word bound
and no assumed normalizer.

This discharges the all-LITERAL-exposures quantifier once one cut is
proved. Embedded elementary returns and the triangle exchange can now be
transported to the head from anywhere in its component. Constructing all
closed walks from such generators is still a separate owner obligation.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.CutConnectivity

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_415
open ClosedReturnReplay ExposureReplay

private def instantiateThree (first second third : Word Nat) : Nat → Word Nat
  | 0 => first
  | 1 => second
  | 2 => third
  | n + 3 => Word.singleton (n + 3)

theorem derivesIncomingEmptySlide (loop anchor : Word Nat) :
    Derives Rank040.basis ((loop ++ loop) ++ (anchor ++ anchor))
      ((anchor ++ (loop ++ loop)) ++ anchor) := by
  have primitive : Derives Rank040.basis (Word.mk 0 [0, 1, 1]) (Word.mk 1 [0, 0, 1]) :=
    Derives.fromBasis (e := law05) (by simp [Rank040.basis])
  have substituted := Derives.subst primitive (instantiateThree loop anchor anchor)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesIncomingNonemptySlide (loop anchor gap : Word Nat) :
    Derives Rank040.basis ((loop ++ loop) ++ ((anchor ++ gap) ++ anchor))
      (((anchor ++ gap) ++ (loop ++ loop)) ++ anchor) := by
  have primitive : Derives Rank040.basis (Word.mk 0 [0, 1, 2, 1]) (Word.mk 1 [2, 0, 0, 1]) :=
    Derives.fromBasis (e := law06) (by simp [Rank040.basis])
  have substituted := Derives.subst primitive (instantiateThree loop anchor gap)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesOutgoingEmptySlide (loop anchor : Word Nat) :
    Derives Rank040.basis ((anchor ++ (loop ++ loop)) ++ anchor)
      ((anchor ++ anchor) ++ (loop ++ loop)) := by
  have primitive : Derives Rank040.basis (Word.mk 0 [1, 1, 0]) (Word.mk 0 [0, 1, 1]) :=
    (Derives.fromBasis (e := law04) (by simp [Rank040.basis])).symm
  have substituted := Derives.subst primitive (instantiateThree anchor loop loop)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

theorem derivesOutgoingNonemptySlide (loop anchor gap : Word Nat) :
    Derives Rank040.basis (((anchor ++ (loop ++ loop)) ++ gap) ++ anchor)
      (((anchor ++ gap) ++ anchor) ++ (loop ++ loop)) := by
  have primitive : Derives Rank040.basis (Word.mk 0 [2, 2, 1, 0]) (Word.mk 0 [1, 0, 2, 2]) :=
    (Derives.fromBasis (e := law09) (by simp [Rank040.basis])).symm
  have substituted := Derives.subst primitive (instantiateThree anchor gap loop)
  simpa [instantiateThree, Word.bind, Word.append, Word.singleton, Word.append_assoc] using substituted

private theorem derives_of_toList_eq {source target source' target' : Word Nat}
    (derivation : Derives Rank040.basis source target)
    (sourceEq : source.toList = source'.toList)
    (targetEq : target.toList = target'.toList) :
    Derives Rank040.basis source' target' := by
  have sourceWordEq := Word.toList_injective sourceEq
  have targetWordEq := Word.toList_injective targetEq
  simpa only [sourceWordEq, targetWordEq] using derivation

private theorem incomingCore (anchor : Nat) (gap : List Nat) (loop : Word Nat) :
    Derives Rank040.basis
      ((loop ++ loop) ++ Word.mk anchor (gap ++ [anchor]))
      (ChainReplay.Context.wrap (anchor :: gap) (loop ++ loop) [anchor]) := by
  cases gap with
  | nil =>
      apply derives_of_toList_eq (derivesIncomingEmptySlide loop (Word.singleton anchor))
      all_goals simp only [ChainReplay.Context.wrap_toList, Word.toList_append, Word.toList_singleton]
      all_goals simp only [Word.toList, List.append_assoc, List.cons_append, List.nil_append]
  | cons head tail =>
      apply derives_of_toList_eq
        (derivesIncomingNonemptySlide loop (Word.singleton anchor) (Word.mk head tail))
      all_goals simp only [ChainReplay.Context.wrap_toList, Word.toList_append, Word.toList_singleton]
      all_goals simp only [Word.toList, List.append_assoc, List.cons_append, List.nil_append]

private theorem outgoingCore (anchor : Nat) (gap : List Nat) (loop : Word Nat) :
    Derives Rank040.basis
      (ChainReplay.Context.wrap [anchor] (loop ++ loop) (gap ++ [anchor]))
      (Word.mk anchor (gap ++ [anchor]) ++ (loop ++ loop)) := by
  cases gap with
  | nil =>
      apply derives_of_toList_eq (derivesOutgoingEmptySlide loop (Word.singleton anchor))
      all_goals simp only [ChainReplay.Context.wrap_toList, Word.toList_append, Word.toList_singleton]
      all_goals simp only [Word.toList, List.append_assoc, List.cons_append, List.nil_append]
  | cons head tail =>
      apply derives_of_toList_eq
        (derivesOutgoingNonemptySlide loop (Word.singleton anchor) (Word.mk head tail))
      all_goals simp only [ChainReplay.Context.wrap_toList, Word.toList_append, Word.toList_singleton]
      all_goals simp only [Word.toList, List.append_assoc, List.cons_append, List.nil_append]

/-- Move the insertion between any two displayed incoming occurrences,
through an arbitrary possibly empty gap and arbitrary raw contexts. -/
theorem derivesIncomingSlide (anchor : Nat) (gap before after : List Nat) (loop : Word Nat) :
    Derives Rank040.basis
      (ChainReplay.Context.wrap before (loop ++ loop) (anchor :: (gap ++ anchor :: after)))
      (ChainReplay.Context.wrap (before ++ anchor :: gap) (loop ++ loop) (anchor :: after)) := by
  apply derives_of_toList_eq
    (ChainReplay.Context.derives_wrap (incomingCore anchor gap loop) before after)
  all_goals simp only [ChainReplay.Context.wrap_toList, Word.toList_append]
  all_goals simp only [Word.toList, List.append_assoc, List.cons_append, List.nil_append]

/-- The analogous movement between outgoing occurrences. -/
theorem derivesOutgoingSlide (anchor : Nat) (gap before after : List Nat) (loop : Word Nat) :
    Derives Rank040.basis
      (ChainReplay.Context.wrap (before ++ [anchor]) (loop ++ loop) (gap ++ anchor :: after))
      (ChainReplay.Context.wrap ((before ++ anchor :: gap) ++ [anchor]) (loop ++ loop) after) := by
  apply derives_of_toList_eq
    (ChainReplay.Context.derives_wrap (outgoingCore anchor gap loop) before after)
  all_goals simp only [ChainReplay.Context.wrap_toList, Word.toList_append]
  all_goals simp only [Word.toList, List.append_assoc, List.cons_append, List.nil_append]

/-- A real occurrence, not just membership in the word's support. -/
structure Occurrence (word : Word Nat) (letter : Nat) where
  before : List Nat
  after : List Nat
  partition : word.toList = before ++ letter :: after

theorem Occurrence.member {word : Word Nat} {letter : Nat} (occurrence : Occurrence word letter) :
    letter ∈ word.toList := by
  rw [occurrence.partition]
  simp

theorem occurrence_exists {word : Word Nat} {letter : Nat} (member : letter ∈ word.toList) :
    Nonempty (Occurrence word letter) := by
  obtain ⟨before, after, partition⟩ := List.mem_iff_append.mp member
  exact ⟨⟨before, after, partition⟩⟩

def Occurrence.cut {word : Word Nat} {letter : Nat} (occurrence : Occurrence word letter) :
    BrandtEndpointSide → Exposure word
  | .incoming => ⟨occurrence.before, letter :: occurrence.after, occurrence.partition⟩
  | .outgoing => ⟨occurrence.before ++ [letter], occurrence.after, by
      simpa only [List.append_assoc, List.singleton_append] using occurrence.partition⟩

private theorem orderedOccurrenceInsertions
    {word : Word Nat} {letter : Nat} (first second : Occurrence word letter)
    (side : BrandtEndpointSide) (loop : Word Nat) (extra : List Nat)
    (beforeEq : second.before = first.before ++ extra)
    (suffix : letter :: first.after = extra ++ letter :: second.after) :
    Derives Rank040.basis ((first.cut side).insert loop) ((second.cut side).insert loop) := by
  cases extra with
  | nil =>
      have sameBefore : second.before = first.before := by simpa using beforeEq
      have sameAfter : first.after = second.after := by simpa using suffix
      cases side <;> simp only [Occurrence.cut, Exposure.insert, sameBefore, sameAfter] <;>
        exact Derives.refl _
  | cons head tail =>
      simp only [List.cons_append] at suffix
      injection suffix with sameHead sameAfter
      subst head
      cases side with
      | incoming =>
          simpa only [Occurrence.cut, Exposure.insert, beforeEq, sameAfter] using
            derivesIncomingSlide letter tail first.before second.after loop
      | outgoing =>
          simpa only [Occurrence.cut, Exposure.insert, beforeEq, sameAfter] using
            derivesOutgoingSlide letter tail first.before second.after loop

/-- ALL occurrences of the same directed endpoint give equivalent insertions. -/
theorem sameEndpointInsertions
    {word : Word Nat} {letter : Nat} (first second : Occurrence word letter)
    (side : BrandtEndpointSide) (loop : Word Nat) :
    Derives Rank040.basis ((first.cut side).insert loop) ((second.cut side).insert loop) := by
  have partitionEquality := first.partition.symm.trans second.partition
  rcases List.append_eq_append_iff.mp partitionEquality with
      ⟨extra, beforeEq, suffix⟩ | ⟨extra, beforeEq, suffix⟩
  · exact orderedOccurrenceInsertions first second side loop extra beforeEq suffix
  · exact (orderedOccurrenceInsertions second first side loop extra beforeEq suffix).symm

private theorem adjacentPairSplitFrom (source target : Nat) :
    ∀ (head : Nat) (tail : List Nat),
      (source, target) ∈ Word.adjacentPairsFrom head tail →
        ∃ before after, head :: tail = before ++ source :: target :: after
  | head, [], edge => by simp [Word.adjacentPairsFrom] at edge
  | head, next :: rest, edge => by
      simp only [Word.adjacentPairsFrom, List.mem_cons, Prod.mk.injEq] at edge
      rcases edge with ⟨sameSource, sameTarget⟩ | later
      · subst source
        subst target
        exact ⟨[], rest, rfl⟩
      · obtain ⟨before, after, partition⟩ := adjacentPairSplitFrom source target next rest later
        exact ⟨head :: before, after, by simp [partition]⟩

theorem adjacentPairSplit (word : Word Nat) {source target : Nat}
    (edge : (source, target) ∈ word.adjacentPairs) :
    ∃ before after, word.toList = before ++ source :: target :: after := by
  cases word with
  | mk head tail => exact adjacentPairSplitFrom source target head tail edge

theorem connectedEndpointMembership
    {word : Word Nat} {source target : BrandtEndpoint}
    (connected : BrandtEndpointConnected word source target) :
    source.letter ∈ word.toList ↔ target.letter ∈ word.toList := by
  induction connected with
  | refl => exact Iff.rfl
  | adjacency edge =>
      obtain ⟨before, after, partition⟩ := adjacentPairSplit word edge
      constructor <;> intro _ <;> rw [partition] <;>
        simp [BrandtEndpoint.incoming, BrandtEndpoint.outgoing]
  | symm _ ih => exact ih.symm
  | trans _ _ firstIH secondIH => exact firstIH.trans secondIH

/-- Every generated endpoint-connection path transports arbitrary square
insertions between ANY two actual endpoint occurrences in the original word. -/
theorem connectedEndpointInsertions
    {word : Word Nat} {source target : BrandtEndpoint}
    (connected : BrandtEndpointConnected word source target) (loop : Word Nat) :
    ∀ (first : Occurrence word source.letter) (second : Occurrence word target.letter),
      Derives Rank040.basis ((first.cut source.side).insert loop) ((second.cut target.side).insert loop) := by
  induction connected with
  | refl endpoint =>
      intro first second
      exact sameEndpointInsertions first second endpoint.side loop
  | @adjacency source target edge =>
      intro first second
      obtain ⟨before, after, partition⟩ := adjacentPairSplit word edge
      let outgoing : Occurrence word source := ⟨before, target :: after, partition⟩
      let incoming : Occurrence word target := ⟨before ++ [source], after, by
        simpa only [List.append_assoc, List.singleton_append] using partition⟩
      exact (sameEndpointInsertions first outgoing .outgoing loop).trans
        (sameEndpointInsertions incoming second .incoming loop)
  | symm _ ih =>
      intro first second
      exact (ih second first).symm
  | trans firstConnection _ firstIH secondIH =>
      intro first second
      obtain ⟨middle⟩ := occurrence_exists ((connectedEndpointMembership firstConnection).mp first.member)
      exact (firstIH first middle).trans (secondIH middle second)

/-- The literal-exposure part of fable's invariant, with the actual proof
obligation quantified over every occurrence, not inserted as a field. -/
def EndpointAbsorbs (word : Word Nat) (endpoint : BrandtEndpoint) (loop : Word Nat) : Prop :=
  ∀ occurrence : Occurrence word endpoint.letter,
    Derives Rank040.basis word ((occurrence.cut endpoint.side).insert loop)

theorem endpointAbsorbs_of_one
    {word : Word Nat} {endpoint : BrandtEndpoint} {loop : Word Nat}
    (one : Occurrence word endpoint.letter)
    (absorbs : Derives Rank040.basis word ((one.cut endpoint.side).insert loop)) :
    EndpointAbsorbs word endpoint loop := fun other =>
  absorbs.trans (sameEndpointInsertions one other endpoint.side loop)

theorem endpointAbsorbs_transport
    {word : Word Nat} {source target : BrandtEndpoint} {loop : Word Nat}
    (connected : BrandtEndpointConnected word source target)
    (absorbs : EndpointAbsorbs word source loop) : EndpointAbsorbs word target loop := by
  intro targetOccurrence
  obtain ⟨sourceOccurrence⟩ :=
    occurrence_exists ((connectedEndpointMembership connected).mpr targetOccurrence.member)
  exact (absorbs sourceOccurrence).trans
    (connectedEndpointInsertions connected loop sourceOccurrence targetOccurrence)

theorem endpointAbsorbs_head_iff (word loop : Word Nat) :
    EndpointAbsorbs word (BrandtEndpoint.incoming word.head) loop ↔ SquareAbsorbs word loop := by
  let headOccurrence : Occurrence word word.head := ⟨[], word.tail, rfl⟩
  constructor
  · intro absorbs
    exact absorbs headOccurrence
  · intro absorbs
    exact endpointAbsorbs_of_one headOccurrence absorbs

/-- Embed an actual absorbed core anywhere in a word, then quantify over
all occurrences of its initial endpoint using the proved slide relation. -/
theorem contextualEndpointAbsorbs
    {word core loop : Word Nat} (before after : List Nat)
    (partition : word.toList = before ++ core.toList ++ after)
    (absorbs : SquareAbsorbs core loop) :
    EndpointAbsorbs word (BrandtEndpoint.incoming core.head) loop := by
  let occurrence : Occurrence word core.head := ⟨before, core.tail ++ after, by
    simpa only [Word.toList, List.append_assoc, List.cons_append] using partition⟩
  apply endpointAbsorbs_of_one occurrence
  apply derives_of_toList_eq (ChainReplay.Context.derives_wrap absorbs before after)
  · simpa only [ChainReplay.Context.wrap_toList] using partition.symm
  · simp only [occurrence, BrandtEndpoint.incoming, Occurrence.cut, Exposure.insert,
      ChainReplay.Context.wrap_toList, Word.toList_append]
    simp only [Word.toList, List.append_assoc, List.cons_append]

/-- A square insertion proved for an embedded core reaches the head whenever
the exact Brandt connection says its cut lies in the initial component. -/
theorem contextualAbsorbsAtHead
    {word core loop : Word Nat} (before after : List Nat)
    (partition : word.toList = before ++ core.toList ++ after)
    (connected : BrandtEndpointConnected word
      (BrandtEndpoint.incoming core.head) (BrandtEndpoint.incoming word.head))
    (absorbs : SquareAbsorbs core loop) : SquareAbsorbs word loop :=
  (endpointAbsorbs_head_iff word loop).mp
    (endpointAbsorbs_transport connected (contextualEndpointAbsorbs before after partition absorbs))

theorem literalReturnAbsorbs (letter : Nat) (middle : List Nat) :
    SquareAbsorbs (Word.mk letter (middle ++ [letter])) (Word.mk letter middle) := by
  cases middle with
  | nil => exact SquareAbsorbs.square (Word.singleton letter)
  | cons head tail =>
      exact sandwichSquareAbsorbs (Word.singleton letter) (Word.mk head tail)

/-- Every literal return, at ANY letter in the initial component, is an
actual rank040 absorbed return. The anchor need not be the literal head. -/
theorem enclosedReturnAbsorbsAtHead
    (word : Word Nat) (letter : Nat) (middle before after : List Nat)
    (partition : word.toList = before ++ letter :: (middle ++ letter :: after))
    (connected : BrandtEndpointConnected word
      (BrandtEndpoint.incoming letter) (BrandtEndpoint.incoming word.head)) :
    SquareAbsorbs word (Word.mk letter middle) := by
  apply contextualAbsorbsAtHead (core := Word.mk letter (middle ++ [letter])) before after
    (absorbs := literalReturnAbsorbs letter middle)
  · simpa [Word.toList, List.append_assoc] using partition
  · exact connected

/-- The entire triangle-exchange family also transports from an arbitrary
embedded core to the initial endpoint component. -/
theorem enclosedTriangleAbsorbsAtHead
    (word first second third loop : Word Nat) (before after : List Nat)
    (partition : word.toList = before ++ (triangleWord first second third).toList ++ after)
    (connected : BrandtEndpointConnected word
      (BrandtEndpoint.incoming first.head) (BrandtEndpoint.incoming word.head))
    (generated : GeneratedBlockWord [first, second, third] loop) : SquareAbsorbs word loop :=
  contextualAbsorbsAtHead before after partition connected
    (triangleAbsorbsGenerated first second third loop generated)

/-- Product closure of the all-occurrences invariant when the component has
an actual regular-flank exposure. The two inverse witnesses remain explicit. -/
theorem endpointAbsorbs_regular_product
    (left right first second : Word Nat) (endpoint : BrandtEndpoint)
    (leftWitness : ExposureReplay.InverseWitness left)
    (rightWitness : ExposureReplay.InverseWitness right)
    (connected : BrandtEndpointConnected (left ++ right) endpoint
      (BrandtEndpoint.incoming right.head))
    (firstAbsorbs : EndpointAbsorbs (left ++ right) endpoint first)
    (secondAbsorbs : EndpointAbsorbs (left ++ right) endpoint second) :
    EndpointAbsorbs (left ++ right) endpoint (first ++ second) := by
  let cutOccurrence : Occurrence (left ++ right) right.head :=
    ⟨left.toList, right.tail, Word.toList_append left right⟩
  have firstCut : ExposureReplay.CutAbsorbs left right first :=
    (endpointAbsorbs_transport connected firstAbsorbs) cutOccurrence
  have secondCut : ExposureReplay.CutAbsorbs left right second :=
    (endpointAbsorbs_transport connected secondAbsorbs) cutOccurrence
  have productCut := cutAbsorbsProduct leftWitness rightWitness firstCut secondCut
  have atCut : EndpointAbsorbs (left ++ right) (BrandtEndpoint.incoming right.head) (first ++ second) :=
    endpointAbsorbs_of_one cutOccurrence productCut
  exact endpointAbsorbs_transport connected.symm atCut

/-- The R operation at an actually exposed path segment: the loop pq at
the incoming p-component rotates to qp at the component AFTER p. All
occurrences at the destination are covered by the proven connectivity lift.
It does not pretend that an arbitrary graph path is already exposed. -/
theorem endpointAbsorbs_rotation
    (word first second remainder : Word Nat) (before after : List Nat)
    (partition : word.toList = before ++ first.toList ++ remainder.toList ++ after)
    (absorbs : EndpointAbsorbs word (BrandtEndpoint.incoming first.head) (first ++ second)) :
    EndpointAbsorbs word (BrandtEndpoint.incoming remainder.head) (second ++ first) := by
  let startOccurrence : Occurrence word first.head :=
    ⟨before, first.tail ++ (remainder.toList ++ after), by
      simpa only [Word.toList, List.append_assoc, List.cons_append] using partition⟩
  let endOccurrence : Occurrence word remainder.head :=
    ⟨before ++ first.toList, remainder.tail ++ after, by
      simpa only [Word.toList, List.append_assoc, List.cons_append] using partition⟩
  have atStart : (startOccurrence.cut .incoming).Absorbs (first ++ second) := absorbs startOccurrence
  have split : (startOccurrence.cut .incoming).after = first.toList ++ (remainder.toList ++ after) := rfl
  have rotated := ((startOccurrence.cut .incoming).absorbsRotation_iff first second
    (remainder.toList ++ after) split).mp atStart
  exact endpointAbsorbs_of_one endOccurrence rotated

end SemigroupBasis.CoRoots.Order6Day7.S2_2.Rank040.CutConnectivity
