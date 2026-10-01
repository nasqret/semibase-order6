import SemigroupBasis.CoRoots.Order6SporadicSection19PublishedRootSpanIsolation

namespace SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FirstReturnBridgeCut

open MaximalFactors FactorBoundaries BlockAlignment MacroWitnesses RootFamily
open RootBlockPartition TerminalRepeatBoundary ConnectedTerminalEndpoints
open CanonicalPresentation RootSpanIsolation

theorem square_head_member (root : Word Nat) : root.head ∈ (root ++ root).toList := by
  rw [Word.toList_append]
  exact List.mem_append.mpr (Or.inl (word_head_member root))

theorem square_head_in_flatten (root : Word Nat) (pieces : List (Word Nat))
    (member : (root ++ root) ∈ pieces) : root.head ∈ flatten pieces :=
  (mem_flatten root.head pieces).mpr ⟨root ++ root, member, square_head_member root⟩

theorem span_endpoints (square : Word Nat) (inside : List (Word Nat))
    (shape : SpanShape square inside) :
    ∃ rest initial : List (Word Nat), inside = square :: rest ∧ inside = initial ++ [square] := by
  rcases shape with singleton | repeatedShape
  · exact ⟨[], [], singleton, singleton⟩
  · obtain ⟨middle, equal⟩ := repeatedShape
    exact ⟨middle ++ [square], square :: middle, equal, equal⟩

/-- A root square which returns from an earlier actual partition prefix. -/
def Returning (roots : List (Word Nat)) (before : List (Word Nat)) (piece : Word Nat) : Prop :=
  RootSquare roots piece ∧ piece ∈ before

theorem first_return_split (roots : List (Word Nat)) (before tail : List (Word Nat))
    (present : ∃ piece ∈ tail, Returning roots before piece) :
    ∃ between : List (Word Nat), ∃ piece : Word Nat, ∃ after : List (Word Nat),
      tail = between ++ piece :: after ∧ Returning roots before piece ∧
        (∀ earlier ∈ between, ¬ Returning roots before earlier) := by
  classical
  induction tail with
  | nil =>
    obtain ⟨piece, member, _property⟩ := present
    cases member
  | cons first rest ih =>
    by_cases here : Returning roots before first
    · refine ⟨[], first, rest, rfl, here, ?_⟩
      intro earlier impossible
      cases impossible
    · have later : ∃ piece ∈ rest, Returning roots before piece := by
        obtain ⟨piece, member, property⟩ := present
        rcases List.mem_cons.mp member with equal | remaining
        · subst piece
          exact False.elim (here property)
        · exact ⟨piece, remaining, property⟩
      obtain ⟨between, piece, after, split, property, absent⟩ := ih later
      refine ⟨first :: between, piece, after, ?_, property, ?_⟩
      · simp only [List.cons_append, split]
      · intro earlier member
        rcases List.mem_cons.mp member with equal | remaining
        · subst earlier
          exact here
        · exact absent earlier remaining

/-- Connectedness supplies a root across the cut. Isolation excludes its
occurrence from the selected span, so its second occurrence is in the suffix. -/
theorem connected_span_bridge (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (family : Family roots word) (connected : Connected word)
    (partition : SquarePartition roots word pieces)
    (coverage : ∀ value, Covered roots value ↔ 2 ≤ word.toList.count value)
    (before inside tail : List (Word Nat)) (beforeNonempty : before ≠ [])
    (insideNonempty : inside ≠ []) (split : pieces = before ++ (inside ++ tail))
    (isolated : ∀ value ∈ flatten inside, value ∉ flatten (before ++ tail)) :
    ∃ bridge ∈ roots, (bridge ++ bridge) ∈ before ∧ (bridge ++ bridge) ∈ tail := by
  have rightNonempty : inside ++ tail ≠ [] := by
    cases inside with
    | nil => exact False.elim (insideNonempty rfl)
    | cons first rest => exact List.cons_ne_nil first (rest ++ tail)
  obtain ⟨bridge, member, inBefore, inRight⟩ := connected_partition_cut_root roots word pieces
    connected family partition coverage before (inside ++ tail) beforeNonempty rightNonempty split
  refine ⟨bridge, member, inBefore, ?_⟩
  rcases List.mem_append.mp inRight with inInside | inTail
  · have letterInside := square_head_in_flatten bridge inside inInside
    have letterOutside : bridge.head ∈ flatten (before ++ tail) := by
      rw [FactorBoundaries.flatten_append]
      exact List.mem_append.mpr (Or.inl (square_head_in_flatten bridge before inBefore))
    exact False.elim (isolated bridge.head letterInside letterOutside)
  · exact inTail

/-- Before the first returning square, no root can occur in the earlier
prefix, the isolated selected span, the returning square, or its suffix. -/
theorem first_return_roots_separated (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (terminal : Terminal roots word)
    (partition : SquarePartition roots word pieces)
    (before inside tail between after : List (Word Nat))
    (split : pieces = before ++ (inside ++ tail))
    (isolated : ∀ value ∈ flatten inside, value ∉ flatten (before ++ tail))
    (bridge : Word Nat) (bridgeMember : bridge ∈ roots) (bridgeBefore : (bridge ++ bridge) ∈ before)
    (returnSplit : tail = between ++ (bridge ++ bridge) :: after)
    (minimal : ∀ earlier ∈ between, ¬ Returning roots before earlier) :
    ∀ other ∈ roots, (other ++ other) ∈ between →
      (other ++ other) ∉ (before ++ inside) ++ (bridge ++ bridge) :: after := by
  intro other otherMember inBetween
  have notBefore : (other ++ other) ∉ before := by
    intro present
    exact minimal (other ++ other) inBetween ⟨⟨other, otherMember, rfl⟩, present⟩
  have notInside : (other ++ other) ∉ inside := by
    intro present
    have inTail : (other ++ other) ∈ tail := by
      rw [returnSplit]
      exact List.mem_append.mpr (Or.inl inBetween)
    have letterOutside : other.head ∈ flatten (before ++ tail) := by
      rw [FactorBoundaries.flatten_append]
      exact List.mem_append.mpr (Or.inr (square_head_in_flatten other tail inTail))
    exact isolated other.head (square_head_in_flatten other inside present) letterOutside
  have different : bridge ≠ other := by
    intro equal
    apply notBefore
    rw [← equal]
    exact bridgeBefore
  obtain ⟨start, earlierTail, beforeSplit⟩ := split_member (bridge ++ bridge) before bridgeBefore
  have arranged : pieces = start ++ ((bridge ++ bridge) ::
      ((earlierTail ++ (inside ++ between)) ++ (bridge ++ bridge) :: after)) := by
    rw [split, returnSplit, beforeSplit]
    simp only [List.cons_append, List.append_assoc]
  have inMiddle : (other ++ other) ∈ earlierTail ++ (inside ++ between) :=
    List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr inBetween)))
  have absent := terminal_inner_root_absent roots word pieces terminal partition bridge other
    bridgeMember otherMember different start (earlierTail ++ (inside ++ between)) after arranged inMiddle
  intro outside
  rcases List.mem_append.mp outside with leftSide | rightSide
  · rcases List.mem_append.mp leftSide with earlier | inSpan
    · exact notBefore earlier
    · exact notInside inSpan
  · rcases List.mem_cons.mp rightSide with equal | later
    · apply notBefore
      rw [equal]
      exact bridgeBefore
    · exact absent.2 later

/-- An empty returning prefix would put a repeated square directly after
the selected ending square, contradicting the proved terminal repeat boundary. -/
theorem first_return_nonempty (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (family : Family roots word) (terminal : Terminal roots word)
    (partition : SquarePartition roots word pieces)
    (root bridge : Word Nat) (rootMember : root ∈ roots) (bridgeMember : bridge ∈ roots)
    (before inside tail between after : List (Word Nat))
    (split : pieces = before ++ (inside ++ tail)) (shape : SpanShape (root ++ root) inside)
    (bridgeBefore : (bridge ++ bridge) ∈ before)
    (returnSplit : tail = between ++ (bridge ++ bridge) :: after) : between ≠ [] := by
  intro empty
  obtain ⟨_rest, initial, _starts, ends⟩ := span_endpoints (root ++ root) inside shape
  have arranged : pieces = (before ++ initial) ++ (root ++ root) :: (bridge ++ bridge) :: after := by
    rw [split, returnSplit, empty, ends]
    simp only [List.nil_append, List.append_assoc, List.cons_append]
  have repeated : (bridge ++ bridge) ∈ (before ++ initial) ++ [root ++ root] :=
    List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl bridgeBefore)))
  have outside := terminal_repeat_predecessor roots word pieces family terminal partition
    bridge bridgeMember (before ++ initial) (root ++ root) after arranged repeated
  exact (square_not_outside roots (root ++ root) ⟨root, rootMember, rfl⟩) outside

theorem split_final_piece (pieces : List (Word Nat)) (nonempty : pieces ≠ []) :
    ∃ before : List (Word Nat), ∃ last : Word Nat, pieces = before ++ [last] := by
  classical
  induction pieces with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest ih =>
    by_cases empty : rest = []
    · subst rest
      exact ⟨[], first, rfl⟩
    · obtain ⟨before, last, split⟩ := ih empty
      refine ⟨first :: before, last, ?_⟩
      simp only [List.cons_append, split]

/-- An actual first-return cut. The marker is a nonempty simple partition
factor; equality with an entire printed canonical gap is NOT asserted. -/
structure ReturnCut (roots : List (Word Nat)) (word : Word Nat)
    (before inside tail : List (Word Nat)) where
  bridge : Word Nat
  bridge_member : bridge ∈ roots
  bridge_before : (bridge ++ bridge) ∈ before
  between : List (Word Nat)
  marker : Word Nat
  after : List (Word Nat)
  tail_eq : tail = between ++ marker :: (bridge ++ bridge) :: after
  word_eq : word.toList = flatten before ++ (flatten inside ++
    (flatten between ++ (marker.toList ++ ((bridge ++ bridge).toList ++ flatten after))))
  marker_outside : Outside roots marker
  marker_simple : ∀ value ∈ marker.toList, word.toList.count value = 1
  minimal_return : ∀ earlier ∈ between ++ [marker], ¬ Returning roots before earlier
  between_isolated : ∀ value ∈ flatten between,
    value ∉ flatten ((before ++ inside) ++ marker :: (bridge ++ bridge) :: after)

theorem bridge_cut_from_span (roots : List (Word Nat)) (word : Word Nat)
    (pieces : List (Word Nat)) (family : Family roots word) (terminal : Terminal roots word)
    (connected : Connected word) (partition : SquarePartition roots word pieces)
    (coverage : ∀ value, Covered roots value ↔ 2 ≤ word.toList.count value)
    (root : Word Nat) (rootMember : root ∈ roots) (before inside tail : List (Word Nat))
    (split : pieces = before ++ (inside ++ tail)) (beforeNonempty : before ≠ [])
    (shape : SpanShape (root ++ root) inside)
    (isolated : ∀ value ∈ flatten inside, value ∉ flatten (before ++ tail)) :
    Nonempty (ReturnCut roots word before inside tail) := by
  have insideNonempty : inside ≠ [] := by
    obtain ⟨rest, _initial, starts, _ends⟩ := span_endpoints (root ++ root) inside shape
    rw [starts]
    exact List.cons_ne_nil (root ++ root) rest
  obtain ⟨someBridge, someMember, someBefore, someTail⟩ := connected_span_bridge roots word pieces
    family connected partition coverage before inside tail beforeNonempty insideNonempty split isolated
  have present : ∃ piece ∈ tail, Returning roots before piece :=
    ⟨someBridge ++ someBridge, someTail, ⟨someBridge, someMember, rfl⟩, someBefore⟩
  obtain ⟨region, part, after, returnSplit, returned, minimal⟩ := first_return_split roots before tail present
  rcases returned with ⟨⟨bridge, bridgeMember, rfl⟩, bridgeBefore⟩
  have separated := first_return_roots_separated roots word pieces terminal partition
    before inside tail region after split isolated bridge bridgeMember bridgeBefore returnSplit minimal
  have regionNonempty := first_return_nonempty roots word pieces family terminal partition
    root bridge rootMember bridgeMember before inside tail region after split shape bridgeBefore returnSplit
  obtain ⟨between, marker, regionSplit⟩ := split_final_piece region regionNonempty
  have tailEq : tail = between ++ marker :: (bridge ++ bridge) :: after := by
    rw [returnSplit, regionSplit]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have arranged : pieces = ((before ++ inside) ++ between) ++ marker :: (bridge ++ bridge) :: after := by
    rw [split, tailEq]
    simp only [List.append_assoc]
  have repeated : (bridge ++ bridge) ∈ ((before ++ inside) ++ between) ++ [marker] :=
    List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl
      (List.mem_append.mpr (Or.inl bridgeBefore)))))
  have markerOutside := terminal_repeat_predecessor roots word pieces family terminal partition
    bridge bridgeMember ((before ++ inside) ++ between) marker after arranged repeated
  have markerSimple := (terminal_repeat_predecessor_simple roots word pieces family terminal partition
    coverage bridge bridgeMember ((before ++ inside) ++ between) marker after arranged repeated).2
  have literal : word.toList = flatten before ++ (flatten inside ++
      (flatten between ++ (marker.toList ++ ((bridge ++ bridge).toList ++ flatten after)))) := by
    rw [← partition.1, split, tailEq]
    simp only [FactorBoundaries.flatten_append, flatten]
  have minimalPart : ∀ earlier ∈ between ++ [marker], ¬ Returning roots before earlier := by
    rw [← regionSplit]
    exact minimal
  have betweenSplit : pieces = (before ++ inside) ++ (between ++ marker :: (bridge ++ bridge) :: after) := by
    simpa only [List.append_assoc] using arranged
  have isolatedBetween : ∀ value ∈ flatten between,
      value ∉ flatten ((before ++ inside) ++ marker :: (bridge ++ bridge) :: after) := by
    apply separated_squares_separate_letters roots word pieces family partition coverage
      (before ++ inside) between (marker :: (bridge ++ bridge) :: after) betweenSplit
    intro other otherMember inBetween exterior
    have inRegion : (other ++ other) ∈ region := by
      rw [regionSplit]
      exact List.mem_append.mpr (Or.inl inBetween)
    have absent := separated other otherMember inRegion
    rcases List.mem_append.mp exterior with beforeSide | restSide
    · exact absent (List.mem_append.mpr (Or.inl beforeSide))
    · rcases List.mem_cons.mp restSide with markerEqual | afterSide
      · have markerSquare : RootSquare roots marker := ⟨other, otherMember, markerEqual.symm⟩
        exact (square_not_outside roots marker markerSquare) markerOutside
      · exact absent (List.mem_append.mpr (Or.inr afterSide))
  exact ⟨⟨bridge, bridgeMember, bridgeBefore, between, marker, after, tailEq, literal,
    markerOutside, markerSimple, minimalPart, isolatedBetween⟩⟩

theorem form_span_before_nonempty (word : Word Nat) (form : Form word) (root : Word Nat)
    (before inside tail : List (Word Nat))
    (split : form.first :: expand form.chunks = before ++ (inside ++ tail))
    (shape : SpanShape (root ++ root) inside) (different : (root ++ root) ≠ form.first) :
    before ≠ [] := by
  obtain ⟨rest, _initial, starts, _ends⟩ := span_endpoints (root ++ root) inside shape
  intro empty
  have literal : form.first :: expand form.chunks = (root ++ root) :: (rest ++ tail) := by
    simpa only [empty, starts, List.nil_append, List.cons_append] using split
  exact different (List.cons.inj literal).1.symm

/-- Every noninitial root of the actual canonical Form admits the derived
bridge cut. No semantic equality or pre-supplied following-region isolation
is needed. The chosen marker retains its precise partition-factor scope. -/
theorem form_noninitial_root_cut (word : Word Nat) (form : Form word)
    (root : Word Nat) (rootMember : root ∈ form.roots) (different : (root ++ root) ≠ form.first) :
    ∃ before inside tail : List (Word Nat),
      form.first :: expand form.chunks = before ++ (inside ++ tail) ∧
      SpanShape (root ++ root) inside ∧
      (∀ value ∈ flatten inside, value ∉ flatten (before ++ tail)) ∧
      Nonempty (ReturnCut form.roots word before inside tail) := by
  obtain ⟨before, inside, tail, split, _beforeAbsent, _afterAbsent, shape, isolated⟩ :=
    form_root_span_isolated word form root rootMember
  have beforeNonempty := form_span_before_nonempty word form root before inside tail split shape different
  have cut := bridge_cut_from_span form.roots word (form.first :: expand form.chunks)
    form.family form.terminal form.connected (form_partition word form) form.coverage root rootMember
    before inside tail split beforeNonempty shape isolated
  exact ⟨before, inside, tail, split, shape, isolated, cut⟩

end SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FirstReturnBridgeCut

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FirstReturnBridgeCut.span_endpoints
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FirstReturnBridgeCut.first_return_split
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FirstReturnBridgeCut.connected_span_bridge
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FirstReturnBridgeCut.first_return_roots_separated
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FirstReturnBridgeCut.first_return_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FirstReturnBridgeCut.bridge_cut_from_span
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FirstReturnBridgeCut.form_span_before_nonempty
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection19.Published.FirstReturnBridgeCut.form_noninitial_root_cut
