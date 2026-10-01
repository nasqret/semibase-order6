import SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.CapTwoEndpointMeasureSelection

/-!
# Recomputed endpoint-measure decrease

The dispatcher moves literal occurrences.  This module recomputes endpoint
tags on the displayed target list and proves the corresponding strict
lexicographic drop.  In particular, it never measures a transported tag list
in place of `tagEndpoints next`.

Static off-tree source; not locally elaborated.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
namespace CapTwoRTCRoute

open SemigroupBasis.Examples

/-! ## Endpoint tagging with an explicit later context -/

def endpointTagAgainst (letter : Nat) (later : List Nat) : EndpointTag :=
  if letter ∈ later then EndpointTag.first letter
  else EndpointTag.event letter

def tagEndpointsWith (later : List Nat) : List Nat → List EndpointTag
  | [] => []
  | letter :: rest =>
      endpointTagAgainst letter (rest ++ later) ::
        tagEndpointsWith later rest

@[simp]
theorem tagEndpointsWith_map_letter (later : List Nat) :
    ∀ letters : List Nat,
      (tagEndpointsWith later letters).map EndpointTag.letter = letters
  | [] => rfl
  | letter :: rest => by
      simp only [tagEndpointsWith, List.map_cons,
        tagEndpointsWith_map_letter later rest]
      by_cases present : letter ∈ rest ++ later
      · simp [endpointTagAgainst, present, EndpointTag.first]
      · simp [endpointTagAgainst, present, EndpointTag.event]

theorem tagEndpoints_append_with :
    ∀ left right : List Nat,
      tagEndpoints (left ++ right) =
        tagEndpointsWith right left ++ tagEndpoints right
  | [], _ => rfl
  | letter :: rest, right => by
      simp only [List.cons_append, tagEndpoints, tagEndpointsWith]
      rw [tagEndpoints_append_with rest right]
      rfl

theorem tagEndpointsWith_append (later : List Nat) :
    ∀ left right : List Nat,
      tagEndpointsWith later (left ++ right) =
        tagEndpointsWith (right ++ later) left ++
          tagEndpointsWith later right
  | [], _ => rfl
  | letter :: rest, right => by
      simp only [List.cons_append, tagEndpointsWith]
      rw [tagEndpointsWith_append later rest right]
      simp only [List.append_assoc]

private theorem tagEndpointsWith_congr_later
    {leftLater rightLater : List Nat} :
    ∀ letters : List Nat,
      (∀ tested, tested ∈ letters →
        (tested ∈ leftLater ↔ tested ∈ rightLater)) →
      tagEndpointsWith leftLater letters =
        tagEndpointsWith rightLater letters
  | [], _ => rfl
  | letter :: rest, same => by
      have headSame :
          letter ∈ rest ++ leftLater ↔
            letter ∈ rest ++ rightLater := by
        simp only [List.mem_append]
        exact or_congr Iff.rfl
          (same letter (List.Mem.head rest))
      have tailSame :
          ∀ tested, tested ∈ rest →
            (tested ∈ leftLater ↔ tested ∈ rightLater) := by
        intro tested member
        exact same tested (List.Mem.tail letter member)
      by_cases present : letter ∈ rest ++ leftLater
      · have presentRight : letter ∈ rest ++ rightLater :=
          headSame.mp present
        simp [tagEndpointsWith, endpointTagAgainst, present,
          presentRight,
          tagEndpointsWith_congr_later rest tailSame]
      · have absentRight : letter ∉ rest ++ rightLater := by
          intro member
          exact present (headSame.mpr member)
        simp [tagEndpointsWith, endpointTagAgainst, present,
          absentRight,
          tagEndpointsWith_congr_later rest tailSame]

private theorem tagEndpointsWith_perm_later
    (letters leftLater rightLater : List Nat)
    (permutation : leftLater.Perm rightLater) :
    tagEndpointsWith leftLater letters =
      tagEndpointsWith rightLater letters := by
  apply tagEndpointsWith_congr_later
  intro tested _
  exact permutation.mem_iff

private theorem tagEndpointsWith_cons_absent
    (moved : Nat) (later crossed : List Nat)
    (absent : moved ∉ crossed) :
    tagEndpointsWith (moved :: later) crossed =
      tagEndpointsWith later crossed := by
  apply tagEndpointsWith_congr_later
  intro tested member
  have different : tested ≠ moved := by
    intro equal
    subst tested
    exact absent member
  simp [different]

private theorem move_left_permutation
    (moved : Nat) (crossed later : List Nat) :
    (crossed ++ moved :: later).Perm
      (moved :: crossed ++ later) := by
  exact List.perm_middle

/-- Moving one occurrence left is a literal permutation, including arbitrary
two-sided contexts. -/
theorem move_left_permutation_in_context
    (front crossed later : List Nat) (moved : Nat) :
    (front ++ crossed ++ moved :: later).Perm
      (front ++ moved :: crossed ++ later) := by
  simpa [List.append_assoc] using
    List.Perm.append_left front
      (move_left_permutation moved crossed later)

/-- Recomputing tags after moving one occurrence left across a block not
containing that letter gives the corresponding literal tag move. -/
theorem tagEndpoints_move_left
    (front crossed later : List Nat) (moved : Nat)
    (absent : moved ∉ crossed) :
    let frontTags := tagEndpointsWith (crossed ++ moved :: later) front
    let crossedTags := tagEndpointsWith (moved :: later) crossed
    let movedTag := endpointTagAgainst moved later
    let laterTags := tagEndpoints later
    tagEndpoints (front ++ crossed ++ moved :: later) =
        frontTags ++ crossedTags ++ movedTag :: laterTags ∧
      tagEndpoints (front ++ moved :: crossed ++ later) =
        frontTags ++ movedTag :: crossedTags ++ laterTags := by
  let frontTags := tagEndpointsWith (crossed ++ moved :: later) front
  let crossedTags := tagEndpointsWith (moved :: later) crossed
  let movedTag := endpointTagAgainst moved later
  let laterTags := tagEndpoints later
  have frontSame :
      tagEndpointsWith (moved :: crossed ++ later) front = frontTags := by
    exact (tagEndpointsWith_perm_later front
      (moved :: crossed ++ later) (crossed ++ moved :: later)
      (move_left_permutation moved crossed later).symm)
  have crossedSame :
      tagEndpointsWith later crossed = crossedTags := by
    exact (tagEndpointsWith_cons_absent moved later crossed absent).symm
  constructor
  · rw [show front ++ crossed ++ moved :: later =
        front ++ (crossed ++ moved :: later) by
          simp [List.append_assoc]]
    rw [tagEndpoints_append_with,
      tagEndpoints_append_with]
    simp only [tagEndpoints, frontTags, crossedTags,
      movedTag, laterTags, endpointTagAgainst,
      List.append_assoc]
  · rw [show front ++ moved :: crossed ++ later =
        front ++ (moved :: crossed ++ later) by
          simp [List.append_assoc]]
    rw [tagEndpoints_append_with]
    rw [frontSame]
    rw [tagEndpoints_append_with]
    simp only [tagEndpointsWith]
    rw [crossedSame]
    simp [frontTags, crossedTags, movedTag, laterTags,
      endpointTagAgainst, absent, List.append_assoc]

/-! ## Tag-level arithmetic for the three branches -/

private theorem endpointSeparationTags_move_first_left
    (front crossed later : List EndpointTag) (moved : Nat) :
    endpointSeparationTags
        (front ++ crossed ++ EndpointTag.first moved :: later) =
      endpointSeparationTags
          (front ++ EndpointTag.first moved :: crossed ++ later) +
        eventEndpointCount crossed := by
  simp [endpointSeparationTags_append, firstEndpointCount_append,
    eventEndpointCount_append, endpointSeparationTags,
    firstEndpointCount, eventEndpointCount, EndpointTag.first,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.mul_add, Nat.add_mul]

private theorem endpointSeparationTags_swap_events
    (front later : List EndpointTag) (x y : Nat) :
    endpointSeparationTags
        (front ++ EndpointTag.event x :: EndpointTag.event y :: later) =
      endpointSeparationTags
        (front ++ EndpointTag.event y :: EndpointTag.event x :: later) := by
  simp [endpointSeparationTags_append, firstEndpointCount_append,
    eventEndpointCount_append, endpointSeparationTags,
    firstEndpointCount, eventEndpointCount, EndpointTag.event,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.mul_add, Nat.add_mul]

private theorem eventEndpointCount_tagEndpointsWith_snoc_event_pos
    (front later : List Nat) (terminal : Nat)
    (terminalAbsent : terminal ∉ later) :
    0 < eventEndpointCount
      (tagEndpointsWith later (front ++ [terminal])) := by
  rw [tagEndpointsWith_append]
  simp [tagEndpointsWith, endpointTagAgainst, terminalAbsent,
    eventEndpointCount_append, eventEndpointCount, EndpointTag.event]

private theorem endpointMeasure_lt_of_separation_drop
    {source target : List Nat}
    (drop : endpointSeparation target < endpointSeparation source) :
    EndpointMeasure.Lt (endpointMeasure target)
      (endpointMeasure source) :=
  Or.inl drop

private theorem endpointMeasure_lt_of_first_drop
    {source target : List Nat}
    (separationSame :
      endpointSeparation target = endpointSeparation source)
    (firstDrop :
      ascendingInversions (firstProjection (tagEndpoints target)) <
        ascendingInversions (firstProjection (tagEndpoints source))) :
    EndpointMeasure.Lt (endpointMeasure target)
      (endpointMeasure source) :=
  Or.inr <| Or.inl ⟨separationSame, firstDrop⟩

private theorem endpointMeasure_lt_of_event_drop
    {source target : List Nat}
    (separationSame :
      endpointSeparation target = endpointSeparation source)
    (firstSame :
      ascendingInversions (firstProjection (tagEndpoints target)) =
        ascendingInversions (firstProjection (tagEndpoints source)))
    (eventDrop :
      eventGapInversions (tagEndpoints target) <
        eventGapInversions (tagEndpoints source)) :
    EndpointMeasure.Lt (endpointMeasure target)
      (endpointMeasure source) :=
  Or.inr <| Or.inr ⟨separationSame, firstSame, eventDrop⟩

/-! ## Rich progress result -/

inductive EndpointMeasureProgress (letters : List Nat) : Prop where
  | intro (next : List Nat)
      (reachable : ContextualFrozenRTC letters next)
      (permutation : letters.Perm next)
      (changed : next ≠ letters)
      (decrease : EndpointMeasure.Lt (endpointMeasure next)
        (endpointMeasure letters)) :
      EndpointMeasureProgress letters

/-! The count bridge is public because it is also used by the pivot layer. -/

theorem firstProjection_mem_of_count_eq_two
    {letters : List Nat} {letter : Nat}
    (countTwo : letters.count letter = 2) :
    letter ∈ firstProjection (tagEndpoints letters) := by
  induction letters with
  | nil => simp at countTwo
  | cons head tail inductionHypothesis =>
      by_cases equal : head = letter
      · subst head
        have later : letter ∈ tail := by
          rw [List.count_cons_self] at countTwo
          exact List.count_pos_iff.mp (by omega)
        simp [tagEndpoints, later, firstProjection,
          EndpointTag.first]
      · have tailCount : tail.count letter = 2 := by
          simpa [equal] using countTwo
        have member := inductionHypothesis tailCount
        by_cases later : head ∈ tail
        · simp [tagEndpoints, later, firstProjection,
            EndpointTag.first, member, equal]
        · simp [tagEndpoints, later, firstProjection,
            EndpointTag.event, member, equal]

private theorem ef_progress
    {letters : List Nat}
    (twoLimited : ∀ tested, letters.count tested ≤ 2) :
    EndpointEFCase letters → EndpointMeasureProgress letters
  | .crossing front suffix crossing endpoint before middle after
      shape beforeNonempty eventWitness => by
      let later := middle ++ [crossing] ++ after ++ [endpoint] ++ suffix
      let crossed := crossing :: before
      let next := front ++ [endpoint] ++ crossed ++ later
      have different : crossing ≠ endpoint := by
        intro equal
        subst crossing
        have bound := twoLimited endpoint
        rw [shape] at bound
        simp only [List.count_append, List.count_cons,
          List.count_nil, Nat.add_zero] at bound
        simp at bound
        omega
      have endpointAbsent : endpoint ∉ crossed := by
        intro member
        have endpointBefore : 0 < crossed.count endpoint :=
          List.count_pos_iff.mpr member
        have bound := twoLimited endpoint
        have expandedShape :
            letters = front ++ crossed ++ [endpoint] ++ later := by
          simpa [crossed, later, List.append_assoc] using shape
        rw [expandedShape, List.count_append] at bound
        simp [later, different, Ne.symm different,
          List.count_append] at bound
        omega
      have endpointLater : endpoint ∈ later := by
        simp [later]
      obtain ⟨beforeFront, terminal, beforeShape,
          terminalAbsent⟩ := eventWitness
      have crossedShape :
          crossed = (crossing :: beforeFront) ++ [terminal] := by
        simp [crossed, beforeShape, List.append_assoc]
      have terminalNotLater : terminal ∉ endpoint :: later := by
        simpa [later, List.append_assoc] using terminalAbsent
      have crossedEventPositive :
          0 < eventEndpointCount
            (tagEndpointsWith (endpoint :: later) crossed) := by
        rw [crossedShape]
        exact eventEndpointCount_tagEndpointsWith_snoc_event_pos
          (crossing :: beforeFront) (endpoint :: later) terminal
          terminalNotLater
      have tagMove := tagEndpoints_move_left
        front crossed later endpoint endpointAbsent
      let frontTags := tagEndpointsWith (crossed ++ endpoint :: later) front
      let crossedTags := tagEndpointsWith (endpoint :: later) crossed
      let laterTags := tagEndpoints later
      have sourceShape : letters = front ++ crossed ++ endpoint :: later := by
        simpa [crossed, later, List.append_assoc] using shape
      have targetTags :
          tagEndpoints next =
            frontTags ++ EndpointTag.first endpoint ::
              crossedTags ++ laterTags := by
        have := tagMove.2
        simpa [next, frontTags, crossedTags, laterTags,
          endpointTagAgainst, endpointLater,
          List.append_assoc] using this
      have sourceTags :
          tagEndpoints letters =
            frontTags ++ crossedTags ++ EndpointTag.first endpoint ::
              laterTags := by
        rw [sourceShape]
        have := tagMove.1
        simpa [frontTags, crossedTags, laterTags,
          endpointTagAgainst, endpointLater,
          List.append_assoc] using this
      have separationEquation :
          endpointSeparation letters =
            endpointSeparation next + eventEndpointCount crossedTags := by
        unfold endpointSeparation
        rw [sourceTags, targetTags]
        exact endpointSeparationTags_move_first_left
          frontTags crossedTags laterTags endpoint
      have separationDrop :
          endpointSeparation next < endpointSeparation letters := by
        have positive : 0 < eventEndpointCount crossedTags := by
          simpa [crossedTags] using crossedEventPositive
        omega
      refine ⟨next, ?_, ?_, ?_,
        endpointMeasure_lt_of_separation_drop separationDrop⟩
      · rw [shape]
        simpa [next, crossed, later, List.append_assoc] using
          (frozenPullEndpointCrossing crossing endpoint
            before middle after).context front suffix
      · rw [sourceShape]
        simpa [next] using
          move_left_permutation_in_context
            front crossed later endpoint
      · intro equal
        exact (Nat.ne_of_lt separationDrop)
          (congrArg endpointSeparation equal)
  | .nested front suffix crossing endpoint before middle after
      shape beforeNonempty eventWitness => by
      let later := middle ++ [endpoint] ++ after ++ [crossing] ++ suffix
      let crossed := crossing :: before
      let next := front ++ [endpoint] ++ crossed ++ later
      have different : crossing ≠ endpoint := by
        intro equal
        subst crossing
        have bound := twoLimited endpoint
        rw [shape] at bound
        simp only [List.count_append, List.count_cons,
          List.count_nil, Nat.add_zero] at bound
        simp at bound
        omega
      have endpointAbsent : endpoint ∉ crossed := by
        intro member
        have endpointBefore : 0 < crossed.count endpoint :=
          List.count_pos_iff.mpr member
        have bound := twoLimited endpoint
        have expandedShape :
            letters = front ++ crossed ++ [endpoint] ++ later := by
          simpa [crossed, later, List.append_assoc] using shape
        rw [expandedShape, List.count_append] at bound
        simp [later, different, Ne.symm different,
          List.count_append] at bound
        omega
      have endpointLater : endpoint ∈ later := by
        simp [later]
      obtain ⟨beforeFront, terminal, beforeShape,
          terminalAbsent⟩ := eventWitness
      have crossedShape :
          crossed = (crossing :: beforeFront) ++ [terminal] := by
        simp [crossed, beforeShape, List.append_assoc]
      have terminalNotLater : terminal ∉ endpoint :: later := by
        simpa [later, List.append_assoc] using terminalAbsent
      have crossedEventPositive :
          0 < eventEndpointCount
            (tagEndpointsWith (endpoint :: later) crossed) := by
        rw [crossedShape]
        exact eventEndpointCount_tagEndpointsWith_snoc_event_pos
          (crossing :: beforeFront) (endpoint :: later) terminal
          terminalNotLater
      have tagMove := tagEndpoints_move_left
        front crossed later endpoint endpointAbsent
      let frontTags := tagEndpointsWith (crossed ++ endpoint :: later) front
      let crossedTags := tagEndpointsWith (endpoint :: later) crossed
      let laterTags := tagEndpoints later
      have sourceShape : letters = front ++ crossed ++ endpoint :: later := by
        simpa [crossed, later, List.append_assoc] using shape
      have targetTags :
          tagEndpoints next =
            frontTags ++ EndpointTag.first endpoint ::
              crossedTags ++ laterTags := by
        have := tagMove.2
        simpa [next, frontTags, crossedTags, laterTags,
          endpointTagAgainst, endpointLater,
          List.append_assoc] using this
      have sourceTags :
          tagEndpoints letters =
            frontTags ++ crossedTags ++ EndpointTag.first endpoint ::
              laterTags := by
        rw [sourceShape]
        have := tagMove.1
        simpa [frontTags, crossedTags, laterTags,
          endpointTagAgainst, endpointLater,
          List.append_assoc] using this
      have separationEquation :
          endpointSeparation letters =
            endpointSeparation next + eventEndpointCount crossedTags := by
        unfold endpointSeparation
        rw [sourceTags, targetTags]
        exact endpointSeparationTags_move_first_left
          frontTags crossedTags laterTags endpoint
      have separationDrop :
          endpointSeparation next < endpointSeparation letters := by
        have positive : 0 < eventEndpointCount crossedTags := by
          simpa [crossedTags] using crossedEventPositive
        omega
      refine ⟨next, ?_, ?_, ?_,
        endpointMeasure_lt_of_separation_drop separationDrop⟩
      · rw [shape]
        simpa [next, crossed, later, List.append_assoc] using
          (frozenPullEndpointNested crossing endpoint
            before middle after).context front suffix
      · rw [sourceShape]
        simpa [next] using
          move_left_permutation_in_context
            front crossed later endpoint
      · intro equal
        exact (Nat.ne_of_lt separationDrop)
          (congrArg endpointSeparation equal)

private theorem ff_progress
    {letters : List Nat}
    (twoLimited : ∀ tested, letters.count tested ≤ 2) :
    EndpointFFCase letters → EndpointMeasureProgress letters
  | .laterXY front suffix big small gapA gapB shape ordered => by
      let later := gapA ++ [big] ++ gapB ++ [small] ++ suffix
      let next := front ++ [small, big] ++ later
      have different : big ≠ small := by omega
      have smallAbsent : small ∉ [big] := by
        simp [Ne.symm different]
      have smallLater : small ∈ later := by simp [later]
      have bigLater : big ∈ later := by simp [later]
      have tagMove := tagEndpoints_move_left
        front [big] later small smallAbsent
      let frontTags := tagEndpointsWith ([big] ++ small :: later) front
      let laterTags := tagEndpoints later
      have sourceShape : letters = front ++ [big] ++ small :: later := by
        simpa [later, List.append_assoc] using shape
      have sourceTags :
          tagEndpoints letters =
            frontTags ++ [EndpointTag.first big,
              EndpointTag.first small] ++ laterTags := by
        rw [sourceShape]
        have := tagMove.1
        simpa [frontTags, laterTags, tagEndpointsWith,
          endpointTagAgainst, smallLater, bigLater,
          List.append_assoc] using this
      have targetTags :
          tagEndpoints next =
            frontTags ++ [EndpointTag.first small,
              EndpointTag.first big] ++ laterTags := by
        have := tagMove.2
        simpa [next, frontTags, laterTags, tagEndpointsWith,
          endpointTagAgainst, smallLater, bigLater,
          List.append_assoc] using this
      have separationSame :
          endpointSeparation next = endpointSeparation letters := by
        unfold endpointSeparation
        rw [sourceTags, targetTags]
        have equation := endpointSeparationTags_move_first_left
          frontTags [EndpointTag.first big] laterTags small
        simpa [eventEndpointCount, EndpointTag.first] using equation.symm
      have firstEquation :
          ascendingInversions
              (firstProjection (tagEndpoints letters)) =
            ascendingInversions
              (firstProjection (tagEndpoints next)) + 1 := by
        rw [sourceTags, targetTags]
        simpa [firstProjection, EndpointTag.first,
          List.append_assoc] using
          ascendingInversions_swap_adjacent
            (firstProjection frontTags) (firstProjection laterTags)
            big small ordered
      have firstDrop :
          ascendingInversions (firstProjection (tagEndpoints next)) <
            ascendingInversions (firstProjection (tagEndpoints letters)) := by
        omega
      refine ⟨next, ?_, ?_, ?_,
        endpointMeasure_lt_of_first_drop separationSame firstDrop⟩
      · rw [shape]
        simpa [next, later, List.append_assoc] using
          (frozenSwapFirstLaterXY big small gapA gapB).context
            front suffix
      · rw [sourceShape]
        simpa [next] using
          move_left_permutation_in_context
            front [big] later small
      · intro equal
        exact (Nat.ne_of_lt firstDrop)
          (congrArg
            (fun entries =>
              ascendingInversions (firstProjection (tagEndpoints entries)))
            equal)
  | .laterYX front suffix big small gapA gapB shape ordered => by
      let later := gapA ++ [small] ++ gapB ++ [big] ++ suffix
      let next := front ++ [small, big] ++ later
      have different : big ≠ small := by omega
      have smallAbsent : small ∉ [big] := by
        simp [Ne.symm different]
      have smallLater : small ∈ later := by simp [later]
      have bigLater : big ∈ later := by simp [later]
      have tagMove := tagEndpoints_move_left
        front [big] later small smallAbsent
      let frontTags := tagEndpointsWith ([big] ++ small :: later) front
      let laterTags := tagEndpoints later
      have sourceShape : letters = front ++ [big] ++ small :: later := by
        simpa [later, List.append_assoc] using shape
      have sourceTags :
          tagEndpoints letters =
            frontTags ++ [EndpointTag.first big,
              EndpointTag.first small] ++ laterTags := by
        rw [sourceShape]
        have := tagMove.1
        simpa [frontTags, laterTags, tagEndpointsWith,
          endpointTagAgainst, smallLater, bigLater,
          List.append_assoc] using this
      have targetTags :
          tagEndpoints next =
            frontTags ++ [EndpointTag.first small,
              EndpointTag.first big] ++ laterTags := by
        have := tagMove.2
        simpa [next, frontTags, laterTags, tagEndpointsWith,
          endpointTagAgainst, smallLater, bigLater,
          List.append_assoc] using this
      have separationSame :
          endpointSeparation next = endpointSeparation letters := by
        unfold endpointSeparation
        rw [sourceTags, targetTags]
        have equation := endpointSeparationTags_move_first_left
          frontTags [EndpointTag.first big] laterTags small
        simpa [eventEndpointCount, EndpointTag.first] using equation.symm
      have firstEquation :
          ascendingInversions
              (firstProjection (tagEndpoints letters)) =
            ascendingInversions
              (firstProjection (tagEndpoints next)) + 1 := by
        rw [sourceTags, targetTags]
        simpa [firstProjection, EndpointTag.first,
          List.append_assoc] using
          ascendingInversions_swap_adjacent
            (firstProjection frontTags) (firstProjection laterTags)
            big small ordered
      have firstDrop :
          ascendingInversions (firstProjection (tagEndpoints next)) <
            ascendingInversions (firstProjection (tagEndpoints letters)) := by
        omega
      refine ⟨next, ?_, ?_, ?_,
        endpointMeasure_lt_of_first_drop separationSame firstDrop⟩
      · rw [shape]
        simpa [next, later, List.append_assoc] using
          (frozenSwapFirstLaterYX big small gapA gapB).context
            front suffix
      · rw [sourceShape]
        simpa [next] using
          move_left_permutation_in_context
            front [big] later small
      · intro equal
        exact (Nat.ne_of_lt firstDrop)
          (congrArg
            (fun entries =>
              ascendingInversions (firstProjection (tagEndpoints entries)))
            equal)

private theorem ee_progress
    {letters : List Nat}
    (twoLimited : ∀ tested, letters.count tested ≤ 2) :
    EndpointEECase letters → EndpointMeasureProgress letters
  | .firstBigSmall front suffix big small gapA gapB shape ordered => by
      let initial := front ++ [big] ++ gapA ++ [small] ++ gapB
      let later := suffix
      let next := initial ++ [big, small] ++ later
      have different : big ≠ small := by omega
      have bigAbsentLater : big ∉ later := by
        intro member
        have bound := twoLimited big
        rw [shape, List.count_append] at bound
        have laterPositive : 0 < later.count big :=
          List.count_pos_iff.mpr member
        have suffixPositive : 0 < suffix.count big := by
          simpa [later] using laterPositive
        simp [later, different, Ne.symm different,
          List.count_append] at bound
        omega
      have smallAbsentLater : small ∉ later := by
        intro member
        have bound := twoLimited small
        rw [shape, List.count_append] at bound
        have laterPositive : 0 < later.count small :=
          List.count_pos_iff.mpr member
        have suffixPositive : 0 < suffix.count small := by
          simpa [later] using laterPositive
        simp [later, different, Ne.symm different,
          List.count_append] at bound
        omega
      have bigAbsentCrossed : big ∉ [small] := by simp [different]
      have tagMove := tagEndpoints_move_left
        initial [small] later big bigAbsentCrossed
      let frontTags := tagEndpointsWith ([small] ++ big :: later) initial
      let laterTags := tagEndpoints later
      have sourceTags :
          tagEndpoints letters =
            frontTags ++ [EndpointTag.event small,
              EndpointTag.event big] ++ laterTags := by
        rw [shape]
        have := tagMove.1
        simpa [initial, later, frontTags, laterTags, tagEndpointsWith,
          endpointTagAgainst, bigAbsentLater, smallAbsentLater,
          different, Ne.symm different, List.append_assoc] using this
      have targetTags :
          tagEndpoints next =
            frontTags ++ [EndpointTag.event big,
              EndpointTag.event small] ++ laterTags := by
        have := tagMove.2
        simpa [next, later, frontTags, laterTags, tagEndpointsWith,
          endpointTagAgainst, bigAbsentLater, smallAbsentLater,
          different, Ne.symm different, List.append_assoc] using this
      have separationSame :
          endpointSeparation next = endpointSeparation letters := by
        unfold endpointSeparation
        rw [sourceTags, targetTags]
        simpa [List.append_assoc] using
          (endpointSeparationTags_swap_events
            frontTags laterTags small big).symm
      have firstSame :
          ascendingInversions (firstProjection (tagEndpoints next)) =
            ascendingInversions (firstProjection (tagEndpoints letters)) := by
        rw [sourceTags, targetTags]
        simp [firstProjection, EndpointTag.event]
      have smallMultiple :
          small ∈ firstProjection frontTags ++
            firstProjection laterTags := by
        have sourceFirst : small ∈ firstProjection (tagEndpoints letters) := by
          -- The displayed earlier occurrence and cap two make it a first tag.
          have countTwo : letters.count small = 2 := by
            have bound := twoLimited small
            rw [shape] at bound ⊢
            simp [different, Ne.symm different,
              List.count_append] at bound ⊢
            omega
          exact firstProjection_mem_of_count_eq_two
            (letters := letters) countTwo
        simpa [sourceTags, firstProjection,
          EndpointTag.event] using sourceFirst
      have bigMultiple :
          big ∈ firstProjection frontTags ++
            firstProjection laterTags := by
        have sourceFirst : big ∈ firstProjection (tagEndpoints letters) := by
          have countTwo : letters.count big = 2 := by
            have bound := twoLimited big
            rw [shape] at bound ⊢
            simp [different, Ne.symm different,
              List.count_append] at bound ⊢
            omega
          exact firstProjection_mem_of_count_eq_two
            (letters := letters) countTwo
        simpa [sourceTags, firstProjection,
          EndpointTag.event] using sourceFirst
      have eventEquation :
          eventGapInversions (tagEndpoints letters) =
            eventGapInversions (tagEndpoints next) + 1 := by
        rw [sourceTags, targetTags]
        simpa [List.append_assoc] using
          eventGapInversions_swap_adjacent_events
            frontTags laterTags small big
            smallMultiple bigMultiple ordered
      have eventDrop :
          eventGapInversions (tagEndpoints next) <
            eventGapInversions (tagEndpoints letters) := by
        omega
      refine ⟨next, ?_, ?_, ?_,
        endpointMeasure_lt_of_event_drop
          separationSame firstSame eventDrop⟩
      · rw [shape]
        simpa [next, initial, later, List.append_assoc] using
          (frozenSwapLastYX big small gapA gapB).context
            front suffix
      · rw [shape]
        simpa [next, initial, later, List.append_assoc] using
          move_left_permutation_in_context
            initial [small] later big
      · intro equal
        exact (Nat.ne_of_lt eventDrop)
          (congrArg
            (fun entries => eventGapInversions (tagEndpoints entries))
            equal)
  | .firstSmallBig front suffix big small gapA gapB shape ordered => by
      let initial := front ++ [small] ++ gapA ++ [big] ++ gapB
      let later := suffix
      let next := initial ++ [big, small] ++ later
      have different : big ≠ small := by omega
      have bigAbsentLater : big ∉ later := by
        intro member
        have bound := twoLimited big
        rw [shape, List.count_append] at bound
        have laterPositive : 0 < later.count big :=
          List.count_pos_iff.mpr member
        have suffixPositive : 0 < suffix.count big := by
          simpa [later] using laterPositive
        simp [later, different, Ne.symm different,
          List.count_append] at bound
        omega
      have smallAbsentLater : small ∉ later := by
        intro member
        have bound := twoLimited small
        rw [shape, List.count_append] at bound
        have laterPositive : 0 < later.count small :=
          List.count_pos_iff.mpr member
        have suffixPositive : 0 < suffix.count small := by
          simpa [later] using laterPositive
        simp [later, different, Ne.symm different,
          List.count_append] at bound
        omega
      have bigAbsentCrossed : big ∉ [small] := by simp [different]
      have tagMove := tagEndpoints_move_left
        initial [small] later big bigAbsentCrossed
      let frontTags := tagEndpointsWith ([small] ++ big :: later) initial
      let laterTags := tagEndpoints later
      have sourceTags :
          tagEndpoints letters =
            frontTags ++ [EndpointTag.event small,
              EndpointTag.event big] ++ laterTags := by
        rw [shape]
        have := tagMove.1
        simpa [initial, later, frontTags, laterTags, tagEndpointsWith,
          endpointTagAgainst, bigAbsentLater, smallAbsentLater,
          different, Ne.symm different, List.append_assoc] using this
      have targetTags :
          tagEndpoints next =
            frontTags ++ [EndpointTag.event big,
              EndpointTag.event small] ++ laterTags := by
        have := tagMove.2
        simpa [next, later, frontTags, laterTags, tagEndpointsWith,
          endpointTagAgainst, bigAbsentLater, smallAbsentLater,
          different, Ne.symm different, List.append_assoc] using this
      have separationSame :
          endpointSeparation next = endpointSeparation letters := by
        unfold endpointSeparation
        rw [sourceTags, targetTags]
        simpa [List.append_assoc] using
          (endpointSeparationTags_swap_events
            frontTags laterTags small big).symm
      have firstSame :
          ascendingInversions (firstProjection (tagEndpoints next)) =
            ascendingInversions (firstProjection (tagEndpoints letters)) := by
        rw [sourceTags, targetTags]
        simp [firstProjection, EndpointTag.event]
      have smallMultiple :
          small ∈ firstProjection frontTags ++
            firstProjection laterTags := by
        have sourceFirst : small ∈ firstProjection (tagEndpoints letters) := by
          have countTwo : letters.count small = 2 := by
            have bound := twoLimited small
            rw [shape] at bound ⊢
            simp [different, Ne.symm different,
              List.count_append] at bound ⊢
            omega
          exact firstProjection_mem_of_count_eq_two
            (letters := letters) countTwo
        simpa [sourceTags, firstProjection,
          EndpointTag.event] using sourceFirst
      have bigMultiple :
          big ∈ firstProjection frontTags ++
            firstProjection laterTags := by
        have sourceFirst : big ∈ firstProjection (tagEndpoints letters) := by
          have countTwo : letters.count big = 2 := by
            have bound := twoLimited big
            rw [shape] at bound ⊢
            simp [different, Ne.symm different,
              List.count_append] at bound ⊢
            omega
          exact firstProjection_mem_of_count_eq_two
            (letters := letters) countTwo
        simpa [sourceTags, firstProjection,
          EndpointTag.event] using sourceFirst
      have eventEquation :
          eventGapInversions (tagEndpoints letters) =
            eventGapInversions (tagEndpoints next) + 1 := by
        rw [sourceTags, targetTags]
        simpa [List.append_assoc] using
          eventGapInversions_swap_adjacent_events
            frontTags laterTags small big
            smallMultiple bigMultiple ordered
      have eventDrop :
          eventGapInversions (tagEndpoints next) <
            eventGapInversions (tagEndpoints letters) := by
        omega
      refine ⟨next, ?_, ?_, ?_,
        endpointMeasure_lt_of_event_drop
          separationSame firstSame eventDrop⟩
      · rw [shape]
        simpa [next, initial, later, List.append_assoc] using
          (frozenSwapLastYX small big gapA gapB).symm.context
            front suffix
      · rw [shape]
        simpa [next, initial, later, List.append_assoc] using
          move_left_permutation_in_context
            initial [small] later big
      · intro equal
        exact (Nat.ne_of_lt eventDrop)
          (congrArg
            (fun entries => eventGapInversions (tagEndpoints entries))
            equal)

/-- The exact unbounded progress theorem at the measure layer. -/
theorem endpointDisorder_progress_measure
    {letters : List Nat}
    (twoLimited : ∀ tested, letters.count tested ≤ 2)
    (connected : ConnectedComponentSupportConnected letters)
    (positive : (endpointMeasure letters).Positive) :
    EndpointMeasureProgress letters := by
  rcases positive with separationPositive |
      ⟨separationZero, firstPositive⟩ |
      ⟨separationZero, firstZero, eventPositive⟩
  · exact ef_progress twoLimited
      (endpointEFCase_of_positiveSeparation
        twoLimited connected separationPositive)
  · exact ff_progress twoLimited
      (endpointFFCase_of_positiveFirstInversion
        separationZero firstPositive)
  · exact ee_progress twoLimited
      (endpointEECase_of_positiveEventInversion
        separationZero eventPositive)

end CapTwoRTCRoute
end SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
