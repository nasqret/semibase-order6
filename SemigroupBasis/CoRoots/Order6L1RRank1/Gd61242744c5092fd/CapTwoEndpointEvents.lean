import SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.CapTwoEndpointInversions

/-!
# Multiple-event gaps and the E/E dispatcher case

After endpoint separation and first-order inversions vanish, all first tags
precede all event tags.  Singleton events split the multiple events into gaps.
This module measures descending-order inversions independently inside those
gaps and turns a positive coordinate into one of the two literal E/E cases.

Static off-tree source; not locally elaborated.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
namespace CapTwoRTCRoute

/-! ## Event projection and maximal multiple-event runs -/

def eventProjection : List EndpointTag → List Nat
  | [] => []
  | ⟨_, .first⟩ :: rest => eventProjection rest
  | ⟨letter, .event⟩ :: rest => letter :: eventProjection rest

@[simp]
theorem eventProjection_append (left right : List EndpointTag) :
    eventProjection (left ++ right) =
      eventProjection left ++ eventProjection right := by
  induction left with
  | nil => rfl
  | cons tag rest inductionHypothesis =>
      cases tag with
      | mk letter side =>
          cases side <;>
            simp [eventProjection, inductionHypothesis]

@[simp]
theorem eventProjection_map_first (letters : List Nat) :
    eventProjection (letters.map EndpointTag.first) = [] := by
  induction letters with
  | nil => rfl
  | cons letter rest inductionHypothesis =>
      simp [eventProjection, EndpointTag.first, inductionHypothesis]

@[simp]
theorem eventProjection_map_event (letters : List Nat) :
    eventProjection (letters.map EndpointTag.event) = letters := by
  induction letters with
  | nil => rfl
  | cons letter rest inductionHypothesis =>
      simp [eventProjection, EndpointTag.event, inductionHypothesis]

/-! ## The third coordinate -/

/-- Count larger later multiples, stopping at the next singleton event. -/
def countGTInMultipleRun
    (firsts : List Nat) (pivot : Nat) : List Nat → Nat
  | [] => 0
  | value :: rest =>
      if value ∈ firsts then
        (if pivot < value then 1 else 0) +
          countGTInMultipleRun firsts pivot rest
      else
        0

/-- Sum descending-order inversions within each singleton-delimited run. -/
def eventGapInversionsList
    (firsts : List Nat) : List Nat → Nat
  | [] => 0
  | value :: rest =>
      if value ∈ firsts then
        countGTInMultipleRun firsts value rest +
          eventGapInversionsList firsts rest
      else
        eventGapInversionsList firsts rest

def eventGapInversions (tags : List EndpointTag) : Nat :=
  eventGapInversionsList
    (firstProjection tags) (eventProjection tags)

private theorem exists_larger_in_current_run
    (firsts : List Nat) (pivot : Nat) :
    ∀ events : List Nat,
      0 < countGTInMultipleRun firsts pivot events →
        ∃ front larger suffix,
          (∀ value, value ∈ front → value ∈ firsts) ∧
          larger ∈ firsts ∧ pivot < larger ∧
          events = front ++ larger :: suffix
  | [], positive => by
      simp [countGTInMultipleRun] at positive
  | value :: rest, positive => by
      by_cases multiple : value ∈ firsts
      · by_cases larger : pivot < value
        · exact ⟨[], value, rest, by simp, multiple, larger, rfl⟩
        · have tailPositive :
              0 < countGTInMultipleRun firsts pivot rest := by
            simpa [countGTInMultipleRun, multiple, larger] using positive
          obtain ⟨front, selected, suffix, frontMultiple,
              selectedMultiple, ordered, shape⟩ :=
            exists_larger_in_current_run firsts pivot rest tailPositive
          exact ⟨value :: front, selected, suffix,
            by
              intro tested member
              rcases List.mem_cons.mp member with equal | inFront
              · simpa [equal] using multiple
              · exact frontMultiple tested inFront,
            selectedMultiple, ordered,
            by simp [shape, List.append_assoc]⟩
      · simp [countGTInMultipleRun, multiple] at positive

private theorem exists_adjacent_ascent_to_larger
    {firsts : List Nat} {pivot larger : Nat} {middle : List Nat}
    (pivotMultiple : pivot ∈ firsts)
    (middleMultiple : ∀ value, value ∈ middle → value ∈ firsts)
    (largerMultiple : larger ∈ firsts)
    (ordered : pivot < larger) :
    ∃ front small big suffix,
      small < big ∧ small ∈ firsts ∧ big ∈ firsts ∧
      pivot :: middle ++ [larger] = front ++ small :: big :: suffix := by
  have inversionPositive :
      0 < descendingInversions (pivot :: middle ++ [larger]) := by
    by_cases positive :
        0 < descendingInversions (pivot :: middle ++ [larger])
    · exact positive
    · have inversionZero :
          descendingInversions (pivot :: middle ++ [larger]) = 0 :=
        Nat.eq_zero_of_not_pos positive
      have pairwise :
          (pivot :: middle ++ [larger]).Pairwise (· ≥ ·) :=
        (descendingInversions_eq_zero_iff_pairwise
          (pivot :: middle ++ [larger])).mp inversionZero
      have largerLePivot : larger ≤ pivot :=
        (List.pairwise_cons.mp pairwise).1 larger (by simp)
      omega
  obtain ⟨front, small, big, suffix, ascent, shape⟩ :=
    exists_adjacent_ascent_of_descendingInversions_pos
      (pivot :: middle ++ [larger]) inversionPositive
  have everyMultiple :
      ∀ value, value ∈ pivot :: middle ++ [larger] →
        value ∈ firsts := by
    intro value member
    rcases List.mem_cons.mp member with equal | inTail
    · simpa [equal] using pivotMultiple
    · rcases List.mem_append.mp inTail with inMiddle | atEnd
      · exact middleMultiple value inMiddle
      · have equal : value = larger := by simpa using atEnd
        simpa [equal] using largerMultiple
  have smallMultiple : small ∈ firsts :=
    everyMultiple small (by rw [shape]; simp)
  have bigMultiple : big ∈ firsts :=
    everyMultiple big (by rw [shape]; simp)
  exact ⟨front, small, big, suffix, ascent,
    smallMultiple, bigMultiple, shape⟩

/-- A positive third coordinate exposes a literal adjacent ascent of two
multiple events in one singleton-delimited gap. -/
theorem exists_adjacent_multiple_event_ascent
    (firsts : List Nat) :
    ∀ events : List Nat,
      0 < eventGapInversionsList firsts events →
        ∃ front small big suffix,
          small < big ∧ small ∈ firsts ∧ big ∈ firsts ∧
          events = front ++ small :: big :: suffix
  | [], positive => by
      simp [eventGapInversionsList] at positive
  | selected :: rest, positive => by
      by_cases selectedMultiple : selected ∈ firsts
      · by_cases headPositive :
            0 < countGTInMultipleRun firsts selected rest
        · obtain ⟨middle, larger, afterLarger, middleMultiple,
              largerMultiple, selectedLess, restShape⟩ :=
            exists_larger_in_current_run firsts selected rest headPositive
          obtain ⟨insideFront, small, big, insideSuffix,
              ordered, smallMultiple, bigMultiple, insideShape⟩ :=
            exists_adjacent_ascent_to_larger selectedMultiple
              middleMultiple largerMultiple selectedLess
          exact ⟨insideFront, small, big,
            insideSuffix ++ afterLarger, ordered,
            smallMultiple, bigMultiple,
            by
              rw [restShape]
              calc
                selected :: middle ++ larger :: afterLarger =
                    (selected :: middle ++ [larger]) ++
                      afterLarger := by simp [List.append_assoc]
                _ = (insideFront ++ small :: big :: insideSuffix) ++
                      afterLarger := by rw [insideShape]
                _ = insideFront ++ small :: big ::
                      (insideSuffix ++ afterLarger) := by
                    simp [List.append_assoc]⟩
        · have tailPositive :
              0 < eventGapInversionsList firsts rest := by
            simp [eventGapInversionsList, selectedMultiple] at positive
            omega
          obtain ⟨front, small, big, suffix, ordered,
              smallMultiple, bigMultiple, shape⟩ :=
            exists_adjacent_multiple_event_ascent firsts rest tailPositive
          exact ⟨selected :: front, small, big, suffix,
            ordered, smallMultiple, bigMultiple,
            by simp [shape, List.append_assoc]⟩
      · have tailPositive :
            0 < eventGapInversionsList firsts rest := by
          simpa [eventGapInversionsList, selectedMultiple] using positive
        obtain ⟨front, small, big, suffix, ordered,
            smallMultiple, bigMultiple, shape⟩ :=
          exists_adjacent_multiple_event_ascent firsts rest tailPositive
        exact ⟨selected :: front, small, big, suffix,
          ordered, smallMultiple, bigMultiple,
          by simp [shape, List.append_assoc]⟩

private theorem countGTInMultipleRun_swap_adjacent
    (firsts : List Nat) (pivot : Nat)
    (front suffix : List Nat) (small big : Nat)
    (smallMultiple : small ∈ firsts)
    (bigMultiple : big ∈ firsts) :
    countGTInMultipleRun firsts pivot
        (front ++ small :: big :: suffix) =
      countGTInMultipleRun firsts pivot
        (front ++ big :: small :: suffix) := by
  induction front with
  | nil =>
      simp [countGTInMultipleRun, smallMultiple, bigMultiple,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | cons value rest inductionHypothesis =>
      by_cases multiple : value ∈ firsts
      · simp [countGTInMultipleRun, multiple, inductionHypothesis]
      · simp [countGTInMultipleRun, multiple]

/-- Swapping one adjacent event ascent inside a multiple run removes exactly
one third-coordinate inversion. -/
theorem eventGapInversionsList_swap_adjacent
    (firsts front suffix : List Nat) (small big : Nat)
    (smallMultiple : small ∈ firsts)
    (bigMultiple : big ∈ firsts)
    (ordered : small < big) :
    eventGapInversionsList firsts
        (front ++ small :: big :: suffix) =
      eventGapInversionsList firsts
        (front ++ big :: small :: suffix) + 1 := by
  induction front with
  | nil =>
      simp [eventGapInversionsList, countGTInMultipleRun,
        smallMultiple, bigMultiple, ordered,
        show ¬ big < small by omega]
      omega
  | cons value rest inductionHypothesis =>
      by_cases multiple : value ∈ firsts
      · simp only [List.cons_append, eventGapInversionsList]
        rw [if_pos multiple, if_pos multiple,
          countGTInMultipleRun_swap_adjacent firsts value rest suffix
            small big smallMultiple bigMultiple,
          inductionHypothesis]
        omega
      · simp only [List.cons_append, eventGapInversionsList]
        rw [if_neg multiple, if_neg multiple, inductionHypothesis]

/-- Tag-level form of the exact E/E coordinate drop. -/
theorem eventGapInversions_swap_adjacent_events
    (tagFront tagSuffix : List EndpointTag) (small big : Nat)
    (smallMultiple :
      small ∈ firstProjection tagFront ++ firstProjection tagSuffix)
    (bigMultiple :
      big ∈ firstProjection tagFront ++ firstProjection tagSuffix)
    (ordered : small < big) :
    eventGapInversions
        (tagFront ++ EndpointTag.event small ::
          EndpointTag.event big :: tagSuffix) =
      eventGapInversions
          (tagFront ++ EndpointTag.event big ::
            EndpointTag.event small :: tagSuffix) + 1 := by
  simpa [eventGapInversions, EndpointTag.event,
    List.append_assoc] using
    eventGapInversionsList_swap_adjacent
      (firstProjection tagFront ++ firstProjection tagSuffix)
      (eventProjection tagFront) (eventProjection tagSuffix)
      small big smallMultiple bigMultiple ordered

/-! ## Literal E/E extraction -/

inductive EndpointEECase (letters : List Nat) : Prop where
  | firstBigSmall
      (front suffix : List Nat) (big small : Nat)
      (gapA gapB : List Nat)
      (shape :
        letters = front ++ [big] ++ gapA ++ [small] ++ gapB ++
          [small, big] ++ suffix)
      (ordered : small < big) : EndpointEECase letters
  | firstSmallBig
      (front suffix : List Nat) (big small : Nat)
      (gapA gapB : List Nat)
      (shape :
        letters = front ++ [small] ++ gapA ++ [big] ++ gapB ++
          [small, big] ++ suffix)
      (ordered : small < big) : EndpointEECase letters

def EndpointEECase.toDisorderCase
    {letters : List Nat} : EndpointEECase letters → EndpointDisorderCase letters
  | .firstBigSmall front suffix big small gapA gapB shape _ =>
      .eeFirstXY front suffix big small gapA gapB shape
  | .firstSmallBig front suffix big small gapA gapB shape _ =>
      .eeFirstYX front suffix big small gapA gapB shape

/-- With the first two coordinates zero, a positive event-gap inversion
constructs one of the two literal E/E dispatcher cases. -/
theorem endpointEECase_of_positiveEventInversion
    {letters : List Nat}
    (separated : endpointSeparation letters = 0)
    (positive : 0 < eventGapInversions (tagEndpoints letters)) :
    EndpointEECase letters := by
  obtain ⟨firsts, events, tagSeparated⟩ :=
    endpointTags_separated_of_zero (tagEndpoints letters) separated
  have firstProjectionEq :
      firstProjection (tagEndpoints letters) = firsts := by
    rw [tagSeparated]
    simp
  have eventProjectionEq :
      eventProjection (tagEndpoints letters) = events := by
    rw [tagSeparated]
    simp
  unfold eventGapInversions at positive
  rw [firstProjectionEq, eventProjectionEq] at positive
  obtain ⟨beforeEvents, small, big, afterEvents,
      ordered, smallFirst, bigFirst, eventShape⟩ :=
    exists_adjacent_multiple_event_ascent firsts events positive
  have different : big ≠ small := by omega
  have rawSeparated : letters = firsts ++ events := by
    have erased :=
      congrArg (List.map EndpointTag.letter) tagSeparated
    simpa [EndpointTag.first, EndpointTag.event,
      List.map_append, Function.comp_def] using erased
  rcases two_distinct_members_order big small different
      bigFirst smallFirst with
    ⟨firstFront, firstMiddle, firstAfter, firstShape⟩ |
    ⟨firstFront, firstMiddle, firstAfter, firstShape⟩
  · refine .firstBigSmall firstFront afterEvents big small
      firstMiddle (firstAfter ++ beforeEvents) ?_ ordered
    rw [rawSeparated, firstShape, eventShape]
    simp [List.append_assoc]
  · refine .firstSmallBig firstFront afterEvents big small
      firstMiddle (firstAfter ++ beforeEvents) ?_ ordered
    rw [rawSeparated, firstShape, eventShape]
    simp [List.append_assoc]

end CapTwoRTCRoute
end SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
