import SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.CapTwoEndpointTags

/-!
# Numeric endpoint inversions and the F/F dispatcher case

This module provides the two generic adjacent-inversion lemmas used by the
lexicographic endpoint measure and extracts the literal F/F case once the
separation coordinate is zero.

Static off-tree source; not locally elaborated.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
namespace CapTwoRTCRoute

/-! ## First-event projection -/

def firstProjection : List EndpointTag → List Nat
  | [] => []
  | ⟨letter, .first⟩ :: rest => letter :: firstProjection rest
  | ⟨_, .event⟩ :: rest => firstProjection rest

@[simp]
theorem firstProjection_append (left right : List EndpointTag) :
    firstProjection (left ++ right) =
      firstProjection left ++ firstProjection right := by
  induction left with
  | nil => rfl
  | cons tag rest inductionHypothesis =>
      cases tag with
      | mk letter side =>
          cases side <;>
            simp [firstProjection, inductionHypothesis]

@[simp]
theorem firstProjection_map_first (letters : List Nat) :
    firstProjection (letters.map EndpointTag.first) = letters := by
  induction letters with
  | nil => rfl
  | cons letter rest inductionHypothesis =>
      simp [firstProjection, EndpointTag.first, inductionHypothesis]

@[simp]
theorem firstProjection_map_event (letters : List Nat) :
    firstProjection (letters.map EndpointTag.event) = [] := by
  induction letters with
  | nil => rfl
  | cons letter rest inductionHypothesis =>
      simp [firstProjection, EndpointTag.event, inductionHypothesis]

/-! ## Generic ascending and descending inversion counts -/

def countLT (pivot : Nat) : List Nat → Nat
  | [] => 0
  | value :: rest =>
      (if value < pivot then 1 else 0) + countLT pivot rest

def countGT (pivot : Nat) : List Nat → Nat
  | [] => 0
  | value :: rest =>
      (if pivot < value then 1 else 0) + countGT pivot rest

/-- Inversions relative to ascending numeric order. -/
def ascendingInversions : List Nat → Nat
  | [] => 0
  | value :: rest => countLT value rest + ascendingInversions rest

/-- Inversions relative to descending numeric order. -/
def descendingInversions : List Nat → Nat
  | [] => 0
  | value :: rest => countGT value rest + descendingInversions rest

@[simp]
theorem countLT_append (pivot : Nat) (left right : List Nat) :
    countLT pivot (left ++ right) =
      countLT pivot left + countLT pivot right := by
  induction left with
  | nil => simp [countLT]
  | cons value rest inductionHypothesis =>
      simp [countLT, inductionHypothesis, Nat.add_assoc]

@[simp]
theorem countGT_append (pivot : Nat) (left right : List Nat) :
    countGT pivot (left ++ right) =
      countGT pivot left + countGT pivot right := by
  induction left with
  | nil => simp [countGT]
  | cons value rest inductionHypothesis =>
      simp [countGT, inductionHypothesis, Nat.add_assoc]

theorem countLT_eq_zero_iff (pivot : Nat) :
    ∀ values : List Nat,
      countLT pivot values = 0 ↔
        ∀ value, value ∈ values → pivot ≤ value
  | [] => by simp [countLT]
  | value :: rest => by
      rw [countLT, Nat.add_eq_zero,
        countLT_eq_zero_iff pivot rest]
      by_cases small : value < pivot
      · have notOrdered : ¬pivot ≤ value := Nat.not_le.mpr small
        simp [small, notOrdered]
      · have ordered : pivot ≤ value := by omega
        simp [small, ordered]

theorem countGT_eq_zero_iff (pivot : Nat) :
    ∀ values : List Nat,
      countGT pivot values = 0 ↔
        ∀ value, value ∈ values → value ≤ pivot
  | [] => by simp [countGT]
  | value :: rest => by
      rw [countGT, Nat.add_eq_zero,
        countGT_eq_zero_iff pivot rest]
      by_cases large : pivot < value
      · have notOrdered : ¬value ≤ pivot := Nat.not_le.mpr large
        simp [large, notOrdered]
      · have ordered : value ≤ pivot := by omega
        simp [large, ordered]

theorem ascendingInversions_eq_zero_iff_pairwise :
    ∀ values : List Nat,
      ascendingInversions values = 0 ↔ values.Pairwise (· ≤ ·)
  | [] => by simp [ascendingInversions]
  | value :: rest => by
      rw [ascendingInversions, Nat.add_eq_zero,
        countLT_eq_zero_iff value rest,
        ascendingInversions_eq_zero_iff_pairwise rest,
        List.pairwise_cons]

theorem descendingInversions_eq_zero_iff_pairwise :
    ∀ values : List Nat,
      descendingInversions values = 0 ↔ values.Pairwise (· ≥ ·)
  | [] => by simp [descendingInversions]
  | value :: rest => by
      rw [descendingInversions, Nat.add_eq_zero,
        countGT_eq_zero_iff value rest,
        descendingInversions_eq_zero_iff_pairwise rest,
        List.pairwise_cons]

/-- A positive ascending-order inversion count has a literal adjacent
descent. -/
theorem exists_adjacent_descent_of_ascendingInversions_pos :
    ∀ values : List Nat,
      0 < ascendingInversions values →
        ∃ front big small suffix,
          small < big ∧
          values = front ++ big :: small :: suffix
  | [], positive => by simp [ascendingInversions] at positive
  | [_], positive => by simp [ascendingInversions, countLT] at positive
  | first :: second :: rest, positive => by
      by_cases descent : second < first
      · exact ⟨[], first, second, rest, descent, rfl⟩
      · have firstLeSecond : first ≤ second := by omega
        by_cases tailPositive :
            0 < ascendingInversions (second :: rest)
        · rcases exists_adjacent_descent_of_ascendingInversions_pos
              (second :: rest) tailPositive with
            ⟨front, big, small, suffix, ordered, shape⟩
          exact
            ⟨first :: front, big, small, suffix, ordered,
              by simp [shape, List.append_assoc]⟩
        · have tailZero :
              ascendingInversions (second :: rest) = 0 :=
            Nat.eq_zero_of_not_pos tailPositive
          have tailPairwise :
              (second :: rest).Pairwise (· ≤ ·) :=
            (ascendingInversions_eq_zero_iff_pairwise
              (second :: rest)).mp tailZero
          have firstLeAll :
              ∀ tested, tested ∈ second :: rest → first ≤ tested := by
            intro tested member
            rcases List.mem_cons.mp member with equal | inRest
            · subst tested
              exact firstLeSecond
            · exact Nat.le_trans firstLeSecond
                ((List.pairwise_cons.mp tailPairwise).1 tested inRest)
          have wholePairwise :
              (first :: second :: rest).Pairwise (· ≤ ·) :=
            List.pairwise_cons.mpr ⟨firstLeAll, tailPairwise⟩
          have wholeZero :=
            (ascendingInversions_eq_zero_iff_pairwise
              (first :: second :: rest)).mpr wholePairwise
          omega

/-- A positive descending-order inversion count has a literal adjacent
ascent. -/
theorem exists_adjacent_ascent_of_descendingInversions_pos :
    ∀ values : List Nat,
      0 < descendingInversions values →
        ∃ front small big suffix,
          small < big ∧
          values = front ++ small :: big :: suffix
  | [], positive => by simp [descendingInversions] at positive
  | [_], positive => by simp [descendingInversions, countGT] at positive
  | first :: second :: rest, positive => by
      by_cases ascent : first < second
      · exact ⟨[], first, second, rest, ascent, rfl⟩
      · have secondLeFirst : second ≤ first := by omega
        by_cases tailPositive :
            0 < descendingInversions (second :: rest)
        · rcases exists_adjacent_ascent_of_descendingInversions_pos
              (second :: rest) tailPositive with
            ⟨front, small, big, suffix, ordered, shape⟩
          exact
            ⟨first :: front, small, big, suffix, ordered,
              by simp [shape, List.append_assoc]⟩
        · have tailZero :
              descendingInversions (second :: rest) = 0 :=
            Nat.eq_zero_of_not_pos tailPositive
          have tailPairwise :
              (second :: rest).Pairwise (· ≥ ·) :=
            (descendingInversions_eq_zero_iff_pairwise
              (second :: rest)).mp tailZero
          have firstGeAll :
              ∀ tested, tested ∈ second :: rest → tested ≤ first := by
            intro tested member
            rcases List.mem_cons.mp member with equal | inRest
            · subst tested
              exact secondLeFirst
            · exact Nat.le_trans
                ((List.pairwise_cons.mp tailPairwise).1 tested inRest)
                secondLeFirst
          have wholePairwise :
              (first :: second :: rest).Pairwise (· ≥ ·) :=
            List.pairwise_cons.mpr ⟨firstGeAll, tailPairwise⟩
          have wholeZero :=
            (descendingInversions_eq_zero_iff_pairwise
              (first :: second :: rest)).mpr wholePairwise
          omega

private theorem countLT_swap_adjacent
    (pivot x y : Nat) (front suffix : List Nat) :
    countLT pivot (front ++ x :: y :: suffix) =
      countLT pivot (front ++ y :: x :: suffix) := by
  simp [countLT_append, countLT, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

private theorem countGT_swap_adjacent
    (pivot x y : Nat) (front suffix : List Nat) :
    countGT pivot (front ++ x :: y :: suffix) =
      countGT pivot (front ++ y :: x :: suffix) := by
  simp [countGT_append, countGT, Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm]

/-- Swapping one adjacent descent removes exactly one ascending inversion. -/
theorem ascendingInversions_swap_adjacent
    (front suffix : List Nat) (big small : Nat)
    (ordered : small < big) :
    ascendingInversions (front ++ big :: small :: suffix) =
      ascendingInversions (front ++ small :: big :: suffix) + 1 := by
  induction front with
  | nil =>
      simp [ascendingInversions, countLT, ordered,
        show ¬big < small by omega]
      omega
  | cons value rest inductionHypothesis =>
      simp only [List.cons_append, ascendingInversions]
      rw [countLT_swap_adjacent value big small rest suffix,
        inductionHypothesis]
      omega

/-- Swapping one adjacent ascent removes exactly one descending inversion. -/
theorem descendingInversions_swap_adjacent
    (front suffix : List Nat) (small big : Nat)
    (ordered : small < big) :
    descendingInversions (front ++ small :: big :: suffix) =
      descendingInversions (front ++ big :: small :: suffix) + 1 := by
  induction front with
  | nil =>
      simp [descendingInversions, countGT, ordered,
        show ¬big < small by omega]
      omega
  | cons value rest inductionHypothesis =>
      simp only [List.cons_append, descendingInversions]
      rw [countGT_swap_adjacent value small big rest suffix,
        inductionHypothesis]
      omega

/-! ## Zero separation and the first-endpoint branch -/

private theorem firstEndpointCount_map_event (events : List Nat) :
    firstEndpointCount (events.map EndpointTag.event) = 0 := by
  induction events with
  | nil => rfl
  | cons event rest inductionHypothesis =>
      simpa [firstEndpointCount, EndpointTag.event] using
        inductionHypothesis

private theorem firstEndpointCount_eq_zero_iff :
    ∀ tags : List EndpointTag,
      firstEndpointCount tags = 0 ↔
        ∃ events : List Nat, tags = events.map EndpointTag.event
  | [] => by simp [firstEndpointCount]
  | ⟨letter, .first⟩ :: rest => by
      constructor
      · intro zero
        simp [firstEndpointCount] at zero
      · rintro ⟨events, shape⟩
        cases events with
        | nil => cases shape
        | cons event tail =>
            have headEquality := congrArg List.head? shape
            simp [EndpointTag.first, EndpointTag.event] at headEquality
  | ⟨letter, .event⟩ :: rest => by
      constructor
      · intro zero
        have restZero : firstEndpointCount rest = 0 := by
          simpa [firstEndpointCount] using zero
        obtain ⟨events, shape⟩ :=
          (firstEndpointCount_eq_zero_iff rest).mp restZero
        exact ⟨letter :: events, by simp [shape, EndpointTag.event]⟩
      · rintro ⟨events, shape⟩
        rw [shape]
        exact firstEndpointCount_map_event events

/-- Zero separation is exactly an all-F prefix followed by an all-E suffix. -/
theorem endpointTags_separated_of_zero :
    ∀ tags : List EndpointTag,
      endpointSeparationTags tags = 0 →
        ∃ firsts events : List Nat,
          tags = firsts.map EndpointTag.first ++
            events.map EndpointTag.event
  | [], _ => ⟨[], [], rfl⟩
  | ⟨letter, .first⟩ :: rest, zero => by
      have tailZero : endpointSeparationTags rest = 0 := by
        simpa [endpointSeparationTags] using zero
      obtain ⟨firsts, events, shape⟩ :=
        endpointTags_separated_of_zero rest tailZero
      exact ⟨letter :: firsts, events,
        by simp [shape, EndpointTag.first, List.append_assoc]⟩
  | ⟨letter, .event⟩ :: rest, zero => by
      have firstZero : firstEndpointCount rest = 0 := by
        simp [endpointSeparationTags] at zero
        omega
      obtain ⟨events, shape⟩ :=
        (firstEndpointCount_eq_zero_iff rest).mp firstZero
      exact ⟨[], letter :: events,
        by simp [shape, EndpointTag.event]⟩

/-- Raw facts encoded by two adjacent first tags. -/
private theorem adjacent_first_first_roles
    {letters : List Nat} {stem suffix : List EndpointTag} {x y : Nat}
    (different : x ≠ y)
    (shape :
      tagEndpoints letters =
        stem ++ EndpointTag.first x :: EndpointTag.first y :: suffix) :
    let before := stem.map EndpointTag.letter
    let after := suffix.map EndpointTag.letter
    letters = before ++ x :: y :: after ∧
      x ∈ after ∧ y ∈ after := by
  let before := stem.map EndpointTag.letter
  let after := suffix.map EndpointTag.letter
  have rawShape : letters = before ++ x :: y :: after := by
    have erased := congrArg (List.map EndpointTag.letter) shape
    simpa [before, after, EndpointTag.first,
      List.map_append] using erased
  have dropped := congrArg (List.drop stem.length) shape
  have tailShape :
      tagEndpoints (x :: y :: after) =
        EndpointTag.first x :: EndpointTag.first y :: suffix := by
    rw [tagEndpoints_drop, rawShape] at dropped
    simpa [before] using dropped
  have xLater : x ∈ y :: after := by
    by_cases later : x ∈ y :: after
    · exact later
    · have heads := congrArg List.head? tailShape
      simp [tagEndpoints, later, EndpointTag.first,
        EndpointTag.event] at heads
  have xInAfter : x ∈ after := by
    rcases List.mem_cons.mp xLater with equal | member
    · exact False.elim (different equal)
    · exact member
  have yInAfter : y ∈ after := by
    by_cases later : y ∈ after
    · exact later
    · have seconds :=
        congrArg (fun tags : List EndpointTag => (tags.drop 1).head?)
          tailShape
      simp [tagEndpoints, xLater, later, EndpointTag.first,
        EndpointTag.event] at seconds
  change
    letters = before ++ x :: y :: after ∧
      x ∈ after ∧ y ∈ after
  exact ⟨rawShape, xInAfter, yInAfter⟩

inductive EndpointFFCase (letters : List Nat) : Prop where
  | laterXY
      (front suffix : List Nat) (big small : Nat)
      (gapA gapB : List Nat)
      (shape :
        letters = front ++ [big, small] ++ gapA ++ [big] ++
          gapB ++ [small] ++ suffix)
      (ordered : small < big) : EndpointFFCase letters
  | laterYX
      (front suffix : List Nat) (big small : Nat)
      (gapA gapB : List Nat)
      (shape :
        letters = front ++ [big, small] ++ gapA ++ [small] ++
          gapB ++ [big] ++ suffix)
      (ordered : small < big) : EndpointFFCase letters

def EndpointFFCase.toDisorderCase
    {letters : List Nat} : EndpointFFCase letters → EndpointDisorderCase letters
  | .laterXY front suffix big small gapA gapB shape _ =>
      .ffLaterXY front suffix big small gapA gapB shape
  | .laterYX front suffix big small gapA gapB shape _ =>
      .ffLaterYX front suffix big small gapA gapB shape

/-- Once separation is zero, a positive first-order inversion produces one
of the two literal F/F dispatcher cases. -/
theorem endpointFFCase_of_positiveFirstInversion
    {letters : List Nat}
    (separated : endpointSeparation letters = 0)
    (positive :
      0 < ascendingInversions (firstProjection (tagEndpoints letters))) :
    EndpointFFCase letters := by
  obtain ⟨firsts, events, tagSeparated⟩ :=
    endpointTags_separated_of_zero (tagEndpoints letters) separated
  have firstProjectionEq :
      firstProjection (tagEndpoints letters) = firsts := by
    rw [tagSeparated]
    simp
  rw [firstProjectionEq] at positive
  obtain ⟨firstPrefix, big, small, firstSuffix,
      ordered, firstShape⟩ :=
    exists_adjacent_descent_of_ascendingInversions_pos firsts positive
  have tagShape :
      tagEndpoints letters =
        firstPrefix.map EndpointTag.first ++
          EndpointTag.first big :: EndpointTag.first small ::
            (firstSuffix.map EndpointTag.first ++
              events.map EndpointTag.event) := by
    rw [tagSeparated, firstShape]
    simp [List.map_append, List.append_assoc]
  have different : big ≠ small := by omega
  have roles := adjacent_first_first_roles different tagShape
  let rawBefore :=
    (firstPrefix.map EndpointTag.first).map EndpointTag.letter
  let rawAfter :=
    (firstSuffix.map EndpointTag.first ++
      events.map EndpointTag.event).map EndpointTag.letter
  change
    letters = rawBefore ++ big :: small :: rawAfter ∧
      big ∈ rawAfter ∧ small ∈ rawAfter at roles
  rcases roles with ⟨rawShape, bigLater, smallLater⟩
  rcases two_distinct_members_order big small different
      bigLater smallLater with
    ⟨gapA, gapB, suffix, laterShape⟩ |
    ⟨gapA, gapB, suffix, laterShape⟩
  · refine .laterXY rawBefore suffix big small gapA gapB ?_ ordered
    rw [rawShape, laterShape]
    simp [List.append_assoc]
  · refine .laterYX rawBefore suffix big small gapA gapB ?_ ordered
    rw [rawShape, laterShape]
    simp [List.append_assoc]

end CapTwoRTCRoute
end SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
