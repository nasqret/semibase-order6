import SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.CapTwoProgressDispatcher
import SemigroupBasis.Examples.ConnectedComponentFourComponents

/-!
# Endpoint tags and the positive-separation case

This route-local module contains only list combinatorics.  It extracts the
crossing or nested `E/F` dispatcher case from a positive endpoint-separation
count, cap two, and support-connectedness.  It does not use a component
envelope, a semantic equality, or frozen-path coverage.

Static off-tree source; not locally elaborated.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
namespace CapTwoRTCRoute

open SemigroupBasis.Examples

inductive EndpointSide where
  | first
  | event
deriving DecidableEq, Repr

structure EndpointTag where
  letter : Nat
  side : EndpointSide
deriving DecidableEq, Repr

namespace EndpointTag

def first (letter : Nat) : EndpointTag :=
  ⟨letter, EndpointSide.first⟩

def event (letter : Nat) : EndpointTag :=
  ⟨letter, EndpointSide.event⟩

end EndpointTag

/-- Suffix-local occurrence roles.  Under cap two these are exactly first
and final/singleton endpoint events. -/
def tagEndpoints : List Nat → List EndpointTag
  | [] => []
  | letter :: suffix =>
      (if letter ∈ suffix then
        EndpointTag.first letter
      else
        EndpointTag.event letter) :: tagEndpoints suffix

@[simp]
theorem tagEndpoints_map_letter :
    ∀ letters : List Nat,
      (tagEndpoints letters).map EndpointTag.letter = letters
  | [] => rfl
  | letter :: suffix => by
      rw [tagEndpoints, List.map_cons,
        tagEndpoints_map_letter suffix]
      by_cases later : letter ∈ suffix <;>
        simp [later, EndpointTag.first, EndpointTag.event]

@[simp]
theorem tagEndpoints_length (letters : List Nat) :
    (tagEndpoints letters).length = letters.length := by
  simpa only [List.length_map] using
    congrArg List.length (tagEndpoints_map_letter letters)

theorem tagEndpoints_drop (letters : List Nat) :
    ∀ offset : Nat,
      (tagEndpoints letters).drop offset =
        tagEndpoints (letters.drop offset)
  | 0 => rfl
  | offset + 1 => by
      cases letters with
      | nil => rfl
      | cons letter suffix =>
          simpa [tagEndpoints] using tagEndpoints_drop suffix offset

def firstEndpointCount : List EndpointTag → Nat
  | [] => 0
  | ⟨_, .first⟩ :: rest => (firstEndpointCount rest).succ
  | ⟨_, .event⟩ :: rest => firstEndpointCount rest

def eventEndpointCount : List EndpointTag → Nat
  | [] => 0
  | ⟨_, .first⟩ :: rest => eventEndpointCount rest
  | ⟨_, .event⟩ :: rest => (eventEndpointCount rest).succ

/-- Number of chronological `E`-before-`F` pairs. -/
def endpointSeparationTags : List EndpointTag → Nat
  | [] => 0
  | ⟨_, .first⟩ :: rest => endpointSeparationTags rest
  | ⟨_, .event⟩ :: rest =>
      firstEndpointCount rest + endpointSeparationTags rest

def endpointSeparation (letters : List Nat) : Nat :=
  endpointSeparationTags (tagEndpoints letters)

@[simp]
theorem firstEndpointCount_append
    (left right : List EndpointTag) :
    firstEndpointCount (left ++ right) =
      firstEndpointCount left + firstEndpointCount right := by
  induction left with
  | nil => simp [firstEndpointCount]
  | cons tag rest inductionHypothesis =>
      cases tag with
      | mk letter side =>
          cases side <;>
            simp [firstEndpointCount, inductionHypothesis,
              Nat.succ_add]

@[simp]
theorem eventEndpointCount_append
    (left right : List EndpointTag) :
    eventEndpointCount (left ++ right) =
      eventEndpointCount left + eventEndpointCount right := by
  induction left with
  | nil => simp [eventEndpointCount]
  | cons tag rest inductionHypothesis =>
      cases tag with
      | mk letter side =>
          cases side <;>
            simp [eventEndpointCount, inductionHypothesis,
              Nat.succ_add]

/-- Exact cross-term formula for separation inversions. -/
theorem endpointSeparationTags_append
    (left right : List EndpointTag) :
    endpointSeparationTags (left ++ right) =
      endpointSeparationTags left + endpointSeparationTags right +
        eventEndpointCount left * firstEndpointCount right := by
  induction left with
  | nil => simp [endpointSeparationTags, eventEndpointCount]
  | cons tag rest inductionHypothesis =>
      cases tag with
      | mk letter side =>
          cases side <;>
            simp [endpointSeparationTags, firstEndpointCount,
              eventEndpointCount, inductionHypothesis,
              Nat.succ_mul] <;> omega

/-- Every positive separation count exposes an adjacent `E,F` boundary. -/
theorem exists_adjacent_event_first :
    ∀ tags : List EndpointTag,
      0 < endpointSeparationTags tags →
        ∃ stem x y suffix,
          tags = stem ++ EndpointTag.event x ::
            EndpointTag.first y :: suffix := by
  intro tags
  induction tags with
  | nil =>
      intro positive
      simp [endpointSeparationTags] at positive
  | cons tag rest inductionHypothesis =>
      intro positive
      cases tag with
      | mk selected side =>
          cases side with
          | first =>
              have tailPositive : 0 < endpointSeparationTags rest := by
                simpa [endpointSeparationTags, EndpointTag.first] using
                  positive
              obtain ⟨stem, x, y, suffix, shape⟩ :=
                inductionHypothesis tailPositive
              refine ⟨EndpointTag.first selected :: stem,
                x, y, suffix, ?_⟩
              change
                EndpointTag.first selected :: rest =
                  EndpointTag.first selected ::
                    (stem ++ EndpointTag.event x ::
                      EndpointTag.first y :: suffix)
              exact congrArg
                (fun remaining : List EndpointTag =>
                  EndpointTag.first selected :: remaining)
                shape
          | event =>
              cases rest with
              | nil =>
                  simp [endpointSeparationTags, firstEndpointCount,
                    EndpointTag.event] at positive
              | cons next tail =>
                  cases next with
                  | mk letter nextSide =>
                      cases nextSide with
                      | first =>
                          exact ⟨[], selected, letter, tail, rfl⟩
                      | event =>
                          have tailPositive :
                              0 < endpointSeparationTags
                                (EndpointTag.event letter :: tail) := by
                            simp only [endpointSeparationTags,
                              firstEndpointCount, EndpointTag.event] at positive ⊢
                            omega
                          obtain ⟨stem, x, y, suffix, shape⟩ :=
                            inductionHypothesis tailPositive
                          refine ⟨EndpointTag.event selected :: stem,
                            x, y, suffix, ?_⟩
                          change
                            EndpointTag.event selected ::
                                (EndpointTag.event letter :: tail) =
                              EndpointTag.event selected ::
                                (stem ++ EndpointTag.event x ::
                                  EndpointTag.first y :: suffix)
                          exact congrArg
                            (fun remaining : List EndpointTag =>
                              EndpointTag.event selected :: remaining)
                            shape

/-- Erasing one adjacent `E(x),F(y)` tag pair gives its exact raw cut and
the suffix facts encoded by those two roles. -/
private theorem adjacent_event_first_roles
    {letters : List Nat} {stem suffix : List EndpointTag} {x y : Nat}
    (shape :
      tagEndpoints letters =
        stem ++ EndpointTag.event x :: EndpointTag.first y :: suffix) :
    let before := stem.map EndpointTag.letter
    let after := suffix.map EndpointTag.letter
    letters = before ++ x :: y :: after ∧
      x ∉ y :: after ∧ y ∈ after := by
  let before := stem.map EndpointTag.letter
  let after := suffix.map EndpointTag.letter
  have rawShape : letters = before ++ x :: y :: after := by
    have erased := congrArg (List.map EndpointTag.letter) shape
    simpa [before, after, EndpointTag.first, EndpointTag.event,
      List.map_append] using erased
  have dropped := congrArg (List.drop stem.length) shape
  have tailShape :
      tagEndpoints (x :: y :: after) =
        EndpointTag.event x :: EndpointTag.first y :: suffix := by
    rw [tagEndpoints_drop, rawShape] at dropped
    simpa [before] using dropped
  have xNotLater : x ∉ y :: after := by
    intro later
    have heads := congrArg List.head? tailShape
    simp [tagEndpoints, later, EndpointTag.first,
      EndpointTag.event] at heads
  have yLater : y ∈ after := by
    by_cases later : y ∈ after
    · exact later
    · have seconds :=
        congrArg (fun tags : List EndpointTag => (tags.drop 1).head?)
          tailShape
      simp [tagEndpoints, xNotLater, later, EndpointTag.first,
        EndpointTag.event] at seconds
  change
    letters = before ++ x :: y :: after ∧
      x ∉ y :: after ∧ y ∈ after
  exact ⟨rawShape, xNotLater, yLater⟩

/-- Two distinct members of a list occur in exactly one of the two linear
orders needed by the crossing/nested split. -/
theorem two_distinct_members_order
    (x y : Nat) (different : x ≠ y) :
    ∀ {entries : List Nat}, x ∈ entries → y ∈ entries →
      (∃ before middle after,
        entries = before ++ x :: middle ++ y :: after) ∨
      (∃ before middle after,
        entries = before ++ y :: middle ++ x :: after)
  | [], xMember, _ => by simp at xMember
  | head :: tail, xMember, yMember => by
      by_cases headX : head = x
      · subst head
        have yTail : y ∈ tail := by
          rcases List.mem_cons.mp yMember with equal | member
          · exact False.elim (different equal.symm)
          · exact member
        obtain ⟨middle, after, shape⟩ :=
          List.mem_iff_append.mp yTail
        exact Or.inl ⟨[], middle, after, by simp [shape]⟩
      · by_cases headY : head = y
        · subst head
          have xTail : x ∈ tail := by
            rcases List.mem_cons.mp xMember with equal | member
            · exact False.elim (headX equal.symm)
            · exact member
          obtain ⟨middle, after, shape⟩ :=
            List.mem_iff_append.mp xTail
          exact Or.inr ⟨[], middle, after, by simp [shape]⟩
        · have xTail : x ∈ tail :=
            (List.mem_cons.mp xMember).resolve_left (Ne.symm headX)
          have yTail : y ∈ tail :=
            (List.mem_cons.mp yMember).resolve_left (Ne.symm headY)
          rcases two_distinct_members_order x y different xTail yTail with
            ⟨before, middle, after, shape⟩ |
            ⟨before, middle, after, shape⟩
          · exact Or.inl
              ⟨head :: before, middle, after,
                by simp [shape, List.append_assoc]⟩
          · exact Or.inr
              ⟨head :: before, middle, after,
                by simp [shape, List.append_assoc]⟩

/-- The two literal E/F cases, retaining the positive block crossed by the
first endpoint. -/
inductive EndpointEFCase (letters : List Nat) : Prop where
  | crossing
      (front suffix : List Nat)
      (crossing endpoint : Nat)
      (before middle after : List Nat)
      (shape :
        letters = front ++ [crossing] ++ before ++ [endpoint] ++
          middle ++ [crossing] ++ after ++ [endpoint] ++ suffix)
      (beforeNonempty : before ≠ [])
      (eventWitness :
        ∃ beforeFront terminal,
          before = beforeFront ++ [terminal] ∧
          terminal ∉ endpoint ::
            (middle ++ [crossing] ++ after ++ [endpoint] ++ suffix)) :
      EndpointEFCase letters
  | nested
      (front suffix : List Nat)
      (crossing endpoint : Nat)
      (before middle after : List Nat)
      (shape :
        letters = front ++ [crossing] ++ before ++ [endpoint] ++
          middle ++ [endpoint] ++ after ++ [crossing] ++ suffix)
      (beforeNonempty : before ≠ [])
      (eventWitness :
        ∃ beforeFront terminal,
          before = beforeFront ++ [terminal] ∧
          terminal ∉ endpoint ::
            (middle ++ [endpoint] ++ after ++ [crossing] ++ suffix)) :
      EndpointEFCase letters

def EndpointEFCase.toDisorderCase
    {letters : List Nat} : EndpointEFCase letters → EndpointDisorderCase letters
  | .crossing front suffix crossingLetter endpoint before middle after
      shape _ _ =>
      .efCrossing front suffix crossingLetter endpoint before middle after shape
  | .nested front suffix crossingLetter endpoint before middle after
      shape _ _ =>
      .efNested front suffix crossingLetter endpoint before middle after shape

/-- Positive separation, cap two, and support-connectedness construct one of
the two arbitrary-gap E/F dispatcher cases. -/
theorem endpointEFCase_of_positiveSeparation
    {letters : List Nat}
    (twoLimited : ∀ tested, letters.count tested ≤ 2)
    (connected : ConnectedComponentSupportConnected letters)
    (positive : 0 < endpointSeparation letters) :
    EndpointEFCase letters := by
  rcases exists_adjacent_event_first (tagEndpoints letters) positive with
    ⟨tagStem, x, y, tagSuffix, tagShape⟩
  let rawBefore := tagStem.map EndpointTag.letter
  let rawAfter := tagSuffix.map EndpointTag.letter
  have roles := adjacent_event_first_roles tagShape
  change
    letters = rawBefore ++ x :: y :: rawAfter ∧
      x ∉ y :: rawAfter ∧ y ∈ rawAfter at roles
  rcases roles with ⟨rawShape, xNotLater, yLater⟩
  have different : x ≠ y := by
    intro equal
    subst y
    exact xNotLater (List.Mem.head rawAfter)
  have yNotBefore : y ∉ rawBefore := by
    intro yBefore
    have beforePositive : 0 < rawBefore.count y :=
      List.count_pos_iff.mpr yBefore
    have afterPositive : 0 < rawAfter.count y :=
      List.count_pos_iff.mpr yLater
    have bound := twoLimited y
    rw [rawShape, List.count_append] at bound
    simp [different, Ne.symm different] at bound
    omega
  have yNotLeft : y ∉ rawBefore ++ [x] := by
    simp [yNotBefore, Ne.symm different]
  have cutShape :
      letters = (rawBefore ++ [x]) ++ (y :: rawAfter) := by
    rw [rawShape]
    simp [List.append_assoc]
  obtain ⟨crossing, crossingLeft, crossingRight⟩ :=
    connected (rawBefore ++ [x]) (y :: rawAfter) cutShape
      (by simp) (by simp)
  have crossingNeX : crossing ≠ x := by
    intro equal
    subst crossing
    exact xNotLater crossingRight
  have crossingNeY : crossing ≠ y := by
    intro equal
    subst crossing
    exact yNotLeft crossingLeft
  have crossingBefore : crossing ∈ rawBefore := by
    rcases List.mem_append.mp crossingLeft with member | singleton
    · exact member
    · exact False.elim <| crossingNeX (by simpa using singleton)
  have crossingAfter : crossing ∈ rawAfter := by
    rcases List.mem_cons.mp crossingRight with equal | member
    · exact False.elim <| crossingNeY equal
    · exact member
  obtain ⟨front, beforeTail, rawBeforeShape⟩ :=
    List.mem_iff_append.mp crossingBefore
  rcases two_distinct_members_order crossing y crossingNeY
      crossingAfter yLater with
    ⟨middle, after, suffix, rawAfterShape⟩ |
    ⟨middle, after, suffix, rawAfterShape⟩
  · refine .crossing front suffix crossing y
      (beforeTail ++ [x]) middle after ?_ (by simp) ?_
    rw [rawShape, rawBeforeShape, rawAfterShape]
    simp [List.append_assoc]
    exact ⟨beforeTail, x, rfl, by
      simpa [rawAfterShape, List.append_assoc] using xNotLater⟩
  · refine .nested front suffix crossing y
      (beforeTail ++ [x]) middle after ?_ (by simp) ?_
    rw [rawShape, rawBeforeShape, rawAfterShape]
    simp [List.append_assoc]
    exact ⟨beforeTail, x, rfl, by
      simpa [rawAfterShape, List.append_assoc] using xNotLater⟩

end CapTwoRTCRoute
end SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
