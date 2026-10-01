import SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.CapTwoEndpointZeroPivot

/-!
# Uniqueness of the Gd cap-two zero endpoint

The three endpoint coordinates expose a literal first/event split.  Capped
multiplicity and two route-local evaluations of the public catalogue table
then determine that split uniquely.  The evaluator and its reflectors are
proved directly for `SemanticBlockSignature.table`; no generated-table or
Edmunds module is imported.  Semantic validity is used only in the forward
direction and is never turned into a derivation.

Static off-tree source; not locally elaborated.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
namespace CapTwoRTCRoute

open SemigroupBasis
open SemigroupBasis.CoRoots
open SemigroupBasis.CoRoots.Order6L1RRank1
open SemigroupBasis.Examples

/-! ## Occurrence counts carried by endpoint tags -/

@[simp]
theorem tagEndpoints_count_event (selected : Nat) :
    forall letters : List Nat,
      (tagEndpoints letters).count (EndpointTag.event selected) =
        if selected ∈ letters then 1 else 0
  | [] => by simp [tagEndpoints]
  | letter :: rest => by
      have inductionHypothesis := tagEndpoints_count_event selected rest
      by_cases equal : letter = selected
      · subst letter
        by_cases later : selected ∈ rest <;>
          simpa [tagEndpoints, later, EndpointTag.first,
            EndpointTag.event] using inductionHypothesis
      · have reverse : selected ≠ letter := Ne.symm equal
        by_cases later : letter ∈ rest <;>
          simpa [tagEndpoints, later, equal, reverse,
            EndpointTag.first, EndpointTag.event] using inductionHypothesis

@[simp]
theorem tagEndpoints_count_sides (selected : Nat) :
    forall letters : List Nat,
      (tagEndpoints letters).count (EndpointTag.first selected) +
          (tagEndpoints letters).count (EndpointTag.event selected) =
        letters.count selected
  | [] => by simp [tagEndpoints]
  | letter :: rest => by
      have inductionHypothesis := tagEndpoints_count_sides selected rest
      by_cases equal : letter = selected
      · subst letter
        by_cases later : selected ∈ rest <;>
          simp [tagEndpoints, later, EndpointTag.first,
            EndpointTag.event] at inductionHypothesis ⊢ <;>
          omega
      · have reverse : selected ≠ letter := Ne.symm equal
        by_cases later : letter ∈ rest <;>
          simp [tagEndpoints, later, equal, reverse,
            EndpointTag.first, EndpointTag.event]
              at inductionHypothesis ⊢ <;>
          omega

@[simp]
theorem tagEndpoints_count_first (selected : Nat)
    (letters : List Nat) :
    (tagEndpoints letters).count (EndpointTag.first selected) =
      (letters.count selected).pred := by
  have total := tagEndpoints_count_sides selected letters
  have event := tagEndpoints_count_event selected letters
  by_cases member : selected ∈ letters
  · have positive : 0 < letters.count selected :=
      List.count_pos_iff.mpr member
    have counted :
        (tagEndpoints letters).count (EndpointTag.first selected) + 1 =
          letters.count selected := by
      simpa only [tagEndpoints_count_event, if_pos member] using total
    cases count : letters.count selected with
    | zero => simp [count] at positive
    | succ count =>
        simp [count] at counted ⊢
        omega
  · have zero : letters.count selected = 0 :=
      List.count_eq_zero.mpr member
    rw [zero]
    simp [member] at event ⊢
    omega

private theorem nodup_of_count_le_one
    {letters : List Nat}
    (bounded : forall letter, letters.count letter ≤ 1) :
    letters.Nodup := by
  induction letters with
  | nil => simp
  | cons first rest inductionHypothesis =>
      simp only [List.nodup_cons]
      constructor
      · intro member
        have positive : 1 ≤ rest.count first :=
          List.count_pos_iff.mpr member
        have bound := bounded first
        simp only [List.count_cons_self] at bound
        omega
      · apply inductionHypothesis
        intro letter
        have bound := bounded letter
        by_cases equal : first = letter
        · subst letter
          simp only [List.count_cons_self] at bound
          omega
        · rw [List.count_cons_of_ne equal] at bound
          exact bound

private theorem count_firstProjection (selected : Nat) :
    forall tags : List EndpointTag,
      (firstProjection tags).count selected =
        tags.count (EndpointTag.first selected)
  | [] => rfl
  | ⟨letter, side⟩ :: rest => by
      cases side <;>
        by_cases equal : letter = selected <;>
        simp [firstProjection, EndpointTag.first, equal,
          count_firstProjection selected rest]

private theorem count_eventProjection (selected : Nat) :
    forall tags : List EndpointTag,
      (eventProjection tags).count selected =
        tags.count (EndpointTag.event selected)
  | [] => rfl
  | ⟨letter, side⟩ :: rest => by
      cases side <;>
        by_cases equal : letter = selected <;>
        simp [eventProjection, EndpointTag.event, equal,
          count_eventProjection selected rest]

/-! ## A proof-oriented zero split -/

structure EndpointZeroSplit
    (whole firsts events : List Nat) : Prop where
  shape : whole = firsts ++ events
  limited : forall selected, whole.count selected ≤ 2
  firstNodup : firsts.Nodup
  eventNodup : events.Nodup
  firstOrdered : firsts.Pairwise (· ≤ ·)
  firstMem : forall selected,
    selected ∈ firsts ↔ whole.count selected = 2
  eventMem : forall selected,
    selected ∈ events ↔ 0 < whole.count selected
  eventNormal : eventGapInversionsList firsts events = 0

theorem endpointZeroSplit_of_measure_eq_zero
    {letters : List Nat}
    (limited : forall selected, letters.count selected ≤ 2)
    (zero : endpointMeasure letters = ⟨0, 0, 0⟩) :
    exists firsts events, EndpointZeroSplit letters firsts events := by
  have zeroForm := endpointZeroForm_of_measure_eq_zero zero
  obtain ⟨firsts, events, tagShape⟩ := zeroForm.separated
  have rawShape : letters = firsts ++ events := by
    have erased := congrArg (List.map EndpointTag.letter) tagShape
    simpa [EndpointTag.first, EndpointTag.event,
      Function.comp_def, List.map_append] using erased
  have firstProjectionEq :
      firstProjection (tagEndpoints letters) = firsts := by
    have projected := congrArg firstProjection tagShape
    simpa using projected
  have eventProjectionEq :
      eventProjection (tagEndpoints letters) = events := by
    have projected := congrArg eventProjection tagShape
    simpa using projected
  have firstCount : forall selected,
      firsts.count selected = (letters.count selected).pred := by
    intro selected
    calc
      firsts.count selected =
          (firstProjection (tagEndpoints letters)).count selected := by
            rw [firstProjectionEq]
      _ = (tagEndpoints letters).count (EndpointTag.first selected) :=
        count_firstProjection selected (tagEndpoints letters)
      _ = (letters.count selected).pred :=
        tagEndpoints_count_first selected letters
  have eventCount : forall selected,
      events.count selected =
        if selected ∈ letters then 1 else 0 := by
    intro selected
    calc
      events.count selected =
          (eventProjection (tagEndpoints letters)).count selected := by
            rw [eventProjectionEq]
      _ = (tagEndpoints letters).count (EndpointTag.event selected) :=
        count_eventProjection selected (tagEndpoints letters)
      _ = (if selected ∈ letters then 1 else 0) :=
        tagEndpoints_count_event selected letters
  have firstMem : forall selected,
      selected ∈ firsts ↔ letters.count selected = 2 := by
    intro selected
    constructor
    · intro member
      have positive : 0 < firsts.count selected :=
        List.count_pos_iff.mpr member
      rw [firstCount selected] at positive
      have bound := limited selected
      cases count : letters.count selected with
      | zero => simp [count] at positive
      | succ count =>
          simp [count] at positive bound ⊢
          omega
    · intro countTwo
      apply List.count_pos_iff.mp
      rw [firstCount selected, countTwo]
      decide
  have eventMem : forall selected,
      selected ∈ events ↔ 0 < letters.count selected := by
    intro selected
    constructor
    · intro member
      have positive : 0 < events.count selected :=
        List.count_pos_iff.mpr member
      rw [eventCount selected] at positive
      have inLetters : selected ∈ letters := by
        by_cases member : selected ∈ letters
        · exact member
        · simp [member] at positive
      exact List.count_pos_iff.mpr inLetters
    · intro positive
      apply List.count_pos_iff.mp
      rw [eventCount selected]
      have member : selected ∈ letters :=
        List.count_pos_iff.mp positive
      simp [member]
  have firstNodup : firsts.Nodup := by
    apply nodup_of_count_le_one
    intro selected
    rw [firstCount selected]
    have bound := limited selected
    cases count : letters.count selected with
    | zero => simp [count]
    | succ count =>
        simp [count] at bound ⊢
        omega
  have eventNodup : events.Nodup := by
    apply nodup_of_count_le_one
    intro selected
    rw [eventCount selected]
    split <;> omega
  have firstOrdered : firsts.Pairwise (· ≤ ·) := by
    have ordered := zeroForm.firstOrdered
    rw [firstProjectionEq] at ordered
    exact ordered
  have eventNormal :
      eventGapInversionsList firsts events = 0 := by
    have normal := zeroForm.eventNormal
    unfold eventGapInversions at normal
    rw [firstProjectionEq, eventProjectionEq] at normal
    exact normal
  exact ⟨firsts, events,
    ⟨rawShape, limited, firstNodup, eventNodup,
      firstOrdered, firstMem, eventMem, eventNormal⟩⟩

/-! ## Route-local chronological order -/

namespace EndpointChronology

def Before : List Nat → Nat → Nat → Prop
  | [], _, _ => False
  | head :: tail, earlier, later =>
      (earlier = head ∧ later ∈ tail) ∨
        Before tail earlier later

theorem left_mem
    {events : List Nat} {earlier later : Nat}
    (before : Before events earlier later) :
    earlier ∈ events := by
  induction events with
  | nil => simpa [Before] using before
  | cons head tail inductionHypothesis =>
      simp only [Before] at before
      rcases before with ⟨rfl, _⟩ | tailBefore
      · exact List.Mem.head tail
      · exact List.Mem.tail head (inductionHypothesis tailBefore)

theorem right_mem
    {events : List Nat} {earlier later : Nat}
    (before : Before events earlier later) :
    later ∈ events := by
  induction events with
  | nil => simpa [Before] using before
  | cons head tail inductionHypothesis =>
      simp only [Before] at before
      rcases before with ⟨_, laterMember⟩ | tailBefore
      · exact List.Mem.tail head laterMember
      · exact List.Mem.tail head (inductionHypothesis tailBefore)

theorem asymm
    {events : List Nat} (nodup : events.Nodup)
    {earlier later : Nat}
    (forward : Before events earlier later) :
    ¬ Before events later earlier := by
  induction events with
  | nil => simpa [Before] using forward
  | cons head tail inductionHypothesis =>
      have headAbsent := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      simp only [Before] at forward ⊢
      intro reverse
      rcases forward with ⟨rfl, laterMember⟩ | tailForward
      · rcases reverse with ⟨_, headMember⟩ | tailReverse
        · exact headAbsent headMember
        · exact headAbsent (right_mem tailReverse)
      · rcases reverse with ⟨laterEqual, _⟩ | tailReverse
        · subst later
          exact headAbsent (right_mem tailForward)
        · exact inductionHypothesis tailNodup tailForward tailReverse

theorem before_append_cross
    (front back : List Nat) {earlier later : Nat}
    (earlierMember : earlier ∈ front)
    (laterMember : later ∈ back) :
    Before (front ++ back) earlier later := by
  induction front with
  | nil => simp at earlierMember
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp earlierMember with equal | member
      · subst earlier
        exact Or.inl ⟨rfl, List.mem_append_right tail laterMember⟩
      · exact Or.inr
          (inductionHypothesis member)

theorem mem_front_of_before_split
    (front rest : List Nat) (selected earlier : Nat)
    (nodup : (front ++ selected :: rest).Nodup)
    (before : Before (front ++ selected :: rest) earlier selected) :
    earlier ∈ front := by
  induction front with
  | nil =>
      have selectedAbsent := (List.nodup_cons.mp nodup).1
      simp only [List.nil_append, Before] at before
      rcases before with ⟨rfl, selectedMember⟩ | tailBefore
      · exact False.elim (selectedAbsent selectedMember)
      · exact False.elim
          (selectedAbsent (right_mem tailBefore))
  | cons head tail inductionHypothesis =>
      have tailNodup := (List.nodup_cons.mp nodup).2
      simp only [List.cons_append, Before] at before
      rcases before with ⟨equal, _⟩ | tailBefore
      · exact List.mem_cons.mpr (Or.inl equal)
      · exact List.mem_cons.mpr
          (Or.inr (inductionHypothesis tailNodup tailBefore))

theorem before_append_iff_of_absent
    (front rest : List Nat) {earlier later : Nat}
    (earlierAbsent : earlier ∉ front)
    (laterAbsent : later ∉ front) :
    Before (front ++ rest) earlier later ↔
      Before rest earlier later := by
  induction front with
  | nil => simp
  | cons head tail inductionHypothesis =>
      have earlierNe : earlier ≠ head := by
        intro equal
        subst earlier
        exact earlierAbsent (List.Mem.head tail)
      have laterNe : later ≠ head := by
        intro equal
        subst later
        exact laterAbsent (List.Mem.head tail)
      have earlierTail : earlier ∉ tail := by
        intro member
        exact earlierAbsent (List.Mem.tail head member)
      have laterTail : later ∉ tail := by
        intro member
        exact laterAbsent (List.Mem.tail head member)
      simp only [List.cons_append, Before]
      rw [inductionHypothesis earlierTail laterTail]
      simp [earlierNe]

end EndpointChronology

/-! ## Route-local evaluator for the public catalogue table -/

namespace RouteBlockProbe

/-- Route-local absence/simple/multiple code; this avoids importing the
broader `S5_107Syntax` surface merely for a one-line definition. -/
def cappedMultiplicity (word : Word Nat) (letter : Nat) : Nat :=
  Nat.min 2 (word.toList.count letter)

private def blockListEval
    (valuation : Nat → Fin 4) (letters : List Nat) : Fin 4 :=
  letters.foldl
    (fun value letter =>
      SemanticBlockSignature.table.mul value (valuation letter))
    (3 : Fin 4)

private theorem table_left_identity (value : Fin 4) :
    SemanticBlockSignature.table.mul (3 : Fin 4) value = value := by
  apply Fin.ext
  revert value
  decide

private theorem table_right_identity (value : Fin 4) :
    SemanticBlockSignature.table.mul value (3 : Fin 4) = value := by
  apply Fin.ext
  revert value
  decide

private theorem block_eval_eq_listEval
    (valuation : Nat → Fin 4) (word : Word Nat) :
    SemanticBlockSignature.table.semigroup.eval valuation word =
      blockListEval valuation word.toList := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun value letter =>
              SemanticBlockSignature.table.mul value
                (valuation letter))
            (valuation head) =
          tail.foldl
            (fun value letter =>
              SemanticBlockSignature.table.mul value
                (valuation letter))
            (SemanticBlockSignature.table.mul
              (3 : Fin 4) (valuation head))
      rw [table_left_identity]

private def multiplicityValuation
    (selected : Nat) : Nat → Fin 4 :=
  fun letter => if letter = selected then 1 else 3

private def multiplicityCode (count : Nat) : Fin 4 :=
  if count = 0 then 3 else if count = 1 then 1 else 0

private theorem multiplicityCode_selected (count : Nat) :
    SemanticBlockSignature.table.mul
        (multiplicityCode count) (1 : Fin 4) =
      multiplicityCode (count + 1) := by
  by_cases zero : count = 0
  · subst count
    decide
  · by_cases one : count = 1
    · subst count
      decide
    · have successorZero : count + 1 ≠ 0 := by omega
      have successorOne : count + 1 ≠ 1 := by omega
      simp [multiplicityCode, zero, one, successorZero, successorOne] <;>
        decide

private theorem multiplicityFold
    (selected : Nat) :
    forall (letters : List Nat) (initialCount : Nat),
      letters.foldl
          (fun value letter =>
            SemanticBlockSignature.table.mul value
              (multiplicityValuation selected letter))
          (multiplicityCode initialCount) =
        multiplicityCode
          (initialCount + letters.count selected)
  | [], _ => by simp
  | letter :: rest, initialCount => by
      simp only [List.foldl_cons]
      by_cases equal : letter = selected
      · subst letter
        rw [show multiplicityValuation selected selected =
            (1 : Fin 4) by simp [multiplicityValuation]]
        rw [multiplicityCode_selected]
        rw [multiplicityFold selected rest (initialCount + 1)]
        congr 1
        simp
        omega
      · rw [show multiplicityValuation selected letter =
            (3 : Fin 4) by simp [multiplicityValuation, equal]]
        rw [table_right_identity]
        rw [multiplicityFold selected rest initialCount]
        simp [equal]

private theorem block_eval_multiplicity
    (word : Word Nat) (selected : Nat) :
    SemanticBlockSignature.table.semigroup.eval
        (multiplicityValuation selected) word =
      multiplicityCode (word.toList.count selected) := by
  rw [block_eval_eq_listEval]
  unfold blockListEval
  simpa [multiplicityCode] using
    multiplicityFold selected word.toList 0

private theorem multiplicityCode_reflects_cap
    {leftCount rightCount : Nat}
    (equal :
      multiplicityCode leftCount =
        multiplicityCode rightCount) :
    Nat.min 2 leftCount = Nat.min 2 rightCount := by
  by_cases leftZero : leftCount = 0
  · subst leftCount
    by_cases rightZero : rightCount = 0
    · subst rightCount
      rfl
    · by_cases rightOne : rightCount = 1
      · subst rightCount
        simp [multiplicityCode] at equal
      · simp [multiplicityCode, rightZero, rightOne] at equal
  · by_cases leftOne : leftCount = 1
    · subst leftCount
      by_cases rightZero : rightCount = 0
      · subst rightCount
        simp [multiplicityCode] at equal
      · by_cases rightOne : rightCount = 1
        · subst rightCount
          rfl
        · simp [multiplicityCode, rightZero, rightOne] at equal
    · by_cases rightZero : rightCount = 0
      · subst rightCount
        simp [multiplicityCode, leftZero, leftOne] at equal
      · by_cases rightOne : rightCount = 1
        · subst rightCount
          simp [multiplicityCode, leftZero, leftOne] at equal
        · simp only [Nat.min_def]
          split <;> split <;> omega

theorem valid_cappedMultiplicity
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemanticBlockSignature.table.semigroup)
    (letter : Nat) :
    RouteBlockProbe.cappedMultiplicity identity.lhs letter =
      RouteBlockProbe.cappedMultiplicity identity.rhs letter := by
  have evaluated := valid (multiplicityValuation letter)
  rw [block_eval_multiplicity, block_eval_multiplicity] at evaluated
  exact multiplicityCode_reflects_cap evaluated

inductive OrderSymbol where
  | other
  | x
  | y
deriving DecidableEq

inductive OrderGapState where
  | empty
  | onlyYOne
  | onlyYMany
  | onlyXOne
  | onlyXMany
  | simpleXY
  | simpleYX
  | xOneYManyXFirst
  | xOneYManyYFirst
  | xManyYOneBefore
  | xManyYOneAfterXFirst
  | xManyYOneAfterYFirst
  | xManyYManyBefore
  | xManyYManyAfterXFirst
  | xManyYManyAfterYFirst
deriving DecidableEq

def orderStep : OrderGapState → OrderSymbol → OrderGapState
  | state, .other => state
  | .empty, .x => .onlyXOne
  | .onlyYOne, .x => .simpleYX
  | .onlyYMany, .x => .xOneYManyYFirst
  | .onlyXOne, .x => .onlyXMany
  | .onlyXMany, .x => .onlyXMany
  | .simpleXY, .x => .xManyYOneAfterXFirst
  | .simpleYX, .x => .xManyYOneAfterYFirst
  | .xOneYManyXFirst, .x => .xManyYManyAfterXFirst
  | .xOneYManyYFirst, .x => .xManyYManyAfterYFirst
  | .xManyYOneBefore, .x => .xManyYOneAfterXFirst
  | .xManyYOneAfterXFirst, .x => .xManyYOneAfterXFirst
  | .xManyYOneAfterYFirst, .x => .xManyYOneAfterYFirst
  | .xManyYManyBefore, .x => .xManyYManyAfterXFirst
  | .xManyYManyAfterXFirst, .x => .xManyYManyAfterXFirst
  | .xManyYManyAfterYFirst, .x => .xManyYManyAfterYFirst
  | .empty, .y => .onlyYOne
  | .onlyYOne, .y => .onlyYMany
  | .onlyYMany, .y => .onlyYMany
  | .onlyXOne, .y => .simpleXY
  | .onlyXMany, .y => .xManyYOneBefore
  | .simpleXY, .y => .xOneYManyXFirst
  | .simpleYX, .y => .xOneYManyYFirst
  | .xOneYManyXFirst, .y => .xOneYManyXFirst
  | .xOneYManyYFirst, .y => .xOneYManyYFirst
  | .xManyYOneBefore, .y => .xManyYManyBefore
  | .xManyYOneAfterXFirst, .y => .xManyYManyAfterXFirst
  | .xManyYOneAfterYFirst, .y => .xManyYManyAfterYFirst
  | .xManyYManyBefore, .y => .xManyYManyBefore
  | .xManyYManyAfterXFirst, .y => .xManyYManyAfterXFirst
  | .xManyYManyAfterYFirst, .y => .xManyYManyAfterYFirst

private def orderStateValue : OrderGapState → Fin 4
  | .empty => 3
  | .onlyYOne => 1
  | .onlyYMany => 0
  | .onlyXOne => 2
  | .onlyXMany => 2
  | .simpleXY => 1
  | .simpleYX => 0
  | .xOneYManyXFirst => 0
  | .xOneYManyYFirst => 0
  | .xManyYOneBefore => 1
  | .xManyYOneAfterXFirst => 0
  | .xManyYOneAfterYFirst => 0
  | .xManyYManyBefore => 0
  | .xManyYManyAfterXFirst => 0
  | .xManyYManyAfterYFirst => 0

private def OrderGapState.xCount : OrderGapState → Nat
  | .empty | .onlyYOne | .onlyYMany => 0
  | .onlyXOne | .simpleXY | .simpleYX
  | .xOneYManyXFirst | .xOneYManyYFirst => 1
  | .onlyXMany | .xManyYOneBefore
  | .xManyYOneAfterXFirst | .xManyYOneAfterYFirst
  | .xManyYManyBefore | .xManyYManyAfterXFirst
  | .xManyYManyAfterYFirst => 2

private def OrderGapState.yCount : OrderGapState → Nat
  | .empty | .onlyXOne | .onlyXMany => 0
  | .onlyYOne | .simpleXY | .simpleYX
  | .xManyYOneBefore | .xManyYOneAfterXFirst
  | .xManyYOneAfterYFirst => 1
  | .onlyYMany | .xOneYManyXFirst | .xOneYManyYFirst
  | .xManyYManyBefore | .xManyYManyAfterXFirst
  | .xManyYManyAfterYFirst => 2

def orderSymbol (x y letter : Nat) : OrderSymbol :=
  if letter = x then .x else if letter = y then .y else .other

private def orderSymbolValue : OrderSymbol → Fin 4
  | .other => 3
  | .x => 2
  | .y => 1

private def orderValuation (x y : Nat) : Nat → Fin 4 :=
  fun letter => orderSymbolValue (orderSymbol x y letter)

def orderGapScan (word : Word Nat) (x y : Nat) : OrderGapState :=
  word.toList.foldl
    (fun state letter => orderStep state (orderSymbol x y letter))
    .empty

private theorem orderStep_value
    (state : OrderGapState) (symbol : OrderSymbol) :
    SemanticBlockSignature.table.mul
        (orderStateValue state) (orderSymbolValue symbol) =
      orderStateValue (orderStep state symbol) := by
  cases state <;> cases symbol <;> decide

private theorem orderStep_xCount
    (state : OrderGapState) (symbol : OrderSymbol) :
    (orderStep state symbol).xCount =
      Nat.min 2
        (state.xCount + if symbol = .x then 1 else 0) := by
  cases state <;> cases symbol <;> decide

private theorem orderStep_yCount
    (state : OrderGapState) (symbol : OrderSymbol) :
    (orderStep state symbol).yCount =
      Nat.min 2
        (state.yCount + if symbol = .y then 1 else 0) := by
  cases state <;> cases symbol <;> decide

private theorem orderState_xCount_le_two (state : OrderGapState) :
    state.xCount ≤ 2 := by
  cases state <;> decide

private theorem orderState_yCount_le_two (state : OrderGapState) :
    state.yCount ≤ 2 := by
  cases state <;> decide

private theorem cap_two_cap_add (left right : Nat) :
    Nat.min 2 (Nat.min 2 left + right) =
      Nat.min 2 (left + right) := by
  by_cases capped : 2 ≤ left
  · have inner : Nat.min 2 left = 2 := Nat.min_eq_left capped
    calc
      Nat.min 2 (Nat.min 2 left + right) =
          Nat.min 2 (2 + right) := by rw [inner]
      _ = 2 := Nat.min_eq_left (by omega)
      _ = Nat.min 2 (left + right) :=
        (Nat.min_eq_left (by omega)).symm
  · have below : left ≤ 2 := by omega
    have inner : Nat.min 2 left = left := Nat.min_eq_right below
    rw [inner]

private theorem orderFold_value (x y : Nat) :
    forall (letters : List Nat) (initial : OrderGapState),
      letters.foldl
          (fun value letter =>
            SemanticBlockSignature.table.mul value
              (orderValuation x y letter))
          (orderStateValue initial) =
        orderStateValue
          (letters.foldl
            (fun state letter =>
              orderStep state (orderSymbol x y letter))
            initial)
  | [], _ => rfl
  | letter :: rest, initial => by
      simp only [List.foldl_cons, orderValuation]
      rw [orderStep_value]
      exact orderFold_value x y rest
        (orderStep initial (orderSymbol x y letter))

private theorem orderFold_xCount (x y : Nat) :
    forall (letters : List Nat) (initial : OrderGapState),
      (letters.foldl
          (fun state letter =>
            orderStep state (orderSymbol x y letter))
          initial).xCount =
        Nat.min 2 (initial.xCount + letters.count x)
  | [], initial => by
      simp only [List.foldl_nil, List.count_nil, Nat.add_zero]
      exact (Nat.min_eq_right
        (orderState_xCount_le_two initial)).symm
  | letter :: rest, initial => by
      simp only [List.foldl_cons]
      rw [orderFold_xCount x y rest]
      rw [orderStep_xCount]
      by_cases equal : letter = x
      · subst letter
        simp only [orderSymbol, if_pos, List.count_cons_self]
        rw [cap_two_cap_add]
        congr 1
        omega
      · have symbolNotX : orderSymbol x y letter ≠ .x := by
          unfold orderSymbol
          rw [if_neg equal]
          split <;> decide
        rw [if_neg symbolNotX]
        rw [cap_two_cap_add]
        simp [equal]

private theorem orderFold_yCount
    (x y : Nat) (different : x ≠ y) :
    forall (letters : List Nat) (initial : OrderGapState),
      (letters.foldl
          (fun state letter =>
            orderStep state (orderSymbol x y letter))
          initial).yCount =
        Nat.min 2 (initial.yCount + letters.count y)
  | [], initial => by
      simp only [List.foldl_nil, List.count_nil, Nat.add_zero]
      exact (Nat.min_eq_right
        (orderState_yCount_le_two initial)).symm
  | letter :: rest, initial => by
      simp only [List.foldl_cons]
      rw [orderFold_yCount x y different rest]
      rw [orderStep_yCount]
      by_cases isY : letter = y
      · subst letter
        have notX : y ≠ x := Ne.symm different
        simp only [orderSymbol, if_neg notX, if_pos,
          List.count_cons_self]
        rw [cap_two_cap_add]
        congr 1
        omega
      · have symbolNotY : orderSymbol x y letter ≠ .y := by
          unfold orderSymbol
          split <;> decide
        rw [if_neg symbolNotY]
        rw [cap_two_cap_add]
        simp [isY]

private theorem block_eval_order
    (word : Word Nat) (x y : Nat) :
    SemanticBlockSignature.table.semigroup.eval
        (orderValuation x y) word =
      orderStateValue (orderGapScan word x y) := by
  rw [block_eval_eq_listEval]
  unfold blockListEval orderGapScan
  simpa [orderStateValue] using
    orderFold_value x y word.toList .empty

private theorem orderGapScan_xCount
    (word : Word Nat) (x y : Nat) :
    (orderGapScan word x y).xCount =
      RouteBlockProbe.cappedMultiplicity word x := by
  unfold orderGapScan RouteBlockProbe.cappedMultiplicity
  simpa [OrderGapState.xCount] using
    orderFold_xCount x y word.toList .empty

private theorem orderGapScan_yCount
    (word : Word Nat) {x y : Nat} (different : x ≠ y) :
    (orderGapScan word x y).yCount =
      RouteBlockProbe.cappedMultiplicity word y := by
  unfold orderGapScan RouteBlockProbe.cappedMultiplicity
  simpa [OrderGapState.yCount] using
    orderFold_yCount x y different word.toList .empty

def SimplePrecedes (word : Word Nat) (x y : Nat) : Prop :=
  x ≠ y ∧ orderGapScan word x y = .simpleXY

def MultipleLastBeforeSimple
    (word : Word Nat) (x y : Nat) : Prop :=
  x ≠ y ∧ orderGapScan word x y = .xManyYOneBefore

private theorem state_eq_simpleXY_of_counts_value
    (state : OrderGapState)
    (xCount : state.xCount = 1)
    (yCount : state.yCount = 1)
    (value : orderStateValue state = 1) :
    state = .simpleXY := by
  cases state <;>
    simp_all [OrderGapState.xCount, OrderGapState.yCount,
      orderStateValue]

private theorem state_eq_xManyYOneBefore_of_counts_value
    (state : OrderGapState)
    (xCount : state.xCount = 2)
    (yCount : state.yCount = 1)
    (value : orderStateValue state = 1) :
    state = .xManyYOneBefore := by
  cases state <;>
    simp_all [OrderGapState.xCount, OrderGapState.yCount,
      orderStateValue]

private theorem simplePrecedes_forward
    {left right : Word Nat} {x y : Nat}
    (equalEval :
      orderStateValue (orderGapScan left x y) =
        orderStateValue (orderGapScan right x y))
    (capped : forall letter,
      RouteBlockProbe.cappedMultiplicity left letter =
        RouteBlockProbe.cappedMultiplicity right letter)
    (precedes : SimplePrecedes left x y) :
    SimplePrecedes right x y := by
  rcases precedes with ⟨different, leftState⟩
  refine ⟨different, ?_⟩
  have rightXCount : (orderGapScan right x y).xCount = 1 := by
    calc
      (orderGapScan right x y).xCount =
          RouteBlockProbe.cappedMultiplicity right x :=
        orderGapScan_xCount right x y
      _ = RouteBlockProbe.cappedMultiplicity left x := (capped x).symm
      _ = (orderGapScan left x y).xCount :=
        (orderGapScan_xCount left x y).symm
      _ = 1 := by rw [leftState]; rfl
  have rightYCount : (orderGapScan right x y).yCount = 1 := by
    calc
      (orderGapScan right x y).yCount =
          RouteBlockProbe.cappedMultiplicity right y :=
        orderGapScan_yCount right different
      _ = RouteBlockProbe.cappedMultiplicity left y := (capped y).symm
      _ = (orderGapScan left x y).yCount :=
        (orderGapScan_yCount left different).symm
      _ = 1 := by rw [leftState]; rfl
  have rightValue :
      orderStateValue (orderGapScan right x y) = 1 := by
    rw [← equalEval, leftState]
    rfl
  exact state_eq_simpleXY_of_counts_value
    (orderGapScan right x y) rightXCount rightYCount rightValue

private theorem lastBefore_forward
    {left right : Word Nat} {x y : Nat}
    (equalEval :
      orderStateValue (orderGapScan left x y) =
        orderStateValue (orderGapScan right x y))
    (capped : forall letter,
      RouteBlockProbe.cappedMultiplicity left letter =
        RouteBlockProbe.cappedMultiplicity right letter)
    (before : MultipleLastBeforeSimple left x y) :
    MultipleLastBeforeSimple right x y := by
  rcases before with ⟨different, leftState⟩
  refine ⟨different, ?_⟩
  have rightXCount : (orderGapScan right x y).xCount = 2 := by
    calc
      (orderGapScan right x y).xCount =
          RouteBlockProbe.cappedMultiplicity right x :=
        orderGapScan_xCount right x y
      _ = RouteBlockProbe.cappedMultiplicity left x := (capped x).symm
      _ = (orderGapScan left x y).xCount :=
        (orderGapScan_xCount left x y).symm
      _ = 2 := by rw [leftState]; rfl
  have rightYCount : (orderGapScan right x y).yCount = 1 := by
    calc
      (orderGapScan right x y).yCount =
          RouteBlockProbe.cappedMultiplicity right y :=
        orderGapScan_yCount right different
      _ = RouteBlockProbe.cappedMultiplicity left y := (capped y).symm
      _ = (orderGapScan left x y).yCount :=
        (orderGapScan_yCount left different).symm
      _ = 1 := by rw [leftState]; rfl
  have rightValue :
      orderStateValue (orderGapScan right x y) = 1 := by
    rw [← equalEval, leftState]
    rfl
  exact state_eq_xManyYOneBefore_of_counts_value
    (orderGapScan right x y) rightXCount rightYCount rightValue

theorem valid_simplePrecedes
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemanticBlockSignature.table.semigroup)
    (capped : forall letter,
      RouteBlockProbe.cappedMultiplicity identity.lhs letter =
        RouteBlockProbe.cappedMultiplicity identity.rhs letter)
    (x y : Nat) :
    SimplePrecedes identity.lhs x y ↔
      SimplePrecedes identity.rhs x y := by
  have evaluated := valid (orderValuation x y)
  rw [block_eval_order, block_eval_order] at evaluated
  constructor
  · exact simplePrecedes_forward evaluated capped
  · exact simplePrecedes_forward evaluated.symm
      (fun letter => (capped letter).symm)

theorem valid_multipleLastBeforeSimple
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy
      SemanticBlockSignature.table.semigroup)
    (capped : forall letter,
      RouteBlockProbe.cappedMultiplicity identity.lhs letter =
        RouteBlockProbe.cappedMultiplicity identity.rhs letter)
    (x y : Nat) :
    MultipleLastBeforeSimple identity.lhs x y ↔
      MultipleLastBeforeSimple identity.rhs x y := by
  have evaluated := valid (orderValuation x y)
  rw [block_eval_order, block_eval_order] at evaluated
  constructor
  · exact lastBefore_forward evaluated capped
  · exact lastBefore_forward evaluated.symm
      (fun letter => (capped letter).symm)

end RouteBlockProbe

/-! ## Pair scanners for the route-local catalogue probes -/

private def pairKeep (x y value : Nat) : Bool :=
  value == x || value == y

private def pairProjection
    (letters : List Nat) (x y : Nat) : List Nat :=
  letters.filter (pairKeep x y)

@[simp]
private theorem pairProjection_append
    (left right : List Nat) (x y : Nat) :
    pairProjection (left ++ right) x y =
      pairProjection left x y ++ pairProjection right x y := by
  simp [pairProjection, List.filter_append]

private def orderScanFrom
    (x y : Nat) (initial : RouteBlockProbe.OrderGapState)
    (letters : List Nat) : RouteBlockProbe.OrderGapState :=
  letters.foldl
    (fun state letter =>
      RouteBlockProbe.orderStep state
        (RouteBlockProbe.orderSymbol x y letter))
    initial

private theorem orderScanFrom_pairProjection
    (x y : Nat) :
    forall (letters : List Nat)
      (initial : RouteBlockProbe.OrderGapState),
      orderScanFrom x y initial letters =
        orderScanFrom x y initial (pairProjection letters x y)
  | [], _ => rfl
  | letter :: rest, initial => by
      by_cases isX : letter = x
      · subst letter
        have induction :=
          orderScanFrom_pairProjection x y rest
            (RouteBlockProbe.orderStep initial
              (RouteBlockProbe.orderSymbol x y x))
        simpa [orderScanFrom, pairProjection, pairKeep] using induction
      · by_cases isY : letter = y
        · subst letter
          have induction :=
            orderScanFrom_pairProjection x y rest
              (RouteBlockProbe.orderStep initial
                (RouteBlockProbe.orderSymbol x y y))
          simpa [orderScanFrom, pairProjection, pairKeep, isX]
            using induction
        · have induction :=
            orderScanFrom_pairProjection x y rest initial
          simpa [orderScanFrom, pairProjection, pairKeep,
            RouteBlockProbe.orderSymbol, isX, isY] using induction

private theorem pairProjection_count_of_kept
    (letters : List Nat) (x y selected : Nat)
    (kept : pairKeep x y selected = true) :
    (pairProjection letters x y).count selected =
      letters.count selected := by
  unfold pairProjection
  induction letters with
  | nil => simp
  | cons first rest inductionHypothesis =>
      by_cases equality : first = selected
      · subst first
        simp [kept, inductionHypothesis]
      · by_cases firstKept : pairKeep x y first
        · simp [firstKept, equality, inductionHypothesis]
        · simp [firstKept, equality, inductionHypothesis]

private theorem pairProjection_member
    {letters : List Nat} {x y value : Nat}
    (member : value ∈ pairProjection letters x y) :
    value = x ∨ value = y := by
  have kept := (List.mem_filter.mp member).2
  simpa [pairKeep] using kept

private theorem pairList_length
    {x y : Nat} (different : x ≠ y) :
    forall letters : List Nat,
      (forall value, value ∈ letters → value = x ∨ value = y) →
      letters.length = letters.count x + letters.count y
  | [], _ => by simp
  | value :: rest, onlyPair => by
      have headPair := onlyPair value (by simp)
      have restPair :
          forall selected, selected ∈ rest →
            selected = x ∨ selected = y := by
        intro selected member
        exact onlyPair selected (by simp [member])
      have induction := pairList_length different rest restPair
      rcases headPair with rfl | rfl
      · simp [different, induction]
        omega
      · simp [Ne.symm different, induction]
        omega

private theorem pairList_shape_one_one
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : letters.count x = 1)
    (yCount : letters.count y = 1)
    (onlyPair :
      forall value, value ∈ letters → value = x ∨ value = y) :
    letters = [x, y] ∨ letters = [y, x] := by
  have lengthTwo : letters.length = 2 := by
    rw [pairList_length different letters onlyPair, xCount, yCount]
  rcases letters with _ | ⟨first, rest⟩
  · simp at lengthTwo
  rcases rest with _ | ⟨second, rest⟩
  · simp at lengthTwo
  have restEmpty : rest = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using lengthTwo
  subst rest
  have firstPair := onlyPair first (by simp)
  have secondPair := onlyPair second (by simp)
  rcases firstPair with rfl | rfl
  · rcases secondPair with rfl | rfl
    · simp at xCount
    · exact Or.inl rfl
  · rcases secondPair with rfl | rfl
    · exact Or.inr rfl
    · simp at yCount

private theorem pairProjection_shape_one_one
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : letters.count x = 1)
    (yCount : letters.count y = 1) :
    pairProjection letters x y = [x, y] ∨
      pairProjection letters x y = [y, x] := by
  apply pairList_shape_one_one
  · exact different
  · rw [pairProjection_count_of_kept]
    · exact xCount
    · simp [pairKeep]
  · rw [pairProjection_count_of_kept]
    · exact yCount
    · simp [pairKeep]
  · intro value member
    exact pairProjection_member member

private theorem pairList_shape_two_one
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : letters.count x = 2)
    (yCount : letters.count y = 1)
    (onlyPair :
      forall value, value ∈ letters → value = x ∨ value = y) :
    letters = [x, x, y] ∨
      letters = [x, y, x] ∨
      letters = [y, x, x] := by
  have lengthThree : letters.length = 3 := by
    rw [pairList_length different letters onlyPair, xCount, yCount]
  rcases letters with _ | ⟨first, rest⟩
  · simp at lengthThree
  rcases rest with _ | ⟨second, rest⟩
  · simp at lengthThree
  rcases rest with _ | ⟨third, rest⟩
  · simp at lengthThree
  have restEmpty : rest = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using lengthThree
  subst rest
  have firstPair := onlyPair first (by simp)
  have secondPair := onlyPair second (by simp)
  have thirdPair := onlyPair third (by simp)
  rcases firstPair with rfl | rfl
  · rcases secondPair with rfl | rfl
    · rcases thirdPair with rfl | rfl
      · simp at xCount
      · exact Or.inl rfl
    · rcases thirdPair with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · simp [different] at yCount
  · rcases secondPair with rfl | rfl
    · rcases thirdPair with rfl | rfl
      · exact Or.inr (Or.inr rfl)
      · simp [different] at yCount
    · rcases thirdPair with rfl | rfl
      · simp [different] at yCount
      · simp at yCount

private theorem pairProjection_shape_two_one
    (letters : List Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : letters.count x = 2)
    (yCount : letters.count y = 1) :
    pairProjection letters x y = [x, x, y] ∨
      pairProjection letters x y = [x, y, x] ∨
      pairProjection letters x y = [y, x, x] := by
  apply pairList_shape_two_one
  · exact different
  · rw [pairProjection_count_of_kept]
    · exact xCount
    · simp [pairKeep]
  · rw [pairProjection_count_of_kept]
    · exact yCount
    · simp [pairKeep]
  · intro value member
    exact pairProjection_member member

private theorem simplePrecedes_iff_pairProjection
    (word : Word Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : word.toList.count x = 1)
    (yCount : word.toList.count y = 1) :
    RouteBlockProbe.SimplePrecedes word x y ↔
      pairProjection word.toList x y = [x, y] := by
  rw [RouteBlockProbe.SimplePrecedes]
  have scanEq :
      RouteBlockProbe.orderGapScan word x y =
        orderScanFrom x y .empty
          (pairProjection word.toList x y) := by
    rw [show RouteBlockProbe.orderGapScan word x y =
        orderScanFrom x y .empty word.toList by rfl]
    exact orderScanFrom_pairProjection x y word.toList .empty
  rw [scanEq]
  rcases pairProjection_shape_one_one
      word.toList different xCount yCount with shape | shape
  · rw [shape]
    simp [orderScanFrom, RouteBlockProbe.orderSymbol,
      RouteBlockProbe.orderStep, different, Ne.symm different]
  · rw [shape]
    simp [orderScanFrom, RouteBlockProbe.orderSymbol,
      RouteBlockProbe.orderStep, different, Ne.symm different]

private theorem multipleLastBeforeSimple_iff_pairProjection
    (word : Word Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : word.toList.count x = 2)
    (yCount : word.toList.count y = 1) :
    RouteBlockProbe.MultipleLastBeforeSimple word x y ↔
      pairProjection word.toList x y = [x, x, y] := by
  rw [RouteBlockProbe.MultipleLastBeforeSimple]
  have scanEq :
      RouteBlockProbe.orderGapScan word x y =
        orderScanFrom x y .empty
          (pairProjection word.toList x y) := by
    rw [show RouteBlockProbe.orderGapScan word x y =
        orderScanFrom x y .empty word.toList by rfl]
    exact orderScanFrom_pairProjection x y word.toList .empty
  rw [scanEq]
  rcases pairProjection_shape_two_one
      word.toList different xCount yCount with
    shape | shape | shape
  · rw [shape]
    simp [orderScanFrom, RouteBlockProbe.orderSymbol,
      RouteBlockProbe.orderStep, different, Ne.symm different]
  · rw [shape]
    simp [orderScanFrom, RouteBlockProbe.orderSymbol,
      RouteBlockProbe.orderStep, different, Ne.symm different]
  · rw [shape]
    simp [orderScanFrom, RouteBlockProbe.orderSymbol,
      RouteBlockProbe.orderStep, different, Ne.symm different]

private theorem before_filter
    {events : List Nat} {keep : Nat → Bool}
    {earlier later : Nat}
    (before : EndpointChronology.Before events earlier later)
    (earlierKept : keep earlier = true)
    (laterKept : keep later = true) :
    EndpointChronology.Before
      (events.filter keep) earlier later := by
  induction events with
  | nil => simpa [EndpointChronology.Before] using before
  | cons head tail inductionHypothesis =>
      simp only [EndpointChronology.Before] at before
      rcases before with ⟨rfl, laterMember⟩ | tailBefore
      · have laterFiltered : later ∈ tail.filter keep := by
          simp [laterMember, laterKept]
        simp [earlierKept, EndpointChronology.Before,
          laterFiltered]
      · have tailFiltered := inductionHypothesis tailBefore
        cases keptHead : keep head <;>
          simp [keptHead, EndpointChronology.Before,
            tailFiltered]

private theorem before_of_filter
    {events : List Nat} {keep : Nat → Bool}
    {earlier later : Nat}
    (before : EndpointChronology.Before
      (events.filter keep) earlier later) :
    EndpointChronology.Before events earlier later := by
  induction events with
  | nil => simpa [EndpointChronology.Before] using before
  | cons head tail inductionHypothesis =>
      cases keptHead : keep head
      · have tailBefore : EndpointChronology.Before
            (tail.filter keep) earlier later := by
          simpa [keptHead] using before
        exact Or.inr (inductionHypothesis tailBefore)
      · simp only [List.filter_cons, keptHead, if_true,
          EndpointChronology.Before] at before
        rcases before with ⟨rfl, laterMember⟩ | tailBefore
        · exact Or.inl
            ⟨rfl, (List.mem_filter.mp laterMember).1⟩
        · exact Or.inr (inductionHypothesis tailBefore)

private theorem before_iff_pairProjection
    (events : List Nat) {x y : Nat}
    (nodup : events.Nodup)
    (different : x ≠ y)
    (xMember : x ∈ events)
    (yMember : y ∈ events) :
    EndpointChronology.Before events x y ↔
      pairProjection events x y = [x, y] := by
  have xCount : events.count x = 1 := by
    rw [nodup.count]
    simp [xMember]
  have yCount : events.count y = 1 := by
    rw [nodup.count]
    simp [yMember]
  have xKept : pairKeep x y x = true := by simp [pairKeep]
  have yKept : pairKeep x y y = true := by simp [pairKeep]
  constructor
  · intro before
    have filtered := before_filter before xKept yKept
    rcases pairProjection_shape_one_one
        events different xCount yCount with shape | shape
    · exact shape
    · exfalso
      change EndpointChronology.Before
        (pairProjection events x y) x y at filtered
      rw [shape] at filtered
      simpa [EndpointChronology.Before, different,
        Ne.symm different] using filtered
  · intro shape
    apply before_of_filter (keep := pairKeep x y)
    change EndpointChronology.Before
      (pairProjection events x y) x y
    rw [shape]
    simp [EndpointChronology.Before, different,
      Ne.symm different]

private theorem filter_eq_singleton_of_nodup_mem (selected : Nat) :
    forall {letters : List Nat}, letters.Nodup → selected ∈ letters →
      letters.filter (fun letter => decide (letter = selected)) =
        [selected]
  | [], _, member => by simp at member
  | head :: tail, nodup, member => by
      have headAbsent := (List.nodup_cons.mp nodup).1
      have tailNodup := (List.nodup_cons.mp nodup).2
      by_cases headEq : head = selected
      · subst head
        have selectedAbsent : selected ∉ tail := headAbsent
        have tailFilter :
            tail.filter (fun letter => decide (letter = selected)) =
              [] := by
          apply List.filter_eq_nil_iff.mpr
          intro letter letterMem
          have letterNe : letter ≠ selected := by
            intro equal
            subst letter
            exact selectedAbsent letterMem
          simp [letterNe]
        simp [List.filter_cons, tailFilter]
      · have tailMember : selected ∈ tail := by
          simp only [List.mem_cons] at member
          rcases member with selectedHead | member
          · exact False.elim (headEq selectedHead.symm)
          · exact member
        have induction :=
          filter_eq_singleton_of_nodup_mem selected tailNodup tailMember
        simp [headEq, induction]

private theorem pairProjection_eq_nil_of_absent
    (letters : List Nat) (x y : Nat)
    (xAbsent : x ∉ letters) (yAbsent : y ∉ letters) :
    pairProjection letters x y = [] := by
  unfold pairProjection
  apply List.filter_eq_nil_iff.mpr
  intro letter member
  have notX : letter ≠ x := by
    intro equal
    subst letter
    exact xAbsent member
  have notY : letter ≠ y := by
    intro equal
    subst letter
    exact yAbsent member
  simp [pairKeep, notX, notY]

private theorem pairProjection_eq_singleton
    (letters : List Nat) (x y : Nat)
    (nodup : letters.Nodup)
    (xMember : x ∈ letters) (yAbsent : y ∉ letters) :
    pairProjection letters x y = [x] := by
  calc
    pairProjection letters x y =
        letters.filter (fun letter => decide (letter = x)) := by
      unfold pairProjection
      apply List.filter_congr
      intro letter member
      have notY : letter ≠ y := by
        intro equal
        subst letter
        exact yAbsent member
      by_cases equal : letter = x
      · subst letter
        simp [pairKeep]
      · simp [pairKeep, equal, notY]
    _ = [x] := filter_eq_singleton_of_nodup_mem x nodup xMember

private theorem simplePrecedes_iff_before_events
    {head : Nat} {tail firsts events : List Nat} {x y : Nat}
    (split : EndpointZeroSplit (head :: tail) firsts events)
    (different : x ≠ y)
    (xSimple : x ∉ firsts) (ySimple : y ∉ firsts)
    (xMember : x ∈ events) (yMember : y ∈ events) :
    RouteBlockProbe.SimplePrecedes
        (S5_107.listWordOfCons head tail) x y ↔
      EndpointChronology.Before events x y := by
  have xPositive := (split.eventMem x).mp xMember
  have yPositive := (split.eventMem y).mp yMember
  have xNotTwo : (head :: tail).count x ≠ 2 := by
    intro countTwo
    exact xSimple ((split.firstMem x).mpr countTwo)
  have yNotTwo : (head :: tail).count y ≠ 2 := by
    intro countTwo
    exact ySimple ((split.firstMem y).mpr countTwo)
  have xCount : (head :: tail).count x = 1 := by
    have bound := split.limited x
    omega
  have yCount : (head :: tail).count y = 1 := by
    have bound := split.limited y
    omega
  have firstPairEmpty : pairProjection firsts x y = [] :=
    pairProjection_eq_nil_of_absent firsts x y xSimple ySimple
  have wholeProjection :
      pairProjection (head :: tail) x y =
        pairProjection events x y := by
    rw [split.shape, pairProjection_append, firstPairEmpty]
    simp
  have scanner := simplePrecedes_iff_pairProjection
    (S5_107.listWordOfCons head tail) different
    (by simpa [S5_107.listWordOfCons, Word.toList] using xCount)
    (by simpa [S5_107.listWordOfCons, Word.toList] using yCount)
  change RouteBlockProbe.SimplePrecedes
      (S5_107.listWordOfCons head tail) x y ↔
        pairProjection (head :: tail) x y = [x, y] at scanner
  rw [wholeProjection] at scanner
  exact scanner.trans
    (before_iff_pairProjection events split.eventNodup
      different xMember yMember).symm

private theorem multipleLastBeforeSimple_iff_before_events
    {head : Nat} {tail firsts events : List Nat} {x y : Nat}
    (split : EndpointZeroSplit (head :: tail) firsts events)
    (different : x ≠ y)
    (xMultiple : x ∈ firsts) (ySimple : y ∉ firsts)
    (xMember : x ∈ events) (yMember : y ∈ events) :
    RouteBlockProbe.MultipleLastBeforeSimple
        (S5_107.listWordOfCons head tail) x y ↔
      EndpointChronology.Before events x y := by
  have xCount : (head :: tail).count x = 2 :=
    (split.firstMem x).mp xMultiple
  have yPositive := (split.eventMem y).mp yMember
  have yNotTwo : (head :: tail).count y ≠ 2 := by
    intro countTwo
    exact ySimple ((split.firstMem y).mpr countTwo)
  have yCount : (head :: tail).count y = 1 := by
    have bound := split.limited y
    omega
  have firstPair : pairProjection firsts x y = [x] :=
    pairProjection_eq_singleton firsts x y
      split.firstNodup xMultiple ySimple
  have scanner := multipleLastBeforeSimple_iff_pairProjection
    (S5_107.listWordOfCons head tail) different
    (by simpa [S5_107.listWordOfCons, Word.toList] using xCount)
    (by simpa [S5_107.listWordOfCons, Word.toList] using yCount)
  change RouteBlockProbe.MultipleLastBeforeSimple
      (S5_107.listWordOfCons head tail) x y ↔
        pairProjection (head :: tail) x y = [x, x, y] at scanner
  have wholeProjection :
      pairProjection (head :: tail) x y =
        [x] ++ pairProjection events x y := by
    rw [split.shape, pairProjection_append, firstPair]
  rw [wholeProjection] at scanner
  have eventScanner := before_iff_pairProjection events
    split.eventNodup different xMember yMember
  constructor
  · intro relation
    have shape := scanner.mp relation
    have eventShape : pairProjection events x y = [x, y] := by
      simpa using congrArg List.tail shape
    exact eventScanner.mpr eventShape
  · intro before
    have eventShape := eventScanner.mp before
    apply scanner.mpr
    simp [eventShape]

/-! ## Descending runs and singleton-count induction -/

private theorem countGTInMultipleRun_eq_countGT_of_all_multiple
    (firsts : List Nat) (pivot : Nat) :
    forall events : List Nat,
      (forall value, value ∈ events → value ∈ firsts) →
      countGTInMultipleRun firsts pivot events =
        countGT pivot events
  | [], _ => rfl
  | value :: rest, allMultiple => by
      have valueMultiple : value ∈ firsts :=
        allMultiple value (List.Mem.head rest)
      have restMultiple :
          forall tested, tested ∈ rest → tested ∈ firsts := by
        intro tested member
        exact allMultiple tested (List.Mem.tail value member)
      simp [countGTInMultipleRun, countGT, valueMultiple,
        countGTInMultipleRun_eq_countGT_of_all_multiple
          firsts pivot rest restMultiple]

private theorem countGTInMultipleRun_until_simple
    (firsts : List Nat) (pivot simple : Nat) (rest : List Nat) :
    forall run : List Nat,
      (forall value, value ∈ run → value ∈ firsts) →
      simple ∉ firsts →
      countGTInMultipleRun firsts pivot (run ++ simple :: rest) =
        countGT pivot run
  | [], _, simpleAbsent => by
      simp [countGTInMultipleRun, countGT, simpleAbsent]
  | value :: run, allMultiple, simpleAbsent => by
      have valueMultiple : value ∈ firsts :=
        allMultiple value (List.Mem.head run)
      have tailMultiple :
          forall tested, tested ∈ run → tested ∈ firsts := by
        intro tested member
        exact allMultiple tested (List.Mem.tail value member)
      simp [countGTInMultipleRun, countGT, valueMultiple,
        countGTInMultipleRun_until_simple firsts pivot simple rest
          run tailMultiple simpleAbsent]

private theorem eventGapInversionsList_eq_descending_of_all_multiple
    (firsts : List Nat) :
    forall events : List Nat,
      (forall value, value ∈ events → value ∈ firsts) →
      eventGapInversionsList firsts events =
        descendingInversions events
  | [], _ => rfl
  | value :: rest, allMultiple => by
      have valueMultiple : value ∈ firsts :=
        allMultiple value (List.Mem.head rest)
      have restMultiple :
          forall tested, tested ∈ rest → tested ∈ firsts := by
        intro tested member
        exact allMultiple tested (List.Mem.tail value member)
      simp [eventGapInversionsList, descendingInversions,
        valueMultiple,
        countGTInMultipleRun_eq_countGT_of_all_multiple
          firsts value rest restMultiple,
        eventGapInversionsList_eq_descending_of_all_multiple
          firsts rest restMultiple]

private theorem eventGapInversionsList_split_at_simple
    (firsts : List Nat) (simple : Nat) (rest : List Nat) :
    forall run : List Nat,
      (forall value, value ∈ run → value ∈ firsts) →
      simple ∉ firsts →
      eventGapInversionsList firsts (run ++ simple :: rest) =
        descendingInversions run +
          eventGapInversionsList firsts rest
  | [], _, simpleAbsent => by
      simp [eventGapInversionsList, descendingInversions,
        simpleAbsent]
  | value :: run, allMultiple, simpleAbsent => by
      have valueMultiple : value ∈ firsts :=
        allMultiple value (List.Mem.head run)
      have tailMultiple :
          forall tested, tested ∈ run → tested ∈ firsts := by
        intro tested member
        exact allMultiple tested (List.Mem.tail value member)
      simp only [List.cons_append, eventGapInversionsList,
        descendingInversions]
      rw [if_pos valueMultiple]
      rw [countGTInMultipleRun_until_simple
        firsts value simple rest run tailMultiple simpleAbsent]
      rw [eventGapInversionsList_split_at_simple
        firsts simple rest run tailMultiple simpleAbsent]
      omega

private theorem descending_nodup_eq_of_mem_iff
    {left right : List Nat}
    (leftOrdered : left.Pairwise (· ≥ ·))
    (rightOrdered : right.Pairwise (· ≥ ·))
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (sameMembers : forall value, value ∈ left ↔ value ∈ right) :
    left = right := by
  have permutation : left.Perm right := by
    rw [List.perm_iff_count]
    intro value
    rw [leftNodup.count, rightNodup.count]
    simp only [sameMembers value]
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftGe rightGe =>
      Nat.le_antisymm rightGe leftGe)
    leftOrdered rightOrdered permutation

private def simpleEventCount
    (firsts : List Nat) : List Nat → Nat
  | [] => 0
  | value :: rest =>
      if value ∈ firsts then
        simpleEventCount firsts rest
      else
        (simpleEventCount firsts rest).succ

private theorem simpleEventCount_eq_zero_iff
    (firsts : List Nat) :
    forall events : List Nat,
      simpleEventCount firsts events = 0 ↔
        forall value, value ∈ events → value ∈ firsts
  | [] => by simp [simpleEventCount]
  | value :: rest => by
      by_cases multiple : value ∈ firsts
      · simp [simpleEventCount, multiple,
          simpleEventCount_eq_zero_iff firsts rest]
      · constructor
        · intro zero
          simp [simpleEventCount, multiple] at zero
        · intro allMultiple
          exact False.elim
            (multiple (allMultiple value (List.Mem.head rest)))

private theorem exists_first_simple_of_simpleEventCount_pos
    (firsts : List Nat) :
    forall events : List Nat,
      0 < simpleEventCount firsts events →
        exists run simple rest,
          events = run ++ simple :: rest ∧
          (forall value, value ∈ run → value ∈ firsts) ∧
          simple ∉ firsts
  | [], positive => by simp [simpleEventCount] at positive
  | value :: rest, positive => by
      by_cases multiple : value ∈ firsts
      · have tailPositive :
            0 < simpleEventCount firsts rest := by
          simpa [simpleEventCount, multiple] using positive
        obtain ⟨run, simple, after, shape,
            runMultiple, simpleNotMultiple⟩ :=
          exists_first_simple_of_simpleEventCount_pos
            firsts rest tailPositive
        exact ⟨value :: run, simple, after,
          by simp [shape, List.append_assoc],
          by
            intro tested member
            rcases List.mem_cons.mp member with equal | inRun
            · simpa [equal] using multiple
            · exact runMultiple tested inRun,
          simpleNotMultiple⟩
      · exact ⟨[], value, rest, rfl, by simp, multiple⟩

private theorem simpleEventCount_split_at_simple
    (firsts : List Nat) (simple : Nat) (rest : List Nat) :
    forall run : List Nat,
      (forall value, value ∈ run → value ∈ firsts) →
      simple ∉ firsts →
      simpleEventCount firsts (run ++ simple :: rest) =
        (simpleEventCount firsts rest).succ
  | [], _, simpleAbsent => by
      simp [simpleEventCount, simpleAbsent]
  | value :: run, allMultiple, simpleAbsent => by
      have valueMultiple : value ∈ firsts :=
        allMultiple value (List.Mem.head run)
      have tailMultiple :
          forall tested, tested ∈ run → tested ∈ firsts := by
        intro tested member
        exact allMultiple tested (List.Mem.tail value member)
      simp [simpleEventCount, valueMultiple,
        simpleEventCount_split_at_simple firsts simple rest
          run tailMultiple simpleAbsent]

private theorem zeroEvents_eq_of_probes_of_measure
    (firsts : List Nat) :
    forall measure : Nat,
      forall left right : List Nat,
      simpleEventCount firsts left = measure →
      left.Nodup →
      right.Nodup →
      (forall value,
        value ∈ left ↔ value ∈ right) →
      eventGapInversionsList firsts left = 0 →
      eventGapInversionsList firsts right = 0 →
      (forall {x y},
        x ≠ y →
        x ∈ left → y ∈ left →
        x ∉ firsts → y ∉ firsts →
        (EndpointChronology.Before left x y ↔
          EndpointChronology.Before right x y)) →
      (forall {x y},
        x ≠ y →
        x ∈ left → y ∈ left →
        x ∈ firsts → y ∉ firsts →
        (EndpointChronology.Before left x y ↔
          EndpointChronology.Before right x y)) →
      left = right := by
  intro measure
  induction measure using Nat.strongRecOn with
  | ind measure inductionHypothesis =>
      intro left right measureEq leftNodup rightNodup sameMembers
        leftZero rightZero simpleOrder lastGap
      by_cases zeroSimple : simpleEventCount firsts left = 0
      · have leftAll :
            forall value, value ∈ left → value ∈ firsts :=
          (simpleEventCount_eq_zero_iff firsts left).mp zeroSimple
        have rightAll :
            forall value, value ∈ right → value ∈ firsts := by
          intro value member
          exact leftAll value ((sameMembers value).mpr member)
        have leftDescending : left.Pairwise (· ≥ ·) := by
          apply (descendingInversions_eq_zero_iff_pairwise left).mp
          rw [← eventGapInversionsList_eq_descending_of_all_multiple
            firsts left leftAll]
          exact leftZero
        have rightDescending : right.Pairwise (· ≥ ·) := by
          apply (descendingInversions_eq_zero_iff_pairwise right).mp
          rw [← eventGapInversionsList_eq_descending_of_all_multiple
            firsts right rightAll]
          exact rightZero
        exact descending_nodup_eq_of_mem_iff
          leftDescending rightDescending leftNodup rightNodup sameMembers
      · have positive : 0 < simpleEventCount firsts left :=
          Nat.pos_of_ne_zero zeroSimple
        obtain ⟨leftRun, simple, leftRest, leftShape,
            leftRunMultiple, simpleNotMultiple⟩ :=
          exists_first_simple_of_simpleEventCount_pos
            firsts left positive
        have simpleLeft : simple ∈ left := by
          rw [leftShape]
          simp
        have simpleRight : simple ∈ right :=
          (sameMembers simple).mp simpleLeft
        obtain ⟨rightRun, rightRest, rightShape⟩ :=
          List.mem_iff_append.mp simpleRight
        have rightRunMultiple :
            forall value, value ∈ rightRun → value ∈ firsts := by
          intro value valueMember
          apply Classical.byContradiction
          intro valueNotMultiple
          have rightSplitNodup :
              (rightRun ++ simple :: rightRest).Nodup := by
            simpa [rightShape] using rightNodup
          have different : value ≠ simple := by
            intro equal
            subst value
            have appendData := List.nodup_append.mp rightSplitNodup
            exact appendData.2.2 simple valueMember simple
              (List.Mem.head rightRest) rfl
          have rightBefore :
              EndpointChronology.Before right value simple :=
            by
              rw [rightShape]
              exact EndpointChronology.before_append_cross
                rightRun (simple :: rightRest)
                valueMember (List.Mem.head rightRest)
          have valueLeft : value ∈ left :=
            (sameMembers value).mpr <| by
              rw [rightShape]
              exact List.mem_append_left (simple :: rightRest) valueMember
          have leftBefore :
              EndpointChronology.Before left value simple :=
            (simpleOrder different valueLeft simpleLeft
              valueNotMultiple simpleNotMultiple).mpr rightBefore
          have leftSplitNodup :
              (leftRun ++ simple :: leftRest).Nodup := by
            simpa [leftShape] using leftNodup
          have valueInLeftRun :=
            EndpointChronology.mem_front_of_before_split
              leftRun leftRest simple value leftSplitNodup
                (by simpa [leftShape] using leftBefore)
          exact valueNotMultiple
            (leftRunMultiple value valueInLeftRun)
        have runMembers : forall value,
            value ∈ leftRun ↔ value ∈ rightRun := by
          intro value
          constructor
          · intro leftMember
            have valueMultiple := leftRunMultiple value leftMember
            have leftSplitNodup :
                (leftRun ++ simple :: leftRest).Nodup := by
              simpa [leftShape] using leftNodup
            have different : value ≠ simple := by
              intro equal
              subst value
              have appendData := List.nodup_append.mp leftSplitNodup
              exact appendData.2.2 simple leftMember simple
                (List.Mem.head leftRest) rfl
            have leftBefore :
                EndpointChronology.Before left value simple := by
              rw [leftShape]
              exact EndpointChronology.before_append_cross
                leftRun (simple :: leftRest)
                leftMember (List.Mem.head leftRest)
            have valueLeft : value ∈ left := by
              rw [leftShape]
              exact List.mem_append_left (simple :: leftRest) leftMember
            have rightBefore :
                EndpointChronology.Before right value simple :=
              (lastGap different valueLeft simpleLeft
                valueMultiple simpleNotMultiple).mp leftBefore
            have rightSplitNodup :
                (rightRun ++ simple :: rightRest).Nodup := by
              simpa [rightShape] using rightNodup
            exact EndpointChronology.mem_front_of_before_split
              rightRun rightRest simple value
              rightSplitNodup (by simpa [rightShape] using rightBefore)
          · intro rightMember
            have valueMultiple := rightRunMultiple value rightMember
            have rightSplitNodup :
                (rightRun ++ simple :: rightRest).Nodup := by
              simpa [rightShape] using rightNodup
            have different : value ≠ simple := by
              intro equal
              subst value
              have appendData := List.nodup_append.mp rightSplitNodup
              exact appendData.2.2 simple rightMember simple
                (List.Mem.head rightRest) rfl
            have rightBefore :
                EndpointChronology.Before right value simple := by
              rw [rightShape]
              exact EndpointChronology.before_append_cross
                rightRun (simple :: rightRest)
                rightMember (List.Mem.head rightRest)
            have valueRight : value ∈ right := by
              rw [rightShape]
              exact List.mem_append_left (simple :: rightRest) rightMember
            have valueLeft : value ∈ left :=
              (sameMembers value).mpr valueRight
            have leftBefore :
                EndpointChronology.Before left value simple :=
              (lastGap different valueLeft simpleLeft
                valueMultiple simpleNotMultiple).mpr rightBefore
            have leftSplitNodup :
                (leftRun ++ simple :: leftRest).Nodup := by
              simpa [leftShape] using leftNodup
            exact EndpointChronology.mem_front_of_before_split
              leftRun leftRest simple value
              leftSplitNodup (by simpa [leftShape] using leftBefore)
        have leftRunNodup : leftRun.Nodup := by
          have splitNodup : (leftRun ++ simple :: leftRest).Nodup := by
            simpa [leftShape] using leftNodup
          exact (List.nodup_append.mp splitNodup).1
        have rightRunNodup : rightRun.Nodup := by
          have splitNodup : (rightRun ++ simple :: rightRest).Nodup := by
            simpa [rightShape] using rightNodup
          exact (List.nodup_append.mp splitNodup).1
        have leftSegmentEq :=
          eventGapInversionsList_split_at_simple
            firsts simple leftRest leftRun
              leftRunMultiple simpleNotMultiple
        have rightSegmentEq :=
          eventGapInversionsList_split_at_simple
            firsts simple rightRest rightRun
              rightRunMultiple simpleNotMultiple
        have leftRunZero : descendingInversions leftRun = 0 := by
          rw [← leftShape] at leftSegmentEq
          rw [leftZero] at leftSegmentEq
          omega
        have rightRunZero : descendingInversions rightRun = 0 := by
          rw [← rightShape] at rightSegmentEq
          rw [rightZero] at rightSegmentEq
          omega
        have leftRunOrdered : leftRun.Pairwise (· ≥ ·) :=
          (descendingInversions_eq_zero_iff_pairwise leftRun).mp
            leftRunZero
        have rightRunOrdered : rightRun.Pairwise (· ≥ ·) :=
          (descendingInversions_eq_zero_iff_pairwise rightRun).mp
            rightRunZero
        have runEqual : leftRun = rightRun :=
          descending_nodup_eq_of_mem_iff
            leftRunOrdered rightRunOrdered
            leftRunNodup rightRunNodup runMembers
        subst rightRun
        have leftRestZero :
            eventGapInversionsList firsts leftRest = 0 := by
          rw [← leftShape] at leftSegmentEq
          rw [leftZero] at leftSegmentEq
          omega
        have rightRestZero :
            eventGapInversionsList firsts rightRest = 0 := by
          rw [← rightShape] at rightSegmentEq
          rw [rightZero] at rightSegmentEq
          omega
        have leftSplitNodup :
            (leftRun ++ simple :: leftRest).Nodup := by
          simpa [leftShape] using leftNodup
        have rightSplitNodup :
            (leftRun ++ simple :: rightRest).Nodup := by
          simpa [rightShape] using rightNodup
        have leftRestNodup : leftRest.Nodup :=
          (List.nodup_cons.mp
            (List.nodup_append.mp leftSplitNodup).2.1).2
        have rightRestNodup : rightRest.Nodup :=
          (List.nodup_cons.mp
            (List.nodup_append.mp rightSplitNodup).2.1).2
        have wholeCounts : forall value,
            left.count value = right.count value := by
          intro value
          rw [leftNodup.count, rightNodup.count]
          simp only [sameMembers value]
        have restCounts : forall value,
            leftRest.count value = rightRest.count value := by
          intro value
          have equal := wholeCounts value
          rw [leftShape, rightShape,
            List.count_append, List.count_append] at equal
          simp only [List.count_cons] at equal
          omega
        have restMembers : forall value,
            value ∈ leftRest ↔ value ∈ rightRest := by
          intro value
          rw [← List.count_pos_iff, ← List.count_pos_iff,
            restCounts value]
        have leftRestCount :
            simpleEventCount firsts leftRest < measure := by
          have splitCount := simpleEventCount_split_at_simple
            firsts simple leftRest leftRun
              leftRunMultiple simpleNotMultiple
          rw [← leftShape, measureEq] at splitCount
          omega
        let commonFront : List Nat := leftRun ++ [simple]
        have leftAppendNodup :
            (commonFront ++ leftRest).Nodup := by
          simpa [commonFront, List.append_assoc] using leftSplitNodup
        have rightAppendNodup :
            (commonFront ++ rightRest).Nodup := by
          simpa [commonFront, List.append_assoc] using rightSplitNodup
        have restSimpleOrder : forall {x y},
            x ≠ y →
            x ∈ leftRest → y ∈ leftRest →
            x ∉ firsts → y ∉ firsts →
            (EndpointChronology.Before leftRest x y ↔
              EndpointChronology.Before rightRest x y) := by
          intro x y different xLeft yLeft xSimple ySimple
          have xRight : x ∈ rightRest := (restMembers x).mp xLeft
          have yRight : y ∈ rightRest := (restMembers y).mp yLeft
          have leftCross := (List.nodup_append.mp leftAppendNodup).2.2
          have rightCross := (List.nodup_append.mp rightAppendNodup).2.2
          have xAbsentLeft : x ∉ commonFront := by
            intro member
            exact leftCross x member x xLeft rfl
          have yAbsentLeft : y ∉ commonFront := by
            intro member
            exact leftCross y member y yLeft rfl
          have xAbsentRight : x ∉ commonFront := by
            intro member
            exact rightCross x member x xRight rfl
          have yAbsentRight : y ∉ commonFront := by
            intro member
            exact rightCross y member y yRight rfl
          have currentOrder := simpleOrder different
            (by rw [leftShape]; simpa [commonFront, List.append_assoc]
              using List.mem_append_right commonFront xLeft)
            (by rw [leftShape]; simpa [commonFront, List.append_assoc]
              using List.mem_append_right commonFront yLeft)
            xSimple ySimple
          have leftCancel :=
            EndpointChronology.before_append_iff_of_absent
              commonFront leftRest xAbsentLeft yAbsentLeft
          have rightCancel :=
            EndpointChronology.before_append_iff_of_absent
              commonFront rightRest xAbsentRight yAbsentRight
          have frontOrder :
              EndpointChronology.Before (commonFront ++ leftRest) x y ↔
                EndpointChronology.Before (commonFront ++ rightRest) x y := by
            simpa [leftShape, rightShape, commonFront,
              List.append_assoc] using currentOrder
          exact leftCancel.symm.trans (frontOrder.trans rightCancel)
        have restLastGap : forall {x y},
            x ≠ y →
            x ∈ leftRest → y ∈ leftRest →
            x ∈ firsts → y ∉ firsts →
            (EndpointChronology.Before leftRest x y ↔
              EndpointChronology.Before rightRest x y) := by
          intro x y different xLeft yLeft xMultiple ySimple
          have xRight : x ∈ rightRest := (restMembers x).mp xLeft
          have yRight : y ∈ rightRest := (restMembers y).mp yLeft
          have leftCross := (List.nodup_append.mp leftAppendNodup).2.2
          have rightCross := (List.nodup_append.mp rightAppendNodup).2.2
          have xAbsentLeft : x ∉ commonFront := by
            intro member
            exact leftCross x member x xLeft rfl
          have yAbsentLeft : y ∉ commonFront := by
            intro member
            exact leftCross y member y yLeft rfl
          have xAbsentRight : x ∉ commonFront := by
            intro member
            exact rightCross x member x xRight rfl
          have yAbsentRight : y ∉ commonFront := by
            intro member
            exact rightCross y member y yRight rfl
          have currentOrder := lastGap different
            (by rw [leftShape]; simpa [commonFront, List.append_assoc]
              using List.mem_append_right commonFront xLeft)
            (by rw [leftShape]; simpa [commonFront, List.append_assoc]
              using List.mem_append_right commonFront yLeft)
            xMultiple ySimple
          have leftCancel :=
            EndpointChronology.before_append_iff_of_absent
              commonFront leftRest xAbsentLeft yAbsentLeft
          have rightCancel :=
            EndpointChronology.before_append_iff_of_absent
              commonFront rightRest xAbsentRight yAbsentRight
          have frontOrder :
              EndpointChronology.Before (commonFront ++ leftRest) x y ↔
                EndpointChronology.Before (commonFront ++ rightRest) x y := by
            simpa [leftShape, rightShape, commonFront,
              List.append_assoc] using currentOrder
          exact leftCancel.symm.trans (frontOrder.trans rightCancel)
        have restEqual : leftRest = rightRest := by
          exact inductionHypothesis
            (simpleEventCount firsts leftRest) leftRestCount
            leftRest rightRest rfl
            leftRestNodup rightRestNodup restMembers
            leftRestZero rightRestZero
            restSimpleOrder restLastGap
        rw [leftShape, rightShape, restEqual]

private theorem zeroEvents_eq_of_probes
    (firsts left right : List Nat)
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (sameMembers : forall value, value ∈ left ↔ value ∈ right)
    (leftZero : eventGapInversionsList firsts left = 0)
    (rightZero : eventGapInversionsList firsts right = 0)
    (simpleOrder : forall {x y},
      x ≠ y → x ∈ left → y ∈ left →
      x ∉ firsts → y ∉ firsts →
      (EndpointChronology.Before left x y ↔
        EndpointChronology.Before right x y))
    (lastGap : forall {x y},
      x ≠ y → x ∈ left → y ∈ left →
      x ∈ firsts → y ∉ firsts →
      (EndpointChronology.Before left x y ↔
        EndpointChronology.Before right x y)) :
    left = right := by
  exact zeroEvents_eq_of_probes_of_measure firsts
    (simpleEventCount firsts left) left right rfl
    leftNodup rightNodup sameMembers leftZero rightZero
    simpleOrder lastGap

/-! ## Catalogue-block validity fixes a zero endpoint -/

private theorem literalCounts_eq_of_block_valid
    {left right : Word Nat}
    (leftLimited : forall selected, left.toList.count selected ≤ 2)
    (rightLimited : forall selected, right.toList.count selected ≤ 2)
    (valid :
      (Identity.mk left right).SatisfiedBy
        SemanticBlockSignature.table.semigroup) :
    forall selected,
      left.toList.count selected = right.toList.count selected := by
  intro selected
  have capped := RouteBlockProbe.valid_cappedMultiplicity
    (Identity.mk left right) valid selected
  unfold RouteBlockProbe.cappedMultiplicity at capped
  calc
    left.toList.count selected =
        Nat.min 2 (left.toList.count selected) :=
      (Nat.min_eq_right (leftLimited selected)).symm
    _ = Nat.min 2 (right.toList.count selected) := capped
    _ = right.toList.count selected :=
      Nat.min_eq_right (rightLimited selected)

theorem zeroEndpoint_unique_of_block_valid
    {leftHead rightHead : Nat}
    {leftTail rightTail : List Nat}
    (leftLimited : forall selected,
      (leftHead :: leftTail).count selected ≤ 2)
    (rightLimited : forall selected,
      (rightHead :: rightTail).count selected ≤ 2)
    (leftZero :
      endpointMeasure (leftHead :: leftTail) = ⟨0, 0, 0⟩)
    (rightZero :
      endpointMeasure (rightHead :: rightTail) = ⟨0, 0, 0⟩)
    (valid :
      (Identity.mk
        (S5_107.listWordOfCons leftHead leftTail)
        (S5_107.listWordOfCons rightHead rightTail)).SatisfiedBy
          SemanticBlockSignature.table.semigroup) :
    leftHead :: leftTail = rightHead :: rightTail := by
  obtain ⟨leftFirsts, leftEvents, leftSplit⟩ :=
    endpointZeroSplit_of_measure_eq_zero leftLimited leftZero
  obtain ⟨rightFirsts, rightEvents, rightSplit⟩ :=
    endpointZeroSplit_of_measure_eq_zero rightLimited rightZero
  let leftWord := S5_107.listWordOfCons leftHead leftTail
  let rightWord := S5_107.listWordOfCons rightHead rightTail
  let identity : Identity Nat := Identity.mk leftWord rightWord
  have counts : forall selected,
      (leftHead :: leftTail).count selected =
        (rightHead :: rightTail).count selected := by
    intro selected
    have equal := literalCounts_eq_of_block_valid
      (left := leftWord) (right := rightWord)
      (by
        intro tested
        simpa [leftWord, S5_107.listWordOfCons, Word.toList] using
          leftLimited tested)
      (by
        intro tested
        simpa [rightWord, S5_107.listWordOfCons, Word.toList] using
          rightLimited tested)
      (by simpa [identity, leftWord, rightWord] using valid)
      selected
    simpa [leftWord, rightWord, S5_107.listWordOfCons,
      Word.toList] using equal
  have sameFirstMembers : forall selected,
      selected ∈ leftFirsts ↔ selected ∈ rightFirsts := by
    intro selected
    rw [leftSplit.firstMem selected,
      rightSplit.firstMem selected, counts selected]
  have firstEqual : leftFirsts = rightFirsts :=
    natList_eq_of_pairwise_le_nodup_mem_iff
      leftSplit.firstOrdered rightSplit.firstOrdered
      leftSplit.firstNodup rightSplit.firstNodup sameFirstMembers
  subst rightFirsts
  have sameEventMembers : forall selected,
      selected ∈ leftEvents ↔ selected ∈ rightEvents := by
    intro selected
    rw [leftSplit.eventMem selected,
      rightSplit.eventMem selected, counts selected]
  have capped : forall selected,
      RouteBlockProbe.cappedMultiplicity leftWord selected =
        RouteBlockProbe.cappedMultiplicity rightWord selected :=
    fun selected =>
      RouteBlockProbe.valid_cappedMultiplicity
        identity (by simpa [identity, leftWord, rightWord] using valid)
        selected
  have simpleOrder : forall {x y},
      x ≠ y → x ∈ leftEvents → y ∈ leftEvents →
      x ∉ leftFirsts → y ∉ leftFirsts →
      (EndpointChronology.Before leftEvents x y ↔
        EndpointChronology.Before rightEvents x y) := by
    intro x y different xMember yMember xSimple ySimple
    have leftBridge := simplePrecedes_iff_before_events
      leftSplit different xSimple ySimple xMember yMember
    have rightBridge := simplePrecedes_iff_before_events
      rightSplit different xSimple ySimple
      ((sameEventMembers x).mp xMember)
      ((sameEventMembers y).mp yMember)
    have probe := RouteBlockProbe.valid_simplePrecedes
      identity (by simpa [identity, leftWord, rightWord] using valid)
      capped x y
    simpa [identity, leftWord, rightWord] using
      leftBridge.symm.trans (probe.trans rightBridge)
  have lastGap : forall {x y},
      x ≠ y → x ∈ leftEvents → y ∈ leftEvents →
      x ∈ leftFirsts → y ∉ leftFirsts →
      (EndpointChronology.Before leftEvents x y ↔
        EndpointChronology.Before rightEvents x y) := by
    intro x y different xMember yMember xMultiple ySimple
    have leftBridge := multipleLastBeforeSimple_iff_before_events
      leftSplit different xMultiple ySimple xMember yMember
    have rightBridge := multipleLastBeforeSimple_iff_before_events
      rightSplit different xMultiple ySimple
      ((sameEventMembers x).mp xMember)
      ((sameEventMembers y).mp yMember)
    have probe :=
      RouteBlockProbe.valid_multipleLastBeforeSimple
        identity (by simpa [identity, leftWord, rightWord] using valid)
        capped x y
    simpa [identity, leftWord, rightWord] using
      leftBridge.symm.trans (probe.trans rightBridge)
  have eventsEqual : leftEvents = rightEvents :=
    zeroEvents_eq_of_probes leftFirsts leftEvents rightEvents
      leftSplit.eventNodup rightSplit.eventNodup sameEventMembers
      leftSplit.eventNormal rightSplit.eventNormal
      simpleOrder lastGap
  rw [leftSplit.shape, rightSplit.shape, eventsEqual]

/-- Two nonempty cap-two zero endpoints carrying the same route semantic key
are literally equal.  Connectedness is retained in the public signature
because this theorem is consumed by component pivots; it is not needed by
the stronger list-level uniqueness argument above. -/
theorem zeroEndpoint_unique
    {left right : List Nat}
    (leftNonempty : left ≠ [])
    (rightNonempty : right ≠ [])
    (leftLimited : forall selected, left.count selected ≤ 2)
    (rightLimited : forall selected, right.count selected ≤ 2)
    (_leftConnected : ConnectedComponentSupportConnected left)
    (_rightConnected : ConnectedComponentSupportConnected right)
    (leftZero : endpointMeasure left = ⟨0, 0, 0⟩)
    (rightZero : endpointMeasure right = ⟨0, 0, 0⟩)
    (same : EndpointSemanticAgreement left right) :
    left = right := by
  obtain ⟨leftHead, leftTail, leftShape⟩ :=
    List.exists_cons_of_ne_nil leftNonempty
  obtain ⟨rightHead, rightTail, rightShape⟩ :=
    List.exists_cons_of_ne_nil rightNonempty
  have catalogueValid := same.blockTheory
    leftHead leftTail rightHead rightTail leftShape rightShape
  rw [leftShape, rightShape]
  apply zeroEndpoint_unique_of_block_valid
  · intro selected
    simpa [leftShape] using leftLimited selected
  · intro selected
    simpa [rightShape] using rightLimited selected
  · simpa [leftShape] using leftZero
  · simpa [rightShape] using rightZero
  · exact catalogueValid

end CapTwoRTCRoute
end SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
