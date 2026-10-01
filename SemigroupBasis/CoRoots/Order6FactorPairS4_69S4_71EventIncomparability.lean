import SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71EventOrder

/-!
# Incomparable endpoint events for `S4_69 x S4_71`

The maximal common event order permits a genuine non-quadratic crossing:
the sole occurrence of one letter can cross the first occurrence of a
different quadratic letter.  This module proves that this is the only such
case.

The proof reads the block component of `SameJointSignature` literally.
Chronological order of two simple events is exactly `SimplePrecedes`, while
chronological order of a last event before a simple event is exactly
`MultipleLastBeforeSimple`.  Both relations are retained by the block
signature.  Consequently simple/simple and simple/last disagreements are
impossible.  First/last endpoints of one letter are already ordered in both
words by `first_before_last_encoded`, so the existing distinct-decoding
theorem excludes same-letter pairs.
-/

namespace SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71

open SemigroupBasis

namespace EventIncomparability

private def pairKeep (x y value : Nat) : Bool :=
  value == x || value == y

private def pairProjection
    (letters : List Nat) (x y : Nat) : List Nat :=
  letters.filter (pairKeep x y)

private def orderScanFrom
    (x y : Nat) (initial : S5_793Invariant.OrderGapState)
    (letters : List Nat) : S5_793Invariant.OrderGapState :=
  letters.foldl
    (fun state letter =>
      S5_793Invariant.orderStep state
        (S5_793Invariant.orderSymbol x y letter))
    initial

private theorem orderScanFrom_pairProjection
    (x y : Nat) :
    ∀ (letters : List Nat)
      (initial : S5_793Invariant.OrderGapState),
      orderScanFrom x y initial letters =
        orderScanFrom x y initial (pairProjection letters x y)
  | [], _ => rfl
  | letter :: rest, initial => by
      by_cases isX : letter = x
      · subst letter
        have induction :=
          orderScanFrom_pairProjection x y rest
            (S5_793Invariant.orderStep initial
              (S5_793Invariant.orderSymbol x y x))
        simpa [orderScanFrom, pairProjection, pairKeep] using induction
      · by_cases isY : letter = y
        · subst letter
          have induction :=
            orderScanFrom_pairProjection x y rest
              (S5_793Invariant.orderStep initial
                (S5_793Invariant.orderSymbol x y y))
          simpa [orderScanFrom, pairProjection, pairKeep, isX]
            using induction
        · have induction :=
            orderScanFrom_pairProjection x y rest initial
          simpa [orderScanFrom, pairProjection, pairKeep,
            S5_793Invariant.orderSymbol, isX, isY] using induction

private theorem pairProjection_count_of_kept
    (letters : List Nat) (x y selected : Nat)
    (kept : pairKeep x y selected = true) :
    (pairProjection letters x y).count selected =
      letters.count selected := by
  unfold pairProjection
  induction letters with
  | nil => simp
  | cons first rest induction =>
      by_cases equality : first = selected
      · subst first
        simp [kept, induction]
      · by_cases firstKept : pairKeep x y first
        · simp [firstKept, equality, induction]
        · simp [firstKept, equality, induction]

private theorem pairProjection_member
    {letters : List Nat} {x y value : Nat}
    (member : value ∈ pairProjection letters x y) :
    value = x ∨ value = y := by
  have kept := (List.mem_filter.mp member).2
  simpa [pairKeep] using kept

private theorem pairList_length
    {x y : Nat} (different : x ≠ y) :
    ∀ letters : List Nat,
      (∀ value, value ∈ letters → value = x ∨ value = y) →
      letters.length = letters.count x + letters.count y
  | [], _ => by simp
  | value :: rest, onlyPair => by
      have headPair := onlyPair value (by simp)
      have restPair :
          ∀ selected, selected ∈ rest →
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
      ∀ value, value ∈ letters → value = x ∨ value = y) :
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
      ∀ value, value ∈ letters → value = x ∨ value = y) :
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
      · exact Or.inr <| Or.inl rfl
      · simp [different] at yCount
  · rcases secondPair with rfl | rfl
    · rcases thirdPair with rfl | rfl
      · exact Or.inr <| Or.inr rfl
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
    S5_793Invariant.SimplePrecedes word x y ↔
      pairProjection word.toList x y = [x, y] := by
  rw [S5_793Invariant.SimplePrecedes]
  have scanEq :
      S5_793Invariant.orderGapScan word x y =
        orderScanFrom x y .empty
          (pairProjection word.toList x y) := by
    rw [show S5_793Invariant.orderGapScan word x y =
        orderScanFrom x y .empty word.toList by rfl]
    exact orderScanFrom_pairProjection x y word.toList .empty
  rw [scanEq]
  rcases pairProjection_shape_one_one
      word.toList different xCount yCount with shape | shape
  · rw [shape]
    simp [orderScanFrom, S5_793Invariant.orderSymbol,
      S5_793Invariant.orderStep, different, Ne.symm different]
  · rw [shape]
    simp [orderScanFrom, S5_793Invariant.orderSymbol,
      S5_793Invariant.orderStep, different, Ne.symm different]

private theorem multipleLastBeforeSimple_iff_pairProjection
    (word : Word Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : word.toList.count x = 2)
    (yCount : word.toList.count y = 1) :
    S5_793Invariant.MultipleLastBeforeSimple word x y ↔
      pairProjection word.toList x y = [x, x, y] := by
  rw [S5_793Invariant.MultipleLastBeforeSimple]
  have scanEq :
      S5_793Invariant.orderGapScan word x y =
        orderScanFrom x y .empty
          (pairProjection word.toList x y) := by
    rw [show S5_793Invariant.orderGapScan word x y =
        orderScanFrom x y .empty word.toList by rfl]
    exact orderScanFrom_pairProjection x y word.toList .empty
  rw [scanEq]
  rcases pairProjection_shape_two_one
      word.toList different xCount yCount with
    shape | shape | shape
  · rw [shape]
    simp [orderScanFrom, S5_793Invariant.orderSymbol,
      S5_793Invariant.orderStep, different, Ne.symm different]
  · rw [shape]
    simp [orderScanFrom, S5_793Invariant.orderSymbol,
      S5_793Invariant.orderStep, different, Ne.symm different]
  · rw [shape]
    simp [orderScanFrom, S5_793Invariant.orderSymbol,
      S5_793Invariant.orderStep, different, Ne.symm different]

private def eventPairProjection
    (events : List EndpointEvent) (x y : Nat) :
    List EndpointEvent :=
  events.filter (fun event => pairKeep x y event.letter)

@[simp]
private theorem endpointEventAt_letter
    (whole : List Nat) (letter : Nat) (suffix : List Nat) :
    (endpointEventAt whole letter suffix).letter = letter := by
  unfold endpointEventAt
  split
  · rfl
  · split <;> rfl

private theorem endpointEventAt_pairProjection
    (whole suffix : List Nat) {x y letter : Nat}
    (kept : pairKeep x y letter = true) :
    endpointEventAt
        (pairProjection whole x y) letter
        (pairProjection suffix x y) =
      endpointEventAt whole letter suffix := by
  have countEq :=
    pairProjection_count_of_kept whole x y letter kept
  have memberEq :
      letter ∈ pairProjection suffix x y ↔
        letter ∈ suffix := by
    simp [pairProjection, kept]
  by_cases countOne : whole.count letter = 1
  · have projectedCountOne :
        (pairProjection whole x y).count letter = 1 :=
      countEq.trans countOne
    simp [endpointEventAt, countOne, projectedCountOne]
  · have projectedNotOne :
        (pairProjection whole x y).count letter ≠ 1 := by
      intro projectedCountOne
      exact countOne (countEq.symm.trans projectedCountOne)
    by_cases later : letter ∈ suffix
    · have projectedLater :
          letter ∈ pairProjection suffix x y :=
        memberEq.mpr later
      simp [endpointEventAt, countOne, projectedNotOne,
        later, projectedLater]
    · have projectedNotLater :
          letter ∉ pairProjection suffix x y := by
        intro projectedLater
        exact later (memberEq.mp projectedLater)
      simp [endpointEventAt, countOne, projectedNotOne,
        later, projectedNotLater]

private theorem eventPairProjection_encodeAux
    (whole : List Nat) (x y : Nat) :
    ∀ current : List Nat,
      eventPairProjection
          (encodeEndpointEventsAux whole current) x y =
        encodeEndpointEventsAux
          (pairProjection whole x y)
          (pairProjection current x y)
  | [] => rfl
  | letter :: suffix => by
      cases kept : pairKeep x y letter
      · change
          List.filter
              (fun event => pairKeep x y event.letter)
              (endpointEventAt whole letter suffix ::
                encodeEndpointEventsAux whole suffix) =
            encodeEndpointEventsAux
              (pairProjection whole x y)
              (List.filter (pairKeep x y) (letter :: suffix))
        simp only [List.filter_cons, endpointEventAt_letter, kept,
          Bool.false_eq_true, if_false]
        simpa only [eventPairProjection, pairProjection] using
          eventPairProjection_encodeAux whole x y suffix
      · change
          List.filter
              (fun event => pairKeep x y event.letter)
              (endpointEventAt whole letter suffix ::
                encodeEndpointEventsAux whole suffix) =
            encodeEndpointEventsAux
              (pairProjection whole x y)
              (List.filter (pairKeep x y) (letter :: suffix))
        simp only [List.filter_cons, endpointEventAt_letter, kept,
          if_true]
        rw [encodeEndpointEventsAux]
        have headEquality :
            endpointEventAt
                (pairProjection whole x y) letter
                (List.filter (pairKeep x y) suffix) =
              endpointEventAt whole letter suffix := by
          simpa only [pairProjection] using
            endpointEventAt_pairProjection whole suffix kept
        have tailEquality :
            List.filter
                (fun event => pairKeep x y event.letter)
                (encodeEndpointEventsAux whole suffix) =
              encodeEndpointEventsAux
                (pairProjection whole x y)
                (List.filter (pairKeep x y) suffix) := by
          simpa only [eventPairProjection, pairProjection] using
            eventPairProjection_encodeAux whole x y suffix
        rw [headEquality]
        exact congrArg
          (List.cons (endpointEventAt whole letter suffix))
          tailEquality

private theorem eventPairProjection_encode
    (letters : List Nat) (x y : Nat) :
    eventPairProjection (encodeEndpointEvents letters) x y =
      encodeEndpointEvents (pairProjection letters x y) := by
  exact eventPairProjection_encodeAux letters x y letters

private theorem chronologicallyBefore_filter
    {α : Type} {events : List α} {keep : α → Bool}
    {earlier later : α}
    (before :
      EventOrder.ChronologicallyBefore events earlier later)
    (earlierKept : keep earlier = true)
    (laterKept : keep later = true) :
    EventOrder.ChronologicallyBefore
      (events.filter keep) earlier later := by
  induction events with
  | nil =>
      simpa [EventOrder.ChronologicallyBefore] using before
  | cons head tail induction =>
      simp only [EventOrder.ChronologicallyBefore] at before
      rcases before with ⟨rfl, laterMember⟩ | tailBefore
      · have laterFiltered : later ∈ tail.filter keep := by
          simp [laterMember, laterKept]
        simp [earlierKept, EventOrder.ChronologicallyBefore,
          laterFiltered]
      · have tailFiltered :=
          induction tailBefore
        cases keptHead : keep head <;>
          simp [keptHead, EventOrder.ChronologicallyBefore,
            tailFiltered]

private theorem chronologicallyBefore_of_filter
    {α : Type} {events : List α} {keep : α → Bool}
    {earlier later : α}
    (before :
      EventOrder.ChronologicallyBefore
        (events.filter keep) earlier later) :
    EventOrder.ChronologicallyBefore events earlier later := by
  induction events with
  | nil =>
      simpa [EventOrder.ChronologicallyBefore] using before
  | cons head tail induction =>
      cases keptHead : keep head
      · have tailBefore :
          EventOrder.ChronologicallyBefore
            (tail.filter keep) earlier later := by
          simpa [keptHead] using before
        exact Or.inr (induction tailBefore)
      · simp only [List.filter_cons, keptHead, if_true,
          EventOrder.ChronologicallyBefore] at before
        rcases before with ⟨rfl, laterMember⟩ | tailBefore
        · exact Or.inl
            ⟨rfl, (List.mem_filter.mp laterMember).1⟩
        · exact Or.inr (induction tailBefore)

private theorem simple_event_before_iff_pairProjection
    (word : Word Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : word.toList.count x = 1)
    (yCount : word.toList.count y = 1) :
    EventOrder.ChronologicallyBefore
        (encodedWordEvents word) (.simple x) (.simple y) ↔
      pairProjection word.toList x y = [x, y] := by
  have xKept : pairKeep x y x = true := by
    simp [pairKeep]
  have yKept : pairKeep x y y = true := by
    simp [pairKeep]
  constructor
  · intro before
    have filteredBefore :=
      chronologicallyBefore_filter
        (keep := fun event : EndpointEvent =>
          pairKeep x y event.letter)
        before (by simpa using xKept) (by simpa using yKept)
    change
      EventOrder.ChronologicallyBefore
        (eventPairProjection (encodedWordEvents word) x y)
        (.simple x) (.simple y) at filteredBefore
    rw [encodedWordEvents,
      eventPairProjection_encode word.toList x y] at filteredBefore
    rcases pairProjection_shape_one_one
        word.toList different xCount yCount with shape | shape
    · exact shape
    · exfalso
      rw [shape] at filteredBefore
      simpa [encodeEndpointEvents, encodeEndpointEventsAux,
        endpointEventAt, EventOrder.ChronologicallyBefore,
        different, Ne.symm different] using filteredBefore
  · intro shape
    apply chronologicallyBefore_of_filter
      (keep := fun event : EndpointEvent =>
        pairKeep x y event.letter)
    change
      EventOrder.ChronologicallyBefore
        (eventPairProjection (encodedWordEvents word) x y)
        (.simple x) (.simple y)
    rw [encodedWordEvents,
      eventPairProjection_encode word.toList x y, shape]
    simp [encodeEndpointEvents, encodeEndpointEventsAux,
      endpointEventAt, EventOrder.ChronologicallyBefore,
      different, Ne.symm different]

private theorem last_simple_event_before_iff_pairProjection
    (word : Word Nat) {x y : Nat}
    (different : x ≠ y)
    (xCount : word.toList.count x = 2)
    (yCount : word.toList.count y = 1) :
    EventOrder.ChronologicallyBefore
        (encodedWordEvents word) (.last x) (.simple y) ↔
      pairProjection word.toList x y = [x, x, y] := by
  have xKept : pairKeep x y x = true := by
    simp [pairKeep]
  have yKept : pairKeep x y y = true := by
    simp [pairKeep]
  constructor
  · intro before
    have filteredBefore :=
      chronologicallyBefore_filter
        (keep := fun event : EndpointEvent =>
          pairKeep x y event.letter)
        before (by simpa using xKept) (by simpa using yKept)
    change
      EventOrder.ChronologicallyBefore
        (eventPairProjection (encodedWordEvents word) x y)
        (.last x) (.simple y) at filteredBefore
    rw [encodedWordEvents,
      eventPairProjection_encode word.toList x y] at filteredBefore
    rcases pairProjection_shape_two_one
        word.toList different xCount yCount with
      shape | shape | shape
    · exact shape
    · exfalso
      rw [shape] at filteredBefore
      simpa [encodeEndpointEvents, encodeEndpointEventsAux,
        endpointEventAt, EventOrder.ChronologicallyBefore,
        different, Ne.symm different] using filteredBefore
    · exfalso
      rw [shape] at filteredBefore
      simpa [encodeEndpointEvents, encodeEndpointEventsAux,
        endpointEventAt, EventOrder.ChronologicallyBefore,
        different, Ne.symm different] using filteredBefore
  · intro shape
    apply chronologicallyBefore_of_filter
      (keep := fun event : EndpointEvent =>
        pairKeep x y event.letter)
    change
      EventOrder.ChronologicallyBefore
        (eventPairProjection (encodedWordEvents word) x y)
        (.last x) (.simple y)
    rw [encodedWordEvents,
      eventPairProjection_encode word.toList x y, shape]
    simp [encodeEndpointEvents, encodeEndpointEventsAux,
      endpointEventAt, EventOrder.ChronologicallyBefore,
      different, Ne.symm different]

/-- On a reduced word, the block scanner's order of two simple letters is
exactly the chronological order of their simple endpoint events. -/
theorem simplePrecedes_iff_simple_event_before
    (word : Word Nat) {x y : Nat}
    (different : x ≠ y)
    (xMember : EndpointEvent.simple x ∈ encodedWordEvents word)
    (yMember : EndpointEvent.simple y ∈ encodedWordEvents word) :
    S5_793Invariant.SimplePrecedes word x y ↔
      EventOrder.ChronologicallyBefore
        (encodedWordEvents word) (.simple x) (.simple y) := by
  have xCount : word.toList.count x = 1 :=
    (simple_mem_encodeEndpointEvents_iff word.toList x).1 xMember
  have yCount : word.toList.count y = 1 :=
    (simple_mem_encodeEndpointEvents_iff word.toList y).1 yMember
  exact
    (simplePrecedes_iff_pairProjection
      word different xCount yCount).trans
        (simple_event_before_iff_pairProjection
          word different xCount yCount).symm

/-- On a two-limited word, the block scanner says that the last occurrence
of `x` is before the simple letter `y` exactly when the corresponding last
and simple endpoint events occur in that order. -/
theorem multipleLastBeforeSimple_iff_last_simple_event_before
    (word : Word Nat)
    (twoLimited : ∀ tested, word.toList.count tested ≤ 2)
    {x y : Nat}
    (different : x ≠ y)
    (lastMember : EndpointEvent.last x ∈ encodedWordEvents word)
    (simpleMember : EndpointEvent.simple y ∈ encodedWordEvents word) :
    S5_793Invariant.MultipleLastBeforeSimple word x y ↔
      EventOrder.ChronologicallyBefore
        (encodedWordEvents word) (.last x) (.simple y) := by
  have xCount : word.toList.count x = 2 :=
    (last_mem_encodeEndpointEvents_iff twoLimited x).1 lastMember
  have yCount : word.toList.count y = 1 :=
    (simple_mem_encodeEndpointEvents_iff word.toList y).1 simpleMember
  exact
    (multipleLastBeforeSimple_iff_pairProjection
      word different xCount yCount).trans
        (last_simple_event_before_iff_pairProjection
          word different xCount yCount).symm

/-- Equal joint signatures preserve the chronological order of any two
distinct simple endpoint events. -/
theorem simple_event_order_iff_of_sameJointSignature
    {left right : Word Nat}
    (same : SameJointSignature left right)
    (leftTwoLimited :
      ∀ tested, left.toList.count tested ≤ 2)
    (rightTwoLimited :
      ∀ tested, right.toList.count tested ≤ 2)
    {x y : Nat}
    (different : x ≠ y)
    (xMember : EndpointEvent.simple x ∈ encodedWordEvents left)
    (yMember : EndpointEvent.simple y ∈ encodedWordEvents left) :
    EventOrder.ChronologicallyBefore
        (encodedWordEvents left) (.simple x) (.simple y) ↔
      EventOrder.ChronologicallyBefore
        (encodedWordEvents right) (.simple x) (.simple y) := by
  have permutation :=
    encodedWordEvents_perm same leftTwoLimited rightTwoLimited
  have xTarget : EndpointEvent.simple x ∈ encodedWordEvents right :=
    permutation.mem_iff.mp xMember
  have yTarget : EndpointEvent.simple y ∈ encodedWordEvents right :=
    permutation.mem_iff.mp yMember
  exact
    (simplePrecedes_iff_simple_event_before
      left different xMember yMember).symm.trans <|
      (same.block.simpleSequence x y).trans <|
        simplePrecedes_iff_simple_event_before
          right different xTarget yTarget

/-- Equal joint signatures preserve whether the last occurrence of a
quadratic letter lies before a distinct simple letter. -/
theorem last_simple_event_order_iff_of_sameJointSignature
    {left right : Word Nat}
    (same : SameJointSignature left right)
    (leftTwoLimited :
      ∀ tested, left.toList.count tested ≤ 2)
    (rightTwoLimited :
      ∀ tested, right.toList.count tested ≤ 2)
    {x y : Nat}
    (different : x ≠ y)
    (lastMember : EndpointEvent.last x ∈ encodedWordEvents left)
    (simpleMember : EndpointEvent.simple y ∈ encodedWordEvents left) :
    EventOrder.ChronologicallyBefore
        (encodedWordEvents left) (.last x) (.simple y) ↔
      EventOrder.ChronologicallyBefore
        (encodedWordEvents right) (.last x) (.simple y) := by
  have permutation :=
    encodedWordEvents_perm same leftTwoLimited rightTwoLimited
  have lastTarget : EndpointEvent.last x ∈ encodedWordEvents right :=
    permutation.mem_iff.mp lastMember
  have simpleTarget : EndpointEvent.simple y ∈ encodedWordEvents right :=
    permutation.mem_iff.mp simpleMember
  exact
    (multipleLastBeforeSimple_iff_last_simple_event_before
      left leftTwoLimited different lastMember simpleMember).symm.trans <|
      (same.block.lastGap x y).trans <|
        multipleLastBeforeSimple_iff_last_simple_event_before
          right rightTwoLimited different lastTarget simpleTarget

private theorem incomparable_false_of_preserved_order
    {α : Type} {source target : List α} {eventA eventB : α}
    (sourceNodup : source.Nodup)
    (targetNodup : target.Nodup)
    (different : eventA ≠ eventB)
    (eventASource : eventA ∈ source)
    (eventBSource : eventB ∈ source)
    (eventATarget : eventA ∈ target)
    (eventBTarget : eventB ∈ target)
    (preserved :
      EventOrder.ChronologicallyBefore source eventA eventB ↔
        EventOrder.ChronologicallyBefore target eventA eventB)
    (incomparable :
      SemigroupBasis.Normalization.EventLinearExtensions.Incomparable
        (EventOrder.CommonPrecedes source target) eventA eventB) :
    False := by
  rcases
      EventOrder.incomparable_order_disagreement
        sourceNodup targetNodup different
        eventASource eventBSource eventATarget eventBTarget
        incomparable with
    sourceForward | sourceReverse
  · have targetForward := preserved.mp sourceForward.1
    exact
      (EventOrder.chronologicallyBefore_asymm
        targetNodup targetForward) sourceForward.2
  · have sourceForward := preserved.mpr sourceReverse.2
    exact
      (EventOrder.chronologicallyBefore_asymm
        sourceNodup sourceForward) sourceReverse.1

/-- Complete evidence attached to the role classification of an
incomparable pair. -/
structure IncomparableEventClassification
    (left right : Word Nat)
    (eventA eventB : EndpointEvent) : Prop where
  decodedDistinct :
    eventA.letter ≠ eventB.letter
  roles :
    (left.toList.count eventA.letter = 2 ∧
      left.toList.count eventB.letter = 2 ∧
      right.toList.count eventA.letter = 2 ∧
      right.toList.count eventB.letter = 2) ∨
    ∃ simpleLetter firstLetter,
      simpleLetter ≠ firstLetter ∧
        ((eventA = .simple simpleLetter ∧
            eventB = .first firstLetter) ∨
          (eventA = .first firstLetter ∧
            eventB = .simple simpleLetter))
  oppositeOrientation :
    (EventOrder.ChronologicallyBefore
          (encodedWordEvents left) eventA eventB ∧
        EventOrder.ChronologicallyBefore
          (encodedWordEvents right) eventB eventA) ∨
      (EventOrder.ChronologicallyBefore
          (encodedWordEvents left) eventB eventA ∧
        EventOrder.ChronologicallyBefore
          (encodedWordEvents right) eventA eventB)

/-- The only non-quadratic incomparable pair consists of one simple event
and the first endpoint of a different quadratic letter.

The conclusion also records exact multiplicity two in both words for the
quadratic/quadratic branch, decoded-letter distinctness, and the two
opposite chronological orientations. -/
theorem classify_incomparable_joint_events
    {left right : Word Nat}
    (same : SameJointSignature left right)
    (leftTwoLimited :
      ∀ tested, left.toList.count tested ≤ 2)
    (rightTwoLimited :
      ∀ tested, right.toList.count tested ≤ 2)
    {eventA eventB : EndpointEvent}
    (different : eventA ≠ eventB)
    (eventAMember : eventA ∈ encodedWordEvents left)
    (eventBMember : eventB ∈ encodedWordEvents left)
    (incomparable :
      SemigroupBasis.Normalization.EventLinearExtensions.Incomparable
        (jointEventPrecedes left right) eventA eventB) :
    IncomparableEventClassification left right eventA eventB := by
  have eventPermutation :=
    encodedWordEvents_perm same leftTwoLimited rightTwoLimited
  have eventATarget : eventA ∈ encodedWordEvents right :=
    eventPermutation.mem_iff.mp eventAMember
  have eventBTarget : eventB ∈ encodedWordEvents right :=
    eventPermutation.mem_iff.mp eventBMember
  have decodedDistinct :
      eventA.letter ≠ eventB.letter :=
    incomparable_decode_distinct
      same leftTwoLimited rightTwoLimited
      different eventAMember eventBMember incomparable
  have oppositeOrientation :
      (EventOrder.ChronologicallyBefore
            (encodedWordEvents left) eventA eventB ∧
          EventOrder.ChronologicallyBefore
            (encodedWordEvents right) eventB eventA) ∨
        (EventOrder.ChronologicallyBefore
            (encodedWordEvents left) eventB eventA ∧
          EventOrder.ChronologicallyBefore
            (encodedWordEvents right) eventA eventB) := by
    exact
      EventOrder.incomparable_order_disagreement
        (encodedWordEvents_nodup leftTwoLimited)
        (encodedWordEvents_nodup rightTwoLimited)
        different eventAMember eventBMember
        eventATarget eventBTarget incomparable
  refine ⟨decodedDistinct, ?_, oppositeOrientation⟩
  cases eventA with
  | simple letterA =>
      cases eventB with
      | simple letterB =>
          have letterDifferent : letterA ≠ letterB := by
            simpa using decodedDistinct
          have preserved :=
            simple_event_order_iff_of_sameJointSignature
              same leftTwoLimited rightTwoLimited
              letterDifferent eventAMember eventBMember
          exact
            (incomparable_false_of_preserved_order
              (encodedWordEvents_nodup leftTwoLimited)
              (encodedWordEvents_nodup rightTwoLimited)
              different eventAMember eventBMember
              eventATarget eventBTarget preserved
              (by simpa [jointEventPrecedes] using incomparable)).elim
      | first letterB =>
          exact Or.inr
            ⟨letterA, letterB, by simpa using decodedDistinct,
              Or.inl ⟨rfl, rfl⟩⟩
      | last letterB =>
          have letterDifferent : letterB ≠ letterA := by
            exact Ne.symm (by simpa using decodedDistinct)
          have preserved :=
            last_simple_event_order_iff_of_sameJointSignature
              same leftTwoLimited rightTwoLimited
              letterDifferent eventBMember eventAMember
          have swapped :
              SemigroupBasis.Normalization.EventLinearExtensions.Incomparable
                (jointEventPrecedes left right)
                (.last letterB) (.simple letterA) :=
            ⟨incomparable.2, incomparable.1⟩
          exact
            (incomparable_false_of_preserved_order
              (encodedWordEvents_nodup leftTwoLimited)
              (encodedWordEvents_nodup rightTwoLimited)
              (by intro equality; cases equality)
              eventBMember eventAMember eventBTarget eventATarget
              preserved
              (by simpa [jointEventPrecedes] using swapped)).elim
  | first letterA =>
      have leftACount : left.toList.count letterA = 2 :=
        (first_mem_encodeEndpointEvents_iff
          leftTwoLimited letterA).1 eventAMember
      have rightACount : right.toList.count letterA = 2 := by
        rw [← reduced_count_eq_of_sameJointSignature
          same leftTwoLimited rightTwoLimited letterA]
        exact leftACount
      cases eventB with
      | simple letterB =>
          exact Or.inr
            ⟨letterB, letterA, by
                exact Ne.symm (by simpa using decodedDistinct),
              Or.inr ⟨rfl, rfl⟩⟩
      | first letterB =>
          have leftBCount : left.toList.count letterB = 2 :=
            (first_mem_encodeEndpointEvents_iff
              leftTwoLimited letterB).1 eventBMember
          have rightBCount : right.toList.count letterB = 2 := by
            rw [← reduced_count_eq_of_sameJointSignature
              same leftTwoLimited rightTwoLimited letterB]
            exact leftBCount
          exact Or.inl
            ⟨leftACount, leftBCount, rightACount, rightBCount⟩
      | last letterB =>
          have leftBCount : left.toList.count letterB = 2 :=
            (last_mem_encodeEndpointEvents_iff
              leftTwoLimited letterB).1 eventBMember
          have rightBCount : right.toList.count letterB = 2 := by
            rw [← reduced_count_eq_of_sameJointSignature
              same leftTwoLimited rightTwoLimited letterB]
            exact leftBCount
          exact Or.inl
            ⟨leftACount, leftBCount, rightACount, rightBCount⟩
  | last letterA =>
      have leftACount : left.toList.count letterA = 2 :=
        (last_mem_encodeEndpointEvents_iff
          leftTwoLimited letterA).1 eventAMember
      have rightACount : right.toList.count letterA = 2 := by
        rw [← reduced_count_eq_of_sameJointSignature
          same leftTwoLimited rightTwoLimited letterA]
        exact leftACount
      cases eventB with
      | simple letterB =>
          have letterDifferent : letterA ≠ letterB := by
            simpa using decodedDistinct
          have preserved :=
            last_simple_event_order_iff_of_sameJointSignature
              same leftTwoLimited rightTwoLimited
              letterDifferent eventAMember eventBMember
          exact
            (incomparable_false_of_preserved_order
              (encodedWordEvents_nodup leftTwoLimited)
              (encodedWordEvents_nodup rightTwoLimited)
              different eventAMember eventBMember
              eventATarget eventBTarget preserved
              (by simpa [jointEventPrecedes] using incomparable)).elim
      | first letterB =>
          have leftBCount : left.toList.count letterB = 2 :=
            (first_mem_encodeEndpointEvents_iff
              leftTwoLimited letterB).1 eventBMember
          have rightBCount : right.toList.count letterB = 2 := by
            rw [← reduced_count_eq_of_sameJointSignature
              same leftTwoLimited rightTwoLimited letterB]
            exact leftBCount
          exact Or.inl
            ⟨leftACount, leftBCount, rightACount, rightBCount⟩
      | last letterB =>
          have leftBCount : left.toList.count letterB = 2 :=
            (last_mem_encodeEndpointEvents_iff
              leftTwoLimited letterB).1 eventBMember
          have rightBCount : right.toList.count letterB = 2 := by
            rw [← reduced_count_eq_of_sameJointSignature
              same leftTwoLimited rightTwoLimited letterB]
            exact leftBCount
          exact Or.inl
            ⟨leftACount, leftBCount, rightACount, rightBCount⟩

end EventIncomparability

end SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71
