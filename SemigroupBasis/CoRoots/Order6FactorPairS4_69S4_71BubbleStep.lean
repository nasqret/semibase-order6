import SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71ForcedDirection
import SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71CoveredSimpleFirstSwap

namespace SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71

open SemigroupBasis

/-!
# One event-resolved bubble step

The original width-free draft used

`right.toList.idxOf e < right.toList.idxOf x`

as the sole assertion that the adjacent occurrences `x, e` are inverted.
That is insufficient: `List.idxOf` names first occurrences, while the
displayed occurrence can be a last endpoint.  The three-letter word
`[0, 1, 0]` records the defect exactly.

The corrected contract below names both endpoint events and records their
opposite chronological orientations.  The raw `idxOf` comparison remains
only as a projection used by the already proved `forcedDirection` theorem
in the `simple, first` branch.

All constructive branches are discharged here except one isolated
mathematical input: coverage of an event-resolved `first, simple` crossing.
The integrated forced-direction theorem has the opposite source orientation,
so treating it as if it supplied this branch would reintroduce the defect.
-/

/-! ## Counterexample to the raw first-occurrence contract -/

/-- Source and target for the smallest raw-`idxOf` counterexample. -/
def rawIdxOfCounterexampleSource : Word Nat :=
  ⟨0, [1, 0]⟩

/-- The adjacent exchange requested by the defective contract. -/
def rawIdxOfCounterexampleSwap : Word Nat :=
  ⟨0, [0, 1]⟩

private theorem rawIdxOfCounterexampleSource_twoLimited :
    ∀ tested,
      rawIdxOfCounterexampleSource.toList.count tested ≤ 2 := by
  intro tested
  by_cases zero : tested = 0
  · subst tested
    decide
  · by_cases one : tested = 1
    · subst tested
      decide
    · change [0, 1, 0].count tested ≤ 2
      simp [zero, one, Ne.symm zero, Ne.symm one]

private theorem rawIdxOfCounterexampleSwap_twoLimited :
    ∀ tested,
      rawIdxOfCounterexampleSwap.toList.count tested ≤ 2 := by
  intro tested
  by_cases zero : tested = 0
  · subst tested
    decide
  · by_cases one : tested = 1
    · subst tested
      decide
    · change [0, 0, 1].count tested ≤ 2
      simp [zero, one, Ne.symm zero, Ne.symm one]

/-- Fable's original premises, with the pinned Lean 4.28 list API. -/
def RawIdxOfBubblePremises
    (left right : Word Nat) (j x e : Nat) : Prop :=
  SameJointSignature left right ∧
    (∀ tested, left.toList.count tested ≤ 2) ∧
    (∀ tested, right.toList.count tested ≤ 2) ∧
    0 < j ∧
    j + 1 ≤ left.toList.length ∧
    left.toList[j - 1]? = some x ∧
    left.toList[j]? = some e ∧
    right.toList.idxOf e < right.toList.idxOf x

/-- The raw premises hold when the displayed `e` is the last occurrence of
`0`, even though the two displayed endpoint events are not inverted. -/
theorem rawIdxOfBubblePremises_counterexample :
    RawIdxOfBubblePremises
      rawIdxOfCounterexampleSource
      rawIdxOfCounterexampleSource
      2 1 0 := by
  refine
    ⟨SameJointSignature.refl _,
      rawIdxOfCounterexampleSource_twoLimited,
      rawIdxOfCounterexampleSource_twoLimited,
      ?_, ?_, ?_, ?_, ?_⟩ <;>
    decide

/-- The requested exchange changes the retained last-before-simple event
order, hence cannot preserve the joint signature. -/
theorem rawIdxOfCounterexampleSwap_not_same :
    ¬ SameJointSignature
      rawIdxOfCounterexampleSwap
      rawIdxOfCounterexampleSource := by
  intro same
  have lastMember :
      EndpointEvent.last 0 ∈
        encodedWordEvents rawIdxOfCounterexampleSwap := by
    decide
  have simpleMember :
      EndpointEvent.simple 1 ∈
        encodedWordEvents rawIdxOfCounterexampleSwap := by
    decide
  have preserved :=
    EventIncomparability.last_simple_event_order_iff_of_sameJointSignature
      same
      rawIdxOfCounterexampleSwap_twoLimited
      rawIdxOfCounterexampleSource_twoLimited
      (x := 0) (y := 1)
      (by decide) lastMember simpleMember
  have sourceBefore :
      EventOrder.ChronologicallyBefore
        (encodedWordEvents rawIdxOfCounterexampleSwap)
        (.last 0) (.simple 1) := by
    change
      EventOrder.ChronologicallyBefore
        [EndpointEvent.first 0, EndpointEvent.last 0,
          EndpointEvent.simple 1]
        (EndpointEvent.last 0) (EndpointEvent.simple 1)
    simp [EventOrder.ChronologicallyBefore]
  have targetNotBefore :
      ¬ EventOrder.ChronologicallyBefore
        (encodedWordEvents rawIdxOfCounterexampleSource)
        (.last 0) (.simple 1) := by
    change
      ¬ EventOrder.ChronologicallyBefore
          [EndpointEvent.first 0, EndpointEvent.simple 1,
            EndpointEvent.last 0]
          (EndpointEvent.last 0) (EndpointEvent.simple 1)
    simp [EventOrder.ChronologicallyBefore]
  exact targetNotBefore (preserved.mp sourceBefore)

/-- Consequently the exact conclusion of the raw draft fails on the
three-letter counterexample. -/
theorem rawIdxOfBubbleConclusion_counterexample :
    ¬ ∃ next : Word Nat,
      Derives basis rawIdxOfCounterexampleSource next ∧
        SameJointSignature next rawIdxOfCounterexampleSource ∧
        next.toList =
          rawIdxOfCounterexampleSource.toList.take (2 - 1) ++
            0 :: 1 ::
              rawIdxOfCounterexampleSource.toList.drop (2 + 1) := by
  rintro ⟨next, _derives, nextSame, nextShape⟩
  apply rawIdxOfCounterexampleSwap_not_same
  have nextEq : next = rawIdxOfCounterexampleSwap := by
    apply Word.toList_injective
    calc
      next.toList =
          rawIdxOfCounterexampleSource.toList.take (2 - 1) ++
            0 :: 1 ::
              rawIdxOfCounterexampleSource.toList.drop (2 + 1) :=
        nextShape
      _ = rawIdxOfCounterexampleSwap.toList := by
        decide
  simpa [nextEq] using nextSame

/-! ## Corrected event-resolved contract -/

/-- Structural facts attached to a first endpoint at a specified position.
These are intentionally explicit until the encoding-to-position projection
is isolated as its own list lemma. -/
structure FirstEndpointAt
    (letters : List Nat) (position letter : Nat) : Prop where
  noEarlier :
    ∀ tested, tested < position →
      letters[tested]? ≠ some letter
  later :
    letter ∈ letters.drop (position + 1)

/-- A genuinely inverted adjacent occurrence pair.

`sourceForward` and `targetReverse` are the decisive correction: they refer
to occurrence-resolved endpoint events.  The raw first-occurrence comparison
needed by `forcedDirection` is projected from `targetReverse` inside
`bubble_step`; callers never have to supply the defective letter-level API.
-/
structure EventResolvedAdjacentInversion
    (left right : Word Nat) (position x e : Nat) where
  eventX : EndpointEvent
  eventE : EndpointEvent
  xAt :
    left.toList[position]? = some x
  eAt :
    left.toList[position + 1]? = some e
  eventXAt :
    (encodedWordEvents left)[position]? = some eventX
  eventEAt :
    (encodedWordEvents left)[position + 1]? = some eventE
  xDecoded :
    eventX.letter = x
  eDecoded :
    eventE.letter = e
  different :
    eventX ≠ eventE
  sourceForward :
    EventOrder.ChronologicallyBefore
      (encodedWordEvents left) eventX eventE
  targetReverse :
    EventOrder.ChronologicallyBefore
      (encodedWordEvents right) eventE eventX
  xFirst :
    eventX = .first x →
      FirstEndpointAt left.toList position x
  eFirst :
    eventE = .first e →
      FirstEndpointAt left.toList (position + 1) e

/-- The raw counterexample cannot satisfy the corrected event inversion:
its source and target event lists are identical. -/
theorem rawIdxOfCounterexample_not_eventResolved :
    EventResolvedAdjacentInversion
      rawIdxOfCounterexampleSource
      rawIdxOfCounterexampleSource
      1 1 0 → False := by
  intro site
  exact
    (EventOrder.chronologicallyBefore_asymm
      (encodedWordEvents_nodup
        rawIdxOfCounterexampleSource_twoLimited)
      site.sourceForward)
      site.targetReverse

private theorem splitAtAdjacent
    {letters : List Nat} {position x e : Nat}
    (xAt : letters[position]? = some x)
    (eAt : letters[position + 1]? = some e) :
    letters =
      letters.take position ++
        x :: e :: letters.drop (position + 2) := by
  obtain ⟨positionInBounds, valueAtPosition⟩ :=
    List.getElem?_eq_some_iff.mp xAt
  obtain ⟨nextInBounds, valueAtNext⟩ :=
    List.getElem?_eq_some_iff.mp eAt
  have splitAtX :
      letters =
        letters.take position ++
          x :: letters.drop (position + 1) := by
    calc
      letters = letters.take position ++ letters.drop position :=
        (List.take_append_drop position letters).symm
      _ = letters.take position ++ x :: letters.drop (position + 1) := by
        congr 1
        simpa [valueAtPosition] using
          List.drop_eq_getElem_cons positionInBounds
  have dropAfterX :
      letters.drop (position + 1) =
        e :: letters.drop (position + 2) := by
    simpa [valueAtNext, Nat.add_assoc] using
      (List.drop_eq_getElem_cons nextInBounds)
  calc
    letters =
        letters.take position ++
          x :: letters.drop (position + 1) :=
      splitAtX
    _ =
        letters.take position ++
          x :: e :: letters.drop (position + 2) := by
      rw [dropAfterX]

theorem coveredAt_guard_members
    {letters : List Nat} {position : Nat}
    (covered : CoveredAt letters position) :
    ∃ guard,
      guard ∈ letters.take position ∧
        guard ∈ letters.drop (position + 2) := by
  rcases covered with
    ⟨guard, past, future, _guardCount, pastBefore,
      siteBeforeFuture, futureInBounds, guardAtPast, guardAtFuture⟩
  refine ⟨guard, ?_, ?_⟩
  · obtain ⟨pastInBounds, valueAtPast⟩ :=
      List.getElem?_eq_some_iff.mp guardAtPast
    apply List.mem_take_iff_getElem.mpr
    exact ⟨past, by omega, valueAtPast⟩
  · obtain ⟨futureInBounds', valueAtFuture⟩ :=
      List.getElem?_eq_some_iff.mp guardAtFuture
    apply List.mem_drop_iff_getElem.mpr
    refine ⟨future - (position + 2), ?_, ?_⟩
    · omega
    · have indexEquality :
          position + 2 + (future - (position + 2)) = future := by
        omega
      simpa [indexEquality] using valueAtFuture

theorem firstEndpoint_later_after_adjacent
    {letters : List Nat} {position x e : Nat}
    (different : x ≠ e)
    (eAt : letters[position + 1]? = some e)
    (first : FirstEndpointAt letters position x) :
    x ∈ letters.drop (position + 2) := by
  obtain ⟨nextInBounds, valueAtNext⟩ :=
    List.getElem?_eq_some_iff.mp eAt
  have dropAfterX :
      letters.drop (position + 1) =
        e :: letters.drop (position + 2) := by
    simpa [valueAtNext, Nat.add_assoc] using
      (List.drop_eq_getElem_cons nextInBounds)
  have laterInDrop := first.later
  rw [dropAfterX] at laterInDrop
  rcases List.mem_cons.mp laterInDrop with equal | later
  · exact (different equal).elim
  · exact later

private theorem chronologicallyBefore_map
    {α β : Type} (map : α → β)
    {events : List α} {earlier later : α}
    (before :
      EventOrder.ChronologicallyBefore events earlier later) :
    EventOrder.ChronologicallyBefore
      (events.map map) (map earlier) (map later) := by
  induction events with
  | nil =>
      simpa [EventOrder.ChronologicallyBefore] using before
  | cons head tail inductionHypothesis =>
      simp only [EventOrder.ChronologicallyBefore] at before ⊢
      rcases before with ⟨rfl, laterMember⟩ | tailBefore
      · exact
          Or.inl
            ⟨rfl, List.mem_map_of_mem laterMember⟩
      · exact Or.inr (inductionHypothesis tailBefore)

private theorem rawChronologicalOfEncoded
    {letters : List Nat} {earlier later : EndpointEvent}
    (before :
      EventOrder.ChronologicallyBefore
        (encodeEndpointEvents letters) earlier later) :
    EventOrder.ChronologicallyBefore
      letters earlier.letter later.letter := by
  have mapped :=
    chronologicallyBefore_map EndpointEvent.letter before
  change
    EventOrder.ChronologicallyBefore
      (decodeEndpointEvents (encodeEndpointEvents letters))
      earlier.letter later.letter at mapped
  simpa using mapped

private theorem idxOf_lt_idxOf_of_chronologicallyBefore_right_count_one :
    ∀ {letters : List Nat} {earlier later : Nat},
      EventOrder.ChronologicallyBefore letters earlier later →
        letters.count later = 1 →
          letters.idxOf earlier < letters.idxOf later
  | [], _, _, before, _ => by
      simpa [EventOrder.ChronologicallyBefore] using before
  | head :: tail, earlier, later, before, countOne => by
      simp only [EventOrder.ChronologicallyBefore] at before
      rcases before with ⟨rfl, laterMember⟩ | tailBefore
      · have laterNeEarlier : later ≠ earlier := by
          intro equality
          subst later
          have tailPositive : 0 < tail.count earlier :=
            List.count_pos_iff.mpr laterMember
          simp only [List.count_cons_self] at countOne
          omega
        simp only [List.idxOf_cons, cond_eq_ite, beq_iff_eq,
          if_true, if_neg (Ne.symm laterNeEarlier)]
        omega
      · have laterMember : later ∈ tail :=
          EventOrder.chronologicallyBefore_right_mem tailBefore
        have headNeLater : head ≠ later := by
          intro equality
          subst head
          have tailPositive : 0 < tail.count later :=
            List.count_pos_iff.mpr laterMember
          simp only [List.count_cons_self] at countOne
          omega
        have tailCountOne : tail.count later = 1 := by
          simpa [headNeLater] using countOne
        have tailOrder :=
          idxOf_lt_idxOf_of_chronologicallyBefore_right_count_one
            tailBefore tailCountOne
        by_cases headEqEarlier : head = earlier
        · subst head
          simp only [List.idxOf_cons, cond_eq_ite, beq_iff_eq,
            if_true, if_neg headNeLater]
          omega
        · simp only [List.idxOf_cons, cond_eq_ite, beq_iff_eq,
            if_neg headEqEarlier, if_neg headNeLater]
          omega

/-- Endpoint chronology projects to raw first-occurrence order when the
right-hand event decodes a simple letter. -/
theorem idxOf_lt_idxOf_of_encodedBefore_right_count_one
    {letters : List Nat} {earlier later : EndpointEvent}
    (before :
      EventOrder.ChronologicallyBefore
        (encodeEndpointEvents letters) earlier later)
    (laterCount : letters.count later.letter = 1) :
    letters.idxOf earlier.letter < letters.idxOf later.letter :=
  idxOf_lt_idxOf_of_chronologicallyBefore_right_count_one
    (rawChronologicalOfEncoded before) laterCount

private theorem packageBubbleResult
    {left right : Word Nat} {target : List Nat}
    (same : SameJointSignature left right)
    (listed : ListDerives left.toList target) :
    ∃ next : Word Nat,
      Derives basis left next ∧
        SameJointSignature next right ∧
        next.toList = target := by
  cases left with
  | mk leftHead leftTail =>
      change
        ListDerives (leftHead :: leftTail) target
        at listed
      obtain
        ⟨rightHead, rightTail, targetShape, wordDerivation⟩ :=
        S5_107.ListDerives.from_cons listed
      let next := S5_107.listWordOfCons rightHead rightTail
      have leftNext :
          SameJointSignature
            (S5_107.listWordOfCons leftHead leftTail) next :=
        sameJointSignature_of_factor_valid
          ⟨S5_107.listWordOfCons leftHead leftTail, next⟩
          (fun valuation =>
            wordDerivation.sound modelsS4_69 valuation)
          (fun valuation =>
            wordDerivation.sound modelsS4_71 valuation)
      refine ⟨next, wordDerivation, leftNext.symm.trans same, ?_⟩
      simpa [next, S5_107.listWordOfCons] using targetShape.symm

/-- Package a nonempty list derivation as a word derivation while transporting
the complete joint signature to the resulting word. -/
theorem wordResultOfListDerives
    {left right : Word Nat} {target : List Nat}
    (same : SameJointSignature left right)
    (listed : ListDerives left.toList target) :
    ∃ next : Word Nat,
      Derives basis left next ∧
        SameJointSignature next right ∧
        next.toList = target :=
  packageBubbleResult same listed

private theorem listDerives_of_source_eq
    {source displayed target : List Nat}
    (shape : source = displayed)
    (listed : ListDerives displayed target) :
    ListDerives source target := by
  subst displayed
  exact listed

/-!
The sole residual hypothesis in `bubble_step` is deliberately local:
if the classified source roles are `first x, simple e`, the site is covered.
The opposite role orientation is proved inside the theorem from the
integrated `forcedDirection` result.
-/

/-- One corrected event-resolved bubble step.

The classifier removes the impossible simple/simple and last/simple cases.
Quadratic pairs use the unconditional endpoint swap.  A source
`simple, first` pair is covered by contradiction with `forcedDirection`.
Only the mirror `first, simple` coverage fact remains an explicit input.
-/
theorem bubble_step
    {left right : Word Nat} {position x e : Nat}
    (same : SameJointSignature left right)
    (leftTwo : ∀ tested, left.toList.count tested ≤ 2)
    (rightTwo : ∀ tested, right.toList.count tested ≤ 2)
    (site :
      EventResolvedAdjacentInversion left right position x e)
    (firstSimpleCovered :
      site.eventX = .first x →
        site.eventE = .simple e →
          CoveredAt left.toList position) :
    ∃ next : Word Nat,
      Derives basis left next ∧
        SameJointSignature next right ∧
        next.toList =
          left.toList.take position ++
            e :: x :: left.toList.drop (position + 2) := by
  have eventXMember :
      site.eventX ∈ encodedWordEvents left :=
    EventOrder.chronologicallyBefore_left_mem
      site.sourceForward
  have eventEMember :
      site.eventE ∈ encodedWordEvents left :=
    EventOrder.chronologicallyBefore_right_mem
      site.sourceForward
  have incomparable :
      SemigroupBasis.Normalization.EventLinearExtensions.Incomparable
        (jointEventPrecedes left right)
        site.eventX site.eventE := by
    simpa [jointEventPrecedes] using
      EventOrder.incomparable_of_opposite_orders
        (encodedWordEvents_nodup leftTwo)
        (encodedWordEvents_nodup rightTwo)
        site.sourceForward site.targetReverse
  have classified :=
    EventIncomparability.classify_incomparable_joint_events
      same leftTwo rightTwo site.different
      eventXMember eventEMember incomparable
  have decodedDifferent : x ≠ e := by
    intro equality
    apply classified.decodedDistinct
    calc
      site.eventX.letter = x := site.xDecoded
      _ = e := equality
      _ = site.eventE.letter := site.eDecoded.symm
  have sourceShape :=
    splitAtAdjacent site.xAt site.eAt
  rcases classified.roles with quadratic | simpleFirst
  · rcases quadratic with
      ⟨eventXCount, eventECount, _targetXCount, _targetECount⟩
    have xCount : left.toList.count x = 2 := by
      rw [← site.xDecoded]
      exact eventXCount
    have eCount : left.toList.count e = 2 := by
      rw [← site.eDecoded]
      exact eventECount
    have xCountAtSite :
        (left.toList.take position ++
            x :: e :: left.toList.drop (position + 2)).count x = 2 := by
      rw [← sourceShape]
      exact xCount
    have eCountAtSite :
        (left.toList.take position ++
            x :: e :: left.toList.drop (position + 2)).count e = 2 := by
      rw [← sourceShape]
      exact eCount
    have localSwap :=
      listDerivesAdjacentQuadraticSwap
        (pre := left.toList.take position)
        (post := left.toList.drop (position + 2))
        decodedDifferent xCountAtSite eCountAtSite
    have listed :
        ListDerives left.toList
          (left.toList.take position ++
            e :: x :: left.toList.drop (position + 2)) := by
      exact listDerives_of_source_eq sourceShape localSwap
    exact packageBubbleResult same listed
  · rcases simpleFirst with
      ⟨simpleLetter, firstLetter, simpleNeFirst, orientation⟩
    rcases orientation with sourceSimpleFirst | sourceFirstSimple
    · rcases sourceSimpleFirst with
        ⟨eventXRole, eventERole⟩
      have xEquality : x = simpleLetter := by
        calc
          x = site.eventX.letter := site.xDecoded.symm
          _ = simpleLetter := by simp [eventXRole]
      have eEquality : e = firstLetter := by
        calc
          e = site.eventE.letter := site.eDecoded.symm
          _ = firstLetter := by simp [eventERole]
      subst x
      subst e
      have simpleMember :
          EndpointEvent.simple simpleLetter ∈
            encodedWordEvents left := by
        simpa [eventXRole] using eventXMember
      have firstMember :
          EndpointEvent.first firstLetter ∈
            encodedWordEvents left := by
        simpa [eventERole] using eventEMember
      have simpleCount :
          left.toList.count simpleLetter = 1 :=
        (simple_mem_encodeEndpointEvents_iff
          left.toList simpleLetter).1 <| by
            simpa [encodedWordEvents] using simpleMember
      have firstCount :
          left.toList.count firstLetter = 2 :=
        (first_mem_encodeEndpointEvents_iff
          leftTwo firstLetter).1 <| by
            simpa [encodedWordEvents] using firstMember
      have firstData :=
        site.eFirst eventERole
      have firstFuture :
          firstLetter ∈ left.toList.drop (position + 2) := by
        simpa [Nat.add_assoc] using firstData.later
      have covered :
          CoveredAt left.toList position := by
        apply Classical.byContradiction
        intro uncovered
        have forced :=
          forcedDirection
            left right position simpleLetter firstLetter
            same leftTwo rightTwo
            simpleCount firstCount
            site.xAt site.eAt
            firstData.noEarlier uncovered
        have targetSimpleCount :
            right.toList.count simpleLetter = 1 :=
          (reduced_count_eq_of_sameJointSignature
            same leftTwo rightTwo simpleLetter).symm.trans simpleCount
        have targetRawOrder :
            EventOrder.ChronologicallyBefore
              right.toList firstLetter simpleLetter := by
          simpa [eventXRole, eventERole] using
            rawChronologicalOfEncoded site.targetReverse
        have reversed :
            right.toList.idxOf firstLetter <
              right.toList.idxOf simpleLetter := by
          exact
            idxOf_lt_idxOf_of_chronologicallyBefore_right_count_one
              targetRawOrder targetSimpleCount
        omega
      obtain ⟨guard, guardPast, guardFuture⟩ :=
        coveredAt_guard_members covered
      have localSwap :=
        listDerivesCoveredSimpleFirstSwap
          (left.toList.take position)
          (left.toList.drop (position + 2))
          guard simpleLetter firstLetter
          guardPast guardFuture firstFuture
      have listed :
          ListDerives left.toList
            (left.toList.take position ++
              firstLetter :: simpleLetter ::
                left.toList.drop (position + 2)) := by
        exact listDerives_of_source_eq sourceShape localSwap
      exact packageBubbleResult same listed
    · rcases sourceFirstSimple with
        ⟨eventXRole, eventERole⟩
      have xEquality : x = firstLetter := by
        calc
          x = site.eventX.letter := site.xDecoded.symm
          _ = firstLetter := by simp [eventXRole]
      have eEquality : e = simpleLetter := by
        calc
          e = site.eventE.letter := site.eDecoded.symm
          _ = simpleLetter := by simp [eventERole]
      subst x
      subst e
      have covered :
          CoveredAt left.toList position :=
        firstSimpleCovered eventXRole eventERole
      have firstData :=
        site.xFirst eventXRole
      have firstFuture :
          firstLetter ∈ left.toList.drop (position + 2) :=
        firstEndpoint_later_after_adjacent
          (Ne.symm simpleNeFirst) site.eAt firstData
      obtain ⟨guard, guardPast, guardFuture⟩ :=
        coveredAt_guard_members covered
      have localSwap :=
        listDerivesCoveredFirstSimpleSwap
          (left.toList.take position)
          (left.toList.drop (position + 2))
          guard simpleLetter firstLetter
          guardPast guardFuture firstFuture
      have listed :
          ListDerives left.toList
            (left.toList.take position ++
              simpleLetter :: firstLetter ::
                left.toList.drop (position + 2)) := by
        exact listDerives_of_source_eq sourceShape localSwap
      exact packageBubbleResult same listed

end SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71
