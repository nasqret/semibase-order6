import SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71JointSignatureCanonicalization
import SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71BubbleStep

namespace SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71

open SemigroupBasis
open SemigroupBasis.Normalization.EventLinearExtensions

/-!
# Target-head scheduler for `S4_69 x S4_71`

The scheduler works with endpoint-event lists as control data and with their
decoded letter lists as the actual equational words.  Intermediate control
lists need not be re-encoded after every swap: permutation preserves the
event inventory, while the common-order linear-extension certificate keeps
every first endpoint before its matching last endpoint.
-/

private theorem linearExtension_notPrecedes_reverse
    {α : Type} {precedes : α → α → Prop}
    {events : List α} {earlier later : α}
    (extension : LinearExtension precedes events)
    (before : EventOrder.ChronologicallyBefore events earlier later) :
    ¬ precedes later earlier := by
  induction events with
  | nil =>
      simpa [EventOrder.ChronologicallyBefore] using before
  | cons head tail inductionHypothesis =>
      have ordered := List.pairwise_cons.mp extension.ordered
      simp only [EventOrder.ChronologicallyBefore] at before
      rcases before with ⟨rfl, laterMember⟩ | tailBefore
      · exact ordered.1 later laterMember
      · exact
          inductionHypothesis
            { nodup := (List.nodup_cons.mp extension.nodup).2
              ordered := ordered.2 }
            tailBefore

private theorem linearExtension_swapAdjacent
    {α : Type} {precedes : α → α → Prop}
    {initial suffix : List α} {left right : α}
    (extension :
      LinearExtension precedes
        (initial ++ left :: right :: suffix))
    (independent : Incomparable precedes left right) :
    LinearExtension precedes
      (initial ++ right :: left :: suffix) := by
  have tailSwap :
      (left :: right :: suffix).Perm
        (right :: left :: suffix) := by
    simpa using List.Perm.swap right left suffix
  have wholeSwap :
      (initial ++ left :: right :: suffix).Perm
        (initial ++ right :: left :: suffix) :=
    tailSwap.append_left initial
  refine
    { nodup := wholeSwap.nodup_iff.mp extension.nodup
      ordered := ?_ }
  rcases List.pairwise_append.mp extension.ordered with
    ⟨prefixOrdered, sourceTailOrdered, prefixToTail⟩
  have leftData := List.pairwise_cons.mp sourceTailOrdered
  have rightData := List.pairwise_cons.mp leftData.2
  apply List.pairwise_append.mpr
  refine ⟨prefixOrdered, ?_, ?_⟩
  · apply List.pairwise_cons.mpr
    refine ⟨?_, ?_⟩
    · intro later laterMember
      rcases List.mem_cons.mp laterMember with rfl | inSuffix
      · exact independent.1
      · exact rightData.1 later inSuffix
    · apply List.pairwise_cons.mpr
      refine ⟨?_, rightData.2⟩
      intro later inSuffix
      exact leftData.1 later (by simp [inSuffix])
  · intro earlier earlierMember later laterMember
    apply prefixToTail earlier earlierMember later
    simp only [List.mem_cons] at laterMember ⊢
    rcases laterMember with rightEq | leftEq | inSuffix
    · exact Or.inr (Or.inl rightEq)
    · exact Or.inl leftEq
    · exact Or.inr (Or.inr inSuffix)

private theorem linearExtension_dropPrefix
    {α : Type} {precedes : α → α → Prop}
    {initial suffix : List α}
    (extension : LinearExtension precedes (initial ++ suffix)) :
    LinearExtension precedes suffix := by
  have suffixSublist : suffix.Sublist (initial ++ suffix) :=
    List.sublist_append_right initial suffix
  exact
    { nodup := extension.nodup.sublist suffixSublist
      ordered := extension.ordered.sublist suffixSublist }

private theorem chronologicallyBefore_append_head_of_mem
    {α : Type} (initial : List α) {head later : α}
    {suffix : List α} (laterMember : later ∈ suffix) :
    EventOrder.ChronologicallyBefore
      (initial ++ head :: suffix) head later := by
  induction initial with
  | nil =>
      exact Or.inl ⟨rfl, laterMember⟩
  | cons first rest inductionHypothesis =>
      exact Or.inr inductionHypothesis

private theorem decoded_count_eq_of_control_perm
    {anchor : Word Nat} {control : List EndpointEvent}
    (permutation : control.Perm (encodedWordEvents anchor))
    (letter : Nat) :
    (decodeEndpointEvents control).count letter =
      anchor.toList.count letter := by
  have mapped := permutation.map EndpointEvent.letter
  have mappedCount := mapped.count letter
  change
    (decodeEndpointEvents control).count letter =
      (decodeEndpointEvents (encodedWordEvents anchor)).count letter
    at mappedCount
  simpa using mappedCount

private theorem first_event_anchor_count_two
    {anchor : Word Nat} {control : List EndpointEvent}
    (anchorTwo : ∀ tested, anchor.toList.count tested ≤ 2)
    (permutation : control.Perm (encodedWordEvents anchor))
    {letter : Nat}
    (member : EndpointEvent.first letter ∈ control) :
    anchor.toList.count letter = 2 := by
  apply (first_mem_encodeEndpointEvents_iff anchorTwo letter).1
  simpa [encodedWordEvents] using permutation.mem_iff.mp member

private theorem common_first_before_last
    {anchor target : Word Nat}
    (same : SameJointSignature anchor target)
    (anchorTwo : ∀ tested, anchor.toList.count tested ≤ 2)
    (targetTwo : ∀ tested, target.toList.count tested ≤ 2)
    {letter : Nat}
    (anchorCount : anchor.toList.count letter = 2) :
    jointEventPrecedes anchor target
      (.first letter) (.last letter) := by
  have targetCount : target.toList.count letter = 2 :=
    (reduced_count_eq_of_sameJointSignature
      same anchorTwo targetTwo letter).symm.trans anchorCount
  exact
    ⟨first_before_last_encoded anchorTwo anchorCount,
      first_before_last_encoded targetTwo targetCount⟩

private theorem decoded_prefix_absent_before_first
    {anchor target : Word Nat}
    (same : SameJointSignature anchor target)
    (anchorTwo : ∀ tested, anchor.toList.count tested ≤ 2)
    (targetTwo : ∀ tested, target.toList.count tested ≤ 2)
    (initial suffix : List EndpointEvent) (letter : Nat)
    (extension :
      LinearExtension (jointEventPrecedes anchor target)
        (initial ++ .first letter :: suffix))
    (permutation :
      (initial ++ .first letter :: suffix).Perm
        (encodedWordEvents anchor)) :
    letter ∉ decodeEndpointEvents initial := by
  intro decodedMember
  rcases List.mem_map.mp decodedMember with
    ⟨event, eventMember, eventLetter⟩
  have eventInControl :
      event ∈ initial ++ .first letter :: suffix := by
    simp [eventMember]
  have eventInAnchor : event ∈ encodedWordEvents anchor :=
    permutation.mem_iff.mp eventInControl
  have firstInControl :
      EndpointEvent.first letter ∈
        initial ++ .first letter :: suffix := by
    simp
  have anchorCount :=
    first_event_anchor_count_two
      anchorTwo permutation firstInControl
  have eventBefore :
      EventOrder.ChronologicallyBefore
        (initial ++ .first letter :: suffix)
        event (.first letter) :=
    (EventOrder.pairwise_chronologicallyBefore
      (initial ++ .first letter :: suffix)).rel_of_mem_append
        eventMember (by simp)
  cases event with
  | simple tested =>
      simp only [EndpointEvent.letter] at eventLetter
      subst tested
      have countOne : anchor.toList.count letter = 1 :=
        (simple_mem_encodeEndpointEvents_iff
          anchor.toList letter).1 <| by
            simpa [encodedWordEvents] using eventInAnchor
      omega
  | first tested =>
      simp only [EndpointEvent.letter] at eventLetter
      subst tested
      exact
        (EventOrder.chronologicallyBefore_asymm
          extension.nodup eventBefore) eventBefore
  | last tested =>
      simp only [EndpointEvent.letter] at eventLetter
      subst tested
      exact
        (linearExtension_notPrecedes_reverse
          extension eventBefore)
          (common_first_before_last
            same anchorTwo targetTwo anchorCount)

private theorem controlledFirstEndpointAt
    {anchor target : Word Nat}
    (same : SameJointSignature anchor target)
    (anchorTwo : ∀ tested, anchor.toList.count tested ≤ 2)
    (targetTwo : ∀ tested, target.toList.count tested ≤ 2)
    (initial suffix : List EndpointEvent) (letter : Nat)
    (extension :
      LinearExtension (jointEventPrecedes anchor target)
        (initial ++ .first letter :: suffix))
    (permutation :
      (initial ++ .first letter :: suffix).Perm
        (encodedWordEvents anchor)) :
    FirstEndpointAt
      (decodeEndpointEvents
        (initial ++ .first letter :: suffix))
      initial.length letter := by
  have prefixAbsent :=
    decoded_prefix_absent_before_first
      same anchorTwo targetTwo initial suffix letter
      extension permutation
  have firstInControl :
      EndpointEvent.first letter ∈
        initial ++ .first letter :: suffix := by
    simp
  have anchorCount :=
    first_event_anchor_count_two
      anchorTwo permutation firstInControl
  have decodedShape :
      decodeEndpointEvents (initial ++ .first letter :: suffix) =
        decodeEndpointEvents initial ++
          letter :: decodeEndpointEvents suffix := by
    simp [decodeEndpointEvents]
  have decodedCount :
      (decodeEndpointEvents
        (initial ++ .first letter :: suffix)).count letter = 2 :=
    (decoded_count_eq_of_control_perm permutation letter).trans
      anchorCount
  have suffixPositive :
      0 < (decodeEndpointEvents suffix).count letter := by
    rw [decodedShape, List.count_append,
      List.count_cons_self] at decodedCount
    have prefixCountZero :
        (decodeEndpointEvents initial).count letter = 0 :=
      List.count_eq_zero.mpr prefixAbsent
    rw [prefixCountZero] at decodedCount
    simp only [Nat.zero_add] at decodedCount
    omega
  refine ⟨?_, ?_⟩
  · intro tested testedLt testedAt
    obtain ⟨testedInBounds, testedValue⟩ :=
      List.getElem?_eq_some_iff.mp testedAt
    have inTake :
        letter ∈
          (decodeEndpointEvents
            (initial ++ .first letter :: suffix)).take initial.length :=
      List.mem_take_iff_getElem.mpr
        ⟨tested, by omega, testedValue⟩
    have inPrefix : letter ∈ decodeEndpointEvents initial := by
      simpa [decodeEndpointEvents] using inTake
    exact prefixAbsent inPrefix
  · have suffixMember : letter ∈ decodeEndpointEvents suffix :=
      List.count_pos_iff.mp suffixPositive
    rw [decodedShape]
    rw [show initial.length = (decodeEndpointEvents initial).length by
      simp [decodeEndpointEvents]]
    rw [List.drop_length_add_append]
    simpa using suffixMember

/-- Convert the membership form of a quadratic bridge into the positional
`CoveredAt` contract consumed by the local simple/first swap theorem. -/
theorem coveredAtOfQuadraticGuardCoversAt
    {letters : List Nat} {position : Nat}
    (covered : QuadraticGuardCoversAt letters position) :
    CoveredAt letters position := by
  rcases covered with
    ⟨guard, guardCount, guardPast, guardFuture⟩
  obtain ⟨past, pastInBounds, pastValue⟩ :=
    List.mem_take_iff_getElem.mp guardPast
  obtain ⟨offset, futureInBounds, futureValue⟩ :=
    List.mem_drop_iff_getElem.mp guardFuture
  refine
    ⟨guard, past, position + 2 + offset,
      guardCount, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · exact
      List.getElem?_eq_some_iff.mpr
        ⟨by omega, pastValue⟩
  · exact
      List.getElem?_eq_some_iff.mpr
        ⟨by omega, futureValue⟩

private structure ControlledWord
    (anchor target : Word Nat) (events : List EndpointEvent) where
  word : Word Nat
  raw : word.toList = decodeEndpointEvents events
  same : SameJointSignature word target
  extension : LinearExtension (jointEventPrecedes anchor target) events
  permutation : events.Perm (encodedWordEvents anchor)

private theorem ControlledWord.count_eq_anchor
    {anchor target : Word Nat} {events : List EndpointEvent}
    (state : ControlledWord anchor target events)
    (letter : Nat) :
    state.word.toList.count letter = anchor.toList.count letter := by
  rw [state.raw]
  exact decoded_count_eq_of_control_perm state.permutation letter

private theorem controlledAdjacentSwap
    {anchor target : Word Nat}
    (same : SameJointSignature anchor target)
    (anchorTwo : ∀ tested, anchor.toList.count tested ≤ 2)
    (targetTwo : ∀ tested, target.toList.count tested ≤ 2)
    {initial suffix : List EndpointEvent}
    {eventX eventE : EndpointEvent}
    (state :
      ControlledWord anchor target
        (initial ++ eventX :: eventE :: suffix))
    (independent :
      Incomparable (jointEventPrecedes anchor target) eventX eventE)
    (targetReverse :
      EventOrder.ChronologicallyBefore
        (encodedWordEvents target) eventE eventX)
    (firstSimpleCovered :
      ∀ {first simple},
        eventX = .first first →
          eventE = .simple simple →
            CoveredAt state.word.toList initial.length) :
    ∃ next :
        ControlledWord anchor target
          (initial ++ eventE :: eventX :: suffix),
      Derives basis state.word next.word := by
  have tailNodup : (eventX :: eventE :: suffix).Nodup :=
    (List.nodup_append.mp state.extension.nodup).2.1
  have different : eventX ≠ eventE := by
    intro equality
    subst eventE
    exact (List.nodup_cons.mp tailNodup).1 (by simp)
  have eventXInControl :
      eventX ∈ initial ++ eventX :: eventE :: suffix := by
    simp
  have eventEInControl :
      eventE ∈ initial ++ eventX :: eventE :: suffix := by
    simp
  have eventXInAnchor : eventX ∈ encodedWordEvents anchor :=
    state.permutation.mem_iff.mp eventXInControl
  have eventEInAnchor : eventE ∈ encodedWordEvents anchor :=
    state.permutation.mem_iff.mp eventEInControl
  have classified :=
    EventIncomparability.classify_incomparable_joint_events
      same anchorTwo targetTwo different
      eventXInAnchor eventEInAnchor independent
  have decodedDifferent : eventX.letter ≠ eventE.letter :=
    classified.decodedDistinct
  have swappedExtension :
      LinearExtension (jointEventPrecedes anchor target)
        (initial ++ eventE :: eventX :: suffix) :=
    linearExtension_swapAdjacent state.extension independent
  have controlSwap :
      (initial ++ eventX :: eventE :: suffix).Perm
        (initial ++ eventE :: eventX :: suffix) := by
    exact
      (show (eventX :: eventE :: suffix).Perm
          (eventE :: eventX :: suffix) by
        simpa using List.Perm.swap eventE eventX suffix).append_left initial
  have swappedPermutation :
      (initial ++ eventE :: eventX :: suffix).Perm
        (encodedWordEvents anchor) :=
    controlSwap.symm.trans state.permutation
  have package
      (listed :
        ListDerives state.word.toList
          (decodeEndpointEvents
            (initial ++ eventE :: eventX :: suffix))) :
      ∃ next :
          ControlledWord anchor target
            (initial ++ eventE :: eventX :: suffix),
        Derives basis state.word next.word := by
    obtain ⟨nextWord, wordDerivation, nextSame, nextRaw⟩ :=
      wordResultOfListDerives state.same listed
    exact
      ⟨{ word := nextWord
         raw := nextRaw
         same := nextSame
         extension := swappedExtension
         permutation := swappedPermutation },
       wordDerivation⟩
  rcases classified.roles with quadratic | mixed
  · rcases quadratic with
      ⟨eventXCount, eventECount, _targetXCount, _targetECount⟩
    have currentXCount :
        state.word.toList.count eventX.letter = 2 :=
      (state.count_eq_anchor eventX.letter).trans eventXCount
    have currentECount :
        state.word.toList.count eventE.letter = 2 :=
      (state.count_eq_anchor eventE.letter).trans eventECount
    have sourceShape :
        state.word.toList =
          decodeEndpointEvents initial ++
            eventX.letter :: eventE.letter ::
              decodeEndpointEvents suffix := by
      simpa [decodeEndpointEvents] using state.raw
    have localXCount :
        (decodeEndpointEvents initial ++
            eventX.letter :: eventE.letter ::
              decodeEndpointEvents suffix).count eventX.letter = 2 := by
      rw [← sourceShape]
      exact currentXCount
    have localECount :
        (decodeEndpointEvents initial ++
            eventX.letter :: eventE.letter ::
              decodeEndpointEvents suffix).count eventE.letter = 2 := by
      rw [← sourceShape]
      exact currentECount
    have localSwap :=
      listDerivesAdjacentQuadraticSwap
        (pre := decodeEndpointEvents initial)
        (post := decodeEndpointEvents suffix)
        decodedDifferent localXCount localECount
    apply package
    simpa [decodeEndpointEvents] using
      (show ListDerives state.word.toList
          (decodeEndpointEvents initial ++
            eventE.letter :: eventX.letter ::
              decodeEndpointEvents suffix) by
        rw [sourceShape]
        exact localSwap)
  · rcases mixed with
      ⟨simpleLetter, firstLetter, simpleNeFirst, orientation⟩
    rcases orientation with sourceSimpleFirst | sourceFirstSimple
    · rcases sourceSimpleFirst with
        ⟨eventXRole, eventERole⟩
      have sourceExtension :
          LinearExtension (jointEventPrecedes anchor target)
            ((initial ++ [EndpointEvent.simple simpleLetter]) ++
              EndpointEvent.first firstLetter :: suffix) := by
        simpa [eventXRole, eventERole, List.append_assoc] using
          state.extension
      have sourcePermutation :
          ((initial ++ [EndpointEvent.simple simpleLetter]) ++
              EndpointEvent.first firstLetter :: suffix).Perm
            (encodedWordEvents anchor) := by
        simpa [eventXRole, eventERole, List.append_assoc] using
          state.permutation
      have firstDataControl :=
        controlledFirstEndpointAt
          same anchorTwo targetTwo
          (initial ++ [.simple simpleLetter]) suffix firstLetter
          sourceExtension sourcePermutation
      have sourceShape :
          state.word.toList =
            decodeEndpointEvents initial ++
              simpleLetter :: firstLetter ::
                decodeEndpointEvents suffix := by
        simpa [eventXRole, eventERole, decodeEndpointEvents] using
          state.raw
      have firstData :
          FirstEndpointAt state.word.toList
            (initial.length + 1) firstLetter := by
        rw [sourceShape]
        simpa [decodeEndpointEvents, List.append_assoc] using
          firstDataControl
      have simpleAt :
          state.word.toList[initial.length]? = some simpleLetter := by
        rw [sourceShape]
        rw [List.getElem?_append_right (by
          simp [decodeEndpointEvents])]
        simp [decodeEndpointEvents]
      have firstAt :
          state.word.toList[initial.length + 1]? = some firstLetter := by
        rw [sourceShape]
        rw [List.getElem?_append_right (by
          simp [decodeEndpointEvents])]
        simp [decodeEndpointEvents]
      have anchorSimpleCount :
          anchor.toList.count simpleLetter = 1 :=
        (simple_mem_encodeEndpointEvents_iff
          anchor.toList simpleLetter).1 <| by
            simpa [eventXRole, encodedWordEvents] using eventXInAnchor
      have anchorFirstCount :
          anchor.toList.count firstLetter = 2 :=
        first_event_anchor_count_two
          anchorTwo state.permutation <| by
            simpa [eventERole] using eventEInControl
      have currentSimpleCount :
          state.word.toList.count simpleLetter = 1 :=
        (state.count_eq_anchor simpleLetter).trans anchorSimpleCount
      have currentFirstCount :
          state.word.toList.count firstLetter = 2 :=
        (state.count_eq_anchor firstLetter).trans anchorFirstCount
      have currentTwo :
          ∀ tested, state.word.toList.count tested ≤ 2 := by
        intro tested
        rw [state.count_eq_anchor tested]
        exact anchorTwo tested
      have targetSimpleCount :
          target.toList.count simpleLetter = 1 :=
        (reduced_count_eq_of_sameJointSignature
          same anchorTwo targetTwo simpleLetter).symm.trans
            anchorSimpleCount
      have targetReverse' :
          EventOrder.ChronologicallyBefore
            (encodedWordEvents target)
            (.first firstLetter) (.simple simpleLetter) := by
        simpa [eventXRole, eventERole] using targetReverse
      have targetFirstBeforeSimple :
          target.toList.idxOf firstLetter <
            target.toList.idxOf simpleLetter :=
        idxOf_lt_idxOf_of_encodedBefore_right_count_one
          targetReverse' targetSimpleCount
      have covered : CoveredAt state.word.toList initial.length := by
        apply Classical.byContradiction
        intro uncovered
        have forced :=
          forcedDirection
            state.word target initial.length simpleLetter firstLetter
            state.same currentTwo targetTwo
            currentSimpleCount currentFirstCount
            simpleAt firstAt firstData.noEarlier uncovered
        omega
      obtain ⟨guard, guardPast, guardFuture⟩ :=
        coveredAt_guard_members covered
      have firstFuture :
          firstLetter ∈
            state.word.toList.drop (initial.length + 2) := by
        simpa [Nat.add_assoc] using firstData.later
      have localSwap :=
        listDerivesCoveredSimpleFirstSwap
          (decodeEndpointEvents initial)
          (decodeEndpointEvents suffix)
          guard simpleLetter firstLetter
          (by
            rw [sourceShape] at guardPast
            rw [show initial.length =
                (decodeEndpointEvents initial).length by
              simp [decodeEndpointEvents]] at guardPast
            rw [List.take_append_of_le_length (Nat.le_refl _)] at guardPast
            simpa using guardPast)
          (by
            rw [sourceShape] at guardFuture
            rw [show initial.length =
                (decodeEndpointEvents initial).length by
              simp [decodeEndpointEvents]] at guardFuture
            rw [List.drop_length_add_append] at guardFuture
            simpa using guardFuture)
          (by
            rw [sourceShape] at firstFuture
            rw [show initial.length =
                (decodeEndpointEvents initial).length by
              simp [decodeEndpointEvents]] at firstFuture
            rw [List.drop_length_add_append] at firstFuture
            simpa using firstFuture)
      apply package
      simpa [eventXRole, eventERole, decodeEndpointEvents] using
        (show ListDerives state.word.toList
            (decodeEndpointEvents initial ++
              firstLetter :: simpleLetter ::
                decodeEndpointEvents suffix) by
          rw [sourceShape]
          exact localSwap)
    · rcases sourceFirstSimple with
        ⟨eventXRole, eventERole⟩
      have sourceExtension :
          LinearExtension (jointEventPrecedes anchor target)
            (initial ++ .first firstLetter ::
              .simple simpleLetter :: suffix) := by
        simpa [eventXRole, eventERole] using state.extension
      have sourcePermutation :
          (initial ++ .first firstLetter ::
              .simple simpleLetter :: suffix).Perm
            (encodedWordEvents anchor) := by
        simpa [eventXRole, eventERole] using state.permutation
      have firstDataControl :=
        controlledFirstEndpointAt
          same anchorTwo targetTwo initial
          (.simple simpleLetter :: suffix) firstLetter
          sourceExtension sourcePermutation
      have sourceShape :
          state.word.toList =
            decodeEndpointEvents initial ++
              firstLetter :: simpleLetter ::
                decodeEndpointEvents suffix := by
        simpa [eventXRole, eventERole, decodeEndpointEvents] using
          state.raw
      have firstData :
          FirstEndpointAt state.word.toList
            initial.length firstLetter := by
        rw [sourceShape]
        simpa [decodeEndpointEvents] using firstDataControl
      have simpleAt :
          state.word.toList[initial.length + 1]? = some simpleLetter := by
        rw [sourceShape]
        rw [List.getElem?_append_right (by
          simp [decodeEndpointEvents])]
        simp [decodeEndpointEvents]
      have firstFuture :
          firstLetter ∈
            state.word.toList.drop (initial.length + 2) :=
        firstEndpoint_later_after_adjacent
          (Ne.symm simpleNeFirst) simpleAt firstData
      have covered : CoveredAt state.word.toList initial.length :=
        firstSimpleCovered eventXRole eventERole
      obtain ⟨guard, guardPast, guardFuture⟩ :=
        coveredAt_guard_members covered
      have localSwap :=
        listDerivesCoveredFirstSimpleSwap
          (decodeEndpointEvents initial)
          (decodeEndpointEvents suffix)
          guard simpleLetter firstLetter
          (by
            rw [sourceShape] at guardPast
            rw [show initial.length =
                (decodeEndpointEvents initial).length by
              simp [decodeEndpointEvents]] at guardPast
            rw [List.take_append_of_le_length (Nat.le_refl _)] at guardPast
            simpa using guardPast)
          (by
            rw [sourceShape] at guardFuture
            rw [show initial.length =
                (decodeEndpointEvents initial).length by
              simp [decodeEndpointEvents]] at guardFuture
            rw [List.drop_length_add_append] at guardFuture
            simpa using guardFuture)
          (by
            rw [sourceShape] at firstFuture
            rw [show initial.length =
                (decodeEndpointEvents initial).length by
              simp [decodeEndpointEvents]] at firstFuture
            rw [List.drop_length_add_append] at firstFuture
            simpa using firstFuture)
      apply package
      simpa [eventXRole, eventERole, decodeEndpointEvents] using
        (show ListDerives state.word.toList
            (decodeEndpointEvents initial ++
              simpleLetter :: firstLetter ::
                decodeEndpointEvents suffix) by
          rw [sourceShape]
          exact localSwap)

private theorem exists_append_last
    {α : Type} :
    ∀ {values : List α},
      values ≠ [] → ∃ initial last, values = initial ++ [last]
  | [], notEmpty => (notEmpty rfl).elim
  | value :: values, _ => by
      cases values with
      | nil =>
          exact ⟨[], value, rfl⟩
      | cons next rest =>
          obtain ⟨initial, last, shape⟩ :=
            exists_append_last
              (values := next :: rest) (by simp)
          exact ⟨value :: initial, last, by simp [shape]⟩

private theorem first_of_incomparable_with_simple_right
    {anchor target : Word Nat}
    (same : SameJointSignature anchor target)
    (anchorTwo : ∀ tested, anchor.toList.count tested ≤ 2)
    (targetTwo : ∀ tested, target.toList.count tested ≤ 2)
    {left right : EndpointEvent} {simple : Nat}
    (different : left ≠ right)
    (leftMember : left ∈ encodedWordEvents anchor)
    (rightMember : right ∈ encodedWordEvents anchor)
    (independent :
      Incomparable (jointEventPrecedes anchor target) left right)
    (rightRole : right = .simple simple) :
    ∃ first, left = .first first := by
  have classified :=
    EventIncomparability.classify_incomparable_joint_events
      same anchorTwo targetTwo different
      leftMember rightMember independent
  rcases classified.roles with quadratic | mixed
  · have rightCountTwo := quadratic.2.1
    have simpleCountTwo : anchor.toList.count simple = 2 := by
      simpa [rightRole] using rightCountTwo
    have rightCountOne : anchor.toList.count simple = 1 :=
      (simple_mem_encodeEndpointEvents_iff
        anchor.toList simple).1 <| by
          simpa [rightRole, encodedWordEvents] using rightMember
    omega
  · rcases mixed with
      ⟨simpleLetter, firstLetter, _different, orientation⟩
    rcases orientation with sourceSimpleFirst | sourceFirstSimple
    · exact (by
        rcases sourceSimpleFirst with ⟨_leftRole, impossible⟩
        rw [rightRole] at impossible
        cases impossible)
    · exact ⟨firstLetter, sourceFirstSimple.1⟩

private theorem controlledGuardCovers
    {anchor target : Word Nat}
    (same : SameJointSignature anchor target)
    (anchorTwo : ∀ tested, anchor.toList.count tested ≤ 2)
    (targetTwo : ∀ tested, target.toList.count tested ≤ 2)
    (prior rest : List EndpointEvent)
    (guard first simple : Nat)
    (state :
      ControlledWord anchor target
        (prior ++ .first guard ::
          .first first :: .simple simple :: rest)) :
    CoveredAt state.word.toList (prior.length + 1) := by
  have firstGuardInControl :
      EndpointEvent.first guard ∈
        prior ++ .first guard ::
          .first first :: .simple simple :: rest := by
    simp
  have firstGuardInAnchor :
      EndpointEvent.first guard ∈ encodedWordEvents anchor :=
    state.permutation.mem_iff.mp firstGuardInControl
  have anchorGuardCount : anchor.toList.count guard = 2 :=
    (first_mem_encodeEndpointEvents_iff
      anchorTwo guard).1 <| by
        simpa [encodedWordEvents] using firstGuardInAnchor
  have lastGuardInAnchor :
      EndpointEvent.last guard ∈ encodedWordEvents anchor :=
    (last_mem_encodeEndpointEvents_iff
      anchorTwo guard).2 anchorGuardCount
  have lastGuardInControl :
      EndpointEvent.last guard ∈
        prior ++ .first guard ::
          .first first :: .simple simple :: rest :=
    state.permutation.mem_iff.mpr lastGuardInAnchor
  have lastGuardNotPrior : EndpointEvent.last guard ∉ prior := by
    intro lastInPrior
    have reverse :
        EventOrder.ChronologicallyBefore
          (prior ++ .first guard ::
            .first first :: .simple simple :: rest)
          (.last guard) (.first guard) :=
      (EventOrder.pairwise_chronologicallyBefore
        (prior ++ .first guard ::
          .first first :: .simple simple :: rest)).rel_of_mem_append
            lastInPrior (by simp)
    exact
      (linearExtension_notPrecedes_reverse state.extension reverse)
        (common_first_before_last
          same anchorTwo targetTwo anchorGuardCount)
  have lastGuardInRest : EndpointEvent.last guard ∈ rest := by
    simp only [List.mem_append, List.mem_cons] at lastGuardInControl
    rcases lastGuardInControl with
      inPrior | atGuard | atFirst | atSimple | inRest
    · exact (lastGuardNotPrior inPrior).elim
    · cases atGuard
    · cases atFirst
    · cases atSimple
    · exact inRest
  have currentGuardCount : state.word.toList.count guard = 2 :=
    (state.count_eq_anchor guard).trans anchorGuardCount
  have rawShape :
      state.word.toList =
        decodeEndpointEvents prior ++
          guard :: first :: simple :: decodeEndpointEvents rest := by
    simpa [decodeEndpointEvents] using state.raw
  have guardPast :
      guard ∈ state.word.toList.take (prior.length + 1) := by
    rw [rawShape]
    rw [show prior.length = (decodeEndpointEvents prior).length by
      simp [decodeEndpointEvents]]
    rw [List.take_length_add_append]
    simp
  have guardFuture :
      guard ∈ state.word.toList.drop (prior.length + 3) := by
    rw [rawShape]
    rw [show prior.length = (decodeEndpointEvents prior).length by
      simp [decodeEndpointEvents]]
    rw [List.drop_length_add_append]
    have mappedRest : guard ∈ decodeEndpointEvents rest := by
      change guard ∈ rest.map EndpointEvent.letter
      exact List.mem_map_of_mem lastGuardInRest
    simpa using mappedRest
  exact
    coveredAtOfQuadraticGuardCoversAt
      ⟨guard, currentGuardCount, guardPast, by
        simpa [Nat.add_assoc] using guardFuture⟩

private theorem controlledMoveSelectedToFront
    {anchor target : Word Nat}
    (same : SameJointSignature anchor target)
    (anchorTwo : ∀ tested, anchor.toList.count tested ≤ 2)
    (targetTwo : ∀ tested, target.toList.count tested ≤ 2)
    (targetExtension :
      LinearExtension (jointEventPrecedes anchor target)
        (encodedWordEvents target))
    (fixed targetTail : List EndpointEvent)
    (selected : EndpointEvent)
    (targetShape :
      encodedWordEvents target = fixed ++ selected :: targetTail) :
    ∀ (crossed source : List EndpointEvent),
      selected ∉ crossed →
      (crossed ++ source).Perm (selected :: targetTail) →
      ∀ state :
        ControlledWord anchor target (fixed ++ crossed ++ source),
        ∃ next :
            ControlledWord anchor target
              (fixed ++ crossed ++ selected :: source.erase selected),
          Derives basis state.word next.word
  | crossed, [], selectedNotCrossed, permutation, _ => by
      have selectedInCrossed : selected ∈ crossed := by
        simpa using
          permutation.mem_iff.mpr (List.Mem.head targetTail)
      exact (selectedNotCrossed selectedInCrossed).elim
  | crossed, head :: tail, selectedNotCrossed, permutation, state => by
      by_cases equal : head = selected
      · subst head
        refine
          ⟨{ word := state.word
             raw := by
               simpa [List.append_assoc] using state.raw
             same := state.same
             extension := by
               simpa [List.append_assoc] using state.extension
             permutation := by
               simpa [List.append_assoc] using state.permutation },
           Derives.refl state.word⟩
      · have selectedInTail : selected ∈ tail := by
          have selectedInWhole :
              selected ∈ crossed ++ head :: tail :=
            permutation.mem_iff.mpr (by simp)
          simpa [selectedNotCrossed, Ne.symm equal] using
            selectedInWhole
        have selectedNotNextCrossed :
            selected ∉ crossed ++ [head] := by
          simp [selectedNotCrossed, Ne.symm equal]
        have nextPermutation :
            ((crossed ++ [head]) ++ tail).Perm
              (selected :: targetTail) := by
          simpa [List.append_assoc] using permutation
        let recursiveState :
            ControlledWord anchor target
              (fixed ++ (crossed ++ [head]) ++ tail) :=
          { word := state.word
            raw := by
              simpa [List.append_assoc] using state.raw
            same := state.same
            extension := by
              simpa [List.append_assoc] using state.extension
            permutation := by
              simpa [List.append_assoc] using state.permutation }
        obtain ⟨moved, moveDerivation⟩ :=
          controlledMoveSelectedToFront
            same anchorTwo targetTwo targetExtension
            fixed targetTail selected targetShape
            (crossed ++ [head]) tail
            selectedNotNextCrossed nextPermutation recursiveState
        let movedLocal :
            ControlledWord anchor target
              ((fixed ++ crossed) ++
                head :: selected :: tail.erase selected) :=
          { word := moved.word
            raw := by
              simpa [List.append_assoc] using moved.raw
            same := moved.same
            extension := by
              simpa [List.append_assoc] using moved.extension
            permutation := by
              simpa [List.append_assoc] using moved.permutation }
        have remainingPermutation :
            (crossed ++ head :: tail.erase selected).Perm targetTail := by
          simpa [List.erase_append, selectedNotCrossed, equal] using
            permutation.erase selected
        have remainingPermutation' :
            ((crossed ++ [head]) ++ tail.erase selected).Perm
              targetTail := by
          simpa [List.append_assoc] using remainingPermutation
        have sourceTailExtension :
            LinearExtension (jointEventPrecedes anchor target)
              ((crossed ++ [head]) ++
                selected :: tail.erase selected) := by
          have fullExtension :
              LinearExtension (jointEventPrecedes anchor target)
                (fixed ++
                  ((crossed ++ [head]) ++
                    selected :: tail.erase selected)) := by
            simpa [List.append_assoc] using movedLocal.extension
          exact linearExtension_dropPrefix fullExtension
        have targetFullExtension :
            LinearExtension (jointEventPrecedes anchor target)
              (fixed ++ selected :: targetTail) := by
          rw [← targetShape]
          exact targetExtension
        have targetTailExtension :
            LinearExtension (jointEventPrecedes anchor target)
              (selected :: targetTail) :=
          linearExtension_dropPrefix targetFullExtension
        have localTailPermutation :
            ((crossed ++ [head]) ++
                selected :: tail.erase selected).Perm
              (selected :: targetTail) := by
          exact
            (List.perm_middle :
              ((crossed ++ [head]) ++
                  selected :: tail.erase selected).Perm
                (selected ::
                  ((crossed ++ [head]) ++ tail.erase selected))).trans
              (remainingPermutation'.cons selected)
        have independentPrefix :
            ∀ event, event ∈ crossed ++ [head] →
              Incomparable
                (jointEventPrecedes anchor target) event selected :=
          prefix_incomparable
            sourceTailExtension targetTailExtension localTailPermutation
        have headIndependent :
            Incomparable
              (jointEventPrecedes anchor target) head selected :=
          independentPrefix head (by simp)
        have headInTargetTail : head ∈ targetTail :=
          remainingPermutation.mem_iff.mp (by simp)
        have targetReverse :
            EventOrder.ChronologicallyBefore
              (encodedWordEvents target) selected head := by
          rw [targetShape]
          exact
            chronologicallyBefore_append_head_of_mem
              fixed headInTargetTail
        have firstSimpleCovered :
            ∀ {first simple},
              head = .first first →
                selected = .simple simple →
                  CoveredAt movedLocal.word.toList
                    (fixed ++ crossed).length := by
          intro first simple headRole selectedRole
          by_cases crossedEmpty : crossed = []
          · subst crossed
            have sourceExtension :
                LinearExtension (jointEventPrecedes anchor target)
                  (fixed ++ .first first ::
                    .simple simple :: tail.erase selected) := by
              simpa [headRole, selectedRole] using movedLocal.extension
            have sourcePermutation :
                (fixed ++ .first first ::
                    .simple simple :: tail.erase selected).Perm
                  (encodedWordEvents anchor) := by
              simpa [headRole, selectedRole] using movedLocal.permutation
            have firstDataControl :=
              controlledFirstEndpointAt
                same anchorTwo targetTwo fixed
                (.simple simple :: tail.erase selected) first
                sourceExtension sourcePermutation
            have sourceRawShape :
                movedLocal.word.toList =
                  decodeEndpointEvents fixed ++
                    first :: simple ::
                      decodeEndpointEvents (tail.erase selected) := by
              simpa [headRole, selectedRole, decodeEndpointEvents] using
                movedLocal.raw
            have firstData :
                FirstEndpointAt movedLocal.word.toList
                  fixed.length first := by
              rw [sourceRawShape]
              simpa [decodeEndpointEvents] using firstDataControl
            have targetRawShape :
                target.toList =
                  decodeEndpointEvents
                    (fixed ++ .simple simple :: targetTail) := by
              calc
                target.toList =
                    decodeEndpointEvents (encodedWordEvents target) := by
                  simp [encodedWordEvents]
                _ =
                    decodeEndpointEvents
                      (fixed ++ .simple simple :: targetTail) := by
                  rw [targetShape, selectedRole]
            have prefixAligned :
                movedLocal.word.toList.take fixed.length =
                  target.toList.take fixed.length := by
              rw [sourceRawShape, targetRawShape]
              simp [decodeEndpointEvents]
            have firstAt :
                movedLocal.word.toList[fixed.length]? = some first := by
              rw [sourceRawShape]
              rw [List.getElem?_append_right (by
                simp [decodeEndpointEvents])]
              simp [decodeEndpointEvents]
            have simpleAt :
                movedLocal.word.toList[fixed.length + 1]? = some simple := by
              rw [sourceRawShape]
              rw [List.getElem?_append_right (by
                simp [decodeEndpointEvents])]
              simp [decodeEndpointEvents]
            have targetSimpleAt :
                target.toList[fixed.length]? = some simple := by
              rw [targetRawShape]
              simp [decodeEndpointEvents]
            have anchorSimpleCount :
                anchor.toList.count simple = 1 :=
              (simple_mem_encodeEndpointEvents_iff
                anchor.toList simple).1 <| by
                  have selectedInAnchor :
                      selected ∈ encodedWordEvents anchor :=
                    movedLocal.permutation.mem_iff.mp (by simp)
                  simpa [selectedRole, encodedWordEvents] using
                    selectedInAnchor
            have currentSimpleCount :
                movedLocal.word.toList.count simple = 1 :=
              (movedLocal.count_eq_anchor simple).trans anchorSimpleCount
            have currentTwo :
                ∀ tested, movedLocal.word.toList.count tested ≤ 2 := by
              intro tested
              rw [movedLocal.count_eq_anchor tested]
              exact anchorTwo tested
            have firstNoEarlier :
                first ∉ movedLocal.word.toList.take fixed.length := by
              intro firstMember
              obtain ⟨position, positionInBounds, valueAtPosition⟩ :=
                List.mem_take_iff_getElem.mp firstMember
              exact
                firstData.noEarlier position (by omega) <|
                  List.getElem?_eq_some_iff.mpr
                    ⟨by omega, valueAtPosition⟩
            simpa using
              (coveredAtOfQuadraticGuardCoversAt <|
                prefixAlignedFirstSimpleCovered
                  (position := fixed.length)
                  movedLocal.same currentTwo targetTwo
                  prefixAligned firstAt simpleAt targetSimpleAt
                  firstNoEarlier currentSimpleCount)
          · obtain ⟨initial, guardEvent, crossedShape⟩ :=
              exists_append_last crossedEmpty
            have guardInPrefix : guardEvent ∈ crossed ++ [head] := by
              rw [crossedShape]
              simp
            have guardIndependent :
                Incomparable
                  (jointEventPrecedes anchor target)
                  guardEvent selected :=
              independentPrefix guardEvent guardInPrefix
            have sourceTailNodup := sourceTailExtension.nodup
            have guardDifferent : guardEvent ≠ selected := by
              exact
                (List.nodup_append.mp sourceTailNodup).2.2
                  guardEvent guardInPrefix selected (by simp)
            have guardInMoved :
                guardEvent ∈
                  (fixed ++ crossed) ++
                    head :: selected :: tail.erase selected := by
              simp [crossedShape]
            have selectedInMoved :
                selected ∈
                  (fixed ++ crossed) ++
                    head :: selected :: tail.erase selected := by
              simp
            have guardInAnchor :
                guardEvent ∈ encodedWordEvents anchor :=
              movedLocal.permutation.mem_iff.mp guardInMoved
            have selectedInAnchor :
                selected ∈ encodedWordEvents anchor :=
              movedLocal.permutation.mem_iff.mp selectedInMoved
            obtain ⟨guard, guardRole⟩ :=
              first_of_incomparable_with_simple_right
                same anchorTwo targetTwo guardDifferent
                guardInAnchor selectedInAnchor guardIndependent
                selectedRole
            let guardState :
                ControlledWord anchor target
                  ((fixed ++ initial) ++ .first guard ::
                    .first first :: .simple simple ::
                      tail.erase selected) :=
              { word := movedLocal.word
                raw := by
                  simpa [crossedShape, guardRole, headRole, selectedRole,
                    List.append_assoc] using movedLocal.raw
                same := movedLocal.same
                extension := by
                  simpa [crossedShape, guardRole, headRole, selectedRole,
                    List.append_assoc] using movedLocal.extension
                permutation := by
                  simpa [crossedShape, guardRole, headRole, selectedRole,
                    List.append_assoc] using movedLocal.permutation }
            have covered :=
              controlledGuardCovers
                same anchorTwo targetTwo
                (fixed ++ initial) (tail.erase selected)
                guard first simple guardState
            have guardWord : guardState.word = movedLocal.word := by
              rfl
            simpa [guardWord, crossedShape, List.append_assoc,
              Nat.add_assoc] using covered
        obtain ⟨swapped, swapDerivation⟩ :=
          controlledAdjacentSwap
            same anchorTwo targetTwo movedLocal
            headIndependent targetReverse firstSimpleCovered
        have movedLocalWord : movedLocal.word = moved.word := by
          rfl
        have swapDerivation' :
            Derives basis moved.word swapped.word := by
          rw [← movedLocalWord]
          exact swapDerivation
        let finalState :
            ControlledWord anchor target
              (fixed ++ crossed ++
                selected :: (head :: tail).erase selected) :=
          { word := swapped.word
            raw := by
              simpa [equal, List.append_assoc] using swapped.raw
            same := swapped.same
            extension := by
              simpa [equal, List.append_assoc] using swapped.extension
            permutation := by
              simpa [equal, List.append_assoc] using swapped.permutation }
        exact
          ⟨finalState, moveDerivation.trans swapDerivation'⟩
termination_by
  _ source => source.length

private theorem controlledCanonicalizeToTarget
    {anchor target : Word Nat}
    (same : SameJointSignature anchor target)
    (anchorTwo : ∀ tested, anchor.toList.count tested ≤ 2)
    (targetTwo : ∀ tested, target.toList.count tested ≤ 2)
    (targetExtension :
      LinearExtension (jointEventPrecedes anchor target)
        (encodedWordEvents target)) :
    ∀ (targetTail sourceTail fixed : List EndpointEvent),
      sourceTail.Perm targetTail →
      encodedWordEvents target = fixed ++ targetTail →
      ∀ state :
        ControlledWord anchor target (fixed ++ sourceTail),
        ∃ final : ControlledWord anchor target (fixed ++ targetTail),
          Derives basis state.word final.word
  | [], sourceTail, fixed, permutation, _, state => by
      have sourceEmpty : sourceTail = [] := permutation.eq_nil
      subst sourceTail
      exact ⟨state, Derives.refl state.word⟩
  | selected :: targetTail, sourceTail, fixed,
      permutation, targetShape, state => by
      have selectedInSource : selected ∈ sourceTail :=
        permutation.mem_iff.mpr (by simp)
      let moveState :
          ControlledWord anchor target (fixed ++ [] ++ sourceTail) :=
        { word := state.word
          raw := by simpa using state.raw
          same := state.same
          extension := by simpa using state.extension
          permutation := by simpa using state.permutation }
      obtain ⟨moved, moveDerivation⟩ :=
        controlledMoveSelectedToFront
          same anchorTwo targetTwo targetExtension
          fixed targetTail selected targetShape
          [] sourceTail (by simp) (by simpa using permutation)
          moveState
      have remainingPermutation :
          (sourceTail.erase selected).Perm targetTail := by
        simpa using permutation.erase selected
      let recursiveState :
          ControlledWord anchor target
            ((fixed ++ [selected]) ++ sourceTail.erase selected) :=
        { word := moved.word
          raw := by
            simpa [List.append_assoc] using moved.raw
          same := moved.same
          extension := by
            simpa [List.append_assoc] using moved.extension
          permutation := by
            simpa [List.append_assoc] using moved.permutation }
      have recursiveTargetShape :
          encodedWordEvents target =
            (fixed ++ [selected]) ++ targetTail := by
        simpa [List.append_assoc] using targetShape
      obtain ⟨final, tailDerivation⟩ :=
        controlledCanonicalizeToTarget
          same anchorTwo targetTwo targetExtension
          targetTail (sourceTail.erase selected)
          (fixed ++ [selected]) remainingPermutation
          recursiveTargetShape recursiveState
      have recursiveWord : recursiveState.word = moved.word := by
        rfl
      have tailDerivation' :
          Derives basis moved.word final.word := by
        rw [← recursiveWord]
        exact tailDerivation
      let finalState :
          ControlledWord anchor target
            (fixed ++ selected :: targetTail) :=
        { word := final.word
          raw := by
            simpa [List.append_assoc] using final.raw
          same := final.same
          extension := by
            simpa [List.append_assoc] using final.extension
          permutation := by
            simpa [List.append_assoc] using final.permutation }
      exact
        ⟨finalState, moveDerivation.trans tailDerivation'⟩
termination_by
  targetTail _ _ => targetTail.length

/-- Every pair of count-reduced words with the same complete joint signature
is connected by the fourteen displayed laws. -/
theorem derives_of_sameJointSignature_twoLimited
    {left right : Word Nat}
    (same : SameJointSignature left right)
    (leftTwo : ∀ tested, left.toList.count tested ≤ 2)
    (rightTwo : ∀ tested, right.toList.count tested ≤ 2) :
    Derives basis left right := by
  have extensions :=
    encodedWordEvents_commonLinearExtensions leftTwo rightTwo
  let initial :
      ControlledWord left right (encodedWordEvents left) :=
    { word := left
      raw := by simp [encodedWordEvents]
      same := same
      extension := extensions.1
      permutation := List.Perm.refl _ }
  have eventPermutation :=
    encodedWordEvents_perm same leftTwo rightTwo
  obtain ⟨final, derivation⟩ :=
    controlledCanonicalizeToTarget
      same leftTwo rightTwo extensions.2
      (encodedWordEvents right) (encodedWordEvents left) []
      eventPermutation (by simp) (by simpa using initial)
  have finalEq : final.word = right := by
    apply Word.toList_injective
    calc
      final.word.toList =
          decodeEndpointEvents (encodedWordEvents right) := by
        simpa using final.raw
      _ = right.toList := by
        simp [encodedWordEvents]
  simpa [finalEq] using derivation

/-- Unrestricted joint-signature canonicalization obtained by count reduction
followed by the event-controlled target-head scheduler. -/
theorem targetHeadJointSignatureCanonicalization :
    JointSignatureCanonicalization := by
  intro left right _leftLong _rightLong same
  have reduced := countReducedPair same
  have middleDerivation :
      Derives basis
        (countReducedWord left) (countReducedWord right) :=
    derives_of_sameJointSignature_twoLimited
      reduced.reducedSame
      reduced.leftTwoLimited reduced.rightTwoLimited
  exact
    reduced.leftDerives.trans <|
      middleDerivation.trans reduced.rightDerives.symm

end SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71
