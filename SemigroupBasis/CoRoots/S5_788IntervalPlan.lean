import SemigroupBasis.CoRoots.S5_788IntervalDerivations
import SemigroupBasis.Examples.ConnectedComponentFourEnvelopeCombinatorics

namespace SemigroupBasis.CoRoots.S5_788

open SemigroupBasis
open SemigroupBasis.Examples

/-- Render a retained endpoint, its current interior, the second endpoint,
and the unprocessed suffix. -/
def initialEnvelopeRender
    (endpoint : Nat) (interior suffix : List Nat) : List Nat :=
  endpoint :: (interior ++ endpoint :: suffix)

/-- The order-preserving interval induction state. The suffix remains linked
to the current envelope, and endpoint capping ensures that the displayed
endpoint has no further occurrence. -/
structure InitialEnvelopeState
    (endpoint : Nat) (interior suffix : List Nat) : Prop where
  linked :
    ConnectedComponentSuffixLinked
      (endpoint :: interior ++ [endpoint]) suffix
  endpointNotInterior : endpoint ∉ interior
  endpointNotSuffix : endpoint ∉ suffix

private theorem initialEnvelope_advance_prefix_mem
    {endpoint crossing value : Nat}
    {interior before left : List Nat}
    (crossingInInterior : crossing ∈ interior)
    (member :
      value ∈
        (endpoint :: interior ++ [endpoint]) ++
          before ++ crossing :: left) :
    value ∈
      (endpoint :: (interior ++ before) ++ [endpoint]) ++
        left := by
  by_cases valueEq : value = crossing
  · subst value
    simp [crossingInInterior]
  · simpa [List.mem_append, valueEq,
      or_assoc, or_left_comm, or_comm] using member

namespace InitialEnvelopeState

/-- Every nonempty linked suffix contains a crossing letter already present
in the interior. It cannot be the endpoint because endpoint capping left only
the two displayed endpoint occurrences. -/
theorem exists_crossing
    {endpoint : Nat} {interior suffix : List Nat}
    (state : InitialEnvelopeState endpoint interior suffix)
    (suffixNonempty : suffix ≠ []) :
    ∃ crossing,
      crossing ∈ interior ∧ crossing ∈ suffix := by
  have intersect :=
    state.linked [] suffix (by simp) suffixNonempty
  rcases intersect with
    ⟨crossing, prefixMember, suffixMember⟩
  have prefixMember' :
      crossing ∈ endpoint :: interior ++ [endpoint] := by
    simpa using prefixMember
  have endpointOrInterior :
      crossing = endpoint ∨ crossing ∈ interior := by
    rcases List.mem_append.mp prefixMember' with
      headOrInterior | endpointMember
    · rcases List.mem_cons.mp headOrInterior with
        equals | interiorMember
      · exact Or.inl equals
      · exact Or.inr interiorMember
    · exact Or.inl (by simpa using endpointMember)
  rcases endpointOrInterior with equals | interiorMember
  · subst crossing
    exact False.elim (state.endpointNotSuffix suffixMember)
  · exact ⟨crossing, interiorMember, suffixMember⟩

/-- Absorbing one crossing occurrence preserves linkedness and the fact that
the endpoint has no hidden occurrence. -/
theorem advance
    {endpoint crossing : Nat}
    {interior suffix before after : List Nat}
    (state : InitialEnvelopeState endpoint interior suffix)
    (crossingInInterior : crossing ∈ interior)
    (suffixShape : suffix = before ++ crossing :: after) :
    InitialEnvelopeState endpoint
      (interior ++ before) after := by
  refine
    { linked := ?_
      endpointNotInterior := ?_
      endpointNotSuffix := ?_ }
  · intro left right afterShape rightNonempty
    have oldSuffixShape :
        suffix =
          (before ++ crossing :: left) ++ right := by
      rw [suffixShape, afterShape]
      simp [List.append_assoc]
    have oldIntersect :=
      state.linked (before ++ crossing :: left) right
        oldSuffixShape rightNonempty
    rcases oldIntersect with
      ⟨value, oldPrefixMember, rightMember⟩
    exact
      ⟨value,
        initialEnvelope_advance_prefix_mem
          crossingInInterior
          (by simpa [List.append_assoc] using oldPrefixMember),
        rightMember⟩
  · intro endpointMember
    rcases List.mem_append.mp endpointMember with
      interiorMember | beforeMember
    · exact state.endpointNotInterior interiorMember
    · apply state.endpointNotSuffix
      rw [suffixShape]
      exact List.mem_append_left _ beforeMember
  · intro endpointMember
    apply state.endpointNotSuffix
    rw [suffixShape]
    exact
      List.mem_append_right before <|
        List.Mem.tail crossing endpointMember

end InitialEnvelopeState

/-- A finite order-preserving plan that repeatedly absorbs a crossing from
the suffix without permuting the established interior. -/
inductive InitialEnvelopePlan
    (endpoint : Nat) : List Nat → List Nat → List Nat → Prop
  | done (interior : List Nat) :
      InitialEnvelopePlan endpoint interior [] interior
  | advance
      {interior suffix before after finalInterior : List Nat}
      {crossing : Nat} :
      crossing ∈ interior →
      suffix = before ++ crossing :: after →
      InitialEnvelopePlan endpoint
        (interior ++ before) after finalInterior →
      InitialEnvelopePlan endpoint
        interior suffix finalInterior

namespace InitialEnvelopePlan

/-- Replay an order-preserving envelope plan using the arbitrary-filler
crossing law. -/
theorem replay
    {endpoint : Nat}
    {interior suffix finalInterior : List Nat}
    (plan :
      InitialEnvelopePlan endpoint
        interior suffix finalInterior) :
    S5_107.ListDerives basis
      (initialEnvelopeRender endpoint interior suffix)
      (initialEnvelopeRender endpoint finalInterior []) := by
  induction plan with
  | done current =>
      exact S5_107.ListDerives.refl _
  | @advance interior suffix before after finalInterior crossing
      crossingInInterior suffixShape _ induction =>
      obtain ⟨left, right, interiorShape⟩ :=
        List.append_of_mem crossingInInterior
      subst suffix
      have absorbed :=
        (listDerivesCrossingInterval
          endpoint crossing left right before).append after
      have first :
          S5_107.ListDerives basis
            (initialEnvelopeRender endpoint interior
              (before ++ crossing :: after))
            (initialEnvelopeRender endpoint
              (interior ++ before) after) := by
        simpa [initialEnvelopeRender, interiorShape,
          List.append_assoc] using absorbed
      exact first.trans induction

end InitialEnvelopePlan

namespace InitialEnvelopeState

/-- Every order-preserving envelope state has a terminating absorption plan.
The recursive suffix is strictly shorter after each crossing. -/
theorem exists_plan
    {endpoint : Nat} :
    ∀ (interior suffix : List Nat),
      InitialEnvelopeState endpoint interior suffix →
        ∃ finalInterior,
          InitialEnvelopePlan endpoint
            interior suffix finalInterior ∧
          endpoint ∉ finalInterior := by
  intro interior suffix state
  by_cases suffixEmpty : suffix = []
  · subst suffix
    exact
      ⟨interior, .done interior,
        state.endpointNotInterior⟩
  · obtain
      ⟨crossing, crossingInInterior, crossingInSuffix⟩ :=
        state.exists_crossing suffixEmpty
    obtain ⟨before, after, suffixShape⟩ :=
      List.append_of_mem crossingInSuffix
    have nextState :=
      state.advance crossingInInterior suffixShape
    obtain ⟨finalInterior, remaining, endpointAbsent⟩ :=
      InitialEnvelopeState.exists_plan
        (interior ++ before) after nextState
    exact
      ⟨finalInterior,
        .advance crossingInInterior suffixShape remaining,
        endpointAbsent⟩
termination_by interior suffix _state => suffix.length
decreasing_by
  rw [suffixShape]
  simp
  omega

end InitialEnvelopeState

/-- A support-connected capped list starts in an order-preserving envelope
state at its first letter. -/
theorem exists_initialEnvelopeState
    {head : Nat} {tail : List Nat}
    (connected :
      ConnectedComponentSupportConnected (head :: tail))
    (lengthAtLeastTwo : 2 ≤ (head :: tail).length)
    (twoLimited :
      UniqueSeparatorTwoLimited (head :: tail)) :
    ∃ interior suffix,
      head :: tail =
        initialEnvelopeRender head interior suffix ∧
      InitialEnvelopeState head interior suffix := by
  obtain ⟨interior, suffix, shape, linkedState⟩ :=
    connectedComponent_exists_initial_envelope
      connected lengthAtLeastTwo
  have endpointNotInterior : head ∉ interior := by
    intro endpointMember
    have positive :
        1 ≤ interior.count head :=
      List.one_le_count_iff.mpr endpointMember
    have bound := twoLimited head
    rw [shape] at bound
    simp only [List.count_cons_self,
      List.count_append] at bound
    omega
  have endpointNotSuffix : head ∉ suffix := by
    intro endpointMember
    have positive :
        1 ≤ suffix.count head :=
      List.one_le_count_iff.mpr endpointMember
    have bound := twoLimited head
    rw [shape] at bound
    simp only [List.count_cons_self,
      List.count_append] at bound
    omega
  refine ⟨interior, suffix, ?_, ?_⟩
  · simpa [initialEnvelopeRender] using shape
  · exact
      { linked := linkedState.linked
        endpointNotInterior := endpointNotInterior
        endpointNotSuffix := endpointNotSuffix }

private theorem firstOccurrenceSequence_eq_self_of_nodup
    {letters : List Nat}
    (nodup : letters.Nodup) :
    firstOccurrenceSequence letters = letters := by
  induction letters with
  | nil =>
      rfl
  | cons letter rest induction =>
      have data := List.nodup_cons.mp nodup
      rw [firstOccurrenceSequence, induction data.2]
      have keep :
          rest.filter (fun next => decide (next ≠ letter)) =
            rest := by
        apply List.filter_eq_self.mpr
        intro next nextMember
        exact decide_eq_true <| by
          intro equals
          subst next
          exact data.1 nextMember
      rw [keep]

private theorem firstOccurrenceSequence_closedEnvelope
    (endpoint : Nat) (interior : List Nat)
    (interiorNodup : interior.Nodup)
    (endpointNotInterior : endpoint ∉ interior) :
    firstOccurrenceSequence
        (initialEnvelopeRender endpoint interior []) =
      endpoint :: interior := by
  have tailNodup :
      (interior ++ [endpoint]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨interiorNodup, by simp, ?_⟩
    intro left leftMember right rightMember equals
    have rightEq : right = endpoint := by
      simpa using rightMember
    subst right
    subst left
    exact endpointNotInterior leftMember
  rw [initialEnvelopeRender, firstOccurrenceSequence,
    firstOccurrenceSequence_eq_self_of_nodup tailNodup]
  have keepInterior :
      interior.filter
          (fun next => decide (next ≠ endpoint)) =
        interior := by
    apply List.filter_eq_self.mpr
    intro next nextMember
    exact decide_eq_true <| by
      intro equals
      subst next
      exact endpointNotInterior nextMember
  rw [List.filter_append, keepInterior]
  simp

/-- Scan an envelope interior left to right, deleting every occurrence that
has already appeared in the retained prefix. -/
private theorem exists_nodupInteriorDerivation
    (endpoint : Nat) :
    ∀ (retained remaining : List Nat),
      retained.Nodup →
      endpoint ∉ retained →
      endpoint ∉ remaining →
      ∃ finalInterior,
        S5_107.ListDerives basis
          (initialEnvelopeRender endpoint
            (retained ++ remaining) [])
          (initialEnvelopeRender endpoint finalInterior []) ∧
        finalInterior.Nodup ∧
        endpoint ∉ finalInterior
  | retained, [], retainedNodup, endpointNotRetained, _ =>
      ⟨retained, by
        simpa using
          S5_107.ListDerives.refl
            (basis := basis)
            (initialEnvelopeRender endpoint retained []),
        retainedNodup, endpointNotRetained⟩
  | retained, current :: rest, retainedNodup,
      endpointNotRetained, endpointNotRemaining => by
      have currentNeEndpoint : current ≠ endpoint := by
        intro equals
        subst current
        exact endpointNotRemaining (List.Mem.head rest)
      have endpointNotRest : endpoint ∉ rest := by
        intro member
        exact endpointNotRemaining
          (List.Mem.tail current member)
      by_cases currentSeen : current ∈ retained
      · obtain ⟨left, middle, retainedShape⟩ :=
          List.append_of_mem currentSeen
        have deleteCurrent :
            S5_107.ListDerives basis
              (initialEnvelopeRender endpoint
                (retained ++ current :: rest) [])
              (initialEnvelopeRender endpoint
                (retained ++ rest) []) := by
          simpa [initialEnvelopeRender, retainedShape,
            List.append_assoc] using
              listDerivesNestedInterval
                endpoint current left middle rest
        obtain
          ⟨finalInterior, remainingDerivation,
            finalNodup, endpointAbsent⟩ :=
            exists_nodupInteriorDerivation
              endpoint retained rest retainedNodup
              endpointNotRetained endpointNotRest
        exact
          ⟨finalInterior,
            deleteCurrent.trans remainingDerivation,
            finalNodup, endpointAbsent⟩
      · have nextNodup :
            (retained ++ [current]).Nodup := by
          apply List.nodup_append.mpr
          refine ⟨retainedNodup, by simp, ?_⟩
          intro left leftMember right rightMember equals
          have rightEq : right = current := by
            simpa using rightMember
          subst right
          subst left
          exact currentSeen leftMember
        have endpointNotNext :
            endpoint ∉ retained ++ [current] := by
          simp [endpointNotRetained, Ne.symm currentNeEndpoint]
        obtain
          ⟨finalInterior, remainingDerivation,
            finalNodup, endpointAbsent⟩ :=
            exists_nodupInteriorDerivation
              endpoint (retained ++ [current]) rest
              nextNodup endpointNotNext endpointNotRest
        refine
          ⟨finalInterior, ?_, finalNodup, endpointAbsent⟩
        simpa [initialEnvelopeRender,
          List.append_assoc] using remainingDerivation
termination_by retained remaining _ _ _ =>
  remaining.length

/-- Delete all repeated interior occurrences of a closed endpoint envelope.
The resulting list is its first-occurrence sequence followed by the retained
endpoint. -/
theorem listDerivesClosedInitialEnvelope
    (endpoint : Nat) (interior : List Nat)
    (endpointNotInterior : endpoint ∉ interior) :
    S5_107.ListDerives basis
      (initialEnvelopeRender endpoint interior [])
      (firstOccurrenceSequence
          (initialEnvelopeRender endpoint interior []) ++
        [endpoint]) := by
  obtain
    ⟨nodupInterior, interiorDerivation,
      interiorNodup, endpointStillAbsent⟩ :=
      exists_nodupInteriorDerivation
        endpoint [] interior
        (by simp) (by simp) endpointNotInterior
  have initialSequence :
      firstOccurrenceSequence
          (initialEnvelopeRender endpoint interior []) =
        endpoint :: nodupInterior := by
    have wordDerivation :=
      S5_107.ListDerives.toWord interiorDerivation
    have preserved :=
      (derives_sameSignature wordDerivation).initials
    calc
      firstOccurrenceSequence
          (initialEnvelopeRender endpoint interior []) =
        firstOccurrenceSequence
          (initialEnvelopeRender endpoint nodupInterior []) := by
            simpa [S5_107.listWordOfCons, Word.toList,
              initialEnvelopeRender] using preserved
      _ = endpoint :: nodupInterior :=
        firstOccurrenceSequence_closedEnvelope
          endpoint nodupInterior interiorNodup
            endpointStillAbsent
  rw [initialSequence]
  simpa [initialEnvelopeRender, List.append_assoc] using
    interiorDerivation

/-- Normalize a support-connected, two-limited component to its
first-occurrence sequence followed by its first letter. -/
theorem listDerivesConnectedInitialEnvelope
    {head : Nat} {tail : List Nat}
    (connected :
      ConnectedComponentSupportConnected (head :: tail))
    (lengthAtLeastTwo : 2 ≤ (head :: tail).length)
    (twoLimited :
      UniqueSeparatorTwoLimited (head :: tail)) :
    S5_107.ListDerives basis
      (head :: tail)
      (firstOccurrenceSequence (head :: tail) ++ [head]) := by
  obtain ⟨interior, suffix, sourceShape, state⟩ :=
    exists_initialEnvelopeState
      connected lengthAtLeastTwo twoLimited
  obtain ⟨finalInterior, plan, endpointAbsent⟩ :=
    state.exists_plan
  have envelopeDerivation := plan.replay
  have closed :=
    listDerivesClosedInitialEnvelope
      head finalInterior endpointAbsent
  have combined :
      S5_107.ListDerives basis
        (head :: tail)
        (firstOccurrenceSequence
            (initialEnvelopeRender head finalInterior []) ++
          [head]) := by
    rw [sourceShape]
    exact envelopeDerivation.trans closed
  have initialSequence :
      firstOccurrenceSequence (head :: tail) =
        firstOccurrenceSequence
          (initialEnvelopeRender head finalInterior []) := by
    have wordDerivation :=
      S5_107.ListDerives.toWord envelopeDerivation
    simpa [S5_107.listWordOfCons, Word.toList,
      initialEnvelopeRender, sourceShape] using
      (derives_sameSignature wordDerivation).initials
  rw [initialSequence]
  exact combined

end SemigroupBasis.CoRoots.S5_788
