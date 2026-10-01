import SemigroupBasis.Examples.ConnectedComponentFourComponents
import SemigroupBasis.Examples.ConnectedComponentFourListDerives

namespace SemigroupBasis.Examples

open SemigroupBasis

private theorem connectedComponentPerm_of_nodup_mem_iff
    {left right : List Nat}
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (sameSupport : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro letter
  rw [leftNodup.count, rightNodup.count]
  simp only [sameSupport letter]

/-- Replay the abstract envelope absorption plan using the concrete
`S4_70` list derivability relation. -/
theorem connectedComponentEnvelopePlan_derives
    {endpoint : Nat}
    {interior suffix finalInterior : List Nat}
    (plan :
      ConnectedComponentEnvelopePlan endpoint
        interior suffix finalInterior) :
    ConnectedComponentListDerives
      (connectedComponentEnvelopeRender endpoint interior suffix)
      (connectedComponentEnvelopeRender endpoint finalInterior []) := by
  let crossingAbsorption :
      ∀ (outer crossing : Nat) (middle before after : List Nat),
        ConnectedComponentListDerives
          (connectedComponentEnvelopeRender outer
            (crossing :: middle) (before ++ crossing :: after))
          (connectedComponentEnvelopeRender outer
            (crossing :: middle ++ before) after) := by
    intro outer crossing middle before after
    simpa [connectedComponentEnvelopeRender, List.append_assoc] using
      (connectedComponentListDerivesCrossing
        outer crossing middle before).append after
  let endpointAbsorption :
      ∀ (outer : Nat) (current before after : List Nat),
        ConnectedComponentListDerives
          (connectedComponentEnvelopeRender outer
            current (before ++ outer :: after))
          (connectedComponentEnvelopeRender outer
            (current ++ before) after) := by
    intro outer current before after
    simpa [connectedComponentEnvelopeRender, List.append_assoc] using
      connectedComponentListDerivesEndpointAbsorption
        outer current before after
  exact plan.replay ConnectedComponentListDerives
    ConnectedComponentListDerives.refl
    (fun first second => first.trans second)
    connectedComponentListDerivesInteriorPermutationContext
    crossingAbsorption endpointAbsorption

/-- Remove every occurrence of the outer endpoint from an envelope
interior. -/
theorem connectedComponentRemoveEndpoint_derives
    (endpoint : Nat) :
    ∀ (interior suffix : List Nat),
      ConnectedComponentListDerives
        (endpoint :: interior ++ endpoint :: suffix)
        (endpoint ::
          interior.filter (fun letter => decide (letter ≠ endpoint)) ++
            endpoint :: suffix)
  | [], suffix => ConnectedComponentListDerives.refl _
  | letter :: rest, suffix => by
      by_cases equals : letter = endpoint
      · subst letter
        have delete :
            ConnectedComponentListDerives
              (endpoint :: endpoint :: rest ++ endpoint :: suffix)
              (endpoint :: rest ++ endpoint :: suffix) := by
          simpa [List.append_assoc] using
            (connectedComponentDeleteMiddleCore
              endpoint [] rest).append suffix
        have recurse :=
          connectedComponentRemoveEndpoint_derives endpoint rest suffix
        simpa using delete.trans recurse
      · have recurse :=
          connectedComponentRemoveEndpoint_derives endpoint rest suffix
        have lifted :=
          connectedComponentListDerivesInteriorCons
            endpoint letter suffix recurse
        simpa [equals] using lifted

/-- Delete repeated interior letters, retaining one representative of each
letter. -/
theorem connectedComponentDistinctInterior_derives
    (endpoint : Nat) :
    ∀ (interior suffix : List Nat),
      ConnectedComponentListDerives
        (endpoint :: interior ++ endpoint :: suffix)
        (endpoint :: connectedComponentDistinctSupport interior ++
          endpoint :: suffix)
  | [], suffix => ConnectedComponentListDerives.refl _
  | letter :: rest, suffix => by
      have recurse :=
        connectedComponentDistinctInterior_derives endpoint rest suffix
      have lifted :=
        connectedComponentListDerivesInteriorCons
          endpoint letter suffix recurse
      let distinctRest := connectedComponentDistinctSupport rest
      by_cases present : letter ∈ distinctRest
      · have arrangeRest :
            distinctRest.Perm
              (letter :: distinctRest.erase letter) :=
          List.perm_cons_erase present
        have arrange :
            (letter :: distinctRest).Perm
              (letter :: letter :: distinctRest.erase letter) :=
          List.Perm.cons letter arrangeRest
        have first :=
          connectedComponentListDerivesInteriorPermutationContext
            endpoint suffix arrange
        have contract :=
          connectedComponentListDerivesInteriorContractionContext
            endpoint letter [] (distinctRest.erase letter) suffix
        have restore :=
          connectedComponentListDerivesInteriorPermutationContext
            endpoint suffix arrangeRest.symm
        rw [connectedComponentDistinctSupport, if_pos present]
        exact lifted.trans (first.trans (contract.trans restore))
      · rw [connectedComponentDistinctSupport, if_neg present]
        exact lifted

/-- The deterministic distinct, sorted envelope interior after removing the
outer endpoint. -/
def connectedComponentNormalizedInterior
    (endpoint : Nat) (interior : List Nat) : List Nat :=
  connectedComponentSortedSupport
    (interior.filter (fun letter => decide (letter ≠ endpoint)))

theorem connectedComponentNormalizeInterior_derives
    (endpoint : Nat) (interior suffix : List Nat) :
    ConnectedComponentListDerives
      (endpoint :: interior ++ endpoint :: suffix)
      (endpoint :: connectedComponentNormalizedInterior endpoint interior ++
        endpoint :: suffix) := by
  have removed :=
    connectedComponentRemoveEndpoint_derives endpoint interior suffix
  let filtered :=
    interior.filter (fun letter => decide (letter ≠ endpoint))
  have distinct :=
    connectedComponentDistinctInterior_derives endpoint filtered suffix
  have sorted :
      (connectedComponentDistinctSupport filtered).Perm
        (connectedComponentSortedSupport filtered) :=
    (List.mergeSort_perm
      (connectedComponentDistinctSupport filtered)
      (fun left right : Nat => decide (left ≤ right))).symm
  have permuted :=
    connectedComponentListDerivesInteriorPermutationContext
      endpoint suffix sorted
  simpa [connectedComponentNormalizedInterior, filtered] using
    removed.trans (distinct.trans permuted)

theorem connectedComponentNormalizedInterior_nodup
    (endpoint : Nat) (interior : List Nat) :
    (connectedComponentNormalizedInterior endpoint interior).Nodup :=
  connectedComponentSortedSupport_nodup _

theorem connectedComponentNormalizedInterior_endpoint_absent
    (endpoint : Nat) (interior : List Nat) :
    endpoint ∉ connectedComponentNormalizedInterior endpoint interior := by
  rw [connectedComponentNormalizedInterior,
    connectedComponentSortedSupport_mem_iff, List.mem_filter]
  simp

theorem connectedComponentNormalizedInterior_mem_iff
    (endpoint tested : Nat) (interior : List Nat) :
    tested ∈ connectedComponentNormalizedInterior endpoint interior ↔
      tested ∈ interior ∧ tested ≠ endpoint := by
  rw [connectedComponentNormalizedInterior,
    connectedComponentSortedSupport_mem_iff, List.mem_filter]
  simp

/-- Duplicate-free endpoint envelopes with the same support derive one
another. If the endpoints differ, duplicate the new endpoint, switch the
envelope, and contract the old endpoint. -/
theorem connectedComponentNormalizedEnvelopes_derives
    (oldEndpoint newEndpoint : Nat)
    (oldInterior newInterior suffix : List Nat)
    (oldNodup : oldInterior.Nodup)
    (newNodup : newInterior.Nodup)
    (oldAbsent : oldEndpoint ∉ oldInterior)
    (newAbsent : newEndpoint ∉ newInterior)
    (sameSupport :
      ∀ letter,
        (letter = oldEndpoint ∨ letter ∈ oldInterior) ↔
          (letter = newEndpoint ∨ letter ∈ newInterior)) :
    ConnectedComponentListDerives
      (oldEndpoint :: oldInterior ++ oldEndpoint :: suffix)
      (newEndpoint :: newInterior ++ newEndpoint :: suffix) := by
  by_cases endpointsEqual : oldEndpoint = newEndpoint
  · subst newEndpoint
    have interiorSupport :
        ∀ letter, letter ∈ oldInterior ↔ letter ∈ newInterior := by
      intro letter
      by_cases endpointLetter : letter = oldEndpoint
      · subst letter
        exact iff_of_false oldAbsent newAbsent
      · simpa [endpointLetter] using sameSupport letter
    exact
      connectedComponentListDerivesInteriorPermutationContext
        oldEndpoint suffix
        (connectedComponentPerm_of_nodup_mem_iff
          oldNodup newNodup interiorSupport)
  · have newInOld : newEndpoint ∈ oldInterior := by
      have supportMember :=
        (sameSupport newEndpoint).2 (Or.inl rfl)
      rcases supportMember with equals | member
      · exact False.elim (endpointsEqual equals.symm)
      · exact member
    have oldInNew : oldEndpoint ∈ newInterior := by
      have supportMember :=
        (sameSupport oldEndpoint).1 (Or.inl rfl)
      rcases supportMember with equals | member
      · exact False.elim (endpointsEqual equals)
      · exact member
    have arrange :
        oldInterior.Perm
          (newEndpoint :: oldInterior.erase newEndpoint) :=
      List.perm_cons_erase newInOld
    have first :=
      connectedComponentListDerivesInteriorPermutationContext
        oldEndpoint suffix arrange
    have duplicate :=
      (connectedComponentListDerivesInteriorContractionContext
        oldEndpoint newEndpoint []
        (oldInterior.erase newEndpoint) suffix).symm
    have switched :=
      connectedComponentListDerivesEndpointSwitchContext
        oldEndpoint newEndpoint
        (oldInterior.erase newEndpoint) suffix
    have contracted :=
      connectedComponentListDerivesInteriorContractionContext
        newEndpoint oldEndpoint []
        (oldInterior.erase newEndpoint) suffix
    have oldNotErased :
        oldEndpoint ∉ oldInterior.erase newEndpoint := by
      rw [List.mem_erase_of_ne endpointsEqual]
      exact oldAbsent
    have currentNodup :
        (oldEndpoint :: oldInterior.erase newEndpoint).Nodup :=
      List.nodup_cons.mpr
        ⟨oldNotErased, oldNodup.erase newEndpoint⟩
    have currentSupport :
        ∀ letter,
          letter ∈ oldEndpoint :: oldInterior.erase newEndpoint ↔
            letter ∈ newInterior := by
      intro letter
      by_cases newLetter : letter = newEndpoint
      · subst letter
        have erasedAbsent :
            newEndpoint ∉ oldInterior.erase newEndpoint := by
          simpa using
            (List.nodup_cons.mp
              (arrange.nodup_iff.mp oldNodup)).1
        simp [Ne.symm endpointsEqual, erasedAbsent, newAbsent]
      · rw [List.mem_cons, List.mem_erase_of_ne newLetter]
        have supportEquality := sameSupport letter
        simpa [newLetter] using supportEquality
    have restore :=
      connectedComponentListDerivesInteriorPermutationContext
        newEndpoint suffix
        (connectedComponentPerm_of_nodup_mem_iff
          currentNodup newNodup currentSupport)
    exact first.trans <|
      duplicate.trans <|
        switched.trans <|
          contracted.trans restore

/-- Canonical components of length at least two are duplicate-free endpoint
envelopes whose endpoint-plus-interior support is exactly the source
support. -/
theorem connectedComponentCanonicalComponent_envelope
    {component : List Nat}
    (lengthAtLeastTwo : 2 ≤ component.length) :
    ∃ endpoint interior,
      connectedComponentCanonicalComponent component =
        endpoint :: interior ++ [endpoint] ∧
      interior.Nodup ∧
      endpoint ∉ interior ∧
      (∀ letter,
        (letter = endpoint ∨ letter ∈ interior) ↔
          letter ∈ component) := by
  have componentNonempty : component ≠ [] := by
    intro empty
    subst component
    simp at lengthAtLeastTwo
  let support := connectedComponentSortedSupport component
  have supportNonempty : support ≠ [] :=
    connectedComponentSortedSupport_nonempty componentNonempty
  have supportNodup : support.Nodup := by
    exact connectedComponentSortedSupport_nodup component
  cases supportShape : support with
  | nil =>
      exact False.elim (supportNonempty supportShape)
  | cons endpoint remaining =>
      cases remaining with
      | nil =>
          have componentLengthNotOne : component.length ≠ 1 := by
            omega
          refine ⟨endpoint, [], ?_, List.nodup_nil, by simp, ?_⟩
          · simp [connectedComponentCanonicalComponent,
              connectedComponentSignatureOfList, support,
              supportShape, componentLengthNotOne]
          · intro letter
            have supportIff :=
              connectedComponentSortedSupport_mem_iff letter component
            have supportShape' :
                connectedComponentSortedSupport component = [endpoint] := by
              simpa [support] using supportShape
            rw [supportShape'] at supportIff
            simpa using supportIff
      | cons next rest =>
          have supportNodup' :
              (endpoint :: next :: rest).Nodup := by
            simpa [supportShape] using supportNodup
          refine
            ⟨endpoint, next :: rest, ?_,
              supportNodup'.tail,
              (List.nodup_cons.mp supportNodup').1,
              ?_⟩
          · simp [connectedComponentCanonicalComponent,
              connectedComponentSignatureOfList, support, supportShape]
          · intro letter
            have supportIff :=
              connectedComponentSortedSupport_mem_iff letter component
            have supportShape' :
                connectedComponentSortedSupport component =
                  endpoint :: next :: rest := by
              simpa [support] using supportShape
            rw [supportShape'] at supportIff
            simpa using supportIff

/-- Every support-connected component derives to its deterministic canonical
component render. -/
theorem connectedComponentCanonicalComponent_derives
    {component : List Nat}
    (nonempty : component ≠ [])
    (connected : ConnectedComponentSupportConnected component) :
    ConnectedComponentListDerives
      component (connectedComponentCanonicalComponent component) := by
  cases component with
  | nil =>
      contradiction
  | cons head tail =>
      cases tail with
      | nil =>
          simpa [connectedComponentCanonicalComponent,
            connectedComponentSignatureOfList,
            connectedComponentSortedSupport,
            connectedComponentDistinctSupport] using
              ConnectedComponentListDerives.refl [head]
      | cons next rest =>
          have lengthAtLeastTwo :
              2 ≤ (head :: next :: rest).length := by
            simp
          obtain ⟨initialInterior, suffix, initialShape, state⟩ :=
            connectedComponent_exists_initial_envelope
              connected lengthAtLeastTwo
          obtain ⟨finalInterior, plan⟩ :=
            state.exists_plan
          have absorbed :
              ConnectedComponentListDerives
                (head :: next :: rest)
                (connectedComponentEnvelopeRender
                  head finalInterior []) := by
            rw [initialShape]
            simpa [connectedComponentEnvelopeRender,
              List.append_assoc] using
                connectedComponentEnvelopePlan_derives plan
          have normalized :=
            connectedComponentNormalizeInterior_derives
              head finalInterior []
          obtain
            ⟨targetEndpoint, targetInterior, targetShape,
              targetNodup, targetAbsent, targetSupport⟩ :=
            connectedComponentCanonicalComponent_envelope
              lengthAtLeastTwo
          have normalizedSupport :
              ∀ letter,
                (letter = head ∨
                    letter ∈
                      connectedComponentNormalizedInterior
                        head finalInterior) ↔
                  letter ∈ head :: next :: rest := by
            intro letter
            constructor
            · intro member
              have finalMember :
                  letter = head ∨ letter ∈ finalInterior := by
                rcases member with equals | interiorMember
                · exact Or.inl equals
                · exact Or.inr <|
                    (connectedComponentNormalizedInterior_mem_iff
                      head letter finalInterior).1 interiorMember |>.1
              have initialMember :=
                (plan.support_iff letter).1 finalMember
              rw [initialShape]
              simpa [List.mem_append, or_assoc, or_left_comm, or_comm]
                using initialMember
            · intro member
              have initialMember :
                  letter = head ∨
                    letter ∈ initialInterior ∨ letter ∈ suffix := by
                rw [initialShape] at member
                simpa [List.mem_append, or_assoc, or_left_comm, or_comm]
                  using member
              have finalMember :=
                (plan.support_iff letter).2 initialMember
              rcases finalMember with equals | interiorMember
              · exact Or.inl equals
              · by_cases equals : letter = head
                · exact Or.inl equals
                · exact Or.inr <|
                    (connectedComponentNormalizedInterior_mem_iff
                      head letter finalInterior).2
                      ⟨interiorMember, equals⟩
          have switched :=
            connectedComponentNormalizedEnvelopes_derives
              head targetEndpoint
              (connectedComponentNormalizedInterior head finalInterior)
              targetInterior []
              (connectedComponentNormalizedInterior_nodup
                head finalInterior)
              targetNodup
              (connectedComponentNormalizedInterior_endpoint_absent
                head finalInterior)
              targetAbsent
              (fun letter =>
                (normalizedSupport letter).trans
                  (targetSupport letter).symm)
          rw [targetShape]
          exact absorbed.trans <| by
            simpa [connectedComponentEnvelopeRender,
              List.append_assoc] using normalized.trans switched

/-- Normalize every component in a component list while preserving their
order. -/
theorem connectedComponentCanonicalComponents_derives
    (components : List (List Nat))
    (nonempty :
      ∀ component, component ∈ components → component ≠ [])
    (connected :
      ∀ component, component ∈ components →
        ConnectedComponentSupportConnected component) :
    ConnectedComponentListDerives
      components.flatten
      (components.flatMap connectedComponentCanonicalComponent) := by
  induction components with
  | nil =>
      exact ConnectedComponentListDerives.refl []
  | cons component rest ih =>
      have componentDerives :=
        connectedComponentCanonicalComponent_derives
          (nonempty component (by simp))
          (connected component (by simp))
      have first :=
        componentDerives.append rest.flatten
      have recurse :=
        ih
          (fun current member =>
            nonempty current (List.Mem.tail component member))
          (fun current member =>
            connected current (List.Mem.tail component member))
      have second :=
        recurse.prepend
          (connectedComponentCanonicalComponent component)
      exact first.trans second

/-- Every list derives to the concatenation of the canonical renders of its
maximal support-connected components. -/
theorem connectedComponentCanonicalRenderList_derives
    (letters : List Nat) :
    ConnectedComponentListDerives
      letters (connectedComponentCanonicalRenderList letters) := by
  let components := connectedComponentDecomposeList letters
  have normalized :=
    connectedComponentCanonicalComponents_derives
      components
      (connectedComponentDecomposeList_nonempty_components letters)
      (connectedComponentDecomposeList_supportConnected letters)
  have flattenEq :=
    connectedComponentDecomposeList_flatten letters
  rw [connectedComponentCanonicalRenderList_eq_flatMap]
  simpa [components, flattenEq] using normalized

/-- Word-level normalization to the deterministic `S4_70` canonical
render. -/
theorem connectedComponentFour_derivesCanonical
    (word : Word Nat) :
    Derives connectedComponentFourBasis word
      (connectedComponentCanonicalRender word) := by
  have listDerivation :
      ConnectedComponentListDerives word.toList
        (connectedComponentCanonicalRender word).toList := by
    simpa using
      connectedComponentCanonicalRenderList_derives word.toList
  cases word with
  | mk sourceHead sourceTail =>
      cases target : connectedComponentCanonicalRender
          { head := sourceHead, tail := sourceTail } with
      | mk targetHead targetTail =>
          rw [target] at listDerivation
          simpa [connectedComponentWordOfCons] using
            listDerivation.toWord

end SemigroupBasis.Examples
