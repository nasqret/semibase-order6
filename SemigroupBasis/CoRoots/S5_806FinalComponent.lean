import SemigroupBasis.CoRoots.S5_806Normalization

namespace SemigroupBasis.CoRoots.S5_806

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## Actual-final connected-component normalization -/

private theorem canonicalComponentFlatMap_mem_iff
    {components : List (List Nat)}
    (nonempty :
      ∀ component, component ∈ components → component ≠ [])
    (tested : Nat) :
    tested ∈ components.flatMap connectedComponentCanonicalComponent ↔
      tested ∈ components.flatten := by
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨component, componentMember, testedMember⟩
    exact List.mem_flatten_of_mem componentMember <|
      (connectedComponentCanonicalComponent_mem_iff
        (nonempty component componentMember) tested).1 testedMember
  · intro testedMember
    rcases List.mem_flatten.mp testedMember with
      ⟨component, componentMember, componentContains⟩
    exact
      ⟨component, componentMember,
        (connectedComponentCanonicalComponent_mem_iff
          (nonempty component componentMember) tested).2
            componentContains⟩

private theorem head_disjoint_flatten
    {head : List Nat} {tail : List (List Nat)}
    (disjoint :
      ∀ component, component ∈ tail →
        ConnectedComponentSupportsDisjoint head component) :
    ConnectedComponentSupportsDisjoint head tail.flatten := by
  intro tested headMember tailMember
  rcases List.mem_flatten.mp tailMember with
    ⟨component, componentMember, componentContains⟩
  exact
    (disjoint component componentMember tested headMember)
      componentContains

/-- If a connected word is split immediately before its final letter, that
letter belongs to the first maximal component of the prefix. Otherwise the
first component would be disjoint from the entire nonempty suffix. -/
private theorem firstPrefixComponent_contains_endpoint
    (stem : List Nat) (endpoint : Nat)
    (connected :
      ConnectedComponentSupportConnected (stem ++ [endpoint]))
    {first : List Nat} {rest : List (List Nat)}
    (decomposition :
      connectedComponentDecomposeList stem = first :: rest) :
    endpoint ∈ first := by
  have firstNonempty : first ≠ [] :=
    connectedComponentDecomposeList_nonempty_components stem first <| by
      rw [decomposition]
      simp
  have flattenShape : first ++ rest.flatten = stem := by
    have flattened := connectedComponentDecomposeList_flatten stem
    rw [decomposition] at flattened
    simpa using flattened
  have pairwise :=
    connectedComponentDecomposeList_pairwiseDisjoint stem
  rw [decomposition] at pairwise
  have firstDisjoint :
      ∀ component, component ∈ rest →
        ConnectedComponentSupportsDisjoint first component := by
    intro component componentMember
    exact (List.pairwise_cons.mp pairwise).1 component componentMember
  have firstDisjointRest :
      ConnectedComponentSupportsDisjoint first rest.flatten :=
    head_disjoint_flatten firstDisjoint
  have split :
      stem ++ [endpoint] =
        first ++ (rest.flatten ++ [endpoint]) := by
    rw [← flattenShape, List.append_assoc]
  obtain ⟨tested, testedInFirst, testedInSuffix⟩ :=
    connected first (rest.flatten ++ [endpoint]) split
      firstNonempty (by simp)
  have testedNotInRest : tested ∉ rest.flatten :=
    firstDisjointRest tested testedInFirst
  have testedEq : tested = endpoint := by
    simpa [testedNotInRest] using testedInSuffix
  simpa [testedEq] using testedInFirst

/-- Retarget the canonical envelope of one prefix component to any selected
member of its support. The nonempty context is what makes the S4_70 endpoint
switch derivable from the S5_806 eighth law. -/
private theorem listDerivesRetargetCanonicalComponentBefore
    (component : List Nat)
    (lengthAtLeastTwo : 2 ≤ component.length)
    (newEndpoint : Nat) (newEndpointMember : newEndpoint ∈ component)
    (context : List Nat) (contextNonempty : context ≠ []) :
    ListDerives
      (connectedComponentCanonicalComponent component ++ context)
      (newEndpoint ::
        connectedComponentNormalizedInterior newEndpoint component ++
          newEndpoint :: context) := by
  obtain
    ⟨oldEndpoint, oldInterior, oldShape, oldNodup, oldAbsent,
      oldSupport⟩ :=
    connectedComponentCanonicalComponent_envelope lengthAtLeastTwo
  have newSupport :
      ∀ tested,
        (tested = newEndpoint ∨
            tested ∈
              connectedComponentNormalizedInterior newEndpoint component) ↔
          tested ∈ component := by
    intro tested
    constructor
    · rintro (equal | interiorMember)
      · simpa [equal] using newEndpointMember
      · exact
          (connectedComponentNormalizedInterior_mem_iff
            newEndpoint tested component).1 interiorMember |>.1
    · intro componentMember
      by_cases equal : tested = newEndpoint
      · exact Or.inl equal
      · exact Or.inr <|
          (connectedComponentNormalizedInterior_mem_iff
            newEndpoint tested component).2
              ⟨componentMember, equal⟩
  have switched :=
    connectedComponentNormalizedEnvelopes_derives
      oldEndpoint newEndpoint oldInterior
      (connectedComponentNormalizedInterior newEndpoint component) []
      oldNodup
      (connectedComponentNormalizedInterior_nodup
        newEndpoint component)
      oldAbsent
      (connectedComponentNormalizedInterior_endpoint_absent
        newEndpoint component)
      (fun tested =>
        (oldSupport tested).trans (newSupport tested).symm)
  have canonicalSwitched :
      ConnectedComponentListDerives
        (connectedComponentCanonicalComponent component)
        (newEndpoint ::
          connectedComponentNormalizedInterior newEndpoint component ++
            [newEndpoint]) := by
    rw [oldShape]
    simpa using switched
  have lifted :=
    liftConnectedComponentListDerivationBefore
      canonicalSwitched contextNonempty
  simpa [List.append_assoc] using lifted

/-- Every support-connected word displayed as `prefix ++ [endpoint]` with a
nonempty prefix derives to an envelope whose endpoint is that actual final
letter. The raw interior has exactly the remaining support, modulo possible
copies of the endpoint that are removed by the deterministic normalizer. -/
theorem existsConnectedComponentFinalEnvelope
    (stem : List Nat) (endpoint : Nat)
    (prefixNonempty : stem ≠ [])
    (connected :
      ConnectedComponentSupportConnected (stem ++ [endpoint])) :
    ∃ interior,
      ListDerives
        (stem ++ [endpoint])
        (endpoint :: interior ++ [endpoint]) ∧
      (∀ tested,
        (tested = endpoint ∨ tested ∈ interior) ↔
          tested ∈ stem ++ [endpoint]) := by
  have decompositionNonempty :=
    connectedComponentDecomposeList_nonempty prefixNonempty
  obtain ⟨first, rest, decomposition⟩ :=
    List.exists_cons_of_ne_nil decompositionNonempty
  have firstNonempty : first ≠ [] :=
    connectedComponentDecomposeList_nonempty_components stem first <| by
      rw [decomposition]
      simp
  have restNonempty :
      ∀ component, component ∈ rest → component ≠ [] := by
    intro component componentMember
    exact
      connectedComponentDecomposeList_nonempty_components stem component
        (by
          rw [decomposition]
          exact List.Mem.tail first componentMember)
  have flattenShape : first ++ rest.flatten = stem := by
    have flattened := connectedComponentDecomposeList_flatten stem
    rw [decomposition] at flattened
    simpa using flattened
  have endpointInFirst : endpoint ∈ first :=
    firstPrefixComponent_contains_endpoint
      stem endpoint connected decomposition
  let restRender :=
    rest.flatMap connectedComponentCanonicalComponent
  have initial :=
    listDerivesConnectedCanonicalBefore stem endpoint []
  rw [connectedComponentCanonicalRenderList_eq_flatMap,
    decomposition] at initial
  have initial' :
      ListDerives
        (stem ++ [endpoint])
        (connectedComponentCanonicalComponent first ++
          restRender ++ [endpoint]) := by
    simpa [restRender, List.append_assoc] using initial
  by_cases firstLengthOne : first.length = 1
  · rcases List.length_eq_one_iff.mp firstLengthOne with
      ⟨only, rfl⟩
    have endpointEq : endpoint = only := by
      simpa using endpointInFirst
    subst only
    have envelope :
        ListDerives
          (stem ++ [endpoint])
          (endpoint :: restRender ++ [endpoint]) := by
      simpa [connectedComponentCanonicalComponent,
        connectedComponentSignatureOfList,
        connectedComponentSortedSupport,
        connectedComponentDistinctSupport,
        List.append_assoc] using initial'
    refine ⟨restRender, envelope, ?_⟩
    intro tested
    rw [canonicalComponentFlatMap_mem_iff restNonempty tested]
    rw [← flattenShape]
    simp [or_assoc, or_left_comm, or_comm]
  · have firstPositive : 0 < first.length :=
      List.length_pos_iff.mpr firstNonempty
    have firstLengthAtLeastTwo : 2 ≤ first.length := by
      omega
    let firstInterior :=
      connectedComponentNormalizedInterior endpoint first
    have retargeted :=
      listDerivesRetargetCanonicalComponentBefore
        first firstLengthAtLeastTwo endpoint endpointInFirst
        (restRender ++ [endpoint]) (by simp)
    have retargeted' :
        ListDerives
          (connectedComponentCanonicalComponent first ++
            restRender ++ [endpoint])
          (endpoint :: firstInterior ++ endpoint ::
            restRender ++ [endpoint]) := by
      simpa [firstInterior, List.append_assoc] using retargeted
    have absorbed :=
      listDerivesEndpointAbsorption
        endpoint firstInterior restRender []
    have absorbed' :
        ListDerives
          (endpoint :: firstInterior ++ endpoint ::
            restRender ++ [endpoint])
          (endpoint :: (firstInterior ++ restRender) ++
            [endpoint]) := by
      simpa [List.append_assoc] using absorbed
    have envelope :
        ListDerives
          (stem ++ [endpoint])
          (endpoint :: (firstInterior ++ restRender) ++
            [endpoint]) :=
      initial'.trans (retargeted'.trans absorbed')
    refine ⟨firstInterior ++ restRender, envelope, ?_⟩
    intro tested
    constructor
    · rintro (equal | interiorMember)
      · subst tested
        simp
      · rcases List.mem_append.mp interiorMember with
          firstMember | restMember
        · have testedInFirst : tested ∈ first :=
            (connectedComponentNormalizedInterior_mem_iff
              endpoint tested first).1 firstMember |>.1
          have testedInPrefix : tested ∈ stem := by
            rw [← flattenShape]
            exact List.mem_append_left _ testedInFirst
          exact List.mem_append_left _ testedInPrefix
        · have testedInRest : tested ∈ rest.flatten :=
            (canonicalComponentFlatMap_mem_iff
              restNonempty tested).1 restMember
          have testedInPrefix : tested ∈ stem := by
            rw [← flattenShape]
            exact List.mem_append_right _ testedInRest
          exact List.mem_append_left _ testedInPrefix
    · intro sourceMember
      rcases List.mem_append.mp sourceMember with
        prefixMember | finalMember
      · rw [← flattenShape] at prefixMember
        rcases List.mem_append.mp prefixMember with
          firstMember | restMember
        · by_cases equal : tested = endpoint
          · exact Or.inl equal
          · exact Or.inr <| List.mem_append_left _ <|
              (connectedComponentNormalizedInterior_mem_iff
                endpoint tested first).2 ⟨firstMember, equal⟩
        · exact Or.inr <| List.mem_append_right _ <|
            (canonicalComponentFlatMap_mem_iff
              restNonempty tested).2 restMember
      · have equal : tested = endpoint := by
          simpa using finalMember
        exact Or.inl equal

private theorem dropLast_append_componentFinal
    (head : Nat) (tail : List Nat) :
    (head :: tail).dropLast ++ [componentFinal (head :: tail)] =
      head :: tail := by
  have reconstruction :=
    List.dropLast_concat_getLast
      (l := head :: tail) (by simp)
  rw [List.getLast_eq_getLastD] at reconstruction
  simpa only [componentFinal, List.getLastD_cons] using reconstruction

/-- The quantified multi-support final-component obligation is discharged
by connected-prefix decomposition and actual-final endpoint retargeting. -/
theorem finalComponentNormalization :
    FinalComponentNormalizationObligation := by
  intro component nonempty connected multiSupport
  cases component with
  | nil => contradiction
  | cons head tail =>
      cases tail with
      | nil =>
          have supportShape :
              connectedComponentSortedSupport [head] = [head] := by
            simp [connectedComponentSortedSupport,
              connectedComponentDistinctSupport]
          rw [supportShape] at multiSupport
          simp at multiSupport
      | cons next rest =>
          let component := head :: next :: rest
          let endpoint := componentFinal component
          let stem := component.dropLast
          have reconstruction : stem ++ [endpoint] = component := by
            simpa [component, endpoint, stem] using
              dropLast_append_componentFinal head (next :: rest)
          have prefixNonempty : stem ≠ [] := by
            intro prefixEmpty
            have lengths := congrArg List.length reconstruction
            rw [prefixEmpty] at lengths
            simp [component] at lengths
          have splitConnected :
              ConnectedComponentSupportConnected
                (stem ++ [endpoint]) := by
            rw [reconstruction]
            simpa [component] using connected
          obtain ⟨rawInterior, envelope, envelopeSupport⟩ :=
            existsConnectedComponentFinalEnvelope
              stem endpoint prefixNonempty splitConnected
          have envelope' :
              ListDerives component
                (endpoint :: rawInterior ++ [endpoint]) := by
            rw [← reconstruction]
            exact envelope
          have envelopeSupport' :
              ∀ tested,
                (tested = endpoint ∨ tested ∈ rawInterior) ↔
                  tested ∈ component := by
            intro tested
            rw [← reconstruction]
            exact envelopeSupport tested
          have interiorsEqual :
              normalizedInterior endpoint rawInterior =
                normalizedInterior endpoint component := by
            apply normalizedInterior_eq_of_mem_iff endpoint
            intro tested different
            constructor
            · intro rawMember
              exact
                (envelopeSupport' tested).1 (Or.inr rawMember)
            · intro componentMember
              rcases (envelopeSupport' tested).2 componentMember with
                equal | rawMember
              · exact False.elim (different equal)
              · exact rawMember
          have normalized :=
            listDerivesNormalizeInterior endpoint rawInterior []
          rw [interiorsEqual] at normalized
          have canonicalEnvelope :
              ListDerives component
                (endpoint :: normalizedInterior endpoint component ++
                  [endpoint]) :=
            envelope'.trans <| by
              simpa [List.append_assoc] using normalized
          have multiSupport' :
              2 ≤ (connectedComponentSortedSupport component).length := by
            simpa [component] using multiSupport
          cases supportShape :
              connectedComponentSortedSupport component with
          | nil =>
              rw [supportShape] at multiSupport'
              simp at multiSupport'
          | cons first remaining =>
              cases remaining with
              | nil =>
                  rw [supportShape] at multiSupport'
                  simp at multiSupport'
              | cons second remaining =>
                  simpa [finalComponentCanonical, supportShape,
                    component, endpoint] using canonicalEnvelope

/-- Unconditional normalization of one nonempty connected final component. -/
theorem listDerivesFinalComponentCanonicalComplete
    (component : List Nat) (nonempty : component ≠ [])
    (connected : ConnectedComponentSupportConnected component) :
    ListDerives component (finalComponentCanonical component) :=
  listDerivesFinalComponentCanonical
    finalComponentNormalization component nonempty connected

/-- Unconditional normalization of every list to the exact S5_806
connected-cut candidate render. -/
theorem listDerivesCanonicalRenderComplete
    (letters : List Nat) :
    ListDerives letters (canonicalRenderList letters) :=
  listDerivesCanonicalRender finalComponentNormalization letters

end SemigroupBasis.CoRoots.S5_806
