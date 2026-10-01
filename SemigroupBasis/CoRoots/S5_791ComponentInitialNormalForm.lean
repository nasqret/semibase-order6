import SemigroupBasis.CoRoots.S5_791EnvelopePlan

namespace SemigroupBasis.CoRoots.S5_791

open SemigroupBasis
open SemigroupBasis.Examples

/-- Close a nonempty first-occurrence order at its first letter. -/
def closeInitialOrder : List Nat → List Nat
  | [] => []
  | first :: rest => first :: rest ++ [first]

/-- Render one connected-component signature in the global first-occurrence
order. A simple unary component stays linear; every other component closes
at its first letter. -/
def componentInitialRender
    (initials : List Nat)
    (signature : connectedComponentSignature) : List Nat :=
  let order :=
    initials.filter fun letter =>
      decide (letter ∈ signature.support)
  if signature.support.length = 1 ∧
      signature.repeatedUnary = false then
    order
  else
    closeInitialOrder order

/-- The deterministic normal form for the exact ordered-component/initial
signature. -/
def componentInitialNormalList (word : Word Nat) : List Nat :=
  let initials := firstOccurrenceSequence word.toList
  (connectedComponentSignaturesWord word).flatMap
    (componentInitialRender initials)

/-- Equality of the semantic signature gives literal equality of the
deterministic normal forms. -/
theorem componentInitialNormalList_eq_of_sameSignature
    {left right : Word Nat}
    (same :
      S5_791Invariant.SameComponentInitialSignature left right) :
    componentInitialNormalList left =
      componentInitialNormalList right := by
  unfold componentInitialNormalList
  rw [same.components, same.initials]

private theorem mem_firstOccurrenceSequence_iff
    (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ firstOccurrenceSequence letters ↔
        selected ∈ letters
  | [] => by
      simp [firstOccurrenceSequence]
  | letter :: rest => by
      by_cases equal : selected = letter
      · subst letter
        simp [firstOccurrenceSequence]
      · simp [firstOccurrenceSequence, equal,
          mem_firstOccurrenceSequence_iff selected rest]

private theorem filter_filter_ne_comm
    (keep : Nat → Bool) (selected : Nat)
    (letters : List Nat) :
    (letters.filter keep).filter
        (fun letter => decide (letter ≠ selected)) =
      (letters.filter
        (fun letter => decide (letter ≠ selected))).filter keep := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro letter _
  exact Bool.and_comm _ _

private theorem filter_ne_then_keep_of_drop
    (keep : Nat → Bool) (selected : Nat)
    (dropped : ¬ keep selected)
    (letters : List Nat) :
    (letters.filter
        (fun letter => decide (letter ≠ selected))).filter keep =
      letters.filter keep := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro letter _
  by_cases equal : letter = selected
  · subst letter
    simp [dropped]
  · simp [equal]

/-- First-occurrence normalization commutes with support restriction. -/
private theorem firstOccurrenceSequence_filter
    (keep : Nat → Bool) :
    ∀ letters : List Nat,
      firstOccurrenceSequence (letters.filter keep) =
        (firstOccurrenceSequence letters).filter keep
  | [] => rfl
  | letter :: rest => by
      by_cases kept : keep letter
      · rw [List.filter_cons, if_pos kept,
          firstOccurrenceSequence, firstOccurrenceSequence,
          firstOccurrenceSequence_filter keep rest,
          List.filter_cons, if_pos kept]
        exact congrArg (List.cons letter) <|
          filter_filter_ne_comm keep letter
            (firstOccurrenceSequence rest)
      · rw [List.filter_cons, if_neg kept,
          firstOccurrenceSequence_filter keep rest,
          firstOccurrenceSequence,
          List.filter_cons, if_neg kept]
        exact
          (filter_ne_then_keep_of_drop keep letter kept
            (firstOccurrenceSequence rest)).symm

private theorem connectedComponentDecomposeList_eq_singleton
    {letters : List Nat}
    (nonempty : letters ≠ [])
    (connected : ConnectedComponentSupportConnected letters) :
    connectedComponentDecomposeList letters = [letters] := by
  have decompositionNonempty :=
    connectedComponentDecomposeList_nonempty nonempty
  obtain ⟨first, rest, decompositionShape⟩ :=
    List.exists_cons_of_ne_nil decompositionNonempty
  cases rest with
  | nil =>
      have flattened :=
        connectedComponentDecomposeList_flatten letters
      rw [decompositionShape] at flattened
      have firstEq : first = letters := by
        simpa using flattened
      simpa [firstEq] using decompositionShape
  | cons second remaining =>
      have firstNonempty :
          first ≠ [] :=
        connectedComponentDecomposeList_nonempty_components letters
          first (by rw [decompositionShape]; simp)
      have suffixNonempty :
          (second :: remaining).flatten ≠ [] := by
        have secondNonempty :
            second ≠ [] :=
          connectedComponentDecomposeList_nonempty_components letters
            second (by rw [decompositionShape]; simp)
        intro flattenedEmpty
        have appendedEmpty :
            second ++ remaining.flatten = [] := by
          simpa using flattenedEmpty
        exact secondNonempty (List.append_eq_nil_iff.mp appendedEmpty).1
      have pairwise :=
        connectedComponentDecomposeList_pairwiseDisjoint letters
      rw [decompositionShape] at pairwise
      have firstToSuffix :=
        (List.pairwise_cons.mp pairwise).1
      have disjoint :
          ConnectedComponentSupportsDisjoint
            first (second :: remaining).flatten := by
        intro letter firstMember suffixMember
        rw [List.mem_flatten] at suffixMember
        rcases suffixMember with
          ⟨candidate, candidateMember, letterMember⟩
        exact
          (firstToSuffix candidate candidateMember
            letter firstMember) letterMember
      have flattened :=
        connectedComponentDecomposeList_flatten letters
      rw [decompositionShape] at flattened
      have sourceShape :
          letters = first ++ (second :: remaining).flatten := by
        simpa using flattened.symm
      obtain ⟨letter, firstMember, suffixMember⟩ :=
        connected first (second :: remaining).flatten
          sourceShape firstNonempty suffixNonempty
      exact False.elim <|
        disjoint letter firstMember suffixMember

private theorem supportConnected_of_same_component_signatures
    {source target : List Nat}
    (sourceNonempty : source ≠ [])
    (sourceConnected :
      ConnectedComponentSupportConnected source)
    (same :
      connectedComponentSignaturesList source =
        connectedComponentSignaturesList target) :
    ConnectedComponentSupportConnected target := by
  have sourceDecomposition :=
    connectedComponentDecomposeList_eq_singleton
      sourceNonempty sourceConnected
  have sourceSignatures :
      connectedComponentSignaturesList source =
        [connectedComponentSignatureOfList source] := by
    simp [connectedComponentSignaturesList, sourceDecomposition]
  have targetSignatures :
      connectedComponentSignaturesList target =
        [connectedComponentSignatureOfList source] := by
    rw [← same, sourceSignatures]
  have targetDecompositionLength :
      (connectedComponentDecomposeList target).length = 1 := by
    have lengths := congrArg List.length targetSignatures
    simpa [connectedComponentSignaturesList] using lengths
  obtain ⟨only, targetDecomposition⟩ :=
    List.length_eq_one_iff.mp targetDecompositionLength
  have onlyConnected :=
    connectedComponentDecomposeList_supportConnected target
      only (by rw [targetDecomposition]; simp)
  have flattened :=
    connectedComponentDecomposeList_flatten target
  rw [targetDecomposition] at flattened
  have onlyEq : only = target := by
    simpa using flattened
  simpa [onlyEq] using onlyConnected

/-- Endpoint capping preserves support-connectedness because every basis
derivation preserves the full ordered component signature. -/
private theorem endpointCap_supportConnected
    {head : Nat} {tail : List Nat}
    (connected :
      ConnectedComponentSupportConnected (head :: tail)) :
    ConnectedComponentSupportConnected
      (uniqueSeparatorEndpointCap (head :: tail)) := by
  have capShape :
      uniqueSeparatorEndpointCap (head :: tail) =
        head :: uniqueSeparatorEndpointCapAux [head] tail := by
    simp [uniqueSeparatorEndpointCap,
      uniqueSeparatorEndpointCapAux]
  have capDerivation :=
    listDerivesEndpointCap (head :: tail)
  rw [capShape] at capDerivation
  have wordDerivation :=
    S5_107.ListDerives.toWord capDerivation
  have sameLists :
      connectedComponentSignaturesList (head :: tail) =
        connectedComponentSignaturesList
          (uniqueSeparatorEndpointCap (head :: tail)) := by
    rw [capShape]
    simpa [connectedComponentSignaturesWord,
      S5_107.listWordOfCons, Word.toList] using
      (derives_sameSignature wordDerivation).components
  exact
    supportConnected_of_same_component_signatures
      (by simp) connected sameLists

private theorem endpointCap_lengthAtLeastTwo
    {head next : Nat} {rest : List Nat}
    (connected :
      ConnectedComponentSupportConnected
        (head :: next :: rest)) :
    2 ≤ (uniqueSeparatorEndpointCap
      (head :: next :: rest)).length := by
  have headInTail :
      head ∈ next :: rest :=
    connectedComponentSupportConnected_cons_tail
      connected (by simp)
  have sourceCount :
      2 ≤ (head :: next :: rest).count head := by
    have positive :
        1 ≤ (next :: rest).count head :=
      List.one_le_count_iff.mpr headInTail
    simp only [List.count_cons_self]
    omega
  have capCount :
      (uniqueSeparatorEndpointCap
        (head :: next :: rest)).count head = 2 :=
    (uniqueSeparatorEndpointCap_count_eq_two_iff
      head (head :: next :: rest)).2 sourceCount
  have countBound :=
    List.count_le_length
      (a := head)
      (l := uniqueSeparatorEndpointCap (head :: next :: rest))
  omega

/-- Local component normal form: a singleton remains linear; every longer
support-connected component closes its first-occurrence sequence. -/
def componentInitialLocalNormalList : List Nat → List Nat
  | [] => []
  | [letter] => [letter]
  | head :: next :: rest =>
      closeInitialOrder
        (firstOccurrenceSequence (head :: next :: rest))

private theorem listDerivesComponentInitialLocalNormal
    (component : List Nat)
    (nonempty : component ≠ [])
    (connected :
      ConnectedComponentSupportConnected component) :
    S5_107.ListDerives basis component
      (componentInitialLocalNormalList component) := by
  cases component with
  | nil =>
      contradiction
  | cons head tail =>
      cases tail with
      | nil =>
          simpa [componentInitialLocalNormalList] using
            S5_107.ListDerives.refl
              (basis := basis) [head]
      | cons next rest =>
          let source := head :: next :: rest
          let capped := uniqueSeparatorEndpointCap source
          have capDerivation :
              S5_107.ListDerives basis source capped :=
            listDerivesEndpointCap source
          have cappedConnected :
              ConnectedComponentSupportConnected capped := by
            exact endpointCap_supportConnected connected
          have cappedLength : 2 ≤ capped.length := by
            exact endpointCap_lengthAtLeastTwo connected
          have cappedTwoLimited :
              UniqueSeparatorTwoLimited capped :=
            uniqueSeparatorEndpointCap_twoLimited source
          have cappedShape :
              capped =
                head ::
                  uniqueSeparatorEndpointCapAux
                    [head] (next :: rest) := by
            simp [capped, source, uniqueSeparatorEndpointCap,
              uniqueSeparatorEndpointCapAux]
          have envelopeDerivation :
              S5_107.ListDerives basis capped
                (firstOccurrenceSequence capped ++ [head]) := by
            rw [cappedShape]
            exact
              listDerivesConnectedInitialEnvelope
                (by simpa [cappedShape] using cappedConnected)
                (by simpa [cappedShape] using cappedLength)
                (by simpa [cappedShape] using cappedTwoLimited)
          have combined :=
            capDerivation.trans envelopeDerivation
          have initialsPreserved :
              firstOccurrenceSequence capped =
                firstOccurrenceSequence source := by
            simpa [capped, source] using
              firstOccurrenceSequence_endpointCap source
          rw [initialsPreserved] at combined
          simpa [source, componentInitialLocalNormalList,
            closeInitialOrder, firstOccurrenceSequence] using combined

private theorem filter_component_of_pairwise :
    ∀ (components : List (List Nat)) (component : List Nat),
      components.Pairwise ConnectedComponentSupportsDisjoint →
      component ∈ components →
      components.flatten.filter
          (fun letter => decide (letter ∈ component)) =
        component
  | [], component, _, member => by
      simp at member
  | current :: remaining, component, pairwise, member => by
      rw [List.pairwise_cons] at pairwise
      rcases List.mem_cons.mp member with componentEq | componentMember
      · subst component
        have currentFilter :
            List.filter
                (fun letter => decide (letter ∈ current)) current =
              current := by
          apply List.filter_eq_self.mpr
          intro letter letterMember
          exact decide_eq_true letterMember
        have remainingFilter :
            remaining.flatten.filter
                (fun letter => decide (letter ∈ current)) =
              [] := by
          apply List.filter_eq_nil_iff.mpr
          intro letter flattenedMember
          simp only [decide_eq_true_eq]
          intro currentMember
          rw [List.mem_flatten] at flattenedMember
          rcases flattenedMember with
            ⟨candidate, candidateMember, candidateContains⟩
          exact
            (pairwise.1 candidate candidateMember
              letter currentMember) candidateContains
        simp [currentFilter, remainingFilter]
      · have currentFilter :
            current.filter
                (fun letter => decide (letter ∈ component)) =
              [] := by
          apply List.filter_eq_nil_iff.mpr
          intro letter currentMember
          simp only [decide_eq_true_eq]
          intro componentContains
          exact
            (pairwise.1 component componentMember
              letter currentMember) componentContains
        rw [List.flatten_cons, List.filter_append,
          currentFilter, List.nil_append]
        exact
          filter_component_of_pairwise
            remaining component pairwise.2 componentMember

private theorem firstOccurrenceSequence_restrict_component
    (word : Word Nat) {component : List Nat}
    (componentMember :
      component ∈
        connectedComponentDecomposeList word.toList) :
    (firstOccurrenceSequence word.toList).filter
        (fun letter =>
          decide
            (letter ∈
              (connectedComponentSignatureOfList component).support)) =
      firstOccurrenceSequence component := by
  have supportFilter :
      (firstOccurrenceSequence word.toList).filter
          (fun letter =>
            decide
              (letter ∈
                (connectedComponentSignatureOfList component).support)) =
        (firstOccurrenceSequence word.toList).filter
          (fun letter => decide (letter ∈ component)) := by
    apply List.filter_congr
    intro letter _
    simp [connectedComponentSignatureOfList_support,
      connectedComponentSortedSupport_mem_iff]
  have wholeFilter :
      word.toList.filter
          (fun letter => decide (letter ∈ component)) =
        component := by
    rw [← connectedComponentDecomposeList_flatten word.toList]
    exact
      filter_component_of_pairwise
        (connectedComponentDecomposeList word.toList)
        component
        (connectedComponentDecomposeList_pairwiseDisjoint
          word.toList)
        componentMember
  calc
    (firstOccurrenceSequence word.toList).filter
          (fun letter =>
            decide
              (letter ∈
                (connectedComponentSignatureOfList component).support)) =
        (firstOccurrenceSequence word.toList).filter
          (fun letter => decide (letter ∈ component)) :=
      supportFilter
    _ =
        firstOccurrenceSequence
          (word.toList.filter
            (fun letter => decide (letter ∈ component))) :=
      (firstOccurrenceSequence_filter
        (fun letter => decide (letter ∈ component))
        word.toList).symm
    _ = firstOccurrenceSequence component := by
      rw [wholeFilter]

private theorem componentInitialLocalNormal_eq_render
    (word : Word Nat) {component : List Nat}
    (componentMember :
      component ∈
        connectedComponentDecomposeList word.toList)
    (componentNonempty : component ≠ []) :
    componentInitialLocalNormalList component =
      componentInitialRender
        (firstOccurrenceSequence word.toList)
        (connectedComponentSignatureOfList component) := by
  have restricted :=
    firstOccurrenceSequence_restrict_component
      word componentMember
  cases component with
  | nil =>
      contradiction
  | cons head tail =>
      cases tail with
      | nil =>
          have signatureShape :
              connectedComponentSignatureOfList [head] =
                ⟨[head], false⟩ := by
            simp [connectedComponentSignatureOfList,
              connectedComponentSortedSupport,
              connectedComponentDistinctSupport]
          have restrictedHead :
              (firstOccurrenceSequence word.toList).filter
                  (fun letter => decide (letter = head)) =
                [head] := by
            simpa [signatureShape, firstOccurrenceSequence] using restricted
          simp [componentInitialLocalNormalList,
            componentInitialRender, signatureShape,
            restrictedHead, firstOccurrenceSequence]
      | cons next rest =>
          have lengthNe :
              (head :: next :: rest).length ≠ 1 := by
            simp
          have notSimple :
              ¬((connectedComponentSignatureOfList
                    (head :: next :: rest)).support.length = 1 ∧
                (connectedComponentSignatureOfList
                    (head :: next :: rest)).repeatedUnary = false) := by
            rintro ⟨supportLength, repeatedFalse⟩
            obtain ⟨letter, supportShape⟩ :=
              List.length_eq_one_iff.mp supportLength
            have sortedShape :
                connectedComponentSortedSupport
                    (head :: next :: rest) =
                  [letter] := by
              rw [← connectedComponentSignatureOfList_support]
              exact supportShape
            have repeatedTrue :
                (connectedComponentSignatureOfList
                    (head :: next :: rest)).repeatedUnary = true := by
              simp [connectedComponentSignatureOfList,
                sortedShape, lengthNe]
            rw [repeatedTrue] at repeatedFalse
            contradiction
          simp [componentInitialLocalNormalList,
            componentInitialRender, restricted, notSimple]

private theorem flatMap_congr_of_mem
    {α β : Type} (left right : α → List β) :
    ∀ letters : List α,
      (∀ letter ∈ letters, left letter = right letter) →
      letters.flatMap left = letters.flatMap right
  | [], _ => rfl
  | letter :: rest, same => by
      rw [List.flatMap_cons, List.flatMap_cons,
        same letter (by simp)]
      exact congrArg (fun suffix => right letter ++ suffix) <|
        flatMap_congr_of_mem left right rest <| by
          intro selected member
          exact same selected (by simp [member])

private theorem componentLocalNormals_eq_normalList
    (word : Word Nat) :
    (connectedComponentDecomposeList word.toList).flatMap
        componentInitialLocalNormalList =
      componentInitialNormalList word := by
  unfold componentInitialNormalList
    connectedComponentSignaturesWord
    connectedComponentSignaturesList
  rw [List.flatMap_map]
  apply flatMap_congr_of_mem
  intro component componentMember
  exact
    componentInitialLocalNormal_eq_render
      word componentMember
      (connectedComponentDecomposeList_nonempty_components
        word.toList component componentMember)

private theorem listDerivesComponentsLocalNormal :
    ∀ components : List (List Nat),
      (∀ component ∈ components, component ≠ []) →
      (∀ component ∈ components,
        ConnectedComponentSupportConnected component) →
      S5_107.ListDerives basis components.flatten
        (components.flatMap componentInitialLocalNormalList)
  | [], _, _ =>
      S5_107.ListDerives.empty
  | component :: remaining, componentNonempty,
      componentConnected => by
      have headDerivation :=
        listDerivesComponentInitialLocalNormal
          component
          (componentNonempty component (by simp))
          (componentConnected component (by simp))
      have tailNonempty :
          ∀ candidate ∈ remaining, candidate ≠ [] := by
        intro candidate member
        exact componentNonempty candidate (by simp [member])
      have tailConnected :
          ∀ candidate ∈ remaining,
            ConnectedComponentSupportConnected candidate := by
        intro candidate member
        exact componentConnected candidate (by simp [member])
      have tailDerivation :=
        listDerivesComponentsLocalNormal
          remaining tailNonempty tailConnected
      have first :=
        headDerivation.append remaining.flatten
      have second :=
        tailDerivation.prepend
          (componentInitialLocalNormalList component)
      simpa [List.flatMap_cons, List.append_assoc] using
        first.trans second

/-- Every word derives to its deterministic component/initial normal form. -/
theorem listDerivesComponentInitialNormal
    (word : Word Nat) :
    S5_107.ListDerives basis word.toList
      (componentInitialNormalList word) := by
  have derivation :=
    listDerivesComponentsLocalNormal
      (connectedComponentDecomposeList word.toList)
      (connectedComponentDecomposeList_nonempty_components
        word.toList)
      (connectedComponentDecomposeList_supportConnected
        word.toList)
  rw [connectedComponentDecomposeList_flatten word.toList]
    at derivation
  rw [componentLocalNormals_eq_normalList word] at derivation
  exact derivation

/-- Unrestricted syntactic completeness of the ordered connected-component
signatures together with the complete first-occurrence sequence. -/
theorem derives_of_sameComponentInitialSignature
    {left right : Word Nat}
    (same :
      S5_791Invariant.SameComponentInitialSignature left right) :
    Derives basis left right := by
  have leftNormal :=
    listDerivesComponentInitialNormal left
  have rightNormal :=
    listDerivesComponentInitialNormal right
  have normalEqual :=
    componentInitialNormalList_eq_of_sameSignature same
  rw [normalEqual] at leftNormal
  have combined := leftNormal.trans rightNormal.symm
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          exact S5_107.ListDerives.toWord combined

end SemigroupBasis.CoRoots.S5_791
