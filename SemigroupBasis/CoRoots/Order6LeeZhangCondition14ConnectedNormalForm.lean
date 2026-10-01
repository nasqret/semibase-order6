import SemigroupBasis.CoRoots.Order6LeeZhangCondition14InteriorNormal
import SemigroupBasis.CoRoots.Order6LeeZhangCondition14Invariant

/-!
# Connected-word normalization for Lee--Zhang Condition 14

This file formalizes the two cases in Lee--Zhang Lemma 9.3.  The first stage
selects the last occurrence of the head and moves it right until it closes the
word.  If the next letter already occurs in the interior, (9.2c) performs the
move.  Otherwise connectedness supplies a letter shared by the interior and
the remaining suffix; the sequence `(9.2a)^-1`, `(9.2d)^-1`, `(9.2a)` performs
the same move.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private abbrev listWordOfCons :=
  SemigroupBasis.CoRoots.S5_107.listWordOfCons

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
      have flattened := connectedComponentDecomposeList_flatten letters
      rw [decompositionShape] at flattened
      have firstEq : first = letters := by
        simpa using flattened
      simpa [firstEq] using decompositionShape
  | cons second remaining =>
      have firstNonempty : first ≠ [] :=
        connectedComponentDecomposeList_nonempty_components letters
          first (by rw [decompositionShape]; simp)
      have suffixNonempty : (second :: remaining).flatten ≠ [] := by
        have secondNonempty : second ≠ [] :=
          connectedComponentDecomposeList_nonempty_components letters
            second (by rw [decompositionShape]; simp)
        intro flattenedEmpty
        have appendedEmpty : second ++ remaining.flatten = [] := by
          simpa using flattenedEmpty
        exact secondNonempty (List.append_eq_nil_iff.mp appendedEmpty).1
      have pairwise :=
        connectedComponentDecomposeList_pairwiseDisjoint letters
      rw [decompositionShape] at pairwise
      have firstToSuffix := (List.pairwise_cons.mp pairwise).1
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
      have flattened := connectedComponentDecomposeList_flatten letters
      rw [decompositionShape] at flattened
      have sourceShape :
          letters = first ++ (second :: remaining).flatten := by
        simpa using flattened.symm
      obtain ⟨letter, firstMember, suffixMember⟩ :=
        connected first (second :: remaining).flatten
          sourceShape firstNonempty suffixNonempty
      exact False.elim <| disjoint letter firstMember suffixMember

private theorem supportConnected_of_same_component_signatures
    {source target : List Nat}
    (sourceNonempty : source ≠ [])
    (sourceConnected : ConnectedComponentSupportConnected source)
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
  have flattened := connectedComponentDecomposeList_flatten target
  rw [targetDecomposition] at flattened
  have onlyEq : only = target := by
    simpa using flattened
  simpa [onlyEq] using onlyConnected

private theorem supportConnected_of_listDerives
    {sourceHead targetHead : Nat}
    {sourceTail targetTail : List Nat}
    (connected :
      ConnectedComponentSupportConnected (sourceHead :: sourceTail))
    (derivation :
      ListDerives (sourceHead :: sourceTail) (targetHead :: targetTail)) :
    ConnectedComponentSupportConnected (targetHead :: targetTail) := by
  have wordDerivation :=
    SemigroupBasis.CoRoots.S5_107.ListDerives.toWord derivation
  have preserved :=
    (derives_sameComponentInitialParitySignature wordDerivation).componentInitial.components
  have sameLists :
      connectedComponentSignaturesList (sourceHead :: sourceTail) =
        connectedComponentSignaturesList (targetHead :: targetTail) := by
    simpa [connectedComponentSignaturesWord, listWordOfCons,
      Word.toList] using preserved
  exact supportConnected_of_same_component_signatures
    (by simp) connected sameLists

private theorem exists_lastOccurrenceSplit (endpoint : Nat) :
    forall letters : List Nat,
      endpoint ∈ letters →
        ∃ before after,
          letters = before ++ endpoint :: after ∧ endpoint ∉ after
  | [], member => by simp at member
  | letter :: rest, member => by
      by_cases endpointInRest : endpoint ∈ rest
      · obtain ⟨before, after, shape, endpointAbsent⟩ :=
          exists_lastOccurrenceSplit endpoint rest endpointInRest
        exact
          ⟨letter :: before, after, by simp [shape], endpointAbsent⟩
      · have letterEq : letter = endpoint := by
          have endpointEq : endpoint = letter := by
            simpa [endpointInRest] using member
          exact endpointEq.symm
        subst letter
        exact ⟨[], rest, by simp, endpointInRest⟩

/-- One Case 2 step of Lee--Zhang Lemma 9.3: move the displayed last endpoint
past the first suffix letter. -/
theorem listDerivesAdvanceClosingEndpoint
    (endpoint next : Nat) (interior suffix : List Nat)
    (connected :
      ConnectedComponentSupportConnected
        ([endpoint] ++ interior ++ [endpoint, next] ++ suffix))
    (endpointNotSuffix : endpoint ∉ next :: suffix) :
    ListDerives
      ([endpoint] ++ interior ++ [endpoint, next] ++ suffix)
      ([endpoint] ++ interior ++ [next, endpoint] ++ suffix) := by
  by_cases nextInInterior : next ∈ interior
  · obtain ⟨before, after, interiorShape⟩ :=
      List.append_of_mem nextInInterior
    have step :=
      (listDerivesContextFinalSwap endpoint next before after).append suffix
    simpa [interiorShape, List.append_assoc] using step
  · have intersect :=
      connected
        ([endpoint] ++ interior ++ [endpoint])
        (next :: suffix)
        (by simp [List.append_assoc])
        (by simp) (by simp)
    obtain ⟨shared, sharedInLeft, sharedInRight⟩ := intersect
    have sharedNeEndpoint : shared ≠ endpoint := by
      intro equal
      subst shared
      exact endpointNotSuffix sharedInRight
    have sharedInInterior : shared ∈ interior := by
      simpa [sharedNeEndpoint, Ne.symm sharedNeEndpoint,
        List.mem_append] using sharedInLeft
    have sharedNeNext : shared ≠ next := by
      intro equal
      subst shared
      exact nextInInterior sharedInInterior
    have sharedInSuffix : shared ∈ suffix := by
      simpa [sharedNeNext] using sharedInRight
    obtain ⟨leftBefore, leftAfter, interiorShape⟩ :=
      List.append_of_mem sharedInInterior
    obtain ⟨rightBefore, rightAfter, suffixShape⟩ :=
      List.append_of_mem sharedInSuffix
    have first :
        ListDerives
          ([endpoint] ++ interior ++ [endpoint, next] ++ suffix)
          ([endpoint] ++ interior ++ [endpoint, endpoint, endpoint, next] ++
            suffix) := by
      simpa [List.append_assoc] using
        ((listDerivesContextSquareDeletion endpoint interior []).symm.append
          (next :: suffix))
    have second :
        ListDerives
          ([endpoint] ++ interior ++ [endpoint, endpoint, endpoint, next] ++
            suffix)
          ([endpoint] ++ interior ++ [endpoint, endpoint, next, endpoint] ++
            suffix) := by
      have core :=
        (listDerivesContextGatherRepeat shared endpoint next
          (leftAfter ++ [endpoint]) rightBefore).symm
      have contextual := core.context ([endpoint] ++ leftBefore) rightAfter
      simpa [interiorShape, suffixShape, List.append_assoc] using contextual
    have third :
        ListDerives
          ([endpoint] ++ interior ++ [endpoint, endpoint, next, endpoint] ++
            suffix)
          ([endpoint] ++ interior ++ [next, endpoint] ++ suffix) := by
      simpa [List.append_assoc] using
        (listDerivesContextSquareDeletion endpoint interior [next]).append
          suffix
    exact first.trans (second.trans third)

/-- Repeat Case 2 until the displayed last endpoint is literally final. -/
theorem listDerivesClosingEndpointToEnd
    (endpoint : Nat) :
    forall (interior suffix : List Nat),
      ConnectedComponentSupportConnected
        ([endpoint] ++ interior ++ [endpoint] ++ suffix) →
      endpoint ∉ suffix →
      ListDerives
        ([endpoint] ++ interior ++ [endpoint] ++ suffix)
        ([endpoint] ++ (interior ++ suffix) ++ [endpoint])
  | interior, [], _, _ => by
      simpa [List.append_assoc] using
        (SemigroupBasis.CoRoots.S5_107.ListDerives.refl
          (basis := basis) ([endpoint] ++ interior ++ [endpoint]))
  | interior, next :: rest, connected, endpointAbsent => by
      have endpointAbsentWhole : endpoint ∉ next :: rest := endpointAbsent
      have first :=
        listDerivesAdvanceClosingEndpoint endpoint next interior rest
          (by simpa [List.append_assoc] using connected)
          endpointAbsentWhole
      have movedConnected :
          ConnectedComponentSupportConnected
            ([endpoint] ++ (interior ++ [next]) ++ [endpoint] ++ rest) := by
        have preserved := supportConnected_of_listDerives
          (by simpa [List.append_assoc] using connected) first
        simpa [List.append_assoc] using preserved
      have endpointAbsentRest : endpoint ∉ rest := by
        intro member
        exact endpointAbsent (List.Mem.tail next member)
      have remaining :=
        listDerivesClosingEndpointToEnd endpoint
          (interior ++ [next]) rest movedConnected endpointAbsentRest
      simpa [List.append_assoc] using first.trans (by
        simpa [List.append_assoc] using remaining)
termination_by interior suffix _ _ => suffix.length

/-- Every non-singleton connected list derives to a closed word with the same
head at both ends. -/
theorem existsClosedHeadDerivation
    {head : Nat} {tail : List Nat}
    (connected : ConnectedComponentSupportConnected (head :: tail))
    (tailNonempty : tail ≠ []) :
    ∃ interior,
      ListDerives (head :: tail) ([head] ++ interior ++ [head]) := by
  have headInTail :=
    connectedComponentSupportConnected_cons_tail connected tailNonempty
  obtain ⟨before, after, tailShape, headAbsent⟩ :=
    exists_lastOccurrenceSplit head tail headInTail
  have closing :=
    listDerivesClosingEndpointToEnd head before after
      (by simpa [tailShape, List.append_assoc] using connected)
      headAbsent
  exact ⟨before ++ after, by
    simpa [tailShape, List.append_assoc] using closing⟩

/-- Closed Case 1 with the existing first-occurrence/parity interior
normalizer replayed between the matching head occurrences. -/
theorem existsClosedParityInteriorNormal
    {head : Nat} {tail : List Nat}
    (connected : ConnectedComponentSupportConnected (head :: tail))
    (tailNonempty : tail ≠ []) :
    ∃ interior,
      ListDerives (head :: tail)
        ([head] ++ parityInitialNormalList interior ++ [head]) := by
  obtain ⟨interior, closed⟩ :=
    existsClosedHeadDerivation connected tailNonempty
  exact
    ⟨interior,
      closed.trans (listDerivesClosedParityInitialNormal head interior)⟩

end SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14
