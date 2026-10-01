import SemigroupBasis.CoRoots.S5_806ConnectedCut

namespace SemigroupBasis.CoRoots.S5_806

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## Deterministic envelope interiors -/

private theorem count_pair_to_front
    (left right : List Nat) (repeated tested : Nat) :
    (left ++ repeated :: repeated :: right).count tested =
      (repeated :: repeated :: left ++ right).count tested := by
  simp only [List.count_append, List.count_cons]
  omega

private theorem count_single_restore
    (left right : List Nat) (repeated tested : Nat) :
    (repeated :: left ++ right).count tested =
      (left ++ repeated :: right).count tested := by
  simp only [List.count_append, List.count_cons]
  omega

/-- Contract two adjacent copies of an interior letter, in arbitrary
interior and right context. -/
theorem listDerivesInteriorContraction
    (endpoint repeated : Nat)
    (left right suffix : List Nat) :
    ListDerives
      (endpoint :: left ++ repeated :: repeated :: right ++
        endpoint :: suffix)
      (endpoint :: left ++ repeated :: right ++ endpoint :: suffix) := by
  have expose :
      (left ++ repeated :: repeated :: right).Perm
        (repeated :: repeated :: left ++ right) := by
    rw [List.perm_iff_count]
    exact count_pair_to_front left right repeated
  have first :=
    listDerivesInteriorPermutation endpoint suffix expose
  let remainder := left ++ right
  have contract :
      ListDerives
        (endpoint :: repeated :: repeated :: remainder ++
          endpoint :: suffix)
        (endpoint :: repeated :: remainder ++ endpoint :: suffix) := by
    cases remainder with
    | nil =>
        have core :=
          (derivesMiddleDuplication
            (Word.singleton endpoint) (Word.singleton repeated)).symm
        have listed :
            ListDerives
              [endpoint, repeated, repeated, endpoint]
              [endpoint, repeated, endpoint] :=
          S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc] using core
        simpa [List.append_assoc] using listed.append suffix
    | cons remainingHead remainingTail =>
        have core :=
          (derivesClosedMiddleDuplication
            (Word.singleton endpoint) (Word.singleton repeated)
            (S5_107.listWordOfCons remainingHead remainingTail)).symm
        have listed :
            ListDerives
              (endpoint :: repeated :: repeated :: remainingHead ::
                remainingTail ++ [endpoint])
              (endpoint :: repeated :: remainingHead :: remainingTail ++
                [endpoint]) :=
          S5_107.ListDerives.words <| by
            simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
              Word.append_assoc, List.append_assoc] using core
        simpa [List.append_assoc] using listed.append suffix
  have restore :
      (repeated :: left ++ right).Perm
        (left ++ repeated :: right) := by
    rw [List.perm_iff_count]
    exact count_single_restore left right repeated
  have third :=
    listDerivesInteriorPermutation endpoint suffix restore
  have firstStep :
      ListDerives
        (endpoint :: left ++ repeated :: repeated :: right ++
          endpoint :: suffix)
        (endpoint :: repeated :: repeated :: remainder ++
          endpoint :: suffix) := by
    simpa [remainder, List.append_assoc] using first
  have thirdStep :
      ListDerives
        (endpoint :: repeated :: remainder ++ endpoint :: suffix)
        (endpoint :: left ++ repeated :: right ++ endpoint :: suffix) := by
    simpa [remainder, List.append_assoc] using third
  exact firstStep.trans (contract.trans thirdStep)

/-- Remove every occurrence of the closing endpoint from the interior. -/
theorem listDerivesRemoveInteriorEndpoint
    (endpoint : Nat) :
    ∀ (interior suffix : List Nat),
      ListDerives
        (endpoint :: interior ++ endpoint :: suffix)
        (endpoint ::
          interior.filter (fun letter => decide (letter ≠ endpoint)) ++
            endpoint :: suffix)
  | [], suffix => S5_107.ListDerives.refl _
  | letter :: rest, suffix => by
      by_cases equal : letter = endpoint
      · subst letter
        have delete :
            ListDerives
              (endpoint :: endpoint :: rest ++ endpoint :: suffix)
              (endpoint :: rest ++ endpoint :: suffix) := by
          simpa [List.append_assoc] using
            (listDerivesDeleteMiddleCore endpoint [] rest).append suffix
        have recurse :=
          listDerivesRemoveInteriorEndpoint endpoint rest suffix
        simpa using delete.trans recurse
      · have recurse :=
          listDerivesRemoveInteriorEndpoint endpoint rest suffix
        have lifted :=
          listDerivesInteriorCons endpoint letter suffix recurse
        simpa [equal] using lifted

/-- Delete repeated interior letters, retaining one representative. -/
theorem listDerivesDistinctInterior
    (endpoint : Nat) :
    ∀ (interior suffix : List Nat),
      ListDerives
        (endpoint :: interior ++ endpoint :: suffix)
        (endpoint :: connectedComponentDistinctSupport interior ++
          endpoint :: suffix)
  | [], suffix => S5_107.ListDerives.refl _
  | letter :: rest, suffix => by
      have recurse :=
        listDerivesDistinctInterior endpoint rest suffix
      have lifted :=
        listDerivesInteriorCons endpoint letter suffix recurse
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
          listDerivesInteriorPermutation endpoint suffix arrange
        have contract :=
          listDerivesInteriorContraction endpoint letter []
            (distinctRest.erase letter) suffix
        have restore :=
          listDerivesInteriorPermutation endpoint suffix arrangeRest.symm
        rw [connectedComponentDistinctSupport, if_pos present]
        exact lifted.trans (first.trans (contract.trans restore))
      · rw [connectedComponentDistinctSupport, if_neg present]
        exact lifted

/-- Sorted duplicate-free envelope interior after deleting the endpoint. -/
def normalizedInterior
    (endpoint : Nat) (interior : List Nat) : List Nat :=
  connectedComponentSortedSupport
    (interior.filter (fun letter => decide (letter ≠ endpoint)))

/-- Normalize an arbitrary endpoint envelope to its deterministic interior. -/
theorem listDerivesNormalizeInterior
    (endpoint : Nat) (interior suffix : List Nat) :
    ListDerives
      (endpoint :: interior ++ endpoint :: suffix)
      (endpoint :: normalizedInterior endpoint interior ++
        endpoint :: suffix) := by
  have removed :=
    listDerivesRemoveInteriorEndpoint endpoint interior suffix
  let filtered :=
    interior.filter (fun letter => decide (letter ≠ endpoint))
  have distinct :=
    listDerivesDistinctInterior endpoint filtered suffix
  have sorted :
      (connectedComponentDistinctSupport filtered).Perm
        (connectedComponentSortedSupport filtered) :=
    (List.mergeSort_perm
      (connectedComponentDistinctSupport filtered)
      (fun left right : Nat => decide (left ≤ right))).symm
  have permuted :=
    listDerivesInteriorPermutation endpoint suffix sorted
  simpa [normalizedInterior, filtered] using
    removed.trans (distinct.trans permuted)

theorem normalizedInterior_mem_iff
    (endpoint tested : Nat) (interior : List Nat) :
    tested ∈ normalizedInterior endpoint interior ↔
      tested ∈ interior ∧ tested ≠ endpoint := by
  rw [normalizedInterior, connectedComponentSortedSupport_mem_iff,
    List.mem_filter]
  simp

theorem normalizedInterior_endpoint_absent
    (endpoint : Nat) (interior : List Nat) :
    endpoint ∉ normalizedInterior endpoint interior := by
  rw [normalizedInterior_mem_iff]
  simp

theorem normalizedInterior_nodup
    (endpoint : Nat) (interior : List Nat) :
    (normalizedInterior endpoint interior).Nodup :=
  connectedComponentSortedSupport_nodup _

theorem normalizedInterior_sorted
    (endpoint : Nat) (interior : List Nat) :
    (normalizedInterior endpoint interior).Pairwise (· ≤ ·) :=
  connectedComponentSortedSupport_sorted _

private theorem sortedNodup_eq_of_mem_iff
    {left right : List Nat}
    (leftSorted : left.Pairwise (· ≤ ·))
    (rightSorted : right.Pairwise (· ≤ ·))
    (leftNodup : left.Nodup) (rightNodup : right.Nodup)
    (sameSupport : ∀ letter, letter ∈ left ↔ letter ∈ right) :
    left = right := by
  have permutation : left.Perm right := by
    rw [List.perm_iff_count]
    intro letter
    rw [leftNodup.count, rightNodup.count]
    simp only [sameSupport letter]
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
    leftSorted rightSorted permutation

/-- Deterministic interiors agree whenever the source lists have the same
support away from the selected endpoint. -/
theorem normalizedInterior_eq_of_mem_iff
    (endpoint : Nat) {left right : List Nat}
    (sameSupport :
      ∀ tested, tested ≠ endpoint →
        (tested ∈ left ↔ tested ∈ right)) :
    normalizedInterior endpoint left =
      normalizedInterior endpoint right := by
  apply sortedNodup_eq_of_mem_iff
    (normalizedInterior_sorted endpoint left)
    (normalizedInterior_sorted endpoint right)
    (normalizedInterior_nodup endpoint left)
    (normalizedInterior_nodup endpoint right)
  intro tested
  rw [normalizedInterior_mem_iff, normalizedInterior_mem_iff]
  by_cases different : tested ≠ endpoint
  · simp [different, sameSupport tested different]
  · simp [different]

/-- A total final-letter selector. Only the nonempty branch is used by the
component normalizer. -/
def componentFinal : List Nat → Nat
  | [] => 0
  | head :: tail => tail.getLastD head

/-- The intended S5_806 render of the last connected component. Unary
components retain one or two copies. A multi-support component is enclosed
by its actual final letter, with the remaining support sorted inside. -/
def finalComponentCanonical (component : List Nat) : List Nat :=
  let support := connectedComponentSortedSupport component
  match support with
  | [] => []
  | [letter] =>
      if component.length = 1 then [letter] else [letter, letter]
  | _ :: _ :: _ =>
      let endpoint := componentFinal component
      endpoint :: normalizedInterior endpoint component ++ [endpoint]

/-- Render all earlier components with the least-support endpoint and reserve
the actual-final endpoint policy for the last component. -/
def canonicalComponents : List (List Nat) → List Nat
  | [] => []
  | [last] => finalComponentCanonical last
  | component :: next :: rest =>
      connectedComponentCanonicalComponent component ++
        canonicalComponents (next :: rest)

/-- The exact deterministic S5_806 connected-cut candidate normal form. -/
def canonicalRenderList (letters : List Nat) : List Nat :=
  canonicalComponents (connectedComponentDecomposeList letters)

/-- Normalize every position before the original final letter using the
complete contextual S4_70 simulation. This theorem is unconditional and
applies to every list. -/
def prefixContextCanonicalList : List Nat → List Nat
  | [] => []
  | head :: tail =>
      connectedComponentCanonicalRenderList
          (head :: tail).dropLast ++
        [tail.getLastD head]

private theorem dropLast_append_final
    (head : Nat) (tail : List Nat) :
    (head :: tail).dropLast ++ [tail.getLastD head] =
      head :: tail := by
  have reconstruction :=
    List.dropLast_concat_getLast
      (l := head :: tail) (by simp)
  rw [List.getLast_eq_getLastD] at reconstruction
  simpa only [List.getLastD_cons] using reconstruction

/-- Unrestricted partial normalizer: every maximal connected component of
the prefix before the original final letter is canonicalized, and the final
letter itself is retained literally as the required nonempty context. -/
theorem listDerivesPrefixContextCanonical :
    ∀ letters : List Nat,
      ListDerives letters (prefixContextCanonicalList letters)
  | [] => S5_107.ListDerives.empty
  | head :: tail => by
      have normalized :=
        listDerivesConnectedCanonicalBefore
          (head :: tail).dropLast (tail.getLastD head) []
      rw [dropLast_append_final head tail] at normalized
      simpa [prefixContextCanonicalList] using normalized

/-- Contract any unary word of length at least two to exactly two copies. -/
private theorem listDerivesRepeatedUnary
    (endpoint : Nat) :
    ∀ (rest : List Nat),
      (∀ letter, letter ∈ rest → letter = endpoint) →
        ListDerives
          (endpoint :: endpoint :: rest) [endpoint, endpoint]
  | [], _ => S5_107.ListDerives.refl _
  | letter :: rest, allEndpoint => by
      have letterEq : letter = endpoint :=
        allEndpoint letter (by simp)
      subst letter
      have core :
          ListDerives
            [endpoint, endpoint, endpoint] [endpoint, endpoint] :=
        S5_107.ListDerives.words <| by
          simpa [S5_107.listWordOfCons, Word.singleton,
            Word.append, Word.append_assoc] using
            (derivesPowerExpansion (Word.singleton endpoint)).symm
      have first := core.append rest
      have remaining :=
        listDerivesRepeatedUnary endpoint rest
          (fun current member =>
            allEndpoint current (List.Mem.tail endpoint member))
      exact first.trans remaining

/-- The final-component normalizer is already complete for unary support. -/
theorem listDerivesFinalUnaryCanonical
    (component : List Nat) (nonempty : component ≠ [])
    {endpoint : Nat}
    (supportEq :
      connectedComponentSortedSupport component = [endpoint]) :
    ListDerives component (finalComponentCanonical component) := by
  cases component with
  | nil => contradiction
  | cons head tail =>
      have headSupport : head ∈ [endpoint] := by
        rw [← supportEq,
          connectedComponentSortedSupport_mem_iff]
        simp
      have headEq : head = endpoint := by
        simpa using headSupport
      subst head
      have tailAll :
          ∀ letter, letter ∈ tail → letter = endpoint := by
        intro letter member
        have supported : letter ∈ [endpoint] := by
          rw [← supportEq,
            connectedComponentSortedSupport_mem_iff]
          exact List.Mem.tail endpoint member
        simpa using supported
      cases tail with
      | nil =>
          simpa [finalComponentCanonical, supportEq] using
            S5_107.ListDerives.refl (basis := basis) [endpoint]
      | cons next rest =>
          have nextEq : next = endpoint :=
            tailAll next (by simp)
          subst next
          have restAll :
              ∀ letter, letter ∈ rest → letter = endpoint := by
            intro letter member
            exact tailAll letter (List.Mem.tail endpoint member)
          simpa [finalComponentCanonical, supportEq] using
            listDerivesRepeatedUnary endpoint rest restAll

/-- The one normalization lemma still missing from the connected-cut layer:
normalize a multi-support connected last component to the actual-final
endpoint render. It is a proposition, not an axiom or an asserted theorem. -/
def FinalComponentNormalizationObligation : Prop :=
  ∀ (component : List Nat),
    component ≠ [] →
      ConnectedComponentSupportConnected component →
        2 ≤ (connectedComponentSortedSupport component).length →
          ListDerives component (finalComponentCanonical component)

/-- Combine the proved unary branch with the explicit multi-support
obligation. -/
theorem listDerivesFinalComponentCanonical
    (finalNormalize : FinalComponentNormalizationObligation)
    (component : List Nat) (nonempty : component ≠ [])
    (connected : ConnectedComponentSupportConnected component) :
    ListDerives component (finalComponentCanonical component) := by
  have supportNonempty :
      connectedComponentSortedSupport component ≠ [] :=
    connectedComponentSortedSupport_nonempty nonempty
  cases supportShape : connectedComponentSortedSupport component with
  | nil =>
      exact False.elim (supportNonempty supportShape)
  | cons endpoint remaining =>
      cases remaining with
      | nil =>
          exact listDerivesFinalUnaryCanonical
            component nonempty supportShape
      | cons next rest =>
          apply finalNormalize component nonempty connected
          rw [supportShape]
          simp

/-- Once the final-component obligation is supplied, every ordered component
list derives to the exact S5_806 component render. -/
theorem listDerivesCanonicalComponents
    (finalNormalize : FinalComponentNormalizationObligation) :
    ∀ (components : List (List Nat)),
      (∀ component, component ∈ components → component ≠ []) →
      (∀ component, component ∈ components →
        ConnectedComponentSupportConnected component) →
      ListDerives components.flatten (canonicalComponents components)
  | [], _, _ => S5_107.ListDerives.empty
  | [component], nonempty, connected => by
      simpa [canonicalComponents] using
        listDerivesFinalComponentCanonical finalNormalize component
          (nonempty component (by simp))
          (connected component (by simp))
  | component :: next :: rest, nonempty, connected => by
      have componentNonempty : component ≠ [] :=
        nonempty component (by simp)
      have componentConnected :
          ConnectedComponentSupportConnected component :=
        connected component (by simp)
      have nextNonempty : next ≠ [] :=
        nonempty next (by simp)
      have contextNonempty : (next :: rest).flatten ≠ [] := by
        change next ++ rest.flatten ≠ []
        intro empty
        exact nextNonempty (List.append_eq_nil_iff.mp empty).1
      obtain ⟨contextHead, contextTail, contextShape⟩ :=
        List.exists_cons_of_ne_nil contextNonempty
      have first :=
        listDerivesConnectedComponentCanonicalBefore
          component componentNonempty componentConnected
          contextHead contextTail
      have first' :
          ListDerives
            (component ++ (next :: rest).flatten)
            (connectedComponentCanonicalComponent component ++
              (next :: rest).flatten) := by
        simpa [contextShape] using first
      have recurse :=
        listDerivesCanonicalComponents finalNormalize (next :: rest)
          (fun current member =>
            nonempty current (List.Mem.tail component member))
          (fun current member =>
            connected current (List.Mem.tail component member))
      have second :=
        recurse.prepend
          (connectedComponentCanonicalComponent component)
      simpa [canonicalComponents] using first'.trans second

/-- The complete connected-cut normalizer follows from exactly the final
component obligation. No semantic completeness or `BasisFor` claim is made. -/
theorem listDerivesCanonicalRender
    (finalNormalize : FinalComponentNormalizationObligation)
    (letters : List Nat) :
    ListDerives letters (canonicalRenderList letters) := by
  let components := connectedComponentDecomposeList letters
  have normalized :=
    listDerivesCanonicalComponents finalNormalize components
      (connectedComponentDecomposeList_nonempty_components letters)
      (connectedComponentDecomposeList_supportConnected letters)
  have flattenEq := connectedComponentDecomposeList_flatten letters
  simpa [canonicalRenderList, components, flattenEq] using normalized

end SemigroupBasis.CoRoots.S5_806
