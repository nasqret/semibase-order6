import SemigroupBasis.CoRoots.S5_804ConnectedCut
import SemigroupBasis.Examples.ConnectedComponentFourComponents

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_804

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
interior and right context. Empty and nonempty residual interiors use the
fourth and seventh basis laws respectively. -/
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

/-- Delete repeated interior letters, retaining one representative of each
letter. -/
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

/-- The sorted, duplicate-free envelope interior after deleting the outer
endpoint. -/
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

/-! ## Quantified connected-component normalization -/

/-- Every support-connected component of length at least two derives to a
sorted, duplicate-free endpoint envelope. Both endpoints are the component's
actual final variable, and the interior is exactly the remaining support.

This is the component-normalization boundary. It does not decompose an
arbitrary word into maximal components and does not assert that table
identities have equal component signatures. -/
theorem existsConnectedComponentNormal
    (stem : List Nat) (endpoint : Nat)
    (prefixNonempty : stem ≠ [])
    (connected :
      ConnectedComponentSupportConnected (stem ++ [endpoint])) :
    ∃ interior,
      ListDerives
        (stem ++ [endpoint])
        (endpoint :: interior ++ [endpoint]) ∧
      endpoint ∉ interior ∧
      interior.Nodup ∧
      interior.Pairwise (· ≤ ·) ∧
      (∀ tested,
        tested ∈ interior ↔
          tested ∈ stem ++ [endpoint] ∧ tested ≠ endpoint) := by
  obtain ⟨rawInterior, envelope, envelopeSupport⟩ :=
    existsConnectedComponentFinalEnvelope
      stem endpoint prefixNonempty connected
  have normalized :=
    listDerivesNormalizeInterior endpoint rawInterior []
  let interior := normalizedInterior endpoint rawInterior
  have derivation :
      ListDerives
        (stem ++ [endpoint])
        (endpoint :: interior ++ [endpoint]) := by
    exact envelope.trans <| by
      simpa [interior, List.append_assoc] using normalized
  refine
    ⟨interior, derivation,
      normalizedInterior_endpoint_absent endpoint rawInterior,
      normalizedInterior_nodup endpoint rawInterior,
      normalizedInterior_sorted endpoint rawInterior, ?_⟩
  intro tested
  rw [normalizedInterior_mem_iff]
  constructor
  · rintro ⟨rawMember, different⟩
    exact
      ⟨(envelopeSupport tested).mp (Or.inr rawMember), different⟩
  · rintro ⟨sourceMember, different⟩
    have endpointOrInterior :=
      (envelopeSupport tested).mpr sourceMember
    rcases endpointOrInterior with equal | rawMember
    · exact False.elim (different equal)
    · exact ⟨rawMember, different⟩

end SemigroupBasis.CoRoots.S5_804
