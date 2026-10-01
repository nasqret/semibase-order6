import SemigroupBasis.CoRoots.S5_402FactorSort

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_402

open SemigroupBasis

/-! ## Square banks as marker-only factors -/

/-- Represent a pure marker bank as square-ended factors with empty blocks. -/
def markerOnlyFactorList (labels : List Nat) :
    List (List Nat × Nat) :=
  labels.map fun marker => ([], marker)

/-- Render a marker bank as adjacent singleton squares. -/
def renderMarkerSquareBank (labels : List Nat) : List Nat :=
  labels.flatMap fun marker => [marker, marker]

@[simp]
theorem renderSquared_markerOnlyFactorList (labels : List Nat) :
    renderSquaredTerminatedBlocks (markerOnlyFactorList labels) =
      renderMarkerSquareBank labels := by
  induction labels with
  | nil =>
      rfl
  | cons marker rest ih =>
      change
        marker :: marker ::
            renderSquaredTerminatedBlocks (markerOnlyFactorList rest) =
          marker :: marker :: renderMarkerSquareBank rest
      exact congrArg (fun tail => marker :: marker :: tail) ih

theorem markerOnlyFactorList_perm
    {source target : List Nat} (permutation : source.Perm target) :
    (markerOnlyFactorList source).Perm
      (markerOnlyFactorList target) := by
  simpa [markerOnlyFactorList] using
    permutation.map (fun marker => ([], marker))

/-- Permute a square bank while preserving an arbitrary retained factor
prefix and final simple suffix. -/
theorem listDerivesMarkerBankPermutation
    (first : List Nat × Nat)
    (retainedTail : List (List Nat × Nat))
    {source target : List Nat} (permutation : source.Perm target)
    (final : List Nat) :
    ListDerives
      (renderSquaredTerminatedBlocks
          (first :: retainedTail ++ markerOnlyFactorList source) ++ final)
      (renderSquaredTerminatedBlocks
          (first :: retainedTail ++ markerOnlyFactorList target) ++ final) := by
  have factorPermutation :
      (retainedTail ++ markerOnlyFactorList source).Perm
        (retainedTail ++ markerOnlyFactorList target) :=
    List.Perm.append_left retainedTail
      (markerOnlyFactorList_perm permutation)
  exact listDerivesSquaredTailPermutation
    factorPermutation first final

/-! ## Local square-factor contraction -/

/-- Contract a marker-only square immediately following any factor carrying
the same marker. -/
theorem listDerivesContractAdjacentMarkerOnlyFactor
    (before after : List (List Nat × Nat))
    (block : List Nat) (marker : Nat) (final : List Nat) :
    ListDerives
      (renderSquaredTerminatedBlocks
          (before ++ [(block, marker), ([], marker)] ++ after) ++ final)
      (renderSquaredTerminatedBlocks
          (before ++ [(block, marker)] ++ after) ++ final) := by
  have contraction :=
    (S5_107.ListDerives.ofWord <|
      derivesLeePowerFourToTwo (Word.singleton marker)).context
        (renderSquaredTerminatedBlocks before ++ block)
        (renderSquaredTerminatedBlocks after ++ final)
  simpa [renderSquaredTerminatedBlocks, Word.singleton, Word.append,
    List.append_assoc] using contraction

/-- Move an item from the front across an arbitrary finite segment. -/
private theorem perm_cons_append
    {α : Type} (item : α) :
    ∀ front back : List α,
      (item :: front ++ back).Perm
        (front ++ item :: back)
  | [], back => List.Perm.refl _
  | head :: tail, back => by
      have swapped :
          (item :: head :: tail ++ back).Perm
            (head :: item :: tail ++ back) :=
        (List.Perm.swap item head (tail ++ back)).symm
      have moved :
          (head :: item :: tail ++ back).Perm
            (head :: tail ++ item :: back) :=
        List.Perm.cons head
          (perm_cons_append item tail back)
      exact swapped.trans moved

/-- Drop the first marker-bank square when its label is already represented
by the retained factor prefix. -/
theorem listDerivesDropMarkerBankHeadUsingRetained
    (first : List Nat × Nat)
    (retainedTail : List (List Nat × Nat))
    (marker : Nat) (labels final : List Nat)
    (represented :
      marker ∈ terminatedFactorMarkers (first :: retainedTail)) :
    ListDerives
      (renderSquaredTerminatedBlocks
          (first :: retainedTail ++
            markerOnlyFactorList (marker :: labels)) ++ final)
      (renderSquaredTerminatedBlocks
          (first :: retainedTail ++ markerOnlyFactorList labels) ++ final) := by
  rcases first with ⟨firstBlock, firstMarker⟩
  simp only [terminatedFactorMarkers, List.map_cons,
    List.mem_cons] at represented
  rcases represented with firstEqual | tailMember
  · subst firstMarker
    let markerFactor : List Nat × Nat := ([], marker)
    have expose :
        (retainedTail ++ markerFactor :: markerOnlyFactorList labels).Perm
          (markerFactor :: retainedTail ++ markerOnlyFactorList labels) :=
      (perm_cons_append markerFactor retainedTail
        (markerOnlyFactorList labels)).symm
    have exposeStep :=
      listDerivesSquaredTailPermutation expose
        (firstBlock, marker) final
    have contractStep :=
      listDerivesContractAdjacentMarkerOnlyFactor
        [] (retainedTail ++ markerOnlyFactorList labels)
        firstBlock marker final
    refine S5_107.ListDerives.trans
      (middle :=
        renderSquaredTerminatedBlocks
            ((firstBlock, marker) :: ([], marker) ::
              (retainedTail ++ markerOnlyFactorList labels)) ++ final) ?_ ?_
    · simpa [markerFactor, markerOnlyFactorList,
        List.append_assoc] using exposeStep
    · simpa [markerFactor, markerOnlyFactorList,
        List.append_assoc] using contractStep
  · rcases List.mem_map.mp tailMember with
      ⟨factor, factorMember, factorMarker⟩
    rcases factor with ⟨block, witnessMarker⟩
    simp only at factorMarker
    subst witnessMarker
    let witness : List Nat × Nat := (block, marker)
    let markerFactor : List Nat × Nat := ([], marker)
    have exposeWitness :
        retainedTail.Perm (witness :: retainedTail.erase witness) :=
      List.perm_cons_erase factorMember
    have exposePrefix :
        (retainedTail ++ markerFactor :: markerOnlyFactorList labels).Perm
          (witness :: retainedTail.erase witness ++
            markerFactor :: markerOnlyFactorList labels) :=
      exposeWitness.append_right
        (markerFactor :: markerOnlyFactorList labels)
    have moveMarker :
        (witness :: retainedTail.erase witness ++
          markerFactor :: markerOnlyFactorList labels).Perm
        (witness :: markerFactor :: retainedTail.erase witness ++
          markerOnlyFactorList labels) :=
      List.Perm.cons witness <|
        (perm_cons_append markerFactor
          (retainedTail.erase witness)
          (markerOnlyFactorList labels)).symm
    have expose := exposePrefix.trans moveMarker
    have exposeStep :=
      listDerivesSquaredTailPermutation expose
        (firstBlock, firstMarker) final
    have contractStep :=
      listDerivesContractAdjacentMarkerOnlyFactor
        [(firstBlock, firstMarker)]
        (retainedTail.erase witness ++ markerOnlyFactorList labels)
        block marker final
    have restore :
        (witness :: retainedTail.erase witness ++
          markerOnlyFactorList labels).Perm
        (retainedTail ++ markerOnlyFactorList labels) :=
      exposeWitness.symm.append_right (markerOnlyFactorList labels)
    have restoreStep :=
      listDerivesSquaredTailPermutation restore
        (firstBlock, firstMarker) final
    refine S5_107.ListDerives.trans
      (middle :=
        renderSquaredTerminatedBlocks
            ((firstBlock, firstMarker) :: witness :: markerFactor ::
              (retainedTail.erase witness ++
                markerOnlyFactorList labels)) ++ final) ?_ ?_
    · simpa [witness, markerFactor, markerOnlyFactorList,
        List.append_assoc] using exposeStep
    · refine S5_107.ListDerives.trans
        (middle :=
          renderSquaredTerminatedBlocks
              ((firstBlock, firstMarker) :: witness ::
                (retainedTail.erase witness ++
                  markerOnlyFactorList labels)) ++ final) ?_ ?_
      · simpa [witness, markerFactor,
          List.append_assoc] using contractStep
      · simpa [witness, markerOnlyFactorList,
          List.append_assoc] using restoreStep

/-- Drop a duplicated marker-bank head by exposing a later equal square,
contracting four copies to two, and restoring the remaining bank order. -/
theorem listDerivesDropDuplicateMarkerBankHead
    (first : List Nat × Nat)
    (retainedTail : List (List Nat × Nat))
    (marker : Nat) (labels final : List Nat)
    (present : marker ∈ labels) :
    ListDerives
      (renderSquaredTerminatedBlocks
          (first :: retainedTail ++
            markerOnlyFactorList (marker :: labels)) ++ final)
      (renderSquaredTerminatedBlocks
          (first :: retainedTail ++ markerOnlyFactorList labels) ++ final) := by
  have expose : labels.Perm (marker :: labels.erase marker) :=
    List.perm_cons_erase present
  have exposeStep :=
    (listDerivesMarkerBankPermutation
      first (retainedTail ++ [([], marker)])
      expose final)
  have contractStep :=
    listDerivesContractAdjacentMarkerOnlyFactor
      (first :: retainedTail)
      (markerOnlyFactorList (labels.erase marker))
      [] marker final
  have restoreStep :=
    listDerivesMarkerBankPermutation
      first retainedTail expose.symm final
  refine S5_107.ListDerives.trans
    (middle :=
      renderSquaredTerminatedBlocks
          (first :: retainedTail ++
            markerOnlyFactorList
              (marker :: marker :: labels.erase marker)) ++ final) ?_ ?_
  · simpa [markerOnlyFactorList,
      List.append_assoc] using exposeStep
  · refine S5_107.ListDerives.trans
      (middle :=
        renderSquaredTerminatedBlocks
            (first :: retainedTail ++
              markerOnlyFactorList (marker :: labels.erase marker)) ++
          final) ?_ ?_
    · simpa [markerOnlyFactorList,
        List.append_assoc] using contractStep
    · simpa [markerOnlyFactorList,
        List.append_assoc] using restoreStep

/-! ## Deduplicating and filtering the marker bank -/

/-- Keep the final occurrence of every marker-bank label. -/
def deduplicateMarkerBank : List Nat → List Nat
  | [] => []
  | marker :: labels =>
      if marker ∈ labels then
        deduplicateMarkerBank labels
      else
        marker :: deduplicateMarkerBank labels

/-- Every marker bank derives to its duplicate-free representative behind
an arbitrary retained factor prefix. -/
theorem listDerivesDeduplicateMarkerBank
    (first : List Nat × Nat)
    (retainedTail : List (List Nat × Nat))
    (final : List Nat) :
    ∀ labels : List Nat,
      ListDerives
        (renderSquaredTerminatedBlocks
            (first :: retainedTail ++ markerOnlyFactorList labels) ++ final)
        (renderSquaredTerminatedBlocks
            (first :: retainedTail ++
              markerOnlyFactorList (deduplicateMarkerBank labels)) ++ final)
  | [] => by
      exact S5_107.ListDerives.refl _
  | marker :: labels => by
      by_cases present : marker ∈ labels
      · have drop :=
          listDerivesDropDuplicateMarkerBankHead
            first retainedTail marker labels final present
        have normalize :=
          listDerivesDeduplicateMarkerBank
            first retainedTail final labels
        simpa [deduplicateMarkerBank, present] using drop.trans normalize
      · have normalize :=
          listDerivesDeduplicateMarkerBank
            first (retainedTail ++ [([], marker)]) final labels
        simpa [deduplicateMarkerBank, present, markerOnlyFactorList,
          List.append_assoc] using normalize

/-- Remove every label already represented by a retained factor. -/
def removeRetainedMarkers
    (retainedMarkers : List Nat) : List Nat → List Nat
  | [] => []
  | marker :: labels =>
      if marker ∈ retainedMarkers then
        removeRetainedMarkers retainedMarkers labels
      else
        marker :: removeRetainedMarkers retainedMarkers labels

/-- Filter represented labels from a marker bank. The witness premise keeps
the protected marker set separate from marker-only factors retained while
the recursion processes the bank. -/
theorem listDerivesRemoveRetainedMarkers
    (first : List Nat × Nat)
    (protectedMarkers : List Nat)
    (final : List Nat) :
    ∀ (retainedTail : List (List Nat × Nat))
      (labels : List Nat),
      (∀ marker, marker ∈ protectedMarkers →
        marker ∈ terminatedFactorMarkers (first :: retainedTail)) →
      ListDerives
        (renderSquaredTerminatedBlocks
            (first :: retainedTail ++ markerOnlyFactorList labels) ++ final)
        (renderSquaredTerminatedBlocks
            (first :: retainedTail ++
              markerOnlyFactorList
                (removeRetainedMarkers protectedMarkers labels)) ++ final)
  | retainedTail, [], _ => by
      exact S5_107.ListDerives.refl _
  | retainedTail, marker :: labels, witnesses => by
      by_cases represented : marker ∈ protectedMarkers
      · have drop :=
          listDerivesDropMarkerBankHeadUsingRetained
            first retainedTail marker labels final
            (witnesses marker represented)
        have normalize :=
          listDerivesRemoveRetainedMarkers
            first protectedMarkers final retainedTail labels witnesses
        simpa [removeRetainedMarkers, represented] using
          drop.trans normalize
      · have extendedWitnesses :
          ∀ tested, tested ∈ protectedMarkers →
            tested ∈ terminatedFactorMarkers
              (first :: (retainedTail ++ [([], marker)])) := by
          intro tested member
          have old := witnesses tested member
          simpa [terminatedFactorMarkers, List.map_append,
            List.append_assoc] using
              (List.mem_append_left [marker] old)
        have normalize :=
          listDerivesRemoveRetainedMarkers
            first protectedMarkers final
            (retainedTail ++ [([], marker)]) labels extendedWitnesses
        simpa [removeRetainedMarkers, represented, markerOnlyFactorList,
          List.append_assoc] using normalize

/-- Deterministic canonical marker bank: deduplicate, remove labels already
represented by successor factors, then sort the remaining labels. -/
def canonicalMarkerBank
    (retainedMarkers labels : List Nat) : List Nat :=
  (removeRetainedMarkers retainedMarkers
      (deduplicateMarkerBank labels)).mergeSort
    (fun left right => decide (left ≤ right))

private theorem mem_deduplicateMarkerBank
    (tested : Nat) :
    ∀ labels : List Nat,
      tested ∈ deduplicateMarkerBank labels ↔ tested ∈ labels
  | [] => by simp [deduplicateMarkerBank]
  | marker :: labels => by
      by_cases present : marker ∈ labels
      · rw [deduplicateMarkerBank]
        simp only [if_pos present,
          mem_deduplicateMarkerBank tested labels, List.mem_cons]
        constructor
        · exact Or.inr
        · intro member
          rcases member with equal | member
          · subst tested
            exact present
          · exact member
      · simpa [deduplicateMarkerBank, present,
          mem_deduplicateMarkerBank tested labels]

private theorem deduplicateMarkerBank_nodup :
    ∀ labels : List Nat, (deduplicateMarkerBank labels).Nodup
  | [] => by simp [deduplicateMarkerBank]
  | marker :: labels => by
      by_cases present : marker ∈ labels
      · simpa [deduplicateMarkerBank, present] using
          deduplicateMarkerBank_nodup labels
      · simp [deduplicateMarkerBank, present,
          mem_deduplicateMarkerBank,
          deduplicateMarkerBank_nodup labels]

private theorem removeRetainedMarkers_eq_filter
    (retainedMarkers : List Nat) :
    ∀ labels : List Nat,
      removeRetainedMarkers retainedMarkers labels =
        labels.filter fun marker => decide (marker ∉ retainedMarkers)
  | [] => rfl
  | marker :: labels => by
      by_cases represented : marker ∈ retainedMarkers
      · simp [removeRetainedMarkers, represented,
          removeRetainedMarkers_eq_filter retainedMarkers labels]
      · simp [removeRetainedMarkers, represented,
          removeRetainedMarkers_eq_filter retainedMarkers labels]

private theorem canonicalMarkerBank_mem_iff
    (retainedMarkers labels : List Nat) (tested : Nat) :
    tested ∈ canonicalMarkerBank retainedMarkers labels ↔
      tested ∈ labels ∧ tested ∉ retainedMarkers := by
  simp only [canonicalMarkerBank, List.mem_mergeSort,
    removeRetainedMarkers_eq_filter, List.mem_filter,
    decide_eq_true_eq, mem_deduplicateMarkerBank]

private theorem canonicalMarkerBank_nodup
    (retainedMarkers labels : List Nat) :
    (canonicalMarkerBank retainedMarkers labels).Nodup := by
  unfold canonicalMarkerBank
  apply (List.mergeSort_perm _ _).nodup_iff.mpr
  rw [removeRetainedMarkers_eq_filter]
  exact (deduplicateMarkerBank_nodup labels).filter _

private theorem canonicalMarkerBank_pairwise
    (retainedMarkers labels : List Nat) :
    (canonicalMarkerBank retainedMarkers labels).Pairwise (· ≤ ·) := by
  have transitive :
      ∀ left middle right : Nat,
        decide (left ≤ middle) = true →
        decide (middle ≤ right) = true →
        decide (left ≤ right) = true := by
    intro left middle right leftMiddle middleRight
    exact decide_eq_true <|
      Nat.le_trans
        (of_decide_eq_true leftMiddle)
        (of_decide_eq_true middleRight)
  have total :
      ∀ left right : Nat,
        (decide (left ≤ right) || decide (right ≤ left)) = true := by
    intro left right
    rcases Nat.le_total left right with leftRight | rightLeft
    · simp [leftRight]
    · simp [rightLeft]
  have sorted :=
    List.pairwise_mergeSort transitive total
      (removeRetainedMarkers retainedMarkers
        (deduplicateMarkerBank labels))
  simpa [canonicalMarkerBank] using
    (sorted.imp fun relation => of_decide_eq_true relation)

/-- The canonical marker bank depends only on the support of labels not
already represented by retained successor factors. -/
theorem canonicalMarkerBank_eq_of_residual_mem_iff
    (retainedMarkers : List Nat) {leftLabels rightLabels : List Nat}
    (sameResidual :
      ∀ marker, marker ∉ retainedMarkers →
        (marker ∈ leftLabels ↔ marker ∈ rightLabels)) :
    canonicalMarkerBank retainedMarkers leftLabels =
      canonicalMarkerBank retainedMarkers rightLabels := by
  have sameMembership :
      ∀ marker,
        marker ∈ canonicalMarkerBank retainedMarkers leftLabels ↔
          marker ∈ canonicalMarkerBank retainedMarkers rightLabels := by
    intro marker
    rw [canonicalMarkerBank_mem_iff,
      canonicalMarkerBank_mem_iff]
    constructor
    · rintro ⟨member, notRetained⟩
      exact ⟨(sameResidual marker notRetained).mp member, notRetained⟩
    · rintro ⟨member, notRetained⟩
      exact ⟨(sameResidual marker notRetained).mpr member, notRetained⟩
  have permutation :
      (canonicalMarkerBank retainedMarkers leftLabels).Perm
        (canonicalMarkerBank retainedMarkers rightLabels) := by
    rw [List.perm_iff_count]
    intro marker
    rw [(canonicalMarkerBank_nodup retainedMarkers leftLabels).count,
      (canonicalMarkerBank_nodup retainedMarkers rightLabels).count]
    simpa only [sameMembership marker]
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftRight rightLeft =>
      Nat.le_antisymm leftRight rightLeft)
    (canonicalMarkerBank_pairwise retainedMarkers leftLabels)
    (canonicalMarkerBank_pairwise retainedMarkers rightLabels)
    permutation

/-- Complete source-level normalization of a marker-only square bank behind
an arbitrary nonempty retained factor prefix. -/
theorem listDerivesCanonicalMarkerBank
    (first : List Nat × Nat)
    (retainedTail : List (List Nat × Nat))
    (labels final : List Nat) :
    ListDerives
      (renderSquaredTerminatedBlocks
          (first :: retainedTail ++ markerOnlyFactorList labels) ++ final)
      (renderSquaredTerminatedBlocks
          (first :: retainedTail ++
            markerOnlyFactorList
              (canonicalMarkerBank
                (terminatedFactorMarkers (first :: retainedTail)) labels)) ++
        final) := by
  have deduplicate :=
    listDerivesDeduplicateMarkerBank
      first retainedTail final labels
  let reduced := deduplicateMarkerBank labels
  let protectedMarkers := terminatedFactorMarkers (first :: retainedTail)
  have remove :=
    listDerivesRemoveRetainedMarkers
      first protectedMarkers final retainedTail reduced
      (fun marker member => member)
  let filtered := removeRetainedMarkers protectedMarkers reduced
  have sort :=
    listDerivesMarkerBankPermutation
      first retainedTail
      (List.mergeSort_perm
        filtered (fun left right : Nat => decide (left ≤ right))).symm
      final
  refine S5_107.ListDerives.trans
    (middle :=
      renderSquaredTerminatedBlocks
          (first :: retainedTail ++ markerOnlyFactorList reduced) ++ final) ?_ ?_
  · simpa [reduced] using deduplicate
  · refine S5_107.ListDerives.trans
      (middle :=
        renderSquaredTerminatedBlocks
            (first :: retainedTail ++ markerOnlyFactorList filtered) ++
          final) ?_ ?_
    · simpa [reduced, protectedMarkers, filtered] using remove
    · simpa [canonicalMarkerBank, reduced, protectedMarkers, filtered] using sort

end SemigroupBasis.CoRoots.S5_402
