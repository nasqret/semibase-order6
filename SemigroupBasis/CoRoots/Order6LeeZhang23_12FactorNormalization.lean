import SemigroupBasis.CoRoots.Order6LeeZhang23_9FactorMoves
import SemigroupBasis.CoRoots.Order6LeeZhang23_9CanonicalBridges

/-!
# Lee--Zhang Proposition 23.12 factor normalization

This module is the derivational factor core for the simple-endpoint branch of
Lee--Zhang Proposition 23.12.  It expands every successor factor into a square
and, when appropriate, a residual factor; moves the resulting factors while
the final residual stays literally fixed; groups all copies of each square in
the canonical marker order; and contracts each nonempty group to one square.

The only derivations used here are consequences of the published four-law
basis `B4Basis`.  The inventory and canonical bridges imported below remain
purely combinatorial.
-/

namespace SemigroupBasis.CoRoots.Order6LeeZhang23_12FactorNormalization

open SemigroupBasis
open Order6LeeZhang23_9Moves
open Order6LeeZhang23_9Scanner
open Order6LeeZhang23_9CanonicalData
open Order6LeeZhang23_9InventoryBridge
open Order6LeeZhang23_9FactorMoves
open Order6LeeZhang23_9CanonicalBridges

/-! ## Expanded factor inventory -/

/-- Expose one square before a block-bearing factor.  A marker-only nonfinal
factor is replaced by its square, since it has no residual simple block. -/
def expandedNonfinalFactor
    (factor : SuccessorFactor) : List SuccessorFactor :=
  if factor.2 = [] then
    [squareFactor factor.1]
  else
    [squareFactor factor.1, factor]

/-- Expand every nonfinal factor independently. -/
def expandedNonfinalFactors
    (factors : List SuccessorFactor) : List SuccessorFactor :=
  factors.flatMap expandedNonfinalFactor

/-- Generic block-bearing subinventory. -/
def blockBearingFactors
    (factors : List SuccessorFactor) : List SuccessorFactor :=
  factors.filter fun factor => decide (factor.2 ≠ [])

/-- All square markers exposed from the nonfinal factors and the fixed final
factor, before deduplication. -/
def expandedSquareMarkers
    (nonfinal : List SuccessorFactor)
    (final : SuccessorFactor) : List Nat :=
  nonfinal.map Prod.fst ++ [final.1]

/-- Every expanded factor that may be permuted.  The final factor contributes
a square here, while its residual copy remains outside and fixed. -/
def expandedBeforeFinalFactors
    (nonfinal : List SuccessorFactor)
    (final : SuccessorFactor) : List SuccessorFactor :=
  expandedNonfinalFactors nonfinal ++ [squareFactor final.1]

/-- Expanding only adds rendered occurrences. -/
theorem renderSuccessorFactor_count_le_expandedNonfinalFactor
    (factor : SuccessorFactor) (tested : Nat) :
    (renderSuccessorFactor factor).count tested <=
      (renderSuccessorFactors
        (expandedNonfinalFactor factor)).count tested := by
  rcases factor with ⟨marker, block⟩
  by_cases blockEmpty : block = []
  · subst block
    by_cases same : tested = marker
    · subst tested
      simp [expandedNonfinalFactor, renderSuccessorFactor,
        renderSuccessorFactors, squareFactor] <;> omega
    · simp [expandedNonfinalFactor, renderSuccessorFactor,
        renderSuccessorFactors, squareFactor, same, Ne.symm same] <;>
          omega
  · by_cases same : tested = marker
    · subst tested
      simp [expandedNonfinalFactor, renderSuccessorFactor,
        renderSuccessorFactors, squareFactor, blockEmpty] <;> omega
    · simp [expandedNonfinalFactor, renderSuccessorFactor,
        renderSuccessorFactors, squareFactor, blockEmpty,
        same, Ne.symm same] <;> omega

/-- Expanding an entire nonfinal inventory only increases every count. -/
theorem renderSuccessorFactors_count_le_expandedNonfinalFactors
    (factors : List SuccessorFactor) (tested : Nat) :
    (renderSuccessorFactors factors).count tested <=
      (renderSuccessorFactors
        (expandedNonfinalFactors factors)).count tested := by
  induction factors with
  | nil =>
      simp [expandedNonfinalFactors, renderSuccessorFactors]
  | cons factor rest induction =>
      have first :=
        renderSuccessorFactor_count_le_expandedNonfinalFactor
          factor tested
      simp only [expandedNonfinalFactors, List.flatMap_cons,
        renderSuccessorFactors_append, renderSuccessorFactors,
        List.count_append] at induction ⊢
      omega

/-- The expansion separates, up to permutation, into one square for every
source marker followed by exactly the block-bearing residual factors. -/
theorem expandedNonfinalFactors_perm_squareFactors_append_blockBearing :
    ∀ factors : List SuccessorFactor,
      (expandedNonfinalFactors factors).Perm
        (factors.map (fun factor => squareFactor factor.1) ++
          blockBearingFactors factors)
  | [] => by
      exact List.Perm.nil
  | factor :: rest => by
      have induction :=
        expandedNonfinalFactors_perm_squareFactors_append_blockBearing
          rest
      by_cases blockEmpty : factor.2 = []
      · have prefixed :=
          List.Perm.cons (squareFactor factor.1) induction
        simpa [expandedNonfinalFactors, expandedNonfinalFactor,
          blockBearingFactors, blockEmpty] using prefixed
      · have expandedTail :=
          List.Perm.cons (squareFactor factor.1)
            (List.Perm.cons factor induction)
        have movedResidual :=
          List.Perm.cons (squareFactor factor.1) <|
            S5_107.perm_cons_append factor
              (rest.map (fun next => squareFactor next.1))
              (blockBearingFactors rest)
        simpa [expandedNonfinalFactors, expandedNonfinalFactor,
            blockBearingFactors, blockEmpty, List.append_assoc] using
          expandedTail.trans movedResidual

/-- The final exposed square joins the nonfinal square bank, while the
block-bearing residual list remains after the complete bank. -/
theorem expandedBeforeFinalFactors_partition_perm
    (nonfinal : List SuccessorFactor)
    (final : SuccessorFactor) :
    (expandedBeforeFinalFactors nonfinal final).Perm
      ((expandedSquareMarkers nonfinal final).map squareFactor ++
        blockBearingFactors nonfinal) := by
  have expanded :=
    (expandedNonfinalFactors_perm_squareFactors_append_blockBearing
      nonfinal).append_right [squareFactor final.1]
  have moveFinal :
      (blockBearingFactors nonfinal ++ [squareFactor final.1]).Perm
        (squareFactor final.1 :: blockBearingFactors nonfinal) :=
    by
      simpa only [List.append_nil] using
        (S5_107.perm_cons_append (squareFactor final.1)
          (blockBearingFactors nonfinal) []).symm
  have moved :=
    List.Perm.append_left
      (nonfinal.map (fun factor => squareFactor factor.1))
      moveFinal
  have moved' :
      ((nonfinal.map (fun factor => squareFactor factor.1) ++
          blockBearingFactors nonfinal) ++ [squareFactor final.1]).Perm
        (nonfinal.map (fun factor => squareFactor factor.1) ++
          squareFactor final.1 :: blockBearingFactors nonfinal) := by
    simpa [List.append_assoc] using moved
  simpa [expandedBeforeFinalFactors, expandedSquareMarkers,
      List.map_append, List.append_assoc] using
    expanded.trans moved'

/-- Every generated nonfinal factor carries a marker projected from a source
nonfinal factor. -/
theorem marker_mem_source_of_mem_expandedNonfinalFactors
    {source : List SuccessorFactor}
    {generated : SuccessorFactor}
    (member : generated ∈ expandedNonfinalFactors source) :
    generated.1 ∈ source.map Prod.fst := by
  change generated ∈ source.flatMap expandedNonfinalFactor at member
  rcases List.mem_flatMap.mp member with
    ⟨factor, factorMember, generatedMember⟩
  rcases factor with ⟨marker, block⟩
  refine List.mem_map.mpr ⟨(marker, block), factorMember, ?_⟩
  by_cases blockEmpty : block = []
  · subst block
    simp [expandedNonfinalFactor] at generatedMember
    subst generated
    rfl
  · simp [expandedNonfinalFactor, blockEmpty] at generatedMember
    rcases generatedMember with generatedSquare | generatedResidual
    · subst generated
      rfl
    · subst generated
      rfl

/-- Every permutable expanded factor, and the fixed final residual itself,
has a marker represented in the exposed square-marker list. -/
theorem marker_mem_expandedSquareMarkers_of_factor_mem
    {nonfinal : List SuccessorFactor}
    {final factor : SuccessorFactor}
    (member :
      factor ∈ expandedBeforeFinalFactors nonfinal final ++ [final]) :
    factor.1 ∈ expandedSquareMarkers nonfinal final := by
  rcases List.mem_append.mp member with beforeFinal | fixedFinal
  · have beforeFinal' :
        factor ∈
          expandedNonfinalFactors nonfinal ++ [squareFactor final.1] := by
      simpa only [expandedBeforeFinalFactors] using beforeFinal
    rcases List.mem_append.mp beforeFinal' with expanded | finalSquare
    · exact List.mem_append_left _ <|
        marker_mem_source_of_mem_expandedNonfinalFactors expanded
    · have factorEq : factor = squareFactor final.1 := by
        simpa using finalSquare
      subst factor
      simp [expandedSquareMarkers, squareFactor]
  · have factorEq : factor = final := by
      simpa using fixedFinal
    subst factor
    unfold expandedSquareMarkers
    exact List.mem_append_right _ (by simp)

/-- Rendering one square factor per marker contributes exactly twice the
marker-list multiplicity. -/
theorem renderSquareFactors_count
    (markers : List Nat) (tested : Nat) :
    (renderSuccessorFactors (markers.map squareFactor)).count tested =
      2 * markers.count tested := by
  induction markers with
  | nil =>
      simp [renderSuccessorFactors]
  | cons marker rest induction =>
      by_cases same : tested = marker
      · subst tested
        simp [renderSuccessorFactors, induction, Nat.mul_add] <;> omega
      · simp [renderSuccessorFactors, induction,
          same, Ne.symm same] <;> omega

/-- A represented square marker is globally multiple in any displayed
square-bank factor context. -/
theorem squareBank_marker_multiple
    (before : List Nat) (markers : List Nat)
    (residual : List SuccessorFactor) (final : SuccessorFactor)
    {marker : Nat} (member : marker ∈ markers) :
    2 <=
      (before ++
        renderSuccessorFactors
          (markers.map squareFactor ++ residual) ++
        renderSuccessorFactor final).count marker := by
  have positive : 0 < markers.count marker :=
    List.count_pos_iff.mpr member
  have bankCount :
      2 <=
        (renderSuccessorFactors
          (markers.map squareFactor)).count marker := by
    rw [renderSquareFactors_count]
    omega
  rw [renderSuccessorFactors_append]
  simp only [List.count_append]
  omega

/-- The square exposed for every marker supplies all multiplicity premises
needed to permute the expanded factors before the fixed final residual. -/
theorem expandedFactorInventory_marker_multiple
    (leading : List Nat)
    (nonfinal : List SuccessorFactor)
    (final : SuccessorFactor) :
    ∀ factor ∈ expandedBeforeFinalFactors nonfinal final ++ [final],
      2 <=
        (leading ++
          renderSuccessorFactors
            (expandedBeforeFinalFactors nonfinal final) ++
          renderSuccessorFactor final).count factor.1 := by
  intro factor member
  have markerMember :=
    marker_mem_expandedSquareMarkers_of_factor_mem member
  have partition :=
    expandedBeforeFinalFactors_partition_perm nonfinal final
  have targetMultiple :=
    squareBank_marker_multiple leading
      (expandedSquareMarkers nonfinal final)
      (blockBearingFactors nonfinal) final markerMember
  have countEquality :=
    renderedFactorPermutation_count_eq_in_context
      partition leading (renderSuccessorFactor final) factor.1
  rw [countEquality]
  exact targetMultiple

/-! ## B4 expansion before the fixed final factor -/

/-- Expand every nonfinal factor while preserving an arbitrary leading list
and one literal fixed final factor. -/
theorem listDerivesExpandNonfinalFactorsBeforeFinal :
    ∀ (leading : List Nat)
      (nonfinal : List SuccessorFactor)
      (final : SuccessorFactor),
      (∀ factor ∈ nonfinal ++ [final],
        2 <=
          (leading ++ renderSuccessorFactors nonfinal ++
            renderSuccessorFactor final).count factor.1) ->
      B4ListDerives
        (leading ++ renderSuccessorFactors nonfinal ++
          renderSuccessorFactor final)
        (leading ++
          renderSuccessorFactors
            (expandedNonfinalFactors nonfinal) ++
          renderSuccessorFactor final)
  | leading, [], final, _ => by
      exact S5_107.ListDerives.refl _
  | leading, (marker, block) :: rest, final, multiples => by
      let factor : SuccessorFactor := (marker, block)
      have selectedMultiple :
          2 <=
            (leading ++ renderSuccessorFactor factor ++
              (renderSuccessorFactors rest ++
                renderSuccessorFactor final)).count marker := by
        have displayed := multiples factor (by simp [factor])
        simpa [factor, renderSuccessorFactors,
          List.append_assoc] using displayed
      have firstStep :
          B4ListDerives
            (leading ++ renderSuccessorFactor factor ++
              (renderSuccessorFactors rest ++
                renderSuccessorFactor final))
            (leading ++
              renderSuccessorFactors
                (expandedNonfinalFactor factor) ++
              (renderSuccessorFactors rest ++
                renderSuccessorFactor final)) := by
        by_cases blockEmpty : block = []
        · have expanded :=
            listDerivesSquareSuccessorFactorMarker
              leading block
                (renderSuccessorFactors rest ++
                  renderSuccessorFactor final)
              marker selectedMultiple
          simpa [factor, expandedNonfinalFactor, blockEmpty,
            renderSuccessorFactors, List.append_assoc] using expanded
        · have expanded :=
            listDerivesSplitSuccessorFactor
              leading block
                (renderSuccessorFactors rest ++
                  renderSuccessorFactor final)
              marker selectedMultiple
          simpa [factor, expandedNonfinalFactor, blockEmpty,
            renderSuccessorFactors,
            renderSquareAndResidualFactor,
            List.append_assoc] using expanded
      have tailMultiples :
          ∀ candidate ∈ rest ++ [final],
            2 <=
              ((leading ++
                  renderSuccessorFactors
                    (expandedNonfinalFactor factor)) ++
                renderSuccessorFactors rest ++
                renderSuccessorFactor final).count candidate.1 := by
        intro candidate member
        have oldMultiple :=
          multiples candidate <| by
            simpa [factor] using
              List.mem_cons_of_mem factor member
        have firstCount :=
          renderSuccessorFactor_count_le_expandedNonfinalFactor
            factor candidate.1
        dsimp [factor] at firstCount oldMultiple ⊢
        simp only [renderSuccessorFactors, List.count_append] at oldMultiple ⊢
        omega
      have recurse :=
        listDerivesExpandNonfinalFactorsBeforeFinal
          (leading ++
            renderSuccessorFactors
              (expandedNonfinalFactor factor))
          rest final tailMultiples
      have recurse' :
          B4ListDerives
            (leading ++
              renderSuccessorFactors
                (expandedNonfinalFactor factor) ++
              (renderSuccessorFactors rest ++
                renderSuccessorFactor final))
            (leading ++
              renderSuccessorFactors
                (expandedNonfinalFactor factor) ++
              (renderSuccessorFactors
                  (expandedNonfinalFactors rest) ++
                renderSuccessorFactor final)) := by
        simpa [List.append_assoc] using recurse
      simpa [factor, expandedNonfinalFactors,
          renderSuccessorFactors, List.append_assoc] using
        firstStep.trans recurse'

/-- Expand all nonfinal factors and also expose the final marker square.  The
original final factor is retained literally as the fixed controller. -/
theorem listDerivesExpandFactorInventoryBeforeFinal
    (leading : List Nat)
    (nonfinal : List SuccessorFactor)
    (final : SuccessorFactor)
    (multiples :
      ∀ factor ∈ nonfinal ++ [final],
        2 <=
          (leading ++ renderSuccessorFactors nonfinal ++
            renderSuccessorFactor final).count factor.1) :
    B4ListDerives
      (leading ++ renderSuccessorFactors nonfinal ++
        renderSuccessorFactor final)
      (leading ++
        renderSuccessorFactors
          (expandedBeforeFinalFactors nonfinal final) ++
        renderSuccessorFactor final) := by
  have nonfinalStep :=
    listDerivesExpandNonfinalFactorsBeforeFinal
      leading nonfinal final multiples
  have finalOldMultiple := multiples final (by simp)
  have countIncrease :=
    renderSuccessorFactors_count_le_expandedNonfinalFactors
      nonfinal final.1
  have finalMultiple :
      2 <=
        ((leading ++
            renderSuccessorFactors
              (expandedNonfinalFactors nonfinal)) ++
          renderSuccessorFactor final).count final.1 := by
    simp only [List.count_append] at finalOldMultiple ⊢
    omega
  have finalStep :=
    listDerivesSplitSuccessorFactor
      (leading ++
        renderSuccessorFactors
          (expandedNonfinalFactors nonfinal))
      final.2 [] final.1 (by
        simpa only [List.append_nil] using finalMultiple)
  have finalStep' :
      B4ListDerives
        (leading ++
          renderSuccessorFactors
            (expandedNonfinalFactors nonfinal) ++
          renderSuccessorFactor final)
        (leading ++
          renderSuccessorFactors
            (expandedBeforeFinalFactors nonfinal final) ++
          renderSuccessorFactor final) := by
    simpa [expandedBeforeFinalFactors, renderSuccessorFactors,
      renderSquareAndResidualFactor, List.append_assoc] using finalStep
  exact nonfinalStep.trans finalStep'

/-! ## Source and canonical marker support -/

/-- Every source factor marker is multiple in the literal nonfinal/final
display supplied by a reversed inventory decomposition. -/
theorem sourceFactor_marker_multiple_of_inventory
    (word : Word Nat)
    (inventory : ReversedInventoryDecomposition word) :
    ∀ factor ∈
        nonfinalSuccessorFactors word.toList ++
          [reverseTerminatedFactor inventory.first],
      2 <=
        (canonicalInitialBlock word ++
          renderSuccessorFactors
            (nonfinalSuccessorFactors word.toList) ++
          renderSuccessorFactor
            (reverseTerminatedFactor inventory.first)).count factor.1 := by
  intro factor member
  have finalShape :=
    finalSuccessorFactors_eq_of_reversedRaw_cons
      word.toList inventory.first inventory.rest inventory.rawShape
  have factorMember : factor ∈ successorFactors word.toList := by
    rw [← nonfinal_append_final_successorFactors word.toList]
    rw [finalShape]
    exact member
  have sourceMultiple :=
    successorFactor_marker_multiple
      word.toList factor.2 factor.1 factorMember
  have reconstructed := reconstruct_nonfinal_final word.toList
  rw [finalShape] at reconstructed
  have displayed :
      canonicalInitialBlock word ++
          renderSuccessorFactors
            (nonfinalSuccessorFactors word.toList) ++
          renderSuccessorFactor
            (reverseTerminatedFactor inventory.first) =
        word.toList := by
    simpa [canonicalInitialBlock, renderSuccessorFactors,
      List.append_assoc] using reconstructed
  rw [displayed]
  exact sourceMultiple

/-- The exposed marker list is literally the complete successor-marker
projection. -/
theorem expandedSquareMarkers_eq_successorMarkers_of_inventory
    (word : Word Nat)
    (inventory : ReversedInventoryDecomposition word) :
    expandedSquareMarkers
        (nonfinalSuccessorFactors word.toList)
        (reverseTerminatedFactor inventory.first) =
      successorMarkers word.toList := by
  have finalShape :=
    finalSuccessorFactors_eq_of_reversedRaw_cons
      word.toList inventory.first inventory.rest inventory.rawShape
  unfold expandedSquareMarkers successorMarkers
  rw [← nonfinal_append_final_successorFactors word.toList,
    finalShape]
  simp [List.map_append]

/-! ## Grouping duplicate square markers -/

/-- Repeat each support marker as often as it occurs in the source marker
list, retaining the supplied support order. -/
def groupedSquareMarkers
    (support source : List Nat) : List Nat :=
  support.flatMap fun marker =>
    List.replicate (source.count marker) marker

private theorem count_replicate_of_ne
    {tested label : Nat} (different : tested ≠ label) :
    ∀ count, (List.replicate count label).count tested = 0
  | 0 => rfl
  | count + 1 => by
      rw [List.replicate_succ,
        List.count_cons_of_ne (Ne.symm different),
        count_replicate_of_ne different count]

/-- Exact multiplicity in a support-grouped marker list. -/
theorem groupedSquareMarkers_count
    (support source : List Nat) (tested : Nat)
    (nodup : support.Nodup) :
    (groupedSquareMarkers support source).count tested =
      if tested ∈ support then source.count tested else 0 := by
  induction support with
  | nil =>
      simp [groupedSquareMarkers]
  | cons marker rest induction =>
      have markerAbsent := (List.nodup_cons.mp nodup).1
      have restNodup := (List.nodup_cons.mp nodup).2
      change
        (List.replicate (source.count marker) marker ++
            groupedSquareMarkers rest source).count tested =
          if tested ∈ marker :: rest then source.count tested else 0
      rw [List.count_append]
      by_cases same : tested = marker
      · subst tested
        rw [List.count_replicate_self, induction restNodup]
        simp [markerAbsent]
      · rw [count_replicate_of_ne same, induction restNodup]
        simp [same]

/-- A noduplicated support with the same membership as the source groups,
but does not change, the complete source marker multiset. -/
theorem source_perm_groupedSquareMarkers
    (support source : List Nat)
    (nodup : support.Nodup)
    (sameSupport : ∀ marker, marker ∈ support ↔ marker ∈ source) :
    source.Perm (groupedSquareMarkers support source) := by
  rw [List.perm_iff_count]
  intro tested
  rw [groupedSquareMarkers_count support source tested nodup]
  by_cases sourceMember : tested ∈ source
  · rw [if_pos ((sameSupport tested).2 sourceMember)]
  · have supportAbsent : tested ∉ support := by
      intro supportMember
      exact sourceMember ((sameSupport tested).1 supportMember)
    rw [if_neg supportAbsent]
    exact List.count_eq_zero.mpr sourceMember

/-- The exposed source marker multiset groups into canonical marker order. -/
theorem expandedSquareMarkers_perm_groupedCanonical
    (word : Word Nat)
    (inventory : ReversedInventoryDecomposition word) :
    (expandedSquareMarkers
        (nonfinalSuccessorFactors word.toList)
        (reverseTerminatedFactor inventory.first)).Perm
      (groupedSquareMarkers
        (canonicalSquareMarkers word)
        (expandedSquareMarkers
          (nonfinalSuccessorFactors word.toList)
          (reverseTerminatedFactor inventory.first))) := by
  apply source_perm_groupedSquareMarkers
  · exact canonicalSquareMarkers_nodup word
  · intro marker
    rw [mem_canonicalSquareMarkers_iff_successorMarker]
    rw [expandedSquareMarkers_eq_successorMarkers_of_inventory
      word inventory]

/-- The complete expanded inventory permutes to grouped canonical-order
squares, canonical nonfinal residual factors, and the unchanged final
residual outside the permuted list. -/
theorem expandedBeforeFinalFactors_perm_groupedCanonical
    (word : Word Nat)
    (inventory : ReversedInventoryDecomposition word) :
    (expandedBeforeFinalFactors
        (nonfinalSuccessorFactors word.toList)
        (reverseTerminatedFactor inventory.first)).Perm
      ((groupedSquareMarkers
          (canonicalSquareMarkers word)
          (expandedSquareMarkers
            (nonfinalSuccessorFactors word.toList)
            (reverseTerminatedFactor inventory.first))).map
          squareFactor ++
        canonicalNonfinalFactors word) := by
  have partition :=
    expandedBeforeFinalFactors_partition_perm
      (nonfinalSuccessorFactors word.toList)
      (reverseTerminatedFactor inventory.first)
  have groupedSquares :=
    (expandedSquareMarkers_perm_groupedCanonical
      word inventory).map squareFactor
  have groupedWithResidual :=
    groupedSquares.append_right
      (blockBearingFactors
        (nonfinalSuccessorFactors word.toList))
  have blockBearingShape :
      blockBearingFactors
          (nonfinalSuccessorFactors word.toList) =
        blockBearingNonfinalFactors word.toList := by
    rfl
  have canonicalResidual :=
    List.Perm.append_left
      ((groupedSquareMarkers
        (canonicalSquareMarkers word)
        (expandedSquareMarkers
          (nonfinalSuccessorFactors word.toList)
          (reverseTerminatedFactor inventory.first))).map squareFactor)
      (canonicalNonfinalFactors_perm_blockBearingNonfinal word).symm
  rw [blockBearingShape] at groupedWithResidual
  exact partition.trans
    (groupedWithResidual.trans canonicalResidual)

/-! ## Contracting each grouped square run -/

/-- Two adjacent square factors contract to one under `x^3 = x^2`. -/
theorem listDerivesContractAdjacentSquareFactors
    (before after : List Nat) (marker : Nat) :
    B4ListDerives
      (before ++
        renderSuccessorFactors
          [squareFactor marker, squareFactor marker] ++ after)
      (before ++
        renderSuccessorFactors [squareFactor marker] ++ after) := by
  have tripleToDouble :
      B4ListDerives [marker, marker, marker] [marker, marker] := by
    simpa [Word.singleton, Word.append] using
      (S5_107.ListDerives.ofWord
        (derivesPowerContraction (Word.singleton marker)))
  have fourToThree :
      B4ListDerives
        [marker, marker, marker, marker]
        [marker, marker, marker] := by
    simpa using tripleToDouble.append [marker]
  have fourToDouble := fourToThree.trans tripleToDouble
  simpa [renderSuccessorFactors, squareFactor,
      List.append_assoc] using
    fourToDouble.context before after

/-- Any positive number of adjacent copies of one square factor contracts to
one copy, in an arbitrary list context. -/
theorem listDerivesContractSquareFactorReplicate
    (marker : Nat) :
    ∀ (extra : Nat) (before after : List Nat),
      B4ListDerives
        (before ++
          renderSuccessorFactors
            (List.replicate (extra + 1) (squareFactor marker)) ++
          after)
        (before ++
          renderSuccessorFactors [squareFactor marker] ++ after)
  | 0, before, after => by
      exact S5_107.ListDerives.refl _
  | extra + 1, before, after => by
      have first :=
        listDerivesContractAdjacentSquareFactors
          before
          (renderSuccessorFactors
            (List.replicate extra (squareFactor marker)) ++ after)
          marker
      have recurse :=
        listDerivesContractSquareFactorReplicate
          marker extra before after
      have recurse' :
          B4ListDerives
            (before ++
              renderSuccessorFactors [squareFactor marker] ++
              (renderSuccessorFactors
                (List.replicate extra (squareFactor marker)) ++ after))
            (before ++
              renderSuccessorFactors [squareFactor marker] ++ after) := by
        simpa [List.replicate_succ, renderSuccessorFactors,
          List.append_assoc] using recurse
      simpa [List.replicate_succ, renderSuccessorFactors,
          List.append_assoc] using
        first.trans recurse'

/-- Positive-count spelling of square-run contraction. -/
theorem listDerivesContractPositiveSquareFactorReplicate
    (marker count : Nat) (before after : List Nat)
    (positive : 0 < count) :
    B4ListDerives
      (before ++
        renderSuccessorFactors
          (List.replicate count (squareFactor marker)) ++ after)
      (before ++
        renderSuccessorFactors [squareFactor marker] ++ after) := by
  cases count with
  | zero => omega
  | succ extra =>
      simpa [Nat.succ_eq_add_one] using
        listDerivesContractSquareFactorReplicate
          marker extra before after

/-- Contract every grouped square run, leaving an arbitrary following factor
renderer and fixed final suffix untouched. -/
theorem listDerivesContractGroupedSquareMarkers
    (source : List Nat) :
    ∀ (support : List Nat) (before after : List Nat),
      (∀ marker ∈ support, 0 < source.count marker) ->
      B4ListDerives
        (before ++
          renderSuccessorFactors
            ((groupedSquareMarkers support source).map squareFactor) ++
          after)
        (before ++
          renderSuccessorFactors
            (support.map squareFactor) ++ after)
  | [], before, after, _ => by
      exact S5_107.ListDerives.refl _
  | marker :: rest, before, after, positive => by
      have markerPositive := positive marker (by simp)
      have contractFirst :=
        listDerivesContractPositiveSquareFactorReplicate
          marker (source.count marker) before
          (renderSuccessorFactors
            ((groupedSquareMarkers rest source).map squareFactor) ++
            after)
          markerPositive
      have restPositive :
          ∀ candidate ∈ rest, 0 < source.count candidate := by
        intro candidate member
        exact positive candidate (List.Mem.tail marker member)
      have recurse :=
        listDerivesContractGroupedSquareMarkers
          source rest
          (before ++
            renderSuccessorFactors [squareFactor marker])
          after restPositive
      have recurse' :
          B4ListDerives
            (before ++
              renderSuccessorFactors [squareFactor marker] ++
              (renderSuccessorFactors
                ((groupedSquareMarkers rest source).map squareFactor) ++
                after))
            (before ++
              renderSuccessorFactors [squareFactor marker] ++
              (renderSuccessorFactors (rest.map squareFactor) ++ after)) := by
        simpa [List.append_assoc] using recurse
      simpa [groupedSquareMarkers, List.map_append,
          List.map_replicate,
          renderSuccessorFactors_append, renderSuccessorFactors,
          List.append_assoc] using
        contractFirst.trans recurse'

/-! ## Canonical factor theorem -/

/-- The literal source factorization reaches the deterministic square bank,
canonical block-bearing nonfinal factors, and the same fixed final factor. -/
theorem listDerivesCanonicalFactorInventory
    (word : Word Nat)
    (headSimple : S5_107.SimpleIn word word.head)
    (inventory : ReversedInventoryDecomposition word) :
    B4ListDerives
      (canonicalInitialBlock word ++
        renderSuccessorFactors
          (nonfinalSuccessorFactors word.toList) ++
        renderSuccessorFactor
          (reverseTerminatedFactor inventory.first))
      (canonicalInitialBlock word ++
        renderSuccessorFactors
          ((canonicalSquareMarkers word).map squareFactor) ++
        renderSuccessorFactors (canonicalNonfinalFactors word) ++
        renderSuccessorFactor
          (reverseTerminatedFactor inventory.first)) := by
  let nonfinal := nonfinalSuccessorFactors word.toList
  let final := reverseTerminatedFactor inventory.first
  let sourceMarkers := expandedSquareMarkers nonfinal final
  let grouped :=
    groupedSquareMarkers (canonicalSquareMarkers word) sourceMarkers
  have sourceMultiples :=
    sourceFactor_marker_multiple_of_inventory word inventory
  have expanded :=
    listDerivesExpandFactorInventoryBeforeFinal
      (canonicalInitialBlock word) nonfinal final <| by
        simpa [nonfinal, final] using sourceMultiples
  have factorPermutation :=
    expandedBeforeFinalFactors_perm_groupedCanonical word inventory
  have expandedMultiples :=
    expandedFactorInventory_marker_multiple
      (canonicalInitialBlock word) nonfinal final
  have movedRaw :=
    listDerivesSuccessorFactorPermutationBeforeFinal
      factorPermutation (canonicalInitialWord word) final <| by
        simpa [nonfinal, final,
          canonicalInitialWord_toList_of_head_simple word headSimple] using
          expandedMultiples
  have moved :
      B4ListDerives
        (canonicalInitialBlock word ++
          renderSuccessorFactors
            (expandedBeforeFinalFactors nonfinal final) ++
          renderSuccessorFactor final)
        (canonicalInitialBlock word ++
          renderSuccessorFactors
            (grouped.map squareFactor ++
              canonicalNonfinalFactors word) ++
          renderSuccessorFactor final) := by
    simpa [nonfinal, final, sourceMarkers, grouped,
      canonicalInitialWord_toList_of_head_simple word headSimple] using
        movedRaw
  have groupedPositive :
      ∀ marker ∈ canonicalSquareMarkers word,
        0 < sourceMarkers.count marker := by
    intro marker markerMember
    apply List.count_pos_iff.mpr
    have successorMember :=
      (mem_canonicalSquareMarkers_iff_successorMarker
        word marker).mp markerMember
    have sourceShape :
        sourceMarkers = successorMarkers word.toList := by
      simpa [sourceMarkers, nonfinal, final] using
        expandedSquareMarkers_eq_successorMarkers_of_inventory
          word inventory
    rw [sourceShape]
    exact successorMember
  have contractedRaw :=
    listDerivesContractGroupedSquareMarkers
      sourceMarkers (canonicalSquareMarkers word)
      (canonicalInitialBlock word)
      (renderSuccessorFactors (canonicalNonfinalFactors word) ++
        renderSuccessorFactor final)
      groupedPositive
  have contracted :
      B4ListDerives
        (canonicalInitialBlock word ++
          renderSuccessorFactors
            (grouped.map squareFactor ++
              canonicalNonfinalFactors word) ++
          renderSuccessorFactor final)
        (canonicalInitialBlock word ++
          renderSuccessorFactors
            ((canonicalSquareMarkers word).map squareFactor) ++
          renderSuccessorFactors (canonicalNonfinalFactors word) ++
          renderSuccessorFactor final) := by
    simpa [grouped, renderSuccessorFactors_append,
      List.append_assoc] using contractedRaw
  simpa [nonfinal, final] using expanded.trans (moved.trans contracted)

/-- Minimal simple-head consumer contract: the source list reaches the exact
deterministic canonical list under the published four-law basis. -/
theorem listDerivesCanonicalList_of_head_simple
    (word : Word Nat)
    (headSimple : S5_107.SimpleIn word word.head)
    (inventory : ReversedInventoryDecomposition word) :
    B4ListDerives word.toList (canonicalList word) := by
  have core :=
    listDerivesCanonicalFactorInventory word headSimple inventory
  have finalShape :=
    finalSuccessorFactors_eq_of_reversedRaw_cons
      word.toList inventory.first inventory.rest inventory.rawShape
  have sourceReconstruction := reconstruct_nonfinal_final word.toList
  rw [finalShape] at sourceReconstruction
  have sourceShape :
      canonicalInitialBlock word ++
          renderSuccessorFactors
            (nonfinalSuccessorFactors word.toList) ++
          renderSuccessorFactor
            (reverseTerminatedFactor inventory.first) =
        word.toList := by
    simpa [canonicalInitialBlock, renderSuccessorFactors,
      List.append_assoc] using sourceReconstruction
  have targetShape :
      canonicalInitialBlock word ++
          renderSuccessorFactors
            ((canonicalSquareMarkers word).map squareFactor) ++
          renderSuccessorFactors (canonicalNonfinalFactors word) ++
          renderSuccessorFactor
            (reverseTerminatedFactor inventory.first) =
        canonicalList word := by
    rw [renderSuccessorFactors_map_squareFactor,
      renderCanonicalNonfinalFactors_eq inventory,
      ← canonicalFinalFactorWord_eq_render_final inventory]
    rfl
  rw [sourceShape, targetShape] at core
  exact core

end SemigroupBasis.CoRoots.Order6LeeZhang23_12FactorNormalization
