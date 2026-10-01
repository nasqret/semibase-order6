import SemigroupBasis.BlockTraceDerives
import SemigroupBasis.CoRoots.Order6SporadicSection15AlphaParsedPostPair

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

namespace AlphaNormalization

private def pairedSortedLabels (letters : List Nat) : List Nat :=
  AlphaPostPair.sortedPairedLabels
    (AlphaPostPair.pairedLabels
      (AlphaOccurrencePairing.pairMarkerOccurrences
        (AlphaParsedBridge.markerLabels letters)))

private theorem mem_pairedLabels_iff
    {markers : List Nat}
    (paired : AlphaOccurrencePairing.PairedMarkerList markers)
    (label : Nat) :
    label ∈ AlphaPostPair.pairedLabels markers ↔ label ∈ markers := by
  induction paired with
  | nil =>
      simp [AlphaPostPair.pairedLabels]
  | pair marker paired induction =>
      simp [AlphaPostPair.pairedLabels, induction]

private theorem pairedLabels_nodup_of_twice
    {markers : List Nat}
    (paired : AlphaOccurrencePairing.PairedMarkerList markers)
    (twice : AlphaOccurrencePairing.TwiceOccurringMarkers markers) :
    (AlphaPostPair.pairedLabels markers).Nodup := by
  induction paired with
  | nil =>
      simp [AlphaPostPair.pairedLabels]
  | @pair marker rest paired induction =>
      have markerCount : (marker :: marker :: rest).count marker = 2 :=
        twice marker (by simp)
      have restCount : rest.count marker = 0 := by
        have countShape : 2 + rest.count marker = 2 := by
          simpa using markerCount
        omega
      have markerNotRest : marker ∉ rest :=
        List.count_eq_zero.mp restCount
      have restTwice :
          AlphaOccurrencePairing.TwiceOccurringMarkers rest := by
        intro tested testedMember
        have different : tested ≠ marker := by
          intro equal
          subst tested
          exact markerNotRest testedMember
        have sourceCount :
            (marker :: marker :: rest).count tested = 2 :=
          twice tested (by simp [testedMember])
        simpa [List.count_cons_of_ne (Ne.symm different)] using sourceCount
      simp only [AlphaPostPair.pairedLabels, List.nodup_cons]
      exact
        ⟨fun member =>
            markerNotRest ((mem_pairedLabels_iff paired marker).mp member),
          induction restTwice⟩

private theorem sortedPairedLabels_pairwise (labels : List Nat) :
    (AlphaPostPair.sortedPairedLabels labels).Pairwise (· ≤ ·) := by
  have transitive :
      ∀ left middle right : Nat,
        decide (left ≤ middle) = true →
        decide (middle ≤ right) = true →
        decide (left ≤ right) = true := by
    intro left middle right first second
    exact decide_eq_true
      (Nat.le_trans
        (of_decide_eq_true first)
        (of_decide_eq_true second))
  have total :
      ∀ left right : Nat,
        (decide (left ≤ right) || decide (right ≤ left)) = true := by
    intro left right
    rcases Nat.le_total left right with first | second
    · simp [first]
    · simp [second]
  have sorted := List.pairwise_mergeSort transitive total labels
  simpa [AlphaPostPair.sortedPairedLabels] using
    (sorted.imp fun relation => of_decide_eq_true relation)

private theorem perm_of_nodup_mem_iff
    {left right : List Nat}
    (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (sameMembers : ∀ label, label ∈ left ↔ label ∈ right) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro label
  rw [leftNodup.count, rightNodup.count]
  simp only [sameMembers label]

private theorem pairedSortedLabels_eq_sortedDoubled
    (letters : List Nat)
    (branch : CanonicalData.canonicalBranch letters = .alpha) :
    pairedSortedLabels letters =
      CanonicalData.sortedDoubledLetters letters := by
  let markers := AlphaParsedBridge.markerLabels letters
  let pairedMarkers :=
    AlphaOccurrencePairing.pairMarkerOccurrences markers
  let labels := AlphaPostPair.pairedLabels pairedMarkers
  have sourceTwice :
      AlphaOccurrencePairing.TwiceOccurringMarkers markers := by
    simpa [markers] using
      AlphaParsedBridge.twiceOccurringMarkers_of_branch_alpha branch
  have markerPermutation : markers.Perm pairedMarkers := by
    simpa [markers, pairedMarkers] using
      AlphaOccurrencePairing.pairMarkerOccurrences_perm markers
  have paired :
      AlphaOccurrencePairing.PairedMarkerList pairedMarkers := by
    simpa [markers, pairedMarkers] using
      AlphaOccurrencePairing.pairMarkerOccurrences_paired
        markers sourceTwice
  have pairedTwice :
      AlphaOccurrencePairing.TwiceOccurringMarkers pairedMarkers := by
    intro label labelMember
    have sourceMember : label ∈ markers :=
      markerPermutation.mem_iff.mpr labelMember
    have sourceCount := sourceTwice label sourceMember
    rw [← (List.perm_iff_count.mp markerPermutation label)]
    exact sourceCount
  have labelsNodup : labels.Nodup := by
    simpa [labels] using pairedLabels_nodup_of_twice paired pairedTwice
  have sameMembers :
      ∀ label,
        label ∈ labels ↔
          label ∈ CanonicalData.sortedDoubledLetters letters := by
    intro label
    constructor
    · intro labelMember
      have pairedMember : label ∈ pairedMarkers :=
        (mem_pairedLabels_iff paired label).mp (by
          simpa [labels] using labelMember)
      have markerMember : label ∈ markers :=
        markerPermutation.mem_iff.mpr pairedMember
      have multiple : 2 ≤ letters.count label := by
        apply (S5_107.mem_terminatedFactorMarkers_iff label letters).1
        simpa [markers, AlphaParsedBridge.markerLabels,
          ParsedWords.factors] using markerMember
      have upper := CanonicalData.count_le_two_of_branch_alpha branch label
      apply (CanonicalData.sortedDoubledLetters_mem_iff label letters).2
      omega
    · intro doubledMember
      have doubled :=
        (CanonicalData.sortedDoubledLetters_mem_iff label letters).1
          doubledMember
      have markerMember : label ∈ markers := by
        apply (S5_107.mem_terminatedFactorMarkers_iff label letters).2
        simpa [markers, AlphaParsedBridge.markerLabels,
          ParsedWords.factors] using (show 2 ≤ letters.count label by omega)
      have pairedMember : label ∈ pairedMarkers :=
        markerPermutation.mem_iff.mp markerMember
      have labelMember := (mem_pairedLabels_iff paired label).mpr pairedMember
      simpa [labels] using labelMember
  have labelPermutation :
      labels.Perm (CanonicalData.sortedDoubledLetters letters) :=
    perm_of_nodup_mem_iff labelsNodup
      (CanonicalData.sortedDoubledLetters_nodup letters) sameMembers
  have sortedPermutation :
      (AlphaPostPair.sortedPairedLabels labels).Perm
        (CanonicalData.sortedDoubledLetters letters) :=
    (AlphaPostPair.sortedPairedLabels_perm labels).trans labelPermutation
  have sortedEquality :
      AlphaPostPair.sortedPairedLabels labels =
        CanonicalData.sortedDoubledLetters letters :=
    List.Perm.eq_of_pairwise
      (fun _ _ _ _ leftLe rightLe => Nat.le_antisymm leftLe rightLe)
      (sortedPairedLabels_pairwise labels)
      (CanonicalData.sortedDoubledLetters_pairwise letters)
      sortedPermutation
  simpa [pairedSortedLabels, markers, pairedMarkers, labels] using
    sortedEquality

private theorem internal_length_eq_twice_pairedSortedLabels
    {letters : List Nat} {internal : List (List Nat)}
    (branch : CanonicalData.canonicalBranch letters = .alpha)
    (gapShape :
      AlphaParsedBridge.postMarkerGaps letters =
        internal ++ [ParsedWords.finalBlock letters]) :
    internal.length + 1 = 2 * (pairedSortedLabels letters).length := by
  let markers := AlphaParsedBridge.markerLabels letters
  let pairedMarkers :=
    AlphaOccurrencePairing.pairMarkerOccurrences markers
  let labels := AlphaPostPair.pairedLabels pairedMarkers
  have twice : AlphaOccurrencePairing.TwiceOccurringMarkers markers := by
    simpa [markers] using
      AlphaParsedBridge.twiceOccurringMarkers_of_branch_alpha branch
  have paired :
      AlphaOccurrencePairing.PairedMarkerList pairedMarkers := by
    simpa [markers, pairedMarkers] using
      AlphaOccurrencePairing.pairMarkerOccurrences_paired markers twice
  have gapLength :=
    AlphaParsedBridge.postMarkerGaps_length_eq_markerLabels_length letters
  rw [gapShape] at gapLength
  have markerPermutation : markers.Perm pairedMarkers := by
    simpa [markers, pairedMarkers] using
      AlphaOccurrencePairing.pairMarkerOccurrences_perm markers
  have pairedLength := AlphaPostPair.pairedLabels_length paired
  simp only [List.length_append, List.length_singleton] at gapLength
  have sortedLengthEq :
      (AlphaPostPair.sortedPairedLabels labels).length = labels.length :=
    (AlphaPostPair.sortedPairedLabels_perm labels).length_eq
  calc
    internal.length + 1 = markers.length := by
      simpa [markers] using gapLength
    _ = pairedMarkers.length := markerPermutation.length_eq
    _ = 2 * labels.length := pairedLength
    _ = 2 * (AlphaPostPair.sortedPairedLabels labels).length := by
      rw [sortedLengthEq]
    _ = 2 * (pairedSortedLabels letters).length := by
      rfl

private theorem filter_terminatedFactorBlocks_ne_nil
    (factors : List ParsedWords.Factor) :
    (S5_107.terminatedFactorBlocks factors).filter
        (fun gap => gap != []) =
      S5_107.nonemptyTerminatedBlocks factors := by
  change (factors.map (fun factor => factor.1)).filter
      (fun gap => gap != []) = S5_107.nonemptyTerminatedBlocks factors
  induction factors with
  | nil =>
      rfl
  | cons factor factors induction =>
      rcases factor with ⟨block, marker⟩
      by_cases empty : block = []
      · subst block
        simp [S5_107.nonemptyTerminatedBlocks, induction]
      · simp [S5_107.nonemptyTerminatedBlocks, empty, induction]

private theorem slots_eq_replicate_nil_of_nonemptyCount_zero :
    ∀ slots : List (List Nat),
      AlphaSlotMoves.nonemptySlotCount slots = 0 →
        slots = List.replicate slots.length []
  | [], _ => by
      rfl
  | [] :: slots, zero => by
      have tailZero : AlphaSlotMoves.nonemptySlotCount slots = 0 := by
        simpa [AlphaSlotMoves.nonemptySlotCount] using zero
      rw [slots_eq_replicate_nil_of_nonemptyCount_zero slots tailZero]
      have wholeEmpty :
          [] :: List.replicate slots.length ([] : List Nat) =
            List.replicate (slots.length + 1) [] := by
        rw [List.replicate_succ]
      rw [wholeEmpty]
      simp
  | (head :: tail) :: slots, zero => by
      simp [AlphaSlotMoves.nonemptySlotCount] at zero

private theorem compacted_eq_filter_append_replicate_nil :
    ∀ slots : List (List Nat),
      AlphaSlotMoves.emptyBeforeNonemptyInversions slots = 0 →
        slots =
          slots.filter (fun slot => slot != []) ++
            List.replicate (slots.count []) []
  | [], _ => by
      simp
  | [] :: slots, zero => by
      have countZero : AlphaSlotMoves.nonemptySlotCount slots = 0 := by
        simp only [AlphaSlotMoves.emptyBeforeNonemptyInversions] at zero
        omega
      have allEmpty :=
        slots_eq_replicate_nil_of_nonemptyCount_zero slots countZero
      rw [allEmpty]
      have wholeEmpty :
          [] :: List.replicate slots.length ([] : List Nat) =
            List.replicate (slots.length + 1) [] := by
        rw [List.replicate_succ]
      rw [wholeEmpty]
      simp
  | (head :: tail) :: slots, zero => by
      have tailZero :
          AlphaSlotMoves.emptyBeforeNonemptyInversions slots = 0 := by
        simpa [AlphaSlotMoves.emptyBeforeNonemptyInversions] using zero
      rw [compacted_eq_filter_append_replicate_nil slots tailZero]
      have filteredCountZero :
          (slots.filter (fun slot => slot != [])).count [] = 0 := by
        rw [List.count_eq_zero]
        simp
      simp [filteredCountZero]

private theorem renderGapSlots_replicate_nil :
    ∀ (markers : List Nat) (count : Nat),
      AlphaSlotMoves.renderGapSlots markers
          (List.replicate count []) =
        markers
  | [], _ => by
      rfl
  | marker :: markers, 0 => by
      rfl
  | marker :: markers, count + 1 => by
      rw [List.replicate_succ]
      simpa only [AlphaSlotMoves.renderGapSlots, List.nil_append] using
        congrArg (List.cons marker)
          (renderGapSlots_replicate_nil markers count)

private theorem pairedMarkers_eq_renderSquares (labels : List Nat) :
    AlphaSlotMoves.pairedMarkers labels =
      CanonicalData.renderSquares labels := by
  induction labels with
  | nil =>
      rfl
  | cons label labels induction =>
      simp [AlphaSlotMoves.pairedMarkers,
        CanonicalData.renderSquares, CanonicalData.renderCopies, induction]

private theorem renderPairedGapSlots_with_empty_tail :
    ∀ (labels : List Nat) (units : List (List Nat)) (emptyCount : Nat),
      units.length + emptyCount + 1 = 2 * labels.length →
      0 < emptyCount →
      AlphaSlotMoves.renderPairedGapSlots labels
          (units ++ List.replicate emptyCount []) =
        CanonicalData.renderAlphaPairs
          ((units.length + 1) / 2) labels units
  | [], units, emptyCount, balanced, _ => by
      simp at balanced
  | label :: labels, [], emptyCount, _, _ => by
      simp [AlphaSlotMoves.renderPairedGapSlots,
        renderGapSlots_replicate_nil,
        pairedMarkers_eq_renderSquares]
  | label :: labels, [unit], emptyCount, _, _ => by
      simp [AlphaSlotMoves.renderPairedGapSlots,
        AlphaSlotMoves.pairedMarkers,
        AlphaSlotMoves.renderGapSlots,
        renderGapSlots_replicate_nil,
        pairedMarkers_eq_renderSquares,
        CanonicalData.renderAlphaPairs]
  | label :: labels, first :: second :: units, emptyCount,
      balanced, positive => by
      have tailBalanced :
          units.length + emptyCount + 1 = 2 * labels.length := by
        simp only [List.length_cons] at balanced
        omega
      have induction :=
        renderPairedGapSlots_with_empty_tail
          labels units emptyCount tailBalanced positive
      have induction' :
          AlphaSlotMoves.renderGapSlots
              (AlphaSlotMoves.pairedMarkers labels)
              (units ++ List.replicate emptyCount []) =
            CanonicalData.renderAlphaPairs
              ((units.length + 1) / 2) labels units := by
        simpa [AlphaSlotMoves.renderPairedGapSlots] using induction
      have separated :
          (((first :: second :: units).length + 1) / 2) =
            ((units.length + 1) / 2) + 1 := by
        simp only [List.length_cons]
        omega
      rw [separated]
      simp [AlphaSlotMoves.renderPairedGapSlots,
        AlphaSlotMoves.pairedMarkers,
        AlphaSlotMoves.renderGapSlots,
        CanonicalData.renderAlphaPairs, induction']
termination_by labels units emptyCount _ _ => units.length

private theorem renderPairedGapSlots_absorb_endpoint :
    ∀ (labels : List Nat) (units : List (List Nat)) (endpoint : List Nat),
      units.length + 1 = 2 * labels.length →
      AlphaSlotMoves.renderPairedGapSlots labels units ++ endpoint =
        CanonicalData.renderAlphaPairs labels.length labels
          (units ++ CanonicalData.optionalRun endpoint)
  | [], units, endpoint, balanced => by
      simp at balanced
  | label :: labels, [], endpoint, balanced => by
      simp only [List.length_nil, List.length_cons] at balanced
      omega
  | label :: labels, [unit], endpoint, balanced => by
      have labelsEmpty : labels = [] := by
        apply List.eq_nil_of_length_eq_zero
        simp only [List.length_cons, List.length_nil] at balanced
        omega
      subst labels
      cases endpoint with
      | nil =>
          simp [AlphaSlotMoves.renderPairedGapSlots,
            AlphaSlotMoves.pairedMarkers,
            AlphaSlotMoves.renderGapSlots,
            CanonicalData.renderAlphaPairs, CanonicalData.optionalRun,
            CanonicalData.renderSquares, CanonicalData.renderCopies]
      | cons endpointHead endpointTail =>
          simp [AlphaSlotMoves.renderPairedGapSlots,
            AlphaSlotMoves.pairedMarkers,
            AlphaSlotMoves.renderGapSlots,
            CanonicalData.renderAlphaPairs, CanonicalData.optionalRun,
            CanonicalData.renderSquares, CanonicalData.renderCopies,
            List.append_assoc]
  | label :: labels, first :: second :: units, endpoint, balanced => by
      have tailBalanced : units.length + 1 = 2 * labels.length := by
        simp only [List.length_cons] at balanced
        omega
      have induction :=
        renderPairedGapSlots_absorb_endpoint
          labels units endpoint tailBalanced
      have induction' :
          AlphaSlotMoves.renderGapSlots
                (AlphaSlotMoves.pairedMarkers labels) units ++ endpoint =
            CanonicalData.renderAlphaPairs labels.length labels
              (units ++ CanonicalData.optionalRun endpoint) := by
        simpa [AlphaSlotMoves.renderPairedGapSlots] using induction
      simp [AlphaSlotMoves.renderPairedGapSlots,
        AlphaSlotMoves.pairedMarkers,
        AlphaSlotMoves.renderGapSlots,
        CanonicalData.renderAlphaPairs, induction', List.append_assoc]
termination_by labels units _endpoint _ => units.length

private theorem anchoredSwapAt :
    ∀ (labels : List Nat) (beforeSlots trailing : List (List Nat))
      (left right : List Nat),
      left ≠ [] →
      right ≠ [] →
      (beforeSlots ++ left :: right :: trailing).length + 1 =
        2 * labels.length →
      AlphaPostPair.AnchoredOccupiedUnitPermutation labels
        (beforeSlots ++ left :: right :: trailing)
        (beforeSlots ++ right :: left :: trailing)
  | labels, [], trailing, left, right, leftNonempty, rightNonempty,
      balanced => by
      obtain ⟨leftHead, leftTail, rfl⟩ :=
        List.exists_cons_of_ne_nil leftNonempty
      obtain ⟨rightHead, rightTail, rfl⟩ :=
        List.exists_cons_of_ne_nil rightNonempty
      cases labels with
      | nil =>
          simp at balanced
      | cons leftAnchor labels =>
          cases labels with
          | nil =>
              simp at balanced
          | cons rightAnchor labels =>
              cases trailing with
              | nil =>
                  simp at balanced
                  omega
              | cons between slots =>
                  exact
                    AlphaPostPair.AnchoredOccupiedUnitPermutation.even
                      leftAnchor rightAnchor leftHead rightHead labels
                      leftTail rightTail between slots
  | labels, [between], trailing, left, right, leftNonempty,
      rightNonempty, balanced => by
      obtain ⟨leftHead, leftTail, rfl⟩ :=
        List.exists_cons_of_ne_nil leftNonempty
      obtain ⟨rightHead, rightTail, rfl⟩ :=
        List.exists_cons_of_ne_nil rightNonempty
      cases labels with
      | nil =>
          simp at balanced
      | cons leftAnchor labels =>
          cases labels with
          | nil =>
              simp at balanced
          | cons rightAnchor labels =>
              exact
                AlphaPostPair.AnchoredOccupiedUnitPermutation.odd
                  leftAnchor rightAnchor leftHead rightHead labels
                  leftTail rightTail between trailing
  | labels, first :: second :: beforeSlots, trailing, left, right,
      leftNonempty, rightNonempty, balanced => by
      cases labels with
      | nil =>
          simp at balanced
      | cons leftAnchor labels =>
          have tailBalanced :
              (beforeSlots ++ left :: right :: trailing).length + 1 =
                2 * labels.length := by
            simp only [List.length_append, List.length_cons] at balanced ⊢
            omega
          exact
            AlphaPostPair.AnchoredOccupiedUnitPermutation.tail
              leftAnchor first second
              (anchoredSwapAt labels beforeSlots trailing left right
                leftNonempty rightNonempty tailBalanced)
termination_by labels beforeSlots trailing left right _ _ _ =>
  beforeSlots.length

private theorem swapClosure_perm
    {source target : List (List Nat)}
    (moves :
      SemigroupBasis.BlockTrace.SwapClosure
        (fun _ _ : List Nat => True) source target) :
    source.Perm target := by
  induction moves with
  | refl items =>
      exact List.Perm.refl items
  | trans first second firstInduction secondInduction =>
      exact firstInduction.trans secondInduction
  | cons head moves induction =>
      exact List.Perm.cons head induction
  | swap left right suffix allowed =>
      exact List.Perm.swap right left suffix

private theorem anchoredPermutation_of_swapClosure
    {source target : List (List Nat)}
    (moves :
      SemigroupBasis.BlockTrace.SwapClosure
        (fun _ _ : List Nat => True) source target)
    (labels : List Nat) (beforeSlots padding : List (List Nat))
    (sourceNonempty : ∀ unit, unit ∈ source → unit ≠ [])
    (balanced :
      (beforeSlots ++ source ++ padding).length + 1 =
        2 * labels.length) :
    AlphaPostPair.AnchoredOccupiedUnitPermutation labels
      (beforeSlots ++ source ++ padding)
      (beforeSlots ++ target ++ padding) := by
  induction moves generalizing labels beforeSlots padding with
  | refl items =>
      exact AlphaPostPair.AnchoredOccupiedUnitPermutation.refl _ _
  | @trans source middle target first second firstInduction secondInduction =>
      have firstPermutation := swapClosure_perm first
      have middleNonempty : ∀ unit, unit ∈ middle → unit ≠ [] := by
        intro unit member
        exact sourceNonempty unit (firstPermutation.mem_iff.mpr member)
      have middleBalanced :
          (beforeSlots ++ middle ++ padding).length + 1 =
            2 * labels.length := by
        have lengthEq := firstPermutation.length_eq
        simp only [List.length_append] at balanced ⊢
        omega
      exact
        AlphaPostPair.AnchoredOccupiedUnitPermutation.trans
          (firstInduction labels beforeSlots padding sourceNonempty balanced)
          (secondInduction labels beforeSlots padding middleNonempty
            middleBalanced)
  | @cons head source target moves induction =>
      have tailNonempty : ∀ unit, unit ∈ source → unit ≠ [] := by
        intro unit member
        exact sourceNonempty unit (List.Mem.tail head member)
      have shiftedBalanced :
          ((beforeSlots ++ [head]) ++ source ++ padding).length + 1 =
            2 * labels.length := by
        simpa [List.append_assoc] using balanced
      have shifted :=
        induction labels (beforeSlots ++ [head]) padding tailNonempty
          shiftedBalanced
      simpa [List.append_assoc] using shifted
  | swap left right suffix allowed =>
      have leftNonempty : left ≠ [] := sourceNonempty left (by simp)
      have rightNonempty : right ≠ [] := sourceNonempty right (by simp)
      have swapBalanced :
          (beforeSlots ++ left :: right :: (suffix ++ padding)).length + 1 =
            2 * labels.length := by
        simpa [List.append_assoc] using balanced
      simpa [List.append_assoc] using
        anchoredSwapAt labels beforeSlots (suffix ++ padding) left right
          leftNonempty rightNonempty swapBalanced

/-- Proposition 15.1, alpha branch: every alpha word derives to the
executable canonical representative determined by its doubled labels, sorted
interior simple runs, and endpoint-capacity split. -/
theorem listDerivesCanonical_of_branch_alpha
    (letters : List Nat)
    (branch : CanonicalData.canonicalBranch letters = .alpha) :
    ListDerives letters (CanonicalData.alphaCanonicalList letters) := by
  obtain ⟨internal, compacted, gapShape, pairSortCompact,
      compactedZero, internalPermutation⟩ :=
    AlphaParsedPostPair.listDerivesPairSortAndCompact_of_branch_alpha
      letters branch
  have labelsEq :
      pairedSortedLabels letters =
        CanonicalData.sortedDoubledLetters letters :=
    pairedSortedLabels_eq_sortedDoubled letters branch
  have pairSortCompact' :
      ListDerives letters
        (S5_107.initialSimpleBlock letters ++
          AlphaSlotMoves.renderPairedGapSlots
            (CanonicalData.sortedDoubledLetters letters) compacted ++
          ParsedWords.finalBlock letters) := by
    rw [← labelsEq]
    simpa only [pairedSortedLabels] using pairSortCompact
  have internalBalanced :
      internal.length + 1 =
        2 * (CanonicalData.sortedDoubledLetters letters).length := by
    have rawBalanced :=
      internal_length_eq_twice_pairedSortedLabels branch gapShape
    rw [labelsEq] at rawBalanced
    exact rawBalanced
  obtain ⟨firstFactor, restFactors, factorsShape⟩ :=
    List.exists_cons_of_ne_nil
      (AlphaParsedBridge.factors_ne_nil_of_branch_alpha branch)
  have internalShape :
      internal = S5_107.terminatedFactorBlocks restFactors := by
    have shaped := gapShape
    simp [AlphaParsedBridge.postMarkerGaps, factorsShape] at shaped
    exact shaped.symm
  have internalPayload :
      internal.filter (fun gap => gap != []) =
        S5_107.interiorSimpleBlocks letters := by
    rw [internalShape, filter_terminatedFactorBlocks_ne_nil]
    exact ParsedWords.nonemptyRestBlocks_eq_interiorSimpleBlocks
      letters firstFactor restFactors factorsShape
  let occupied := compacted.filter (fun gap => gap != [])
  let sortedUnits :=
    S5_107.sortedSimpleBlocks (S5_107.interiorSimpleBlocks letters)
  have interiorToOccupied :
      (S5_107.interiorSimpleBlocks letters).Perm occupied := by
    have filtered :=
      internalPermutation.filter (fun gap => gap != [])
    simpa [occupied, internalPayload] using filtered
  have interiorToSorted :
      (S5_107.interiorSimpleBlocks letters).Perm sortedUnits := by
    dsimp [sortedUnits]
    exact (List.mergeSort_perm _ _).symm
  have occupiedToSorted : occupied.Perm sortedUnits :=
    interiorToOccupied.symm.trans interiorToSorted
  have interiorNodup := S5_107.interiorSimpleBlocks_nodup letters
  have occupiedNodup : occupied.Nodup :=
    interiorToOccupied.nodup_iff.mp interiorNodup
  have sortedNodup : sortedUnits.Nodup :=
    interiorToSorted.nodup_iff.mp interiorNodup
  have occupiedNonempty : ∀ unit, unit ∈ occupied → unit ≠ [] := by
    intro unit member
    have member' := member
    simp [occupied] at member'
    exact member'.2
  let emptyCount := compacted.count []
  have compactedShape :
      compacted = occupied ++ List.replicate emptyCount [] := by
    simpa [occupied, emptyCount] using
      compacted_eq_filter_append_replicate_nil compacted compactedZero
  have compactedBalanced :
      compacted.length + 1 =
        2 * (CanonicalData.sortedDoubledLetters letters).length := by
    rw [← internalPermutation.length_eq]
    exact internalBalanced
  have sourceSlotsBalanced :
      (occupied ++ List.replicate emptyCount []).length + 1 =
        2 * (CanonicalData.sortedDoubledLetters letters).length := by
    rw [← compactedShape]
    exact compactedBalanced
  have unitSwaps :
      SemigroupBasis.BlockTrace.SwapClosure
        (fun _ _ : List Nat => True) occupied sortedUnits :=
    SemigroupBasis.BlockTrace.SwapClosure.of_perm_of_dependent_order
      occupiedNodup sortedNodup occupiedToSorted (by
        intro left right leftMember rightMember blocked
        exact False.elim (blocked trivial))
  have unitMoves :
      AlphaPostPair.AnchoredOccupiedUnitPermutation
        (CanonicalData.sortedDoubledLetters letters)
        (occupied ++ List.replicate emptyCount [])
        (sortedUnits ++ List.replicate emptyCount []) := by
    simpa using
      anchoredPermutation_of_swapClosure unitSwaps
        (CanonicalData.sortedDoubledLetters letters) []
        (List.replicate emptyCount []) occupiedNonempty
        (by simpa using sourceSlotsBalanced)
  have sortUnits :=
    AlphaPostPair.listDerivesPermuteOccupiedAlphaUnits unitMoves
      (S5_107.initialSimpleBlock letters)
      (ParsedWords.finalBlock letters)
  have sortFromCompacted :
      ListDerives
        (S5_107.initialSimpleBlock letters ++
          AlphaSlotMoves.renderPairedGapSlots
            (CanonicalData.sortedDoubledLetters letters) compacted ++
          ParsedWords.finalBlock letters)
        (S5_107.initialSimpleBlock letters ++
          AlphaSlotMoves.renderPairedGapSlots
            (CanonicalData.sortedDoubledLetters letters)
            (sortedUnits ++ List.replicate emptyCount []) ++
          ParsedWords.finalBlock letters) := by
    rw [compactedShape]
    exact sortUnits
  have unitLength := occupiedToSorted.length_eq
  have targetSlotsBalanced :
      sortedUnits.length + emptyCount + 1 =
        2 * (CanonicalData.sortedDoubledLetters letters).length := by
    simp only [List.length_append, List.length_replicate] at sourceSlotsBalanced
    omega
  have finalShape := ParsedWords.finalBlock_eq_finalSimpleBlock letters
  have doubledNonempty :=
    CanonicalData.sortedDoubledLetters_ne_nil_of_branch_alpha branch
  have doubledLengthPositive :
      0 < (CanonicalData.sortedDoubledLetters letters).length :=
    List.length_pos_iff.mpr doubledNonempty
  by_cases capacity :
      2 * (CanonicalData.sortedDoubledLetters letters).length - 1 ≤
        sortedUnits.length
  · have emptyCountZero : emptyCount = 0 := by
      omega
    have fullBalanced :
        sortedUnits.length + 1 =
          2 * (CanonicalData.sortedDoubledLetters letters).length := by
      omega
    have absorbed :=
      renderPairedGapSlots_absorb_endpoint
        (CanonicalData.sortedDoubledLetters letters) sortedUnits
        (ParsedWords.finalBlock letters) fullBalanced
    have canonicalShape :
        S5_107.initialSimpleBlock letters ++
            AlphaSlotMoves.renderPairedGapSlots
              (CanonicalData.sortedDoubledLetters letters)
              (sortedUnits ++ List.replicate emptyCount []) ++
            ParsedWords.finalBlock letters =
          CanonicalData.alphaCanonicalList letters := by
      rw [emptyCountZero]
      simp only [List.replicate_zero, List.append_nil]
      rw [List.append_assoc, absorbed]
      simp [CanonicalData.alphaCanonicalList,
        CanonicalData.alphaRenderData, CanonicalData.renderAlphaData,
        capacity, sortedUnits, finalShape]
    rw [canonicalShape] at sortFromCompacted
    exact pairSortCompact'.trans sortFromCompacted
  · have emptyCountPositive : 0 < emptyCount := by
      omega
    have retained :=
      renderPairedGapSlots_with_empty_tail
        (CanonicalData.sortedDoubledLetters letters) sortedUnits
        emptyCount targetSlotsBalanced emptyCountPositive
    have canonicalShape :
        S5_107.initialSimpleBlock letters ++
            AlphaSlotMoves.renderPairedGapSlots
              (CanonicalData.sortedDoubledLetters letters)
              (sortedUnits ++ List.replicate emptyCount []) ++
            ParsedWords.finalBlock letters =
          CanonicalData.alphaCanonicalList letters := by
      rw [retained]
      simp [CanonicalData.alphaCanonicalList,
        CanonicalData.alphaRenderData, CanonicalData.renderAlphaData,
        capacity, sortedUnits, finalShape]
    rw [canonicalShape] at sortFromCompacted
    exact pairSortCompact'.trans sortFromCompacted

end AlphaNormalization

end SemigroupBasis.CoRoots.Order6SporadicSection15
