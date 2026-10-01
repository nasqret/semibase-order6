import SemigroupBasis.CoRoots.S5_402Factorization

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_402

open SemigroupBasis

private abbrev listWordOfCons :=
  S5_107.listWordOfCons

/-! ## Lee-style transposition of square-ended factors -/

/-- List-level anchored block swap for arbitrary nonempty blocks. -/
private theorem listDerivesAnchoredBlockSwapLists
    (anchor : Nat) {left right : List Nat}
    (leftNonempty : left ≠ [])
    (rightNonempty : right ≠ []) :
    ListDerives
      ([anchor] ++ left ++ [anchor] ++ right ++ [anchor])
      ([anchor] ++ right ++ [anchor] ++ left ++ [anchor]) := by
  obtain ⟨leftHead, leftTail, rfl⟩ :=
    List.exists_cons_of_ne_nil leftNonempty
  obtain ⟨rightHead, rightTail, rfl⟩ :=
    List.exists_cons_of_ne_nil rightNonempty
  simpa [listWordOfCons, Word.toList, Word.singleton,
    Word.append, List.append_assoc] using
      (S5_107.ListDerives.ofWord <|
        derivesLeeSimpleBlockSwap
          (Word.singleton anchor)
          (listWordOfCons leftHead leftTail)
          (listWordOfCons rightHead rightTail))

/-- Lee's factor-swap calculation after the controller and both factor
markers have been expanded. Two square moves expose the anchored swap; the
reverse square moves restore the square-ended factor shape. -/
theorem listDerivesExpandedFactorSwap
    (controller leftMarker rightMarker : Nat)
    (leftBlock rightBlock : List Nat) :
    ListDerives
      ([controller, controller, controller, controller] ++
        leftBlock ++ [leftMarker, leftMarker] ++
        rightBlock ++ [rightMarker, rightMarker])
      ([controller, controller, controller, controller] ++
        rightBlock ++ [rightMarker, rightMarker] ++
        leftBlock ++ [leftMarker, leftMarker]) := by
  let firstMiddle : Word Nat :=
    listWordOfCons controller (controller :: leftBlock)
  have firstMoveCore :=
    S5_107.ListDerives.ofWord <|
      derivesLeeSquareTailMove
        (Word.singleton controller)
        firstMiddle
        (Word.singleton leftMarker)
  have firstMove :
      ListDerives
        ([controller, controller, controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker] ++
          rightBlock ++ [rightMarker, rightMarker])
        ([controller, controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker, controller] ++
          rightBlock ++ [rightMarker, rightMarker]) := by
    simpa [firstMiddle, listWordOfCons, Word.toList,
      Word.singleton, Word.append, List.append_assoc] using
        firstMoveCore.append
          (rightBlock ++ [rightMarker, rightMarker])

  let secondMiddle : Word Nat :=
    listWordOfCons controller
      (leftBlock ++
        [leftMarker, leftMarker, controller] ++ rightBlock)
  have secondMove :
      ListDerives
        ([controller, controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker, controller] ++
          rightBlock ++ [rightMarker, rightMarker])
        ([controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker, controller] ++
          rightBlock ++
            [rightMarker, rightMarker, controller]) := by
    simpa [secondMiddle, listWordOfCons, S5_107.listWordOfCons, Word.toList,
      Word.singleton, Word.append, List.append_assoc] using
        (S5_107.ListDerives.ofWord <|
          derivesLeeSquareTailMove
            (Word.singleton controller)
            secondMiddle
            (Word.singleton rightMarker))

  have swapCore :=
    listDerivesAnchoredBlockSwapLists
      controller
      (left := leftBlock ++ [leftMarker, leftMarker])
      (right := rightBlock ++ [rightMarker, rightMarker])
      (by simp) (by simp)
  have swapped :
      ListDerives
        ([controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker, controller] ++
          rightBlock ++
            [rightMarker, rightMarker, controller])
        ([controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker, controller] ++
          leftBlock ++
            [leftMarker, leftMarker, controller]) := by
    simpa [Word.toList, Word.singleton, Word.append,
      List.append_assoc] using
      swapCore.prepend [controller]

  let thirdMiddle : Word Nat :=
    listWordOfCons controller
      (rightBlock ++
        [rightMarker, rightMarker, controller] ++ leftBlock)
  have thirdMoveForward :=
    S5_107.ListDerives.ofWord <|
      derivesLeeSquareTailMove
        (Word.singleton controller)
        thirdMiddle
        (Word.singleton leftMarker)
  have thirdMove :
      ListDerives
        ([controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker, controller] ++
          leftBlock ++
            [leftMarker, leftMarker, controller])
        ([controller, controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker, controller] ++
          leftBlock ++ [leftMarker, leftMarker]) := by
    simpa [thirdMiddle, listWordOfCons, S5_107.listWordOfCons, Word.toList,
      Word.singleton, Word.append, List.append_assoc] using
        thirdMoveForward.symm

  let fourthMiddle : Word Nat :=
    listWordOfCons controller (controller :: rightBlock)
  have fourthMoveCore :=
    S5_107.ListDerives.ofWord <|
      derivesLeeSquareTailMove
        (Word.singleton controller)
        fourthMiddle
        (Word.singleton rightMarker)
  have fourthMove :
      ListDerives
        ([controller, controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker, controller] ++
          leftBlock ++ [leftMarker, leftMarker])
        ([controller, controller, controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker] ++
          leftBlock ++ [leftMarker, leftMarker]) := by
    simpa [fourthMiddle, listWordOfCons, Word.toList,
      Word.singleton, Word.append, List.append_assoc] using
        fourthMoveCore.symm.append
          (leftBlock ++ [leftMarker, leftMarker])

  exact
    firstMove.trans <|
      secondMove.trans <|
        swapped.trans <|
          thirdMove.trans fourthMove

/-- Swap two adjacent square-ended factors using the square at the end of
the preceding factor as controller. The arbitrary prefix, controller block,
and suffix remain fixed. -/
theorem listDerivesSquaredFactorSwapAfterController
    (before controllerBlock leftBlock rightBlock after : List Nat)
    (controller leftMarker rightMarker : Nat) :
    ListDerives
      (before ++ controllerBlock ++ [controller, controller] ++
        leftBlock ++ [leftMarker, leftMarker] ++
        rightBlock ++ [rightMarker, rightMarker] ++ after)
      (before ++ controllerBlock ++ [controller, controller] ++
        rightBlock ++ [rightMarker, rightMarker] ++
        leftBlock ++ [leftMarker, leftMarker] ++ after) := by
  have expandController :=
    (S5_107.ListDerives.ofWord <|
      (derivesLeePowerFourToTwo
        (Word.singleton controller)).symm).context
        (before ++ controllerBlock)
        (leftBlock ++ [leftMarker, leftMarker] ++
          rightBlock ++ [rightMarker, rightMarker] ++ after)
  have expandStep :
      ListDerives
        (before ++ controllerBlock ++ [controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker] ++
          rightBlock ++ [rightMarker, rightMarker] ++ after)
        (before ++ controllerBlock ++
          [controller, controller, controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker] ++
          rightBlock ++ [rightMarker, rightMarker] ++ after) := by
    simpa [Word.toList, Word.singleton, Word.append,
      List.append_assoc] using expandController
  have swapStep :=
    (listDerivesExpandedFactorSwap
      controller leftMarker rightMarker
      leftBlock rightBlock).context
        (before ++ controllerBlock) after
  have swapStep' :
      ListDerives
        (before ++ controllerBlock ++
          [controller, controller, controller, controller] ++
          leftBlock ++ [leftMarker, leftMarker] ++
          rightBlock ++ [rightMarker, rightMarker] ++ after)
        (before ++ controllerBlock ++
          [controller, controller, controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker] ++
          leftBlock ++ [leftMarker, leftMarker] ++ after) := by
    simpa [List.append_assoc] using swapStep
  have contractController :=
    (S5_107.ListDerives.ofWord <|
      derivesLeePowerFourToTwo
        (Word.singleton controller)).context
        (before ++ controllerBlock)
        (rightBlock ++ [rightMarker, rightMarker] ++
          leftBlock ++ [leftMarker, leftMarker] ++ after)
  have contractStep :
      ListDerives
        (before ++ controllerBlock ++
          [controller, controller, controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker] ++
          leftBlock ++ [leftMarker, leftMarker] ++ after)
        (before ++ controllerBlock ++ [controller, controller] ++
          rightBlock ++ [rightMarker, rightMarker] ++
          leftBlock ++ [leftMarker, leftMarker] ++ after) := by
    simpa [Word.toList, Word.singleton, Word.append,
      List.append_assoc] using contractController
  exact expandStep.trans (swapStep'.trans contractStep)

/-- Every permutation of the square-ended factors after one fixed first
factor is derivable. This is the unrestricted Lee-style sorting boundary. -/
theorem listDerivesSquaredTailPermutation
    {source target : List (List Nat × Nat)}
    (permutation : source.Perm target) :
    ∀ (first : List Nat × Nat) (final : List Nat),
      ListDerives
        (renderSquaredTerminatedBlocks
            (first :: source) ++ final)
        (renderSquaredTerminatedBlocks
            (first :: target) ++ final) := by
  induction permutation with
  | nil =>
      intro first final
      exact S5_107.ListDerives.refl _
  | @cons factor source target permutation ih =>
      intro first final
      rcases first with ⟨firstBlock, firstMarker⟩
      have tailStep := ih factor final
      simpa [renderSquaredTerminatedBlocks,
        List.append_assoc] using
          tailStep.prepend
            (firstBlock ++ [firstMarker, firstMarker])
  | swap left right rest =>
      intro first final
      rcases first with ⟨controllerBlock, controller⟩
      rcases left with ⟨leftBlock, leftMarker⟩
      rcases right with ⟨rightBlock, rightMarker⟩
      have swapped :=
        listDerivesSquaredFactorSwapAfterController
          [] controllerBlock leftBlock rightBlock
          (renderSquaredTerminatedBlocks rest ++ final)
          controller leftMarker rightMarker
      simpa [renderSquaredTerminatedBlocks,
        List.append_assoc] using swapped.symm
  | @trans source middle target first second ihFirst ihSecond =>
      intro leading final
      exact
        (ihFirst leading final).trans
          (ihSecond leading final)

/-! ## Deterministic sorting after the fixed first factor -/

/-- Lexicographically compare factor blocks, using the marker as tie-breaker. -/
def terminatedFactorLe
    (left right : List Nat × Nat) : Bool :=
  if left.1 = right.1 then
    decide (left.2 ≤ right.2)
  else
    decide (compare left.1 right.1 != Ordering.gt)

/-- Deterministically sort a list of block-plus-successor factors. -/
def sortedTerminatedFactors
    (factors : List (List Nat × Nat)) :
    List (List Nat × Nat) :=
  factors.mergeSort terminatedFactorLe

private theorem compare_not_gt_iff_le_lists :
    ∀ left right : List Nat,
      compare left right != Ordering.gt ↔ left ≤ right
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | leftHead :: leftTail, rightHead :: rightTail => by
      rw [List.cons_le_cons_iff]
      by_cases less : leftHead < rightHead
      · have compared :
            compare leftHead rightHead = Ordering.lt :=
          Nat.compare_eq_lt.mpr less
        simp [List.compare_cons_cons, compared, less]
      · by_cases equal : leftHead = rightHead
        · subst rightHead
          simpa [List.compare_cons_cons] using
            compare_not_gt_iff_le_lists leftTail rightTail
        · have greater : rightHead < leftHead := by omega
          have compared :
              compare leftHead rightHead = Ordering.gt :=
            Nat.compare_eq_gt.mpr greater
          simp [List.compare_cons_cons, compared, less, equal]

private theorem terminatedFactorLe_transitive
    (left middle right : List Nat × Nat)
    (leftMiddle : terminatedFactorLe left middle = true)
    (middleRight : terminatedFactorLe middle right = true) :
    terminatedFactorLe left right = true := by
  rcases left with ⟨leftBlock, leftMarker⟩
  rcases middle with ⟨middleBlock, middleMarker⟩
  rcases right with ⟨rightBlock, rightMarker⟩
  unfold terminatedFactorLe at leftMiddle middleRight ⊢
  by_cases leftMiddleBlock : leftBlock = middleBlock
  · subst middleBlock
    rw [if_pos rfl] at leftMiddle
    have leftMarkerLe : leftMarker ≤ middleMarker :=
      of_decide_eq_true leftMiddle
    by_cases middleRightBlock : leftBlock = rightBlock
    · subst rightBlock
      rw [if_pos rfl] at middleRight
      rw [if_pos rfl]
      exact decide_eq_true <|
        Nat.le_trans leftMarkerLe (of_decide_eq_true middleRight)
    · rw [if_neg middleRightBlock] at middleRight
      rw [if_neg middleRightBlock]
      exact middleRight
  · rw [if_neg leftMiddleBlock] at leftMiddle
    have leftBlockLe : leftBlock ≤ middleBlock :=
      (compare_not_gt_iff_le_lists
        leftBlock middleBlock).mp (of_decide_eq_true leftMiddle)
    by_cases middleRightBlock : middleBlock = rightBlock
    · subst rightBlock
      rw [if_pos rfl] at middleRight
      rw [if_neg leftMiddleBlock]
      exact decide_eq_true <|
        (compare_not_gt_iff_le_lists
          leftBlock middleBlock).mpr leftBlockLe
    · rw [if_neg middleRightBlock] at middleRight
      have middleBlockLe : middleBlock ≤ rightBlock :=
        (compare_not_gt_iff_le_lists
          middleBlock rightBlock).mp
            (of_decide_eq_true middleRight)
      have leftRightLe : leftBlock ≤ rightBlock :=
        List.le_trans leftBlockLe middleBlockLe
      by_cases leftRightBlock : leftBlock = rightBlock
      · rw [← leftRightBlock] at middleBlockLe
        have middleEqualLeft : middleBlock = leftBlock :=
          List.le_antisymm middleBlockLe leftBlockLe
        exact False.elim <| leftMiddleBlock middleEqualLeft.symm
      · rw [if_neg leftRightBlock]
        exact decide_eq_true <|
          (compare_not_gt_iff_le_lists
            leftBlock rightBlock).mpr leftRightLe

private theorem terminatedFactorLe_total
    (left right : List Nat × Nat) :
    (terminatedFactorLe left right ||
      terminatedFactorLe right left) = true := by
  rcases left with ⟨leftBlock, leftMarker⟩
  rcases right with ⟨rightBlock, rightMarker⟩
  by_cases blocksEqual : leftBlock = rightBlock
  · subst rightBlock
    rcases Nat.le_total leftMarker rightMarker with
      leftRight | rightLeft
    · simp [terminatedFactorLe, leftRight]
    · simp [terminatedFactorLe, rightLeft]
  · rcases List.le_total leftBlock rightBlock with
      leftRight | rightLeft
    · have compared : compare leftBlock rightBlock != Ordering.gt :=
        (compare_not_gt_iff_le_lists
          leftBlock rightBlock).mpr leftRight
      simp [terminatedFactorLe, blocksEqual, compared]
    · have reverseEqual : rightBlock ≠ leftBlock :=
        Ne.symm blocksEqual
      have compared : compare rightBlock leftBlock != Ordering.gt :=
        (compare_not_gt_iff_le_lists
          rightBlock leftBlock).mpr rightLeft
      simp [terminatedFactorLe, blocksEqual, reverseEqual, compared]

private theorem terminatedFactorLe_antisymm
    {left right : List Nat × Nat}
    (leftRight : terminatedFactorLe left right = true)
    (rightLeft : terminatedFactorLe right left = true) :
    left = right := by
  rcases left with ⟨leftBlock, leftMarker⟩
  rcases right with ⟨rightBlock, rightMarker⟩
  unfold terminatedFactorLe at leftRight rightLeft
  by_cases blocksEqual : leftBlock = rightBlock
  · subst rightBlock
    rw [if_pos rfl] at leftRight rightLeft
    have markersEqual : leftMarker = rightMarker :=
      Nat.le_antisymm
        (of_decide_eq_true leftRight)
        (of_decide_eq_true rightLeft)
    subst rightMarker
    rfl
  · have reverseEqual : rightBlock ≠ leftBlock :=
      Ne.symm blocksEqual
    rw [if_neg blocksEqual] at leftRight
    rw [if_neg reverseEqual] at rightLeft
    have blockEqual : leftBlock = rightBlock :=
      List.le_antisymm
        ((compare_not_gt_iff_le_lists
          leftBlock rightBlock).mp (of_decide_eq_true leftRight))
        ((compare_not_gt_iff_le_lists
          rightBlock leftBlock).mp (of_decide_eq_true rightLeft))
    exact False.elim (blocksEqual blockEqual)

private theorem sortedTerminatedFactors_pairwise
    (factors : List (List Nat × Nat)) :
    (sortedTerminatedFactors factors).Pairwise
      (fun left right => terminatedFactorLe left right = true) := by
  simpa [sortedTerminatedFactors] using
    List.pairwise_mergeSort
      terminatedFactorLe_transitive terminatedFactorLe_total factors

theorem sortedTerminatedFactors_eq_of_perm
    {left right : List (List Nat × Nat)}
    (permutation : left.Perm right) :
    sortedTerminatedFactors left = sortedTerminatedFactors right := by
  have sortedPermutation :
      (sortedTerminatedFactors left).Perm
        (sortedTerminatedFactors right) :=
    (List.mergeSort_perm _ _).trans <|
      permutation.trans (List.mergeSort_perm _ _).symm
  exact List.Perm.eq_of_pairwise
    (fun _ _ _ _ leftRight rightLeft =>
      terminatedFactorLe_antisymm leftRight rightLeft)
    (sortedTerminatedFactors_pairwise left)
    (sortedTerminatedFactors_pairwise right)
    sortedPermutation

theorem sortedTerminatedFactors_perm
    (factors : List (List Nat × Nat)) :
    (sortedTerminatedFactors factors).Perm factors := by
  exact List.mergeSort_perm _ _

theorem sortedTerminatedFactors_idempotent
    (factors : List (List Nat × Nat)) :
    sortedTerminatedFactors (sortedTerminatedFactors factors) =
      sortedTerminatedFactors factors :=
  sortedTerminatedFactors_eq_of_perm
    (sortedTerminatedFactors_perm factors)

/-- Factors that carry a nonempty globally simple block. -/
def blockBearingFactors
    (factors : List (List Nat × Nat)) :
    List (List Nat × Nat) :=
  factors.filter fun factor => decide (factor.1 ≠ [])

/-- Marker-only factors, which belong to the eventual repeated-marker tail. -/
def markerOnlyFactors
    (factors : List (List Nat × Nat)) :
    List (List Nat × Nat) :=
  factors.filter fun factor => decide (factor.1 = [])

theorem blockBearingFactors_blocks_nonempty
    (factors : List (List Nat × Nat)) :
    ∀ factor ∈ blockBearingFactors factors, factor.1 ≠ [] := by
  intro factor member
  simp only [blockBearingFactors, List.mem_filter,
    decide_eq_true_eq] at member
  exact member.2

private theorem markerOnlyFactors_blocks_empty_core
    (factors : List (List Nat × Nat)) :
    ∀ factor ∈ markerOnlyFactors factors, factor.1 = [] := by
  intro factor member
  simp only [markerOnlyFactors, List.mem_filter,
    decide_eq_true_eq] at member
  exact member.2

/-- Stable partitioning by block emptiness only permutes the factor list. -/
theorem blockBearingFactors_append_markerOnlyFactors_perm
    (factors : List (List Nat × Nat)) :
    (blockBearingFactors factors ++ markerOnlyFactors factors).Perm
      factors := by
  simpa [blockBearingFactors, markerOnlyFactors] using
    (List.filter_append_perm
      (fun factor : List Nat × Nat =>
        decide (factor.1 ≠ []))
      factors)

/-- Sort the block-bearing successor factors first and the marker-only
factors second. -/
def sortedTerminatedTail
    (factors : List (List Nat × Nat)) :
    List (List Nat × Nat) :=
  sortedTerminatedFactors (blockBearingFactors factors) ++
    sortedTerminatedFactors (markerOnlyFactors factors)

theorem blockBearingFactors_sortedTerminatedTail
    (factors : List (List Nat × Nat)) :
    blockBearingFactors (sortedTerminatedTail factors) =
      sortedTerminatedFactors (blockBearingFactors factors) := by
  unfold sortedTerminatedTail blockBearingFactors
  rw [List.filter_append]
  have keepBlockBearing :
      (sortedTerminatedFactors (blockBearingFactors factors)).filter
          (fun factor : List Nat × Nat =>
            decide (factor.1 ≠ [])) =
        sortedTerminatedFactors (blockBearingFactors factors) := by
    apply List.filter_eq_self.mpr
    intro factor member
    apply decide_eq_true
    exact blockBearingFactors_blocks_nonempty factors factor <|
      (sortedTerminatedFactors_perm
        (blockBearingFactors factors)).mem_iff.mp member
  have dropMarkerOnly :
      (sortedTerminatedFactors (markerOnlyFactors factors)).filter
          (fun factor : List Nat × Nat =>
            decide (factor.1 ≠ [])) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro factor member
    simp only [decide_eq_true_eq]
    intro nonempty
    exact nonempty <|
      markerOnlyFactors_blocks_empty_core factors factor <|
        (sortedTerminatedFactors_perm
          (markerOnlyFactors factors)).mem_iff.mp member
  have keepBlockBearing' :
      (sortedTerminatedFactors
          (List.filter (fun factor : List Nat × Nat =>
            decide (factor.1 ≠ [])) factors)).filter
          (fun factor : List Nat × Nat =>
            decide (factor.1 ≠ [])) =
        sortedTerminatedFactors
          (List.filter (fun factor : List Nat × Nat =>
            decide (factor.1 ≠ [])) factors) := by
    simpa only [blockBearingFactors] using keepBlockBearing
  rw [keepBlockBearing', dropMarkerOnly, List.append_nil]

theorem markerOnlyFactors_sortedTerminatedTail
    (factors : List (List Nat × Nat)) :
    markerOnlyFactors (sortedTerminatedTail factors) =
      sortedTerminatedFactors (markerOnlyFactors factors) := by
  unfold sortedTerminatedTail markerOnlyFactors
  rw [List.filter_append]
  have dropBlockBearing :
      (sortedTerminatedFactors (blockBearingFactors factors)).filter
          (fun factor : List Nat × Nat =>
            decide (factor.1 = [])) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro factor member
    simp only [decide_eq_true_eq]
    exact blockBearingFactors_blocks_nonempty factors factor <|
      (sortedTerminatedFactors_perm
        (blockBearingFactors factors)).mem_iff.mp member
  have keepMarkerOnly :
      (sortedTerminatedFactors (markerOnlyFactors factors)).filter
          (fun factor : List Nat × Nat =>
            decide (factor.1 = [])) =
        sortedTerminatedFactors (markerOnlyFactors factors) := by
    apply List.filter_eq_self.mpr
    intro factor member
    apply decide_eq_true
    exact markerOnlyFactors_blocks_empty_core factors factor <|
      (sortedTerminatedFactors_perm
        (markerOnlyFactors factors)).mem_iff.mp member
  have keepMarkerOnly' :
      (sortedTerminatedFactors
          (List.filter (fun factor : List Nat × Nat =>
            decide (factor.1 = [])) factors)).filter
          (fun factor : List Nat × Nat =>
            decide (factor.1 = [])) =
        sortedTerminatedFactors
          (List.filter (fun factor : List Nat × Nat =>
            decide (factor.1 = [])) factors) := by
    simpa only [markerOnlyFactors] using keepMarkerOnly
  rw [dropBlockBearing, keepMarkerOnly', List.nil_append]

theorem sortedTerminatedTail_perm
    (factors : List (List Nat × Nat)) :
    (sortedTerminatedTail factors).Perm factors := by
  have sortedPartition :
      (sortedTerminatedTail factors).Perm
        (blockBearingFactors factors ++ markerOnlyFactors factors) := by
    exact List.Perm.append
      (sortedTerminatedFactors_perm (blockBearingFactors factors))
      (sortedTerminatedFactors_perm (markerOnlyFactors factors))
  exact sortedPartition.trans
    (blockBearingFactors_append_markerOnlyFactors_perm factors)

/-- Keep the first factor fixed and sort every subsequent factor. -/
def sortedTerminatedBlocks (letters : List Nat) :
    List (List Nat × Nat) :=
  match terminatedBlocks letters with
  | [] => []
  | first :: rest => first :: sortedTerminatedTail rest

/-- Sorting the complete squared factorization preserves the fixed first
factor and the final simple block. -/
theorem listDerivesSortSquaredTerminatedTail
    (letters : List Nat) :
    ListDerives
      (renderSquaredTerminatedBlocks
          (terminatedBlocks letters) ++
        terminatedFinalBlock letters)
      (renderSquaredTerminatedBlocks
          (sortedTerminatedBlocks letters) ++
        terminatedFinalBlock letters) := by
  cases shape : terminatedBlocks letters with
  | nil =>
      simpa [sortedTerminatedBlocks, shape] using
        (S5_107.ListDerives.refl
          (basis := basis) (terminatedFinalBlock letters))
  | cons first rest =>
      have sorted :=
        listDerivesSquaredTailPermutation
          (sortedTerminatedTail_perm rest).symm
          first (terminatedFinalBlock letters)
      simpa [sortedTerminatedBlocks, shape] using sorted

/-- Every word list derives to its locally squared factorization with every
noninitial simple-block-plus-successor factor deterministically sorted. -/
theorem listDerivesSquareAndSortTerminatedFactors
    (letters : List Nat) :
    ListDerives letters
      (renderSquaredTerminatedBlocks
          (sortedTerminatedBlocks letters) ++
        terminatedFinalBlock letters) :=
  (listDerivesSquareAllTerminatedMarkers letters).trans
    (listDerivesSortSquaredTerminatedTail letters)

/-! ## Extracting redundant factor copies into a pure marker tail -/

/-- Move one duplicate marker across an arbitrary middle to the far side of
a displayed final marker square. The empty-middle branch is the primitive
square crossing law; the nonempty branch is Lee's square-tail move. -/
theorem listDerivesExtractDuplicateAcrossFinalSquare
    (marker finalMarker : Nat) (middle suffix : List Nat) :
    ListDerives
      ([marker, marker] ++ middle ++
        [finalMarker, finalMarker] ++ suffix)
      ([marker] ++ middle ++
        [finalMarker, finalMarker, marker] ++ suffix) := by
  cases middle with
  | nil =>
      simpa [Word.singleton, Word.append, List.append_assoc] using
        (S5_107.ListDerives.ofWord <|
          derivesSquareCrossing
            (Word.singleton marker)
            (Word.singleton finalMarker)).append suffix
  | cons head tail =>
      simpa [listWordOfCons, Word.singleton, Word.append,
        List.append_assoc] using
          (S5_107.ListDerives.ofWord <|
            derivesLeeSquareTailMove
              (Word.singleton marker)
              (listWordOfCons head tail)
              (Word.singleton finalMarker)).append suffix

/-- For an arbitrary nonempty factor chain, retain one marker after every
simple block and extract all redundant copies into a pure marker tail. The
last marker remains first in that tail, followed by the earlier markers in
their factor order. -/
theorem listDerivesExtractFactorDuplicates
    (front : List (List Nat × Nat))
    (last : List Nat × Nat) (suffix : List Nat) :
    ListDerives
      (renderSquaredTerminatedBlocks (front ++ [last]) ++ suffix)
      (renderTerminatedBlocks (front ++ [last]) ++
        [last.2] ++ terminatedFactorMarkers front ++ suffix) := by
  induction front generalizing suffix with
  | nil =>
      rcases last with ⟨lastBlock, lastMarker⟩
      simpa [renderSquaredTerminatedBlocks, renderTerminatedBlocks,
        terminatedFactorMarkers, List.append_assoc] using
          (S5_107.ListDerives.refl
            (basis := basis)
            (lastBlock ++ [lastMarker, lastMarker] ++ suffix))
  | cons factor rest ih =>
      rcases factor with ⟨block, marker⟩
      rcases last with ⟨lastBlock, lastMarker⟩
      have tailStep :=
        ih suffix
      have tailStep' :=
        tailStep.prepend (block ++ [marker, marker])
      have extractStep :=
        (listDerivesExtractDuplicateAcrossFinalSquare
          marker lastMarker
          (renderTerminatedBlocks rest ++ lastBlock)
          (terminatedFactorMarkers rest ++ suffix)).prepend block
      refine S5_107.ListDerives.trans
        (middle :=
          block ++
            ([marker, marker] ++
              (renderTerminatedBlocks rest ++ lastBlock) ++
              [lastMarker, lastMarker] ++
              (terminatedFactorMarkers rest ++ suffix))) ?_ ?_
      · simpa [renderSquaredTerminatedBlocks,
          renderTerminatedBlocks, terminatedFactorMarkers,
          List.append_assoc] using tailStep'
      · simpa [renderTerminatedBlocks,
          terminatedFactorMarkers, List.append_assoc] using extractStep

/-! ## Legacy minimum-deficit canonical-tail route -/

/-- Retain the fixed first factor and every subsequent factor that carries a
nonempty simple block. Marker-only factors are represented by the power tail
instead. -/
def retainedSortedFactors (letters : List Nat) :
    List (List Nat × Nat) :=
  match sortedTerminatedBlocks letters with
  | [] => []
  | first :: rest =>
      first :: blockBearingFactors rest

/-- Markers already supplied by the retained successor factors. -/
def retainedSortedMarkers (letters : List Nat) : List Nat :=
  (retainedSortedFactors letters).map fun factor => factor.2

/-- Add only the copies still needed to bring every globally repeated label
to multiplicity two after the retained successor factors are rendered. -/
def renderMarkerDeficitTail
    (letters retainedMarkers : List Nat) : List Nat :=
  (S5_107.sortedMultipleLetters letters).flatMap fun marker =>
    List.replicate (2 - retainedMarkers.count marker) marker

/-- The exact deterministic list promised by the S5_402 structural
certificate: fixed first factor, sorted simple-successor factors, minimum
repeated-marker tail, and fixed final simple block. -/
def simpleSuccessorCanonicalList (letters : List Nat) : List Nat :=
  let retained := retainedSortedFactors letters
  renderTerminatedBlocks retained ++
    renderMarkerDeficitTail letters
      (retained.map fun factor => factor.2) ++
    terminatedFinalBlock letters

/-- Optional legacy route after duplicate extraction. It starts with a pure
marker tail and sorts and contracts that tail to the exact deficit prescribed
by the older minimum-deficit renderer. The square-inventory route does not
require a witness of this structure. -/
structure ExtractedMarkerTailNormalizationObligation : Prop where
  derive :
    ∀ (letters : List Nat)
      (front : List (List Nat × Nat))
      (last : List Nat × Nat),
      sortedTerminatedBlocks letters = front ++ [last] →
        ListDerives
          (renderTerminatedBlocks (front ++ [last]) ++
            [last.2] ++ terminatedFactorMarkers front ++
            terminatedFinalBlock letters)
          (simpleSuccessorCanonicalList letters)

/-- Optional integration boundary from the sorted local-square factorization
to the older minimum marker tail. The canonical square-inventory route closes
completeness independently of this structure. -/
structure CanonicalTailConsolidationObligation : Prop where
  derive :
    ∀ letters : List Nat,
      ListDerives
        (renderSquaredTerminatedBlocks
            (sortedTerminatedBlocks letters) ++
          terminatedFinalBlock letters)
        (simpleSuccessorCanonicalList letters)

end SemigroupBasis.CoRoots.S5_402
