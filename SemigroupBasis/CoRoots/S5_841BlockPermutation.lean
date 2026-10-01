import SemigroupBasis.CoRoots.S5_841QuadraticSwap
import SemigroupBasis.CoRoots.S5_841CompletenessBridge

namespace SemigroupBasis.CoRoots.S5_841

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## Target-directed quadratic block permutations -/

private def blockPrecedenceStep
    (x y : Nat) (state : PrecedenceState) (letter : Nat) :
    PrecedenceState :=
  if letter = x then
    match state with
    | .neither => .onlyX
    | .onlyX => .onlyX
    | .onlyY | .ordered | .violated => .violated
  else if letter = y then
    match state with
    | .neither => .onlyY
    | .onlyX => .ordered
    | .onlyY => .onlyY
    | .ordered => .ordered
    | .violated => .violated
  else state

private theorem precedenceScanList_eq_blockFold
    (letters : List Nat) (x y : Nat) :
    precedenceScanList letters x y =
      letters.foldl (blockPrecedenceStep x y) .neither := by
  rfl

private def blockPairFree
    (x y : Nat) (letters : List Nat) : Prop :=
  x ∉ letters ∧ y ∉ letters

private theorem blockPrecedenceFold_pairFree
    (x y : Nat) :
    ∀ (letters : List Nat) (state : PrecedenceState),
      blockPairFree x y letters →
      letters.foldl (blockPrecedenceStep x y) state = state
  | [], _, _ => rfl
  | letter :: rest, state, free => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact free.1 (List.Mem.head rest)
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact free.2 (List.Mem.head rest)
      have restFree : blockPairFree x y rest :=
        ⟨fun member => free.1 (List.Mem.tail letter member),
          fun member => free.2 (List.Mem.tail letter member)⟩
      simp only [List.foldl_cons]
      rw [show blockPrecedenceStep x y state letter = state by
        simp [blockPrecedenceStep, letterNeX, letterNeY]]
      exact blockPrecedenceFold_pairFree x y rest state restFree

private theorem blockPrecedenceFold_onlyX_of_y_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      y ∉ letters →
      letters.foldl (blockPrecedenceStep x y) .onlyX = .onlyX
  | [], _ => rfl
  | letter :: rest, absent => by
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : y ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show blockPrecedenceStep x y .onlyX letter = .onlyX by
        by_cases isX : letter = x
        · simp [blockPrecedenceStep, isX]
        · simp [blockPrecedenceStep, isX, letterNeY]]
      exact blockPrecedenceFold_onlyX_of_y_absent x y rest restAbsent

private theorem blockPrecedenceFold_ordered_of_x_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters →
      letters.foldl (blockPrecedenceStep x y) .ordered = .ordered
  | [], _ => rfl
  | letter :: rest, absent => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact absent (List.Mem.head rest)
      have restAbsent : x ∉ rest :=
        fun member => absent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      rw [show blockPrecedenceStep x y .ordered letter = .ordered by
        simp [blockPrecedenceStep, letterNeX]]
      exact blockPrecedenceFold_ordered_of_x_absent x y rest restAbsent

private theorem blockPrecedenceFold_violated
    (x y : Nat) :
    ∀ letters : List Nat,
      letters.foldl (blockPrecedenceStep x y) .violated = .violated
  | [] => rfl
  | letter :: rest => by
      simp only [List.foldl_cons]
      rw [show blockPrecedenceStep x y .violated letter = .violated by
        simp [blockPrecedenceStep]]
      exact blockPrecedenceFold_violated x y rest

private theorem blockPrecedenceFold_onlyX_of_x_mem_y_absent
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∈ letters →
      y ∉ letters →
      letters.foldl (blockPrecedenceStep x y) .neither = .onlyX
  | [], member, _ => by simp at member
  | letter :: rest, xMember, yAbsent => by
      have letterNeY : letter ≠ y := by
        intro equal
        subst letter
        exact yAbsent (List.Mem.head rest)
      have restYAbsent : y ∉ rest :=
        fun member => yAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · rw [show blockPrecedenceStep x y .neither letter = .onlyX by
          simp [blockPrecedenceStep, isX]]
        exact
          blockPrecedenceFold_onlyX_of_y_absent
            x y rest restYAbsent
      · have restXMember : x ∈ rest := by
          exact
            (List.mem_cons.mp xMember).resolve_left (Ne.symm isX)
        rw [show blockPrecedenceStep x y .neither letter = .neither by
          simp [blockPrecedenceStep, isX, letterNeY]]
        exact
          blockPrecedenceFold_onlyX_of_x_mem_y_absent
            x y rest restXMember restYAbsent

private theorem blockPrecedenceFold_ordered_of_x_absent_y_mem
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∉ letters →
      y ∈ letters →
      letters.foldl (blockPrecedenceStep x y) .onlyX = .ordered
  | [], _, member => by simp at member
  | letter :: rest, xAbsent, yMember => by
      have letterNeX : letter ≠ x := by
        intro equal
        subst letter
        exact xAbsent (List.Mem.head rest)
      have restXAbsent : x ∉ rest :=
        fun member => xAbsent (List.Mem.tail letter member)
      simp only [List.foldl_cons]
      by_cases isY : letter = y
      · rw [show blockPrecedenceStep x y .onlyX letter = .ordered by
          have yNeX : y ≠ x := fun equal =>
            letterNeX (isY.trans equal)
          simp [blockPrecedenceStep, isY, yNeX]]
        exact
          blockPrecedenceFold_ordered_of_x_absent
            x y rest restXAbsent
      · have restYMember : y ∈ rest := by
          exact
            (List.mem_cons.mp yMember).resolve_left (Ne.symm isY)
        rw [show blockPrecedenceStep x y .onlyX letter = .onlyX by
          simp [blockPrecedenceStep, letterNeX, isY]]
        exact
          blockPrecedenceFold_ordered_of_x_absent_y_mem
            x y rest restXAbsent restYMember

private theorem blockPrecedenceFold_violated_of_x_mem_from_onlyY
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∈ letters →
      letters.foldl (blockPrecedenceStep x y) .onlyY = .violated
  | [], member => by simp at member
  | letter :: rest, member => by
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · rw [show blockPrecedenceStep x y .onlyY letter = .violated by
          simp [blockPrecedenceStep, isX]]
        exact blockPrecedenceFold_violated x y rest
      · have restMember : x ∈ rest := by
          exact
            (List.mem_cons.mp member).resolve_left (Ne.symm isX)
        rw [show blockPrecedenceStep x y .onlyY letter = .onlyY by
          simp [blockPrecedenceStep, isX]]
        exact
          blockPrecedenceFold_violated_of_x_mem_from_onlyY
            x y rest restMember

private theorem blockPrecedenceFold_violated_of_x_mem_from_ordered
    (x y : Nat) :
    ∀ letters : List Nat,
      x ∈ letters →
      letters.foldl (blockPrecedenceStep x y) .ordered = .violated
  | [], member => by simp at member
  | letter :: rest, member => by
      simp only [List.foldl_cons]
      by_cases isX : letter = x
      · rw [show blockPrecedenceStep x y .ordered letter = .violated by
          simp [blockPrecedenceStep, isX]]
        exact blockPrecedenceFold_violated x y rest
      · have restMember : x ∈ rest := by
          exact
            (List.mem_cons.mp member).resolve_left (Ne.symm isX)
        rw [show blockPrecedenceStep x y .ordered letter = .ordered by
          simp [blockPrecedenceStep, isX]]
        exact
          blockPrecedenceFold_violated_of_x_mem_from_ordered
            x y rest restMember

private theorem precedenceScan_ordered_of_split
    {x y : Nat} (different : x ≠ y)
    (before after : List Nat)
    (xInBefore : x ∈ before)
    (yAbsentBefore : y ∉ before)
    (xAbsentAfter : x ∉ after)
    (yInAfter : y ∈ after) :
    precedenceScanList (before ++ x :: after) x y = .ordered := by
  rw [precedenceScanList_eq_blockFold]
  rw [List.foldl_append]
  rw [blockPrecedenceFold_onlyX_of_x_mem_y_absent
    x y before xInBefore yAbsentBefore]
  simp only [List.foldl_cons]
  rw [show blockPrecedenceStep x y .onlyX x = .onlyX by
    simp [blockPrecedenceStep]]
  exact
    blockPrecedenceFold_ordered_of_x_absent_y_mem
      x y after xAbsentAfter yInAfter

private theorem precedenceScan_violated_of_inversion
    {x y : Nat} (different : x ≠ y)
    (before after : List Nat)
    (yAbsentBefore : y ∉ before)
    (xInAfter : x ∈ after) :
    precedenceScanList (before ++ y :: after) x y = .violated := by
  rw [precedenceScanList_eq_blockFold]
  rw [List.foldl_append]
  by_cases xInBefore : x ∈ before
  · rw [blockPrecedenceFold_onlyX_of_x_mem_y_absent
      x y before xInBefore yAbsentBefore]
    simp only [List.foldl_cons]
    rw [show blockPrecedenceStep x y .onlyX y = .ordered by
      simp [blockPrecedenceStep, Ne.symm different]]
    exact
      blockPrecedenceFold_violated_of_x_mem_from_ordered
        x y after xInAfter
  · have free : blockPairFree x y before :=
      ⟨xInBefore, yAbsentBefore⟩
    rw [blockPrecedenceFold_pairFree x y before .neither free]
    simp only [List.foldl_cons]
    rw [show blockPrecedenceStep x y .neither y = .onlyY by
      simp [blockPrecedenceStep, Ne.symm different]]
    exact
      blockPrecedenceFold_violated_of_x_mem_from_onlyY
        x y after xInAfter

private theorem precedenceState_violated_ne_ordered :
    (PrecedenceState.violated : PrecedenceState) ≠ .ordered := by
  decide

private theorem listDerivesMoveMemberToFront
    (fixedPrefix targetTail sourcePost targetPost : List Nat)
    (selected : Nat) :
    ∀ (crossed source : List Nat),
      selected ∉ crossed →
      (crossed ++ source).Perm (selected :: targetTail) →
      (∀ letter, letter ∈ crossed ++ source →
        (fixedPrefix ++ crossed ++ source ++ sourcePost).count letter = 2) →
      (∀ letter, letter ∈ selected :: targetTail →
        (fixedPrefix ++ (selected :: targetTail) ++ targetPost).count letter =
          2) →
      M20ListEquivalent
        (fixedPrefix ++ crossed ++ source ++ sourcePost)
        (fixedPrefix ++ (selected :: targetTail) ++ targetPost) →
      S5_107.ListDerives basis
        (fixedPrefix ++ crossed ++ source ++ sourcePost)
        (fixedPrefix ++ crossed ++
          (selected :: source.erase selected) ++ sourcePost)
  | crossed, [], selectedAbsent, permutation, _, _, _ => by
      have selectedInCrossed : selected ∈ crossed :=
        by simpa using
          permutation.mem_iff.mpr (List.Mem.head targetTail)
      exact False.elim (selectedAbsent selectedInCrossed)
  | crossed, head :: tail, selectedAbsent, permutation,
      sourceQuadratic, targetQuadratic, equivalent => by
      by_cases equal : head = selected
      · subst head
        simpa [List.append_assoc] using
          S5_107.ListDerives.refl (basis := basis)
            (fixedPrefix ++ crossed ++ (selected :: tail) ++ sourcePost)
      · have selectedInBlock :
            selected ∈ crossed ++ head :: tail :=
          permutation.mem_iff.mpr (List.Mem.head targetTail)
        have selectedInSource : selected ∈ head :: tail :=
          (List.mem_append.mp selectedInBlock).resolve_left selectedAbsent
        have selectedInTail : selected ∈ tail := by
          simpa [Ne.symm equal] using selectedInSource
        have nextSelectedAbsent : selected ∉ crossed ++ [head] := by
          simp [selectedAbsent, Ne.symm equal]
        have nextPermutation :
            ((crossed ++ [head]) ++ tail).Perm
              (selected :: targetTail) := by
          simpa [List.append_assoc] using permutation
        have nextSourceQuadratic :
            ∀ letter, letter ∈ (crossed ++ [head]) ++ tail →
              (fixedPrefix ++ (crossed ++ [head]) ++ tail ++ sourcePost).count
                  letter =
                2 := by
          intro letter member
          have oldMember : letter ∈ crossed ++ head :: tail := by
            simpa [List.append_assoc] using member
          simpa [List.append_assoc] using
            sourceQuadratic letter oldMember
        have nextEquivalent :
            M20ListEquivalent
              (fixedPrefix ++ (crossed ++ [head]) ++ tail ++ sourcePost)
              (fixedPrefix ++ (selected :: targetTail) ++ targetPost) := by
          simpa [List.append_assoc] using equivalent
        have moveTail :=
          listDerivesMoveMemberToFront
            fixedPrefix targetTail sourcePost targetPost selected
            (crossed ++ [head]) tail nextSelectedAbsent
            nextPermutation nextSourceQuadratic targetQuadratic
            nextEquivalent
        have movedEquivalent :
            M20ListEquivalent
              ((fixedPrefix ++ crossed) ++
                (head :: selected ::
                  (tail.erase selected ++ sourcePost)))
              (fixedPrefix ++ (selected :: targetTail) ++ targetPost) := by
          have moveSound := M20ListEquivalent.of_derives moveTail
          exact (by
            simpa [List.append_assoc] using
              moveSound.symm.trans nextEquivalent)
        have tailExpose :
            tail.Perm (selected :: tail.erase selected) :=
          List.perm_cons_erase selectedInTail
        have sourceExpose :
            (head :: tail).Perm
              (head :: selected :: tail.erase selected) :=
          List.Perm.cons head tailExpose
        have fullExpose :
            (fixedPrefix ++ crossed ++ (head :: tail) ++ sourcePost).Perm
              ((fixedPrefix ++ crossed) ++
                (head :: selected ::
                  (tail.erase selected ++ sourcePost))) := by
          simpa [List.append_assoc] using
            List.Perm.append
              (List.Perm.append
                (List.Perm.refl (fixedPrefix ++ crossed)) sourceExpose)
              (List.Perm.refl sourcePost)
        have headQuadratic :
            (((fixedPrefix ++ crossed) ++
              (head :: selected ::
                (tail.erase selected ++ sourcePost))).count
                head) =
              2 := by
          calc
            (((fixedPrefix ++ crossed) ++
                (head :: selected ::
                  (tail.erase selected ++ sourcePost))).count
                  head) =
                (((fixedPrefix ++ crossed) ++
                  (head :: tail) ++ sourcePost).count head) := by
              exact (fullExpose.count head).symm
            _ = 2 := by
              simpa [List.append_assoc] using
                sourceQuadratic head (by simp)
        have selectedQuadratic :
            (((fixedPrefix ++ crossed) ++
              (head :: selected ::
                (tail.erase selected ++ sourcePost))).count
                selected) =
              2 := by
          calc
            (((fixedPrefix ++ crossed) ++
                (head :: selected ::
                  (tail.erase selected ++ sourcePost))).count
                  selected) =
                (((fixedPrefix ++ crossed) ++
                  (head :: tail) ++ sourcePost).count selected) := by
              exact (fullExpose.count selected).symm
            _ = 2 := by
              simpa [List.append_assoc] using
                sourceQuadratic selected (by
                  simp [selectedInTail])
        have headInTargetTail : head ∈ targetTail := by
          have headInTarget : head ∈ selected :: targetTail :=
            permutation.mem_iff.mp (by simp)
          simpa [equal] using headInTarget
        have position :
            QuadraticSwapPosition head selected
              (fixedPrefix ++ crossed)
              (tail.erase selected ++ sourcePost) :=
          uniqueSeparatorAdjacentQuadraticPosition_of_counts
            equal headQuadratic selectedQuadratic
        have swap :
            S5_107.ListDerives basis
              ((fixedPrefix ++ crossed) ++
                (head :: selected ::
                  (tail.erase selected ++ sourcePost)))
              ((fixedPrefix ++ crossed) ++
                (selected :: head ::
                  (tail.erase selected ++ sourcePost))) := by
          cases position with
          | futureXY middle between after postShape =>
              rw [postShape]
              simpa [List.append_assoc] using
                (listDerivesL6 head selected middle between).context
                  (fixedPrefix ++ crossed) after
          | futureYX middle between after postShape =>
              rw [postShape]
              simpa [List.append_assoc] using
                (listDerivesL6 selected head middle between).symm.context
                  (fixedPrefix ++ crossed) after
          | straddleXY before left right after preShape postShape =>
              have headCount := headQuadratic
              have selectedCount := selectedQuadratic
              rw [preShape, postShape] at headCount selectedCount
              simp only [List.count_append, List.count_cons] at headCount selectedCount
              simp [equal, Ne.symm equal] at headCount selectedCount
              have headInCurrentPrefix :
                  head ∈ fixedPrefix ++ crossed := by
                rw [preShape]
                simp
              have selectedPrefixCount :
                  (fixedPrefix ++ crossed).count selected = 0 := by
                rw [preShape]
                simp only [List.count_append, List.count_cons]
                simp [equal, Ne.symm equal]
                omega
              have selectedAbsentCurrentPrefix :
                  selected ∉ fixedPrefix ++ crossed :=
                List.count_eq_zero.mp selectedPrefixCount
              have headRestCount :
                  (tail.erase selected ++ sourcePost).count head = 0 := by
                rw [postShape]
                simp only [List.count_append, List.count_cons]
                simp [equal, Ne.symm equal]
                omega
              have headAbsentRest :
                  head ∉ tail.erase selected ++ sourcePost :=
                List.count_eq_zero.mp headRestCount
              have headAbsentSourceAfter :
                  head ∉ selected ::
                    (tail.erase selected ++ sourcePost) := by
                simp [equal, headAbsentRest]
              have selectedAbsentFixedPrefix :
                  selected ∉ fixedPrefix := by
                intro member
                exact selectedAbsentCurrentPrefix
                  (List.mem_append_left crossed member)
              have headInTargetAfter :
                  head ∈ targetTail ++ targetPost :=
                List.mem_append_left targetPost headInTargetTail
              have sourcePrecedence :
                  CompletePrecedenceList
                    ((fixedPrefix ++ crossed) ++
                      (head :: selected ::
                        (tail.erase selected ++ sourcePost)))
                    head selected :=
                ⟨equal, by
                  exact
                    precedenceScan_ordered_of_split equal
                      (fixedPrefix ++ crossed)
                      (selected ::
                        (tail.erase selected ++ sourcePost))
                      headInCurrentPrefix selectedAbsentCurrentPrefix
                      headAbsentSourceAfter (by simp)⟩
              have targetNotPrecedence :
                  ¬ CompletePrecedenceList
                    (fixedPrefix ++ (selected :: targetTail) ++ targetPost)
                    head selected := by
                intro targetPrecedence
                have targetScan :
                    precedenceScanList
                        (fixedPrefix ++ (selected :: targetTail) ++ targetPost)
                        head selected =
                      .violated := by
                  simpa [List.append_assoc] using
                    precedenceScan_violated_of_inversion equal
                      fixedPrefix (targetTail ++ targetPost)
                      selectedAbsentFixedPrefix headInTargetAfter
                exact precedenceState_violated_ne_ordered
                  (targetScan.symm.trans targetPrecedence.2)
              have preserved :=
                m20ListEquivalent_completePrecedenceList
                  movedEquivalent head selected
              exact False.elim
                (targetNotPrecedence (preserved.mp sourcePrecedence))
          | straddleYX before left right after preShape postShape =>
              have headCount := headQuadratic
              have selectedCount := selectedQuadratic
              rw [preShape, postShape] at headCount selectedCount
              simp only [List.count_append, List.count_cons] at headCount selectedCount
              simp [equal, Ne.symm equal] at headCount selectedCount
              have headPrefixCount :
                  (fixedPrefix ++ crossed).count head = 0 := by
                rw [preShape]
                simp only [List.count_append, List.count_cons]
                simp [equal, Ne.symm equal]
                omega
              have headAbsentCurrentPrefix :
                  head ∉ fixedPrefix ++ crossed :=
                List.count_eq_zero.mp headPrefixCount
              have headAbsentFixedPrefix : head ∉ fixedPrefix := by
                intro member
                exact headAbsentCurrentPrefix
                  (List.mem_append_left crossed member)
              have selectedInCurrentPrefix :
                  selected ∈ fixedPrefix ++ crossed := by
                rw [preShape]
                simp
              have selectedInFixedPrefix : selected ∈ fixedPrefix := by
                rcases List.mem_append.mp selectedInCurrentPrefix with
                  inFixed | inCrossed
                · exact inFixed
                · exact False.elim (selectedAbsent inCrossed)
              have fixedSelectedPositive :
                  1 ≤ fixedPrefix.count selected :=
                List.one_le_count_iff.mpr selectedInFixedPrefix
              have targetSelectedCount :=
                targetQuadratic selected (by simp)
              simp only [List.count_append, List.count_cons_self] at targetSelectedCount
              have selectedTargetAfterCount :
                  (targetTail ++ targetPost).count selected = 0 := by
                simp only [List.count_append]
                omega
              have selectedAbsentTargetAfter :
                  selected ∉ targetTail ++ targetPost :=
                List.count_eq_zero.mp selectedTargetAfterCount
              have headInTargetAfter :
                  head ∈ targetTail ++ targetPost :=
                List.mem_append_left targetPost headInTargetTail
              have sourceNotPrecedence :
                  ¬ CompletePrecedenceList
                    ((fixedPrefix ++ crossed) ++
                      (head :: selected ::
                        (tail.erase selected ++ sourcePost)))
                    selected head := by
                intro sourcePrecedence
                have sourceScan :
                    precedenceScanList
                        ((fixedPrefix ++ crossed) ++
                          (head :: selected ::
                            (tail.erase selected ++ sourcePost)))
                        selected head =
                      .violated := by
                  exact
                    precedenceScan_violated_of_inversion
                      (Ne.symm equal) (fixedPrefix ++ crossed)
                      (selected ::
                        (tail.erase selected ++ sourcePost))
                      headAbsentCurrentPrefix (by simp)
                exact precedenceState_violated_ne_ordered
                  (sourceScan.symm.trans sourcePrecedence.2)
              have targetPrecedence :
                  CompletePrecedenceList
                    (fixedPrefix ++ (selected :: targetTail) ++ targetPost)
                    selected head :=
                ⟨Ne.symm equal, by
                  simpa [List.append_assoc] using
                    precedenceScan_ordered_of_split
                      (Ne.symm equal) fixedPrefix
                      (targetTail ++ targetPost)
                      selectedInFixedPrefix headAbsentFixedPrefix
                      selectedAbsentTargetAfter headInTargetAfter⟩
              have preserved :=
                m20ListEquivalent_completePrecedenceList
                  movedEquivalent selected head
              exact False.elim
                (sourceNotPrecedence (preserved.mpr targetPrecedence))
          | pastXY before left middle preShape =>
              rw [preShape]
              simpa [List.append_assoc] using
                (listDerivesL8 head selected left middle).context
                  before (tail.erase selected ++ sourcePost)
          | pastYX before left middle preShape =>
              rw [preShape]
              simpa [List.append_assoc] using
                (listDerivesL8 selected head left middle).symm.context
                  before (tail.erase selected ++ sourcePost)
        have complete := moveTail.trans <| by
          simpa [List.append_assoc] using swap
        simpa [equal, List.append_assoc] using complete
termination_by
  _ source => source.length

/-- Target-directed quadratic block permutation. The semantic target may
have a different suffix; the derivation changes only the source block and
retains `sourcePost`. Exact quadratic counts are required in both complete
contexts so repeated labels remain controlled during target selection. -/
theorem listDerivesQuadraticBlockPermutationAgainst :
    ∀ (target source pre sourcePost targetPost : List Nat),
      source.Perm target →
      (∀ letter, letter ∈ source →
        (pre ++ source ++ sourcePost).count letter = 2) →
      (∀ letter, letter ∈ target →
        (pre ++ target ++ targetPost).count letter = 2) →
      M20ListEquivalent
        (pre ++ source ++ sourcePost)
        (pre ++ target ++ targetPost) →
      S5_107.ListDerives basis
        (pre ++ source ++ sourcePost)
        (pre ++ target ++ sourcePost)
  | [], source, pre, sourcePost, _, permutation, _, _, _ => by
      have sourceEmpty : source = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using permutation.length_eq
      subst source
      simpa [List.append_assoc] using
        S5_107.ListDerives.refl (basis := basis) (pre ++ sourcePost)
  | selected :: targetTail, source, pre, sourcePost, targetPost,
      permutation, sourceQuadratic, targetQuadratic, equivalent => by
      have moveRaw :=
        listDerivesMoveMemberToFront
          pre targetTail sourcePost targetPost selected [] source
          (by simp) (by simpa using permutation)
          (by simpa [List.append_assoc] using sourceQuadratic)
          targetQuadratic (by simpa [List.append_assoc] using equivalent)
      have move :
          S5_107.ListDerives basis
            (pre ++ source ++ sourcePost)
            ((pre ++ [selected]) ++ source.erase selected ++ sourcePost) := by
        simpa [List.append_assoc] using moveRaw
      have selectedInSource : selected ∈ source :=
        permutation.mem_iff.mpr (by simp)
      have sourceExpose :
          source.Perm (selected :: source.erase selected) :=
        List.perm_cons_erase selectedInSource
      have erasedPermutation :
          (source.erase selected).Perm targetTail := by
        simpa using permutation.erase selected
      have fullExpose :
          (pre ++ source ++ sourcePost).Perm
            ((pre ++ [selected]) ++ source.erase selected ++ sourcePost) := by
        simpa [List.append_assoc] using
          List.Perm.append
            (List.Perm.append (List.Perm.refl pre) sourceExpose)
            (List.Perm.refl sourcePost)
      have erasedSourceQuadratic :
          ∀ letter, letter ∈ source.erase selected →
            ((pre ++ [selected]) ++ source.erase selected ++ sourcePost).count
                letter =
              2 := by
        intro letter erasedMember
        have sourceMember : letter ∈ source :=
          List.mem_of_mem_erase erasedMember
        calc
          ((pre ++ [selected]) ++ source.erase selected ++ sourcePost).count
              letter =
              (pre ++ source ++ sourcePost).count letter := by
            exact (fullExpose.count letter).symm
          _ = 2 := sourceQuadratic letter sourceMember
      have erasedTargetQuadratic :
          ∀ letter, letter ∈ targetTail →
            ((pre ++ [selected]) ++ targetTail ++ targetPost).count letter =
              2 := by
        intro letter member
        simpa [List.append_assoc] using
          targetQuadratic letter (List.Mem.tail selected member)
      have exposedEquivalent :
          M20ListEquivalent
            ((pre ++ [selected]) ++ source.erase selected ++ sourcePost)
            ((pre ++ [selected]) ++ targetTail ++ targetPost) := by
        have moveSound := M20ListEquivalent.of_derives move
        have exposedToTarget := moveSound.symm.trans equivalent
        simpa [List.append_assoc] using exposedToTarget
      have rest :=
        listDerivesQuadraticBlockPermutationAgainst
          targetTail (source.erase selected) (pre ++ [selected])
          sourcePost targetPost erasedPermutation
          erasedSourceQuadratic erasedTargetQuadratic exposedEquivalent
      exact move.trans <| by
        simpa [List.append_assoc] using rest
termination_by
  target _ _ _ _ => target.length

/-- Same-suffix form used by the six-case block-permutation obligation. -/
theorem listDerivesQuadraticBlockPermutation
    (target source pre post : List Nat)
    (permutation : source.Perm target)
    (quadratic :
      ∀ letter, letter ∈ source →
        (pre ++ source ++ post).count letter = 2)
    (equivalent :
      M20ListEquivalent
        (pre ++ source ++ post)
        (pre ++ target ++ post)) :
    S5_107.ListDerives basis
      (pre ++ source ++ post)
      (pre ++ target ++ post) := by
  have contextPermutation :
      (pre ++ source ++ post).Perm (pre ++ target ++ post) :=
    List.Perm.append
      (List.Perm.append (List.Perm.refl pre) permutation)
      (List.Perm.refl post)
  have targetQuadratic :
      ∀ letter, letter ∈ target →
        (pre ++ target ++ post).count letter = 2 := by
    intro letter targetMember
    have sourceMember : letter ∈ source :=
      permutation.mem_iff.mpr targetMember
    calc
      (pre ++ target ++ post).count letter =
          (pre ++ source ++ post).count letter :=
        (contextPermutation.count letter).symm
      _ = 2 := quadratic letter sourceMember
  exact
    listDerivesQuadraticBlockPermutationAgainst
      target source pre post post permutation quadratic targetQuadratic
      equivalent

/-- The local six-position swap and target-directed selection sort give the
complete quadratic block-permutation witness required by the next bridge. -/
theorem quadraticBlockPermutationSixCase :
    QuadraticBlockPermutationSixCaseObligation :=
  { adjacent := listDerivesAdjacentQuadraticSwap
    blockPermutation := listDerivesQuadraticBlockPermutation }

end SemigroupBasis.CoRoots.S5_841
