import SemigroupBasis.CoRoots.Order6SporadicSection11CanonicalExistence

namespace SemigroupBasis.CoRoots.Order6SporadicSection11

open SemigroupBasis
open SemigroupBasis.Examples

private theorem mem_firstOccurrenceSequenceList_iff
    (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ firstOccurrenceSequenceList letters ↔ selected ∈ letters
  | [] => by
      simp [firstOccurrenceSequenceList, firstOccurrenceSequence]
  | letter :: rest => by
      by_cases equal : selected = letter
      · subst letter
        simp [firstOccurrenceSequenceList, firstOccurrenceSequence]
      · simp [firstOccurrenceSequenceList, firstOccurrenceSequence, equal]
        exact mem_firstOccurrenceSequenceList_iff selected rest

private theorem map_value_eq_of_map_eq
    (leftValue rightValue : Nat → Nat) :
    ∀ {letters : List Nat},
      letters.map leftValue = letters.map rightValue →
      ∀ selected, selected ∈ letters →
        leftValue selected = rightValue selected
  | [], _, selected, member => by
      simp at member
  | letter :: rest, equal, selected, member => by
      have headEqual : leftValue letter = rightValue letter :=
        (List.cons.inj equal).1
      have tailEqual : rest.map leftValue = rest.map rightValue :=
        (List.cons.inj equal).2
      rcases List.mem_cons.mp member with selectedEqual | selectedMem
      · subst selected
        exact headEqual
      · exact map_value_eq_of_map_eq
          leftValue rightValue tailEqual selected selectedMem

/-- Equality of the aligned finite signature yields capped multiplicity
equality for every variable, including variables outside the support. -/
theorem capped_count_eq_of_signature_eq
    {left right : Word Nat}
    (same : signature left = signature right)
    (selected : Nat) :
    Nat.min (left.toList.count selected) 3 =
      Nat.min (right.toList.count selected) 3 := by
  have order :
      firstOccurrenceSequenceList left.toList =
        firstOccurrenceSequenceList right.toList :=
    congrArg Signature.firstOccurrences same
  have counts :
      cappedCountsList left.toList = cappedCountsList right.toList :=
    congrArg Signature.cappedCounts same
  change
    (firstOccurrenceSequenceList left.toList).map
        (fun letter => Nat.min (left.toList.count letter) 3) =
      (firstOccurrenceSequenceList right.toList).map
        (fun letter => Nat.min (right.toList.count letter) 3) at counts
  rw [← order] at counts
  by_cases leftMem : selected ∈ left.toList
  · have selectedInOrder :
        selected ∈ firstOccurrenceSequenceList left.toList :=
      (mem_firstOccurrenceSequenceList_iff selected left.toList).2 leftMem
    exact map_value_eq_of_map_eq
      (fun letter => Nat.min (left.toList.count letter) 3)
      (fun letter => Nat.min (right.toList.count letter) 3)
      counts selected selectedInOrder
  · have rightNotMem : selected ∉ right.toList := by
      intro rightMem
      have rightInOrder :
          selected ∈ firstOccurrenceSequenceList right.toList :=
        (mem_firstOccurrenceSequenceList_iff selected right.toList).2 rightMem
      have leftInOrder :
          selected ∈ firstOccurrenceSequenceList left.toList := by
        rw [order]
        exact rightInOrder
      exact leftMem <|
        (mem_firstOccurrenceSequenceList_iff selected left.toList).1
          leftInOrder
    simp [List.count_eq_zero.mpr leftMem,
      List.count_eq_zero.mpr rightNotMem]

private theorem final_wordOfPrefixFinal
    (stem : List Nat) (final : Nat) :
    (wordOfPrefixFinal stem final).final = final := by
  induction stem with
  | nil => rfl
  | cons letter rest induction =>
      rw [wordOfPrefixFinal_cons, Word.final_append]
      exact induction

theorem terminalStatus_wordOfPrefixFinal_of_not_mem
    {stem : List Nat} {final : Nat} (notMem : final ∉ stem) :
    (signature (wordOfPrefixFinal stem final)).terminal =
      .simple final := by
  change terminalStatusOfOption
      (SemigroupBasis.CoRoots.S5_345.simpleFinalVariable
        (wordOfPrefixFinal stem final)) = .simple final
  simp [SemigroupBasis.CoRoots.S5_345.simpleFinalVariable,
    toList_wordOfPrefixFinal, final_wordOfPrefixFinal,
    List.count_eq_zero.mpr notMem, terminalStatusOfOption]

theorem terminalStatus_wordOfPrefixFinal_of_mem
    {stem : List Nat} {final : Nat} (member : final ∈ stem) :
    (signature (wordOfPrefixFinal stem final)).terminal =
      .nonsimple := by
  have positive : 0 < stem.count final :=
    List.count_pos_iff.mpr member
  change terminalStatusOfOption
      (SemigroupBasis.CoRoots.S5_345.simpleFinalVariable
        (wordOfPrefixFinal stem final)) = .nonsimple
  have nonzero : stem.count final ≠ 0 := Nat.ne_of_gt positive
  simp [SemigroupBasis.CoRoots.S5_345.simpleFinalVariable,
    toList_wordOfPrefixFinal, final_wordOfPrefixFinal,
    terminalStatusOfOption, nonzero]

private def removeLetter
    (selected : Nat) (letters : List Nat) : List Nat :=
  letters.filter (fun letter => decide (letter ≠ selected))

private theorem firstOccurrenceSequence_cons_eq
    (letter : Nat) (rest : List Nat) :
    firstOccurrenceSequence (letter :: rest) =
      letter :: removeLetter letter (firstOccurrenceSequence rest) :=
  rfl

private theorem removeLetter_append
    (selected : Nat) (left right : List Nat) :
    removeLetter selected (left ++ right) =
      removeLetter selected left ++ removeLetter selected right := by
  simp [removeLetter, List.filter_append]

private theorem firstOccurrenceSequence_append_final
    (final : Nat) :
    ∀ before : List Nat,
      firstOccurrenceSequence (before ++ [final]) =
        if final ∈ before then
          firstOccurrenceSequence before
        else
          firstOccurrenceSequence before ++ [final]
  | [] => by
      simp [firstOccurrenceSequence]
  | letter :: rest => by
      have induction := firstOccurrenceSequence_append_final final rest
      by_cases equal : letter = final
      · subst letter
        rw [List.cons_append, firstOccurrenceSequence_cons_eq, induction]
        simp only [List.mem_cons, true_or, if_true]
        by_cases present : final ∈ rest
        · rw [if_pos present]
          exact (firstOccurrenceSequence_cons_eq final rest).symm
        · rw [if_neg present, removeLetter_append]
          simpa [removeLetter] using
            (firstOccurrenceSequence_cons_eq final rest).symm
      · have reverse : final ≠ letter := Ne.symm equal
        rw [List.cons_append, firstOccurrenceSequence_cons_eq, induction]
        by_cases present : final ∈ rest
        · have fullPresent : final ∈ letter :: rest :=
            List.Mem.tail letter present
          rw [if_pos present, if_pos fullPresent]
          exact (firstOccurrenceSequence_cons_eq letter rest).symm
        · have fullAbsent : final ∉ letter :: rest := by
            simp [reverse, present]
          rw [if_neg present, if_neg fullAbsent, removeLetter_append]
          have keepFinal : removeLetter letter [final] = [final] := by
            simp [removeLetter, reverse]
          rw [keepFinal]
          simp [firstOccurrenceSequence_cons_eq]

private def ListBefore (first second : Nat) : List Nat → Prop
  | [] => False
  | letter :: rest =>
      (letter = first ∧ second ∈ rest) ∨ ListBefore first second rest

private theorem ListBefore.left_mem
    {first second : Nat} :
    ∀ {letters : List Nat}, ListBefore first second letters → first ∈ letters
  | [], before => by
      simp [ListBefore] at before
  | letter :: rest, before => by
      rcases before with head | tail
      · exact List.mem_cons.mpr (Or.inl head.1.symm)
      · exact List.mem_cons_of_mem letter (ListBefore.left_mem tail)

private theorem ListBefore.right_mem
    {first second : Nat} :
    ∀ {letters : List Nat}, ListBefore first second letters → second ∈ letters
  | [], before => by
      simp [ListBefore] at before
  | letter :: rest, before => by
      rcases before with head | tail
      · exact List.mem_cons_of_mem letter head.2
      · exact List.mem_cons_of_mem letter (ListBefore.right_mem tail)

private theorem ListBefore.filter_ne
    {first second removed : Nat}
    (firstNeRemoved : first ≠ removed)
    (secondNeRemoved : second ≠ removed) :
    ∀ {letters : List Nat},
      ListBefore first second letters →
        ListBefore first second
          (letters.filter (fun letter => decide (letter ≠ removed)))
  | [], before => by
      simp [ListBefore] at before
  | letter :: rest, before => by
      by_cases equal : letter = removed
      · subst letter
        rcases before with head | tail
        · exact False.elim (firstNeRemoved head.1.symm)
        · simpa [ListBefore] using
            ListBefore.filter_ne firstNeRemoved secondNeRemoved tail
      · have result :
            (letter = first ∧
                second ∈ rest.filter
                  (fun value => decide (value ≠ removed))) ∨
              ListBefore first second
                (rest.filter
                  (fun value => decide (value ≠ removed))) := by
          rcases before with head | tail
          · exact Or.inl ⟨head.1, List.mem_filter.mpr ⟨head.2, by
                simp [secondNeRemoved]⟩⟩
          · exact Or.inr <|
              ListBefore.filter_ne firstNeRemoved secondNeRemoved tail
        simpa [ListBefore, equal] using result

private theorem ListBefore.asymm_of_nodup
    {first second : Nat} :
    ∀ {letters : List Nat},
      letters.Nodup → ListBefore first second letters →
        ¬ ListBefore second first letters
  | [], _, before => by
      simp [ListBefore] at before
  | letter :: rest, nodup, forward => by
      have data := List.nodup_cons.mp nodup
      intro reverse
      rcases forward with forwardHead | forwardTail
      · rcases reverse with reverseHead | reverseTail
        · have firstMem : first ∈ rest := reverseHead.2
          exact data.1 (by simpa [forwardHead.1] using firstMem)
        · exact data.1 (by
            simpa [forwardHead.1] using ListBefore.right_mem reverseTail)
      · rcases reverse with reverseHead | reverseTail
        · exact data.1 (by
            simpa [reverseHead.1] using ListBefore.right_mem forwardTail)
        · exact ListBefore.asymm_of_nodup
            data.2 forwardTail reverseTail

private theorem ListBefore.firstOccurrence_of_prefix
    {selected final : Nat}
    (different : selected ≠ final) :
    ∀ (before after : List Nat),
      final ∉ before → selected ∈ before →
        ListBefore selected final
          (firstOccurrenceSequence (before ++ [final] ++ after))
  | [], _, _, selectedMem => by
      simp at selectedMem
  | letter :: rest, after, finalNotMem, selectedMem => by
      have finalNotRest : final ∉ rest := by
        exact fun member => finalNotMem (List.Mem.tail letter member)
      have finalNeLetter : final ≠ letter := by
        intro equal
        subst letter
        exact finalNotMem (List.Mem.head rest)
      by_cases selectedEq : selected = letter
      · subst selected
        have finalInSequence :
            final ∈ firstOccurrenceSequence (rest ++ [final] ++ after) :=
          (mem_firstOccurrenceSequenceList_iff final
            (rest ++ [final] ++ after)).2 (by simp)
        have finalInFilter :
            final ∈
              (firstOccurrenceSequence (rest ++ [final] ++ after)).filter
                (fun value => decide (value ≠ letter)) :=
          List.mem_filter.mpr ⟨finalInSequence, by simp [finalNeLetter]⟩
        exact Or.inl ⟨rfl, finalInFilter⟩
      · have selectedMemRest : selected ∈ rest := by
          simpa [selectedEq] using selectedMem
        have inside :=
          ListBefore.firstOccurrence_of_prefix different
            rest after finalNotRest selectedMemRest
        exact Or.inr <|
          ListBefore.filter_ne selectedEq finalNeLetter inside

private theorem normal_count_le_three
    {letters : List Nat}
    (normal : S5_530.S5_530Normal letters)
    (tested : Nat) :
    letters.count tested ≤ 3 := by
  induction normal with
  | nil => simp
  | single letter rest _ notMem induction =>
      by_cases equal : tested = letter
      · subst tested
        simp [List.count_eq_zero.mpr notMem]
      · simpa [List.count_cons_of_ne (Ne.symm equal)] using induction
  | double letter rest _ notMem induction =>
      by_cases equal : tested = letter
      · subst tested
        simp [List.count_eq_zero.mpr notMem]
      · simpa [List.count_cons_of_ne (Ne.symm equal)] using induction
  | triple letter rest _ notMem induction =>
      by_cases equal : tested = letter
      · subst tested
        simp [List.count_eq_zero.mpr notMem]
      · simpa [List.count_cons_of_ne (Ne.symm equal)] using induction

private theorem wordOfPrefixFinal_count_le_three
    {stem : List Nat} {final tested : Nat}
    (normal : S5_530.S5_530Normal stem)
    (finalBound : stem.count final ≤ 2) :
    (wordOfPrefixFinal stem final).toList.count tested ≤ 3 := by
  rw [toList_wordOfPrefixFinal, List.count_append]
  by_cases equal : tested = final
  · subst tested
    simp
    omega
  · have bound := normal_count_le_three normal tested
    simpa [equal, Ne.symm equal] using bound

/-- Canonical protected words with equal signatures are equal once their final
owners agree. -/
theorem canonicalProtectedWord_eq_of_signature_eq_of_final_eq
    {left right : Word Nat}
    (leftCanonical : CanonicalProtectedWord left)
    (rightCanonical : CanonicalProtectedWord right)
    (same : signature left = signature right)
    (sameFinal : left.final = right.final) :
    left = right := by
  rcases leftCanonical with
    ⟨leftPrefix, leftFinal, leftEq,
      leftNormal, leftFinalBound, leftOwner⟩
  rcases rightCanonical with
    ⟨rightPrefix, rightFinal, rightEq,
      rightNormal, rightFinalBound, rightOwner⟩
  rw [leftEq, rightEq, final_wordOfPrefixFinal,
    final_wordOfPrefixFinal] at sameFinal
  subst rightFinal
  rw [leftEq, rightEq] at same ⊢
  have sameTerminal := congrArg Signature.terminal same
  by_cases leftFinalMem : leftFinal ∈ leftPrefix
  · have rightFinalMem : leftFinal ∈ rightPrefix := by
      apply Decidable.byContradiction
      intro rightFinalNotMem
      rw [terminalStatus_wordOfPrefixFinal_of_mem leftFinalMem,
        terminalStatus_wordOfPrefixFinal_of_not_mem rightFinalNotMem] at sameTerminal
      cases sameTerminal
    have order :
        firstOccurrenceSequence leftPrefix =
          firstOccurrenceSequence rightPrefix := by
      have fullOrder :
          firstOccurrenceSequence (leftPrefix ++ [leftFinal]) =
            firstOccurrenceSequence (rightPrefix ++ [leftFinal]) := by
        simpa [signature, firstOccurrenceSequenceList,
          toList_wordOfPrefixFinal] using
            congrArg Signature.firstOccurrences same
      simpa [firstOccurrenceSequence_append_final,
        leftFinalMem, rightFinalMem] using fullOrder
    have fullCounts :
        ∀ tested,
          (wordOfPrefixFinal leftPrefix leftFinal).toList.count tested =
            (wordOfPrefixFinal rightPrefix leftFinal).toList.count tested := by
      intro tested
      have capped := capped_count_eq_of_signature_eq same tested
      have leftBound :=
        wordOfPrefixFinal_count_le_three leftNormal leftFinalBound
          (tested := tested)
      have rightBound :=
        wordOfPrefixFinal_count_le_three rightNormal rightFinalBound
          (tested := tested)
      simpa [Nat.min_eq_left leftBound,
        Nat.min_eq_left rightBound] using capped
    have prefixCounts :
        ∀ tested, leftPrefix.count tested = rightPrefix.count tested := by
      intro tested
      have equal := fullCounts tested
      rw [toList_wordOfPrefixFinal, toList_wordOfPrefixFinal,
        List.count_append, List.count_append] at equal
      by_cases testedFinal : tested = leftFinal
      · subst tested
        simp at equal
        omega
      · simpa [testedFinal] using equal
    have prefixEq :=
      S5_530.s5_530Normal_eq_of_invariants
        leftNormal rightNormal order prefixCounts
    rw [prefixEq]
  · have rightFinalNotMem : leftFinal ∉ rightPrefix := by
      intro rightFinalMem
      rw [terminalStatus_wordOfPrefixFinal_of_not_mem leftFinalMem,
        terminalStatus_wordOfPrefixFinal_of_mem rightFinalMem] at sameTerminal
      cases sameTerminal
    have orderWithFinal :
        firstOccurrenceSequence leftPrefix ++ [leftFinal] =
          firstOccurrenceSequence rightPrefix ++ [leftFinal] := by
      have fullOrder :
          firstOccurrenceSequence (leftPrefix ++ [leftFinal]) =
            firstOccurrenceSequence (rightPrefix ++ [leftFinal]) := by
        simpa [signature, firstOccurrenceSequenceList,
          toList_wordOfPrefixFinal] using
            congrArg Signature.firstOccurrences same
      simpa [firstOccurrenceSequence_append_final,
        leftFinalMem, rightFinalNotMem] using fullOrder
    have order :
        firstOccurrenceSequence leftPrefix =
          firstOccurrenceSequence rightPrefix :=
      List.append_cancel_right orderWithFinal
    have fullCounts :
        ∀ tested,
          (wordOfPrefixFinal leftPrefix leftFinal).toList.count tested =
            (wordOfPrefixFinal rightPrefix leftFinal).toList.count tested := by
      intro tested
      have capped := capped_count_eq_of_signature_eq same tested
      have leftBound :=
        wordOfPrefixFinal_count_le_three leftNormal leftFinalBound
          (tested := tested)
      have rightBound :=
        wordOfPrefixFinal_count_le_three rightNormal rightFinalBound
          (tested := tested)
      simpa [Nat.min_eq_left leftBound,
        Nat.min_eq_left rightBound] using capped
    have prefixCounts :
        ∀ tested, leftPrefix.count tested = rightPrefix.count tested := by
      intro tested
      have equal := fullCounts tested
      rw [toList_wordOfPrefixFinal, toList_wordOfPrefixFinal,
        List.count_append, List.count_append] at equal
      by_cases testedFinal : tested = leftFinal
      · subst tested
        simp at equal
        omega
      · simpa [testedFinal] using equal
    have prefixEq :=
      S5_530.s5_530Normal_eq_of_invariants
        leftNormal rightNormal order prefixCounts
    rw [prefixEq]

theorem canonicalProtectedWord_final_eq_of_signature_eq
    {left right : Word Nat}
    (leftCanonical : CanonicalProtectedWord left)
    (rightCanonical : CanonicalProtectedWord right)
    (same : signature left = signature right) :
    left.final = right.final := by
  rcases leftCanonical with
    ⟨leftPrefix, leftFinal, leftEq,
      leftNormal, leftFinalBound, leftOwner⟩
  rcases rightCanonical with
    ⟨rightPrefix, rightFinal, rightEq,
      rightNormal, rightFinalBound, rightOwner⟩
  rw [leftEq, rightEq] at same ⊢
  simp only [final_wordOfPrefixFinal]
  have sameTerminal := congrArg Signature.terminal same
  rcases leftOwner with leftSimple | leftNonsimple
  · rcases rightOwner with rightSimple | rightNonsimple
    · rw [terminalStatus_wordOfPrefixFinal_of_not_mem leftSimple,
        terminalStatus_wordOfPrefixFinal_of_not_mem rightSimple] at sameTerminal
      exact TerminalStatus.simple.inj sameTerminal
    · rcases rightNonsimple with
        ⟨rightBefore, rightAfter, rightPrefixEq,
          rightFinalNotBefore, rightAfterNodup⟩
      have rightFinalMem : rightFinal ∈ rightPrefix := by
        rw [rightPrefixEq]
        simp
      rw [terminalStatus_wordOfPrefixFinal_of_not_mem leftSimple,
        terminalStatus_wordOfPrefixFinal_of_mem rightFinalMem] at sameTerminal
      cases sameTerminal
  · rcases leftNonsimple with
      ⟨leftBefore, leftAfter, leftPrefixEq,
        leftFinalNotBefore, leftAfterNodup⟩
    have leftFinalMem : leftFinal ∈ leftPrefix := by
      rw [leftPrefixEq]
      simp
    rcases rightOwner with rightSimple | rightNonsimple
    · rw [terminalStatus_wordOfPrefixFinal_of_mem leftFinalMem,
        terminalStatus_wordOfPrefixFinal_of_not_mem rightSimple] at sameTerminal
      cases sameTerminal
    · rcases rightNonsimple with
        ⟨rightBefore, rightAfter, rightPrefixEq,
          rightFinalNotBefore, rightAfterNodup⟩
      have rightFinalMem : rightFinal ∈ rightPrefix := by
        rw [rightPrefixEq]
        simp
      apply Decidable.byContradiction
      intro finalsEqual
      have rightPrefixPositive : 0 < rightPrefix.count rightFinal :=
        List.count_pos_iff.mpr rightFinalMem
      have rightFinalCappedAtLeast :
          2 ≤ Nat.min
            ((wordOfPrefixFinal rightPrefix rightFinal).toList.count
              rightFinal) 3 := by
        rw [toList_wordOfPrefixFinal, List.count_append]
        simp
        simp only [Nat.min_def]
        split <;> omega
      have rightFinalCappedEqual :=
        capped_count_eq_of_signature_eq same rightFinal
      have leftRightFinalCappedAtLeast :
          2 ≤ Nat.min
            ((wordOfPrefixFinal leftPrefix leftFinal).toList.count
              rightFinal) 3 := by
        rw [rightFinalCappedEqual]
        exact rightFinalCappedAtLeast
      have leftRightFinalAtLeast : 2 ≤ leftPrefix.count rightFinal := by
        rw [toList_wordOfPrefixFinal, List.count_append] at leftRightFinalCappedAtLeast
        simp [finalsEqual] at leftRightFinalCappedAtLeast
        exact Nat.le_trans leftRightFinalCappedAtLeast
          (Nat.min_le_left _ _)
      have leftPrefixPositive : 0 < leftPrefix.count leftFinal :=
        List.count_pos_iff.mpr leftFinalMem
      have leftFinalCappedAtLeast :
          2 ≤ Nat.min
            ((wordOfPrefixFinal leftPrefix leftFinal).toList.count
              leftFinal) 3 := by
        rw [toList_wordOfPrefixFinal, List.count_append]
        simp
        simp only [Nat.min_def]
        split <;> omega
      have leftFinalCappedEqual :=
        capped_count_eq_of_signature_eq same leftFinal
      have rightLeftFinalCappedAtLeast :
          2 ≤ Nat.min
            ((wordOfPrefixFinal rightPrefix rightFinal).toList.count
              leftFinal) 3 := by
        rw [← leftFinalCappedEqual]
        exact leftFinalCappedAtLeast
      have rightLeftFinalAtLeast : 2 ≤ rightPrefix.count leftFinal := by
        rw [toList_wordOfPrefixFinal, List.count_append] at rightLeftFinalCappedAtLeast
        simp [Ne.symm finalsEqual] at rightLeftFinalCappedAtLeast
        exact Nat.le_trans rightLeftFinalCappedAtLeast
          (Nat.min_le_left _ _)
      have rightFinalInLeftBefore : rightFinal ∈ leftBefore := by
        apply Decidable.byContradiction
        intro rightFinalNotBefore
        have afterBound : leftAfter.count rightFinal ≤ 1 := by
          rw [leftAfterNodup.count]
          split <;> omega
        have countEq :
            leftPrefix.count rightFinal = leftAfter.count rightFinal := by
          have beforeCount : leftBefore.count rightFinal = 0 :=
            List.count_eq_zero.mpr rightFinalNotBefore
          rw [leftPrefixEq, List.count_append, List.count_append]
          simp [beforeCount, finalsEqual]
        omega
      have leftFinalInRightBefore : leftFinal ∈ rightBefore := by
        apply Decidable.byContradiction
        intro leftFinalNotBeforeRight
        have afterBound : rightAfter.count leftFinal ≤ 1 := by
          rw [rightAfterNodup.count]
          split <;> omega
        have countEq :
            rightPrefix.count leftFinal = rightAfter.count leftFinal := by
          have beforeCount : rightBefore.count leftFinal = 0 :=
            List.count_eq_zero.mpr leftFinalNotBeforeRight
          rw [rightPrefixEq, List.count_append, List.count_append]
          simp [beforeCount, Ne.symm finalsEqual]
        omega
      have rightBeforeLeft :
          ListBefore rightFinal leftFinal
            (firstOccurrenceSequence leftPrefix) := by
        simpa [leftPrefixEq] using
          ListBefore.firstOccurrence_of_prefix
            (Ne.symm finalsEqual) leftBefore leftAfter
            leftFinalNotBefore rightFinalInLeftBefore
      have leftBeforeRight :
          ListBefore leftFinal rightFinal
            (firstOccurrenceSequence rightPrefix) := by
        simpa [rightPrefixEq] using
          ListBefore.firstOccurrence_of_prefix
            finalsEqual rightBefore rightAfter
            rightFinalNotBefore leftFinalInRightBefore
      have order :
          firstOccurrenceSequence (leftPrefix ++ [leftFinal]) =
            firstOccurrenceSequence (rightPrefix ++ [rightFinal]) := by
        simpa [signature, firstOccurrenceSequenceList,
          toList_wordOfPrefixFinal] using
            congrArg Signature.firstOccurrences same
      rw [firstOccurrenceSequence_append_final leftFinal leftPrefix,
        if_pos leftFinalMem,
        firstOccurrenceSequence_append_final rightFinal rightPrefix,
        if_pos rightFinalMem] at order
      rw [order] at rightBeforeLeft
      exact (ListBefore.asymm_of_nodup
        (firstOccurrenceSequence_nodup rightPrefix)
        rightBeforeLeft) leftBeforeRight

theorem canonicalProtectedWord_eq_of_signature_eq
    {left right : Word Nat}
    (leftCanonical : CanonicalProtectedWord left)
    (rightCanonical : CanonicalProtectedWord right)
    (same : signature left = signature right) :
    left = right :=
  canonicalProtectedWord_eq_of_signature_eq_of_final_eq
    leftCanonical rightCanonical same
    (canonicalProtectedWord_final_eq_of_signature_eq
      leftCanonical rightCanonical same)

theorem section11SignatureDerivationCompleteness :
    SignatureDerivationCompleteness where
  derives := by
    intro left right same
    obtain ⟨leftTarget, leftDerivation, leftCanonical⟩ :=
      derives_canonicalProtectedWord left
    obtain ⟨rightTarget, rightDerivation, rightCanonical⟩ :=
      derives_canonicalProtectedWord right
    have targetSignature :
        signature leftTarget = signature rightTarget :=
      (signature_eq_of_derives leftDerivation).symm.trans <|
        same.trans (signature_eq_of_derives rightDerivation)
    have targetEqual :=
      canonicalProtectedWord_eq_of_signature_eq
        leftCanonical rightCanonical targetSignature
    rw [targetEqual] at leftDerivation
    exact leftDerivation.trans rightDerivation.symm

theorem S6_5614.basisFor : BasisFor S6_5614.table.semigroup basis :=
  S6_5614.basisFor_of_completeness
    section11SignatureDerivationCompleteness

theorem S6_5614.oppositeBasisFor :
    BasisFor S6_5614.table.semigroup.opposite oppositeBasis :=
  S6_5614.oppositeBasisFor_of_completeness
    section11SignatureDerivationCompleteness

theorem S6_9582.basisFor : BasisFor S6_9582.table.semigroup basis :=
  S6_9582.basisFor_of_completeness
    section11SignatureDerivationCompleteness

theorem S6_9582.oppositeBasisFor :
    BasisFor S6_9582.table.semigroup.opposite oppositeBasis :=
  S6_9582.oppositeBasisFor_of_completeness
    section11SignatureDerivationCompleteness

theorem S6_5622.basisFor : BasisFor S6_5622.table.semigroup basis :=
  S6_5622.basisFor_of_completeness
    section11SignatureDerivationCompleteness

theorem S6_5622.oppositeBasisFor :
    BasisFor S6_5622.table.semigroup.opposite oppositeBasis :=
  S6_5622.oppositeBasisFor_of_completeness
    section11SignatureDerivationCompleteness

theorem S6_9451.basisFor : BasisFor S6_9451.table.semigroup basis :=
  S6_9451.basisFor_of_completeness
    section11SignatureDerivationCompleteness

theorem S6_9451.oppositeBasisFor :
    BasisFor S6_9451.table.semigroup.opposite oppositeBasis :=
  S6_9451.oppositeBasisFor_of_completeness
    section11SignatureDerivationCompleteness

end SemigroupBasis.CoRoots.Order6SporadicSection11
