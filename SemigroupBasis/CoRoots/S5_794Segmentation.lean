import SemigroupBasis.CoRoots.S5_794BlockSemantics

namespace SemigroupBasis.CoRoots.S5_794

open SemigroupBasis
open SemigroupBasis.Examples

/-- Retain the letters of `letters` that are globally linear in `whole`. -/
private def simpleProjection
    (whole letters : List Nat) : List Nat :=
  letters.filter fun letter => decide (whole.count letter = 1)

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
    (dropped : ¬keep selected)
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
          (filter_ne_then_keep_of_drop
            keep letter kept (firstOccurrenceSequence rest)).symm

private theorem firstOccurrenceSequence_eq_self_of_nodup
    {letters : List Nat} (nodup : letters.Nodup) :
    firstOccurrenceSequence letters = letters := by
  induction letters with
  | nil => rfl
  | cons letter rest induction =>
      have data := List.nodup_cons.mp nodup
      rw [firstOccurrenceSequence, induction data.2]
      congr 1
      apply List.filter_eq_self.mpr
      intro next member
      exact decide_eq_true <| by
        intro equal
        subst next
        exact data.1 member

private theorem nodup_of_count_le_one
    {letters : List Nat}
    (bounded : ∀ letter, letters.count letter ≤ 1) :
    letters.Nodup := by
  induction letters with
  | nil => simp
  | cons first rest induction =>
      simp only [List.nodup_cons]
      constructor
      · intro member
        have positive : 1 ≤ rest.count first :=
          List.count_pos_iff.mpr member
        have bound := bounded first
        simp only [List.count_cons_self] at bound
        omega
      · apply induction
        intro letter
        have bound := bounded letter
        by_cases equal : first = letter
        · subst first
          simp only [List.count_cons_self] at bound
          omega
        · simpa [equal] using bound

private theorem simpleProjection_self_nodup (letters : List Nat) :
    (simpleProjection letters letters).Nodup := by
  apply nodup_of_count_le_one
  intro letter
  by_cases simple : letters.count letter = 1
  · exact Nat.le_trans
      (List.filter_sublist.count_le letter) (by omega)
  · have absent : letter ∉ simpleProjection letters letters := by
      intro member
      have kept := (List.mem_filter.mp member).2
      simp [simpleProjection, simple] at kept
    rw [List.count_eq_zero.mpr absent]
    omega

private theorem simpleProjection_self_eq_firstOccurrenceFilter
    (letters : List Nat) :
    simpleProjection letters letters =
      (firstOccurrenceSequence letters).filter
        (fun letter => decide (letters.count letter = 1)) := by
  calc
    simpleProjection letters letters =
        firstOccurrenceSequence (simpleProjection letters letters) :=
      (firstOccurrenceSequence_eq_self_of_nodup
        (simpleProjection_self_nodup letters)).symm
    _ = _ := by
      simpa [simpleProjection] using
        firstOccurrenceSequence_filter
          (fun letter => decide (letters.count letter = 1)) letters

private theorem simpleProjection_congr
    {leftWhole rightWhole : List Nat}
    (counts : ∀ letter, leftWhole.count letter = rightWhole.count letter)
    (letters : List Nat) :
    simpleProjection leftWhole letters =
      simpleProjection rightWhole letters := by
  unfold simpleProjection
  apply List.filter_congr
  intro letter _
  simp [counts letter]

private theorem simpleProjection_cons_split
    (pre tail : List Nat) (separator : Nat) (remaining : List Nat)
    (projection :
      simpleProjection (pre ++ tail) tail = separator :: remaining) :
    ∃ before after,
      tail = before ++ separator :: after ∧
      (∀ letter, letter ∈ before →
        (pre ++ tail).count letter ≠ 1) ∧
      simpleProjection (pre ++ tail) after = remaining ∧
      (pre ++ tail).count separator = 1 := by
  have separatorProjected :
      separator ∈ simpleProjection (pre ++ tail) tail := by
    rw [projection]
    simp
  have separatorData := List.mem_filter.mp separatorProjected
  have separatorInTail : separator ∈ tail := separatorData.1
  have separatorSimple : (pre ++ tail).count separator = 1 := by
    simpa [simpleProjection] using separatorData.2
  obtain ⟨before, after, tailShape⟩ :=
    List.append_of_mem separatorInTail
  have separatorSimpleShaped :
      (pre ++ (before ++ separator :: after)).count separator = 1 := by
    simpa [tailShape] using separatorSimple
  have separatorNotBefore : separator ∉ before := by
    intro member
    have positive : 1 ≤ before.count separator :=
      List.one_le_count_iff.mpr member
    simp only [List.count_append, List.count_cons_self] at separatorSimpleShaped
    omega
  have expanded :
      simpleProjection (pre ++ tail) before ++
        separator :: simpleProjection (pre ++ tail) after =
      separator :: remaining := by
    have expandedProjection := projection
    rw [tailShape] at expandedProjection
    unfold simpleProjection at expandedProjection
    rw [List.filter_append] at expandedProjection
    have separatorKept :
        decide
            ((pre ++ (before ++ separator :: after)).count separator = 1) =
          true := by
      simp [separatorSimpleShaped]
    rw [List.filter_cons, if_pos separatorKept] at expandedProjection
    simpa [simpleProjection, tailShape, List.append_assoc] using
      expandedProjection
  have beforeEmpty :
      simpleProjection (pre ++ tail) before = [] := by
    cases beforeProjection : simpleProjection (pre ++ tail) before with
    | nil => rfl
    | cons first rest =>
        rw [beforeProjection] at expanded
        simp only [List.cons_append] at expanded
        have firstEqual : first = separator := by
          injection expanded
        subst first
        have separatorProjectedBefore :
            separator ∈ simpleProjection (pre ++ tail) before := by
          rw [beforeProjection]
          simp
        have separatorBefore : separator ∈ before :=
          (List.mem_filter.mp separatorProjectedBefore).1
        exact False.elim (separatorNotBefore separatorBefore)
  have afterProjection :
      simpleProjection (pre ++ tail) after = remaining := by
    rw [beforeEmpty] at expanded
    simpa using expanded
  have beforeNonlinear :
      ∀ letter, letter ∈ before →
        (pre ++ tail).count letter ≠ 1 := by
    intro letter member countOne
    have projected :
        letter ∈ simpleProjection (pre ++ tail) before :=
      List.mem_filter.mpr ⟨member, by simp [countOne]⟩
    rw [beforeEmpty] at projected
    simp at projected
  exact
    ⟨before, after, tailShape, beforeNonlinear,
      afterProjection, separatorSimple⟩

private theorem nonlinear_of_simpleProjection_nil
    (whole letters : List Nat)
    (projection : simpleProjection whole letters = []) :
    ∀ letter, letter ∈ letters → whole.count letter ≠ 1 := by
  intro letter member countOne
  have projected : letter ∈ simpleProjection whole letters :=
    List.mem_filter.mpr ⟨member, by simp [countOne]⟩
  rw [projection] at projected
  simp at projected

/-- Convert validity of a nonempty-word identity into the list-level `M14`
equivalence used by the block replay. -/
theorem m14ListEquivalent_of_valid
    (left right : Word Nat)
    (valid :
      (Identity.mk left right).SatisfiedBy
        publishedM14Table.semigroup) :
    M14ListEquivalent left.toList right.toList := by
  intro valuation
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          unfold m14ListEval
          change
            leftTail.foldl
                (fun current letter =>
                  publishedM14Mul current (valuation letter))
                (publishedM14Mul 4 (valuation leftHead)) =
              rightTail.foldl
                (fun current letter =>
                  publishedM14Mul current (valuation letter))
                (publishedM14Mul 4 (valuation rightHead))
          rw [show publishedM14Mul 4 (valuation leftHead) =
              valuation leftHead by
                unfold publishedM14Mul
                simp,
            show publishedM14Mul 4 (valuation rightHead) =
              valuation rightHead by
                unfold publishedM14Mul
                simp]
          simpa [Semigroup.eval, publishedM14Table] using valid valuation

private theorem listDerivesSegmented
    (sourceTail targetTail pre : List Nat)
    (sourceLimited :
      UniqueSeparatorTwoLimited (pre ++ sourceTail))
    (targetLimited :
      UniqueSeparatorTwoLimited (pre ++ targetTail))
    (counts :
      ∀ letter,
        (pre ++ sourceTail).count letter =
          (pre ++ targetTail).count letter)
    (simpleEqual :
      simpleProjection (pre ++ sourceTail) sourceTail =
        simpleProjection (pre ++ targetTail) targetTail)
    (equivalent :
      M14ListEquivalent
        (pre ++ sourceTail) (pre ++ targetTail)) :
    S5_107.ListDerives basis
      (pre ++ sourceTail) (pre ++ targetTail) := by
  cases sourceProjection :
      simpleProjection (pre ++ sourceTail) sourceTail with
  | nil =>
      have targetProjection :
          simpleProjection (pre ++ targetTail) targetTail = [] := by
        rw [← simpleEqual, sourceProjection]
      have sourceNonlinear :=
        nonlinear_of_simpleProjection_nil
          (pre ++ sourceTail) sourceTail sourceProjection
      have permutation : sourceTail.Perm targetTail := by
        rw [List.perm_iff_count]
        intro letter
        have total := counts letter
        simp only [List.count_append] at total
        omega
      have quadratic :
          ∀ letter, letter ∈ sourceTail →
            (pre ++ sourceTail ++ []).count letter = 2 := by
        intro letter member
        have positive : 1 ≤ (pre ++ sourceTail).count letter :=
          List.one_le_count_iff.mpr <| by simp [member]
        have bound := sourceLimited letter
        have notOne := sourceNonlinear letter member
        simpa using (show (pre ++ sourceTail).count letter = 2 by omega)
      simpa using
        listDerivesQuadraticBlockPermutationAgainst
          targetTail sourceTail pre [] [] permutation quadratic
          (by simpa using equivalent)
  | cons separator remaining =>
      have targetProjection :
          simpleProjection (pre ++ targetTail) targetTail =
            separator :: remaining := by
        rw [← simpleEqual, sourceProjection]
      obtain
        ⟨sourceBlock, sourceRest, sourceShape,
          sourceBlockNonlinear, sourceRestProjection,
          sourceSeparator⟩ :=
        simpleProjection_cons_split
          pre sourceTail separator remaining sourceProjection
      obtain
        ⟨targetBlock, targetRest, targetShape,
          targetBlockNonlinear, targetRestProjection,
          targetSeparator⟩ :=
        simpleProjection_cons_split
          pre targetTail separator remaining targetProjection
      have sourceRestShorter : sourceRest.length < sourceTail.length := by
        rw [sourceShape]
        simp only [List.length_append, List.length_cons]
        omega
      have sourceLimitedNorm :
          UniqueSeparatorTwoLimited
            (pre ++ sourceBlock ++ separator :: sourceRest) := by
        simpa [sourceShape, List.append_assoc] using sourceLimited
      have targetLimitedNorm :
          UniqueSeparatorTwoLimited
            (pre ++ targetBlock ++ separator :: targetRest) := by
        simpa [targetShape, List.append_assoc] using targetLimited
      have countsNorm :
          ∀ letter,
            (pre ++ sourceBlock ++ separator :: sourceRest).count letter =
              (pre ++ targetBlock ++ separator :: targetRest).count
                letter := by
        intro letter
        simpa [sourceShape, targetShape, List.append_assoc] using
          counts letter
      have equivalentNorm :
          M14ListEquivalent
            (pre ++ sourceBlock ++ separator :: sourceRest)
            (pre ++ targetBlock ++ separator :: targetRest) := by
        simpa [sourceShape, targetShape, List.append_assoc] using equivalent
      have sourceSeparatorNorm :
          (pre ++ sourceBlock ++ separator :: sourceRest).count
              separator = 1 := by
        simpa [sourceShape, List.append_assoc] using sourceSeparator
      have targetSeparatorNorm :
          (pre ++ targetBlock ++ separator :: targetRest).count
              separator = 1 := by
        simpa [targetShape, List.append_assoc] using targetSeparator
      have blockPermutation : sourceBlock.Perm targetBlock := by
        rw [List.perm_iff_count]
        intro letter
        by_cases sourceMember : letter ∈ sourceBlock
        · have sourcePositive :
              1 ≤
                (pre ++ sourceBlock ++ separator :: sourceRest).count
                  letter :=
            List.one_le_count_iff.mpr <| by simp [sourceMember]
          have sourceBound := sourceLimitedNorm letter
          have sourceNotOne :
              (pre ++ sourceBlock ++ separator :: sourceRest).count
                  letter ≠ 1 := by
            simpa [sourceShape, List.append_assoc] using
              sourceBlockNonlinear letter sourceMember
          have sourceTwo :
              (pre ++ sourceBlock ++ separator :: sourceRest).count
                  letter = 2 := by
            omega
          have targetTwo :
              (pre ++ targetBlock ++ separator :: targetRest).count
                  letter = 2 := by
            calc
              _ =
                  (pre ++ sourceBlock ++ separator :: sourceRest).count
                    letter := (countsNorm letter).symm
              _ = 2 := sourceTwo
          have cut :=
            prefixCount_eq_of_m14Equivalent
              (leftPrefix := pre ++ sourceBlock)
              (leftRest := sourceRest)
              (rightPrefix := pre ++ targetBlock)
              (rightRest := targetRest)
              sourceTwo targetTwo
              sourceSeparatorNorm targetSeparatorNorm equivalentNorm
          simp only [List.count_append] at cut
          omega
        · by_cases targetMember : letter ∈ targetBlock
          · have targetPositive :
                1 ≤
                  (pre ++ targetBlock ++ separator :: targetRest).count
                    letter :=
              List.one_le_count_iff.mpr <| by simp [targetMember]
            have targetBound := targetLimitedNorm letter
            have targetNotOne :
                (pre ++ targetBlock ++ separator :: targetRest).count
                    letter ≠ 1 := by
              simpa [targetShape, List.append_assoc] using
                targetBlockNonlinear letter targetMember
            have targetTwo :
                (pre ++ targetBlock ++ separator :: targetRest).count
                    letter = 2 := by
              omega
            have sourceTwo :
                (pre ++ sourceBlock ++ separator :: sourceRest).count
                    letter = 2 := by
              calc
                _ =
                    (pre ++ targetBlock ++ separator :: targetRest).count
                      letter := countsNorm letter
                _ = 2 := targetTwo
            have cut :=
              prefixCount_eq_of_m14Equivalent
                (leftPrefix := pre ++ sourceBlock)
                (leftRest := sourceRest)
                (rightPrefix := pre ++ targetBlock)
                (rightRest := targetRest)
                sourceTwo targetTwo
                sourceSeparatorNorm targetSeparatorNorm equivalentNorm
            simp only [List.count_append] at cut
            omega
          · rw [List.count_eq_zero.mpr sourceMember,
              List.count_eq_zero.mpr targetMember]
      have sourceQuadratic :
          ∀ letter, letter ∈ sourceBlock →
            (pre ++ sourceBlock ++ separator :: sourceRest).count
                letter = 2 := by
        intro letter member
        have positive :
            1 ≤
              (pre ++ sourceBlock ++ separator :: sourceRest).count
                letter :=
          List.one_le_count_iff.mpr <| by simp [member]
        have bound := sourceLimitedNorm letter
        have notOne :
            (pre ++ sourceBlock ++ separator :: sourceRest).count
                letter ≠ 1 := by
          simpa [sourceShape, List.append_assoc] using
            sourceBlockNonlinear letter member
        omega
      have move :=
        listDerivesQuadraticBlockPermutationAgainst
          targetBlock sourceBlock pre
          (separator :: sourceRest) (separator :: targetRest)
          blockPermutation sourceQuadratic
          equivalentNorm
      have fullPermutation :
          (pre ++ sourceBlock ++ separator :: sourceRest).Perm
            (pre ++ targetBlock ++ separator :: sourceRest) := by
        simpa [List.append_assoc] using
          List.Perm.append
            (List.Perm.append (List.Perm.refl pre) blockPermutation)
            (List.Perm.refl (separator :: sourceRest))
      let nextPre := pre ++ targetBlock ++ [separator]
      have nextEquivalent :
          M14ListEquivalent
            (nextPre ++ sourceRest) (nextPre ++ targetRest) := by
        have moved :=
          (M14ListEquivalent.of_derives move).symm.trans equivalentNorm
        simpa [nextPre, List.append_assoc] using moved
      have nextCounts :
          ∀ letter,
            (nextPre ++ sourceRest).count letter =
              (nextPre ++ targetRest).count letter := by
        intro letter
        calc
          (nextPre ++ sourceRest).count letter =
              (pre ++ sourceBlock ++ separator :: sourceRest).count
                letter := by
            simpa [nextPre, List.append_assoc] using
              (fullPermutation.count letter).symm
          _ =
              (pre ++ targetBlock ++ separator :: targetRest).count
                letter := by
            exact countsNorm letter
          _ = (nextPre ++ targetRest).count letter := by
            simp [nextPre, List.append_assoc]
      have nextSourceLimited :
          UniqueSeparatorTwoLimited (nextPre ++ sourceRest) := by
        intro letter
        calc
          (nextPre ++ sourceRest).count letter =
              (pre ++ sourceBlock ++ separator :: sourceRest).count
                letter := by
            simpa [nextPre, List.append_assoc] using
              (fullPermutation.count letter).symm
          _ ≤ 2 := sourceLimitedNorm letter
      have nextTargetLimited :
          UniqueSeparatorTwoLimited (nextPre ++ targetRest) := by
        intro letter
        simpa [nextPre, List.append_assoc] using targetLimitedNorm letter
      have nextSimpleEqual :
          simpleProjection (nextPre ++ sourceRest) sourceRest =
            simpleProjection (nextPre ++ targetRest) targetRest := by
        calc
          simpleProjection (nextPre ++ sourceRest) sourceRest =
              simpleProjection
                (pre ++ sourceBlock ++ separator :: sourceRest)
                sourceRest := by
            apply simpleProjection_congr
            intro letter
            simpa [nextPre, List.append_assoc] using
              (fullPermutation.count letter).symm
          _ = remaining := by
            simpa [sourceShape, List.append_assoc] using sourceRestProjection
          _ = simpleProjection
                (pre ++ targetBlock ++ separator :: targetRest)
                targetRest := by
            simpa [targetShape, List.append_assoc] using
              targetRestProjection.symm
          _ = simpleProjection (nextPre ++ targetRest) targetRest := by
            simp [nextPre, List.append_assoc]
      have recurse :=
        listDerivesSegmented sourceRest targetRest nextPre
          nextSourceLimited nextTargetLimited nextCounts
          nextSimpleEqual nextEquivalent
      simpa [sourceShape, targetShape, List.append_assoc] using move.trans (by
        simpa [nextPre, List.append_assoc] using recurse)
termination_by sourceTail.length
decreasing_by
  exact sourceRestShorter

/-- Capped words with equal multiplicities and equal first-occurrence
sequences derive one another whenever they are `M14`-equivalent. -/
theorem listDerivesCappedOfCountsFirstSequence
    (left right : Word Nat)
    (leftLimited : UniqueSeparatorTwoLimited left.toList)
    (rightLimited : UniqueSeparatorTwoLimited right.toList)
    (counts :
      ∀ letter,
        left.toList.count letter = right.toList.count letter)
    (firstSequence :
      firstOccurrenceSequence left.toList =
        firstOccurrenceSequence right.toList)
    (equivalent : M14ListEquivalent left.toList right.toList) :
    S5_107.ListDerives basis left.toList right.toList := by
  have simpleEqual :
      simpleProjection left.toList left.toList =
        simpleProjection right.toList right.toList := by
    calc
      simpleProjection left.toList left.toList =
          (firstOccurrenceSequence left.toList).filter
            (fun letter => decide (left.toList.count letter = 1)) :=
        simpleProjection_self_eq_firstOccurrenceFilter left.toList
      _ =
          (firstOccurrenceSequence right.toList).filter
            (fun letter => decide (right.toList.count letter = 1)) := by
        rw [firstSequence]
        apply List.filter_congr
        intro letter _
        simp [counts letter]
      _ = simpleProjection right.toList right.toList :=
        (simpleProjection_self_eq_firstOccurrenceFilter right.toList).symm
  simpa using
    listDerivesSegmented left.toList right.toList []
      leftLimited rightLimited counts simpleEqual equivalent

end SemigroupBasis.CoRoots.S5_794
