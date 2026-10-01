import SemigroupBasis.CoRoots.Order6PublishedMonoid14CanonicalUniqueness
import SemigroupBasis.CoRoots.S6_8496ProbeKernel

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6PublishedMonoid14.S6_8496

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6PublishedMonoid14

/-! ## Evaluation bridge -/

/-- Folding the full nonempty word from the identity element is its ordinary
semigroup evaluation. -/
theorem eval_eq_probeFold_toList
    (valuation : Nat → Fin 6) (word : Word Nat) :
    table.semigroup.eval valuation word =
      probeFold valuation word.toList 4 := by
  cases word with
  | mk head tail =>
      simpa [Semigroup.eval, Word.toList] using
        (eval_eq_probeFold_four valuation head tail).symm

private theorem singleton_split_not_left
    {whole before after : List Nat} {separator : Nat}
    (shape : whole = before ++ separator :: after)
    (simple : whole.count separator = 1) :
    separator ∉ before := by
  intro member
  have positive : 0 < before.count separator :=
    List.count_pos_iff.mpr member
  rw [shape, List.count_append, List.count_cons_self] at simple
  omega

private theorem singleton_split_not_right
    {whole before after : List Nat} {separator : Nat}
    (shape : whole = before ++ separator :: after)
    (simple : whole.count separator = 1) :
    separator ∉ after := by
  intro member
  have positive : 0 < after.count separator :=
    List.count_pos_iff.mpr member
  rw [shape, List.count_append, List.count_cons_self] at simple
  omega

/-! ## Support of each separator-indexed gap -/

theorem valid_initialGap_support_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    {leftGap rightGap leftAfter rightAfter : List Nat}
    {current : Nat}
    (leftShape :
      identity.lhs.toList = leftGap ++ current :: leftAfter)
    (rightShape :
      identity.rhs.toList = rightGap ++ current :: rightAfter)
    (leftCurrentSimple :
      identity.lhs.toList.count current = 1)
    (rightCurrentSimple :
      identity.rhs.toList.count current = 1)
    (leftRepeated : ∀ letter, letter ∈ leftGap →
      2 ≤ identity.lhs.toList.count letter)
    (rightRepeated : ∀ letter, letter ∈ rightGap →
      2 ≤ identity.rhs.toList.count letter) :
    ∀ tested, tested ∈ leftGap ↔ tested ∈ rightGap := by
  have leftCurrentAbsent : current ∉ leftGap :=
    singleton_split_not_left leftShape leftCurrentSimple
  have rightCurrentAbsent : current ∉ rightGap :=
    singleton_split_not_left rightShape rightCurrentSimple
  intro tested
  by_cases testedCurrent : tested = current
  · subst tested
    constructor
    · exact fun member => False.elim (leftCurrentAbsent member)
    · exact fun member => False.elim (rightCurrentAbsent member)
  · have semanticEq := valid (initialSupportProbe current tested)
    rw [eval_eq_probeFold_toList, eval_eq_probeFold_toList,
      leftShape, rightShape,
      initialSupport_eval leftGap leftAfter current tested
        testedCurrent
        (fun x hx => fun equality =>
          leftCurrentAbsent (equality ▸ hx)),
      initialSupport_eval rightGap rightAfter current tested
        testedCurrent
        (fun x hx => fun equality =>
          rightCurrentAbsent (equality ▸ hx))] at semanticEq
    constructor
    · intro leftMember
      apply Classical.byContradiction
      intro rightMember
      simp [leftMember, rightMember] at semanticEq
    · intro rightMember
      apply Classical.byContradiction
      intro leftMember
      simp [leftMember, rightMember] at semanticEq

theorem valid_interiorGap_support_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    {leftBefore rightBefore leftGap rightGap leftAfter rightAfter : List Nat}
    {previous current : Nat}
    (leftShape :
      identity.lhs.toList =
        leftBefore ++ previous :: (leftGap ++ current :: leftAfter))
    (rightShape :
      identity.rhs.toList =
        rightBefore ++ previous :: (rightGap ++ current :: rightAfter))
    (leftPreviousSimple :
      identity.lhs.toList.count previous = 1)
    (rightPreviousSimple :
      identity.rhs.toList.count previous = 1)
    (leftCurrentSimple :
      identity.lhs.toList.count current = 1)
    (rightCurrentSimple :
      identity.rhs.toList.count current = 1)
    (leftRepeated : ∀ letter, letter ∈ leftGap →
      2 ≤ identity.lhs.toList.count letter)
    (rightRepeated : ∀ letter, letter ∈ rightGap →
      2 ≤ identity.rhs.toList.count letter) :
    ∀ tested, tested ∈ leftGap ↔ tested ∈ rightGap := by
  have leftPreviousBefore : previous ∉ leftBefore :=
    singleton_split_not_left leftShape leftPreviousSimple
  have leftPreviousAfter :
      previous ∉ leftGap ++ current :: leftAfter :=
    singleton_split_not_right leftShape leftPreviousSimple
  have rightPreviousBefore : previous ∉ rightBefore :=
    singleton_split_not_left rightShape rightPreviousSimple
  have rightPreviousAfter :
      previous ∉ rightGap ++ current :: rightAfter :=
    singleton_split_not_right rightShape rightPreviousSimple
  have leftCurrentShape :
      identity.lhs.toList =
        (leftBefore ++ previous :: leftGap) ++ current :: leftAfter := by
    simpa [List.append_assoc] using leftShape
  have rightCurrentShape :
      identity.rhs.toList =
        (rightBefore ++ previous :: rightGap) ++ current :: rightAfter := by
    simpa [List.append_assoc] using rightShape
  have leftCurrentBefore :
      current ∉ leftBefore ++ previous :: leftGap :=
    singleton_split_not_left leftCurrentShape leftCurrentSimple
  have rightCurrentBefore :
      current ∉ rightBefore ++ previous :: rightGap :=
    singleton_split_not_left rightCurrentShape rightCurrentSimple
  have previousCurrent : current ≠ previous := by
    intro equality
    subst current
    exact leftPreviousAfter (by simp)
  have leftGapPrevious : ∀ x ∈ leftGap, x ≠ previous := by
    intro x member equality
    subst x
    exact leftPreviousAfter (List.mem_append_left _ member)
  have rightGapPrevious : ∀ x ∈ rightGap, x ≠ previous := by
    intro x member equality
    subst x
    exact rightPreviousAfter (List.mem_append_left _ member)
  have leftGapCurrent : ∀ x ∈ leftGap, x ≠ current := by
    intro x member equality
    subst x
    exact leftCurrentBefore (by simp [member])
  have rightGapCurrent : ∀ x ∈ rightGap, x ≠ current := by
    intro x member equality
    subst x
    exact rightCurrentBefore (by simp [member])
  have leftAfterPrevious : ∀ x ∈ leftAfter, x ≠ previous := by
    intro x member equality
    subst x
    exact leftPreviousAfter (by simp [member])
  have rightAfterPrevious : ∀ x ∈ rightAfter, x ≠ previous := by
    intro x member equality
    subst x
    exact rightPreviousAfter (by simp [member])
  intro tested
  by_cases testedPrevious : tested = previous
  · subst tested
    constructor
    · exact fun member => False.elim
        ((leftGapPrevious previous member) rfl)
    · exact fun member => False.elim
        ((rightGapPrevious previous member) rfl)
  · by_cases testedCurrent : tested = current
    · subst tested
      constructor
      · exact fun member => False.elim
          ((leftGapCurrent current member) rfl)
      · exact fun member => False.elim
          ((rightGapCurrent current member) rfl)
    · have semanticEq :=
        valid (interiorSupportProbe previous current tested)
      rw [eval_eq_probeFold_toList, eval_eq_probeFold_toList,
        leftShape, rightShape,
        show leftBefore ++ previous :: (leftGap ++ current :: leftAfter) =
            (leftBefore ++ previous :: leftGap) ++ current :: leftAfter from by
          simp [List.append_assoc],
        show rightBefore ++ previous :: (rightGap ++ current :: rightAfter) =
            (rightBefore ++ previous :: rightGap) ++ current :: rightAfter from by
          simp [List.append_assoc],
        interiorSupport_eval leftBefore leftGap leftAfter
          previous current tested previousCurrent testedPrevious
          testedCurrent
          (fun x hx => fun equality =>
            leftPreviousBefore (equality ▸ hx))
          leftGapPrevious leftGapCurrent leftAfterPrevious,
        interiorSupport_eval rightBefore rightGap rightAfter
          previous current tested previousCurrent testedPrevious
          testedCurrent
          (fun x hx => fun equality =>
            rightPreviousBefore (equality ▸ hx))
          rightGapPrevious rightGapCurrent rightAfterPrevious] at semanticEq
      constructor
      · intro leftMember
        apply Classical.byContradiction
        intro rightMember
        simp [leftMember, rightMember] at semanticEq
      · intro rightMember
        apply Classical.byContradiction
        intro leftMember
        simp [leftMember, rightMember] at semanticEq

theorem valid_finalGap_support_iff
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    {leftBefore rightBefore leftGap rightGap : List Nat}
    {previous : Nat}
    (leftShape :
      identity.lhs.toList = leftBefore ++ previous :: leftGap)
    (rightShape :
      identity.rhs.toList = rightBefore ++ previous :: rightGap)
    (leftPreviousSimple :
      identity.lhs.toList.count previous = 1)
    (rightPreviousSimple :
      identity.rhs.toList.count previous = 1)
    (leftRepeated : ∀ letter, letter ∈ leftGap →
      2 ≤ identity.lhs.toList.count letter)
    (rightRepeated : ∀ letter, letter ∈ rightGap →
      2 ≤ identity.rhs.toList.count letter) :
    ∀ tested, tested ∈ leftGap ↔ tested ∈ rightGap := by
  have leftPreviousBefore : previous ∉ leftBefore :=
    singleton_split_not_left leftShape leftPreviousSimple
  have leftPreviousGap : previous ∉ leftGap :=
    singleton_split_not_right leftShape leftPreviousSimple
  have rightPreviousBefore : previous ∉ rightBefore :=
    singleton_split_not_left rightShape rightPreviousSimple
  have rightPreviousGap : previous ∉ rightGap :=
    singleton_split_not_right rightShape rightPreviousSimple
  intro tested
  by_cases testedPrevious : tested = previous
  · subst tested
    constructor
    · exact fun member => False.elim (leftPreviousGap member)
    · exact fun member => False.elim (rightPreviousGap member)
  · have semanticEq := valid (finalSupportProbe previous tested)
    rw [eval_eq_probeFold_toList, eval_eq_probeFold_toList,
      leftShape, rightShape,
      finalSupport_eval leftBefore leftGap previous tested
        testedPrevious
        (fun x hx => fun equality =>
          leftPreviousBefore (equality ▸ hx))
        (fun x hx => fun equality =>
          leftPreviousGap (equality ▸ hx)),
      finalSupport_eval rightBefore rightGap previous tested
        testedPrevious
        (fun x hx => fun equality =>
          rightPreviousBefore (equality ▸ hx))
        (fun x hx => fun equality =>
          rightPreviousGap (equality ▸ hx))] at semanticEq
    constructor
    · intro leftMember
      by_cases rightMember : tested ∈ rightGap
      · exact rightMember
      · simp [leftMember, rightMember] at semanticEq
    · intro rightMember
      by_cases leftMember : tested ∈ leftGap
      · exact leftMember
      · simp [leftMember, rightMember] at semanticEq

/-! ## First-occurrence order within a gap -/

private theorem pairHead_eq_of_initialOrder
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    {leftGap rightGap leftAfter rightAfter : List Nat}
    (leftShape : identity.lhs.toList = leftGap ++ leftAfter)
    (rightShape : identity.rhs.toList = rightGap ++ rightAfter)
    (support : ∀ tested, tested ∈ leftGap ↔ tested ∈ rightGap) :
    ∀ first second,
      first ≠ second →
      first ∈ leftGap →
      second ∈ leftGap →
      (leftGap.filter (pairKeep first second)).head? =
        (rightGap.filter (pairKeep first second)).head? := by
  intro first second different firstMember secondMember
  have rightFirst := (support first).mp firstMember
  have semanticEq := valid (initialOrderProbe first second)
  rw [eval_eq_probeFold_toList, eval_eq_probeFold_toList,
    leftShape, rightShape,
    initialOrder_eval leftGap leftAfter first second
      different firstMember,
    initialOrder_eval rightGap rightAfter first second
      different rightFirst] at semanticEq
  rw [pairProjection_head?_eq_findPair,
    pairProjection_head?_eq_findPair]
  let selected := fun x : Nat => decide (x = first ∨ x = second)
  cases leftFound : leftGap.find? selected with
  | none =>
      have impossible :=
        (List.find?_eq_none.mp leftFound) first firstMember
      simp [selected] at impossible
  | some leftFirst =>
      cases rightFound : rightGap.find? selected with
      | none =>
          have impossible :=
            (List.find?_eq_none.mp rightFound) first rightFirst
          simp [selected] at impossible
      | some rightFirstValue =>
          have leftSelectedBool : selected leftFirst = true :=
            List.find?_some leftFound
          have rightSelectedBool : selected rightFirstValue = true :=
            List.find?_some rightFound
          have leftSelected :
              leftFirst = first ∨ leftFirst = second := by
            exact of_decide_eq_true (by
              simpa [selected] using leftSelectedBool)
          have rightSelected :
              rightFirstValue = first ∨ rightFirstValue = second := by
            exact of_decide_eq_true (by
              simpa [selected] using rightSelectedBool)
          rw [leftFound, rightFound] at semanticEq
          have valueEq : leftFirst = rightFirstValue := by
            rcases leftSelected with rfl | rfl <;>
              rcases rightSelected with rfl | rfl
            · rfl
            · by_cases hit : rightFirstValue = leftFirst
              · exact hit.symm
              · exfalso
                simp [hit, Ne.symm hit] at semanticEq
            · by_cases hit : rightFirstValue = leftFirst
              · exact hit.symm
              · exfalso
                simp [hit, Ne.symm hit] at semanticEq
            · rfl
          exact congrArg some valueEq

private theorem pairHead_eq_of_noninitialOrder
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup)
    {leftBefore rightBefore leftGap rightGap leftAfter rightAfter : List Nat}
    {previous : Nat}
    (leftShape :
      identity.lhs.toList =
        leftBefore ++ previous :: (leftGap ++ leftAfter))
    (rightShape :
      identity.rhs.toList =
        rightBefore ++ previous :: (rightGap ++ rightAfter))
    (leftPreviousSimple :
      identity.lhs.toList.count previous = 1)
    (rightPreviousSimple :
      identity.rhs.toList.count previous = 1)
    (support : ∀ tested, tested ∈ leftGap ↔ tested ∈ rightGap) :
    ∀ first second,
      first ≠ second →
      first ∈ leftGap →
      second ∈ leftGap →
      (leftGap.filter (pairKeep first second)).head? =
        (rightGap.filter (pairKeep first second)).head? := by
  have leftPreviousBefore : previous ∉ leftBefore :=
    singleton_split_not_left leftShape leftPreviousSimple
  have leftPreviousAfter : previous ∉ leftGap ++ leftAfter :=
    singleton_split_not_right leftShape leftPreviousSimple
  have rightPreviousBefore : previous ∉ rightBefore :=
    singleton_split_not_left rightShape rightPreviousSimple
  have rightPreviousAfter : previous ∉ rightGap ++ rightAfter :=
    singleton_split_not_right rightShape rightPreviousSimple
  intro first second different firstMember secondMember
  have rightFirst := (support first).mp firstMember
  have firstPrevious : first ≠ previous := by
    intro equality
    subst first
    exact leftPreviousAfter (List.mem_append_left _ firstMember)
  have secondPrevious : second ≠ previous := by
    intro equality
    subst second
    exact leftPreviousAfter (List.mem_append_left _ secondMember)
  have leftOrderEval :
      probeFold (orderProbe previous first second)
          (leftBefore ++ previous :: (leftGap ++ leftAfter)) 4 =
        (match leftGap.find? (fun x => decide (x = first ∨ x = second)) with
          | none => 1
          | some x => if x = first then 2 else 0) := by
    simpa only [List.cons_append, List.append_assoc] using
      (interiorOrder_eval leftBefore leftGap leftAfter
        previous first second different firstPrevious secondPrevious
        (fun x hx => fun equality =>
          leftPreviousBefore (equality ▸ hx))
        (fun x hx => fun equality =>
          leftPreviousAfter
            (List.mem_append_left _ (equality ▸ hx)))
        (fun x hx => fun equality =>
          leftPreviousAfter
            (List.mem_append_right leftGap (equality ▸ hx)))
        firstMember)
  have rightOrderEval :
      probeFold (orderProbe previous first second)
          (rightBefore ++ previous :: (rightGap ++ rightAfter)) 4 =
        (match rightGap.find? (fun x => decide (x = first ∨ x = second)) with
          | none => 1
          | some x => if x = first then 2 else 0) := by
    simpa only [List.cons_append, List.append_assoc] using
      (interiorOrder_eval rightBefore rightGap rightAfter
        previous first second different firstPrevious secondPrevious
        (fun x hx => fun equality =>
          rightPreviousBefore (equality ▸ hx))
        (fun x hx => fun equality =>
          rightPreviousAfter
            (List.mem_append_left _ (equality ▸ hx)))
        (fun x hx => fun equality =>
          rightPreviousAfter
            (List.mem_append_right rightGap (equality ▸ hx)))
        rightFirst)
  have semanticEq := valid (orderProbe previous first second)
  rw [eval_eq_probeFold_toList, eval_eq_probeFold_toList,
    leftShape, rightShape, leftOrderEval, rightOrderEval] at semanticEq
  rw [pairProjection_head?_eq_findPair,
    pairProjection_head?_eq_findPair]
  let selected := fun x : Nat => decide (x = first ∨ x = second)
  cases leftFound : leftGap.find? selected with
  | none =>
      have impossible :=
        (List.find?_eq_none.mp leftFound) first firstMember
      simp [selected] at impossible
  | some leftFirst =>
      cases rightFound : rightGap.find? selected with
      | none =>
          have impossible :=
            (List.find?_eq_none.mp rightFound) first rightFirst
          simp [selected] at impossible
      | some rightFirstValue =>
          have leftSelectedBool : selected leftFirst = true :=
            List.find?_some leftFound
          have rightSelectedBool : selected rightFirstValue = true :=
            List.find?_some rightFound
          have leftSelected :
              leftFirst = first ∨ leftFirst = second := by
            exact of_decide_eq_true (by
              simpa [selected] using leftSelectedBool)
          have rightSelected :
              rightFirstValue = first ∨ rightFirstValue = second := by
            exact of_decide_eq_true (by
              simpa [selected] using rightSelectedBool)
          rw [leftFound, rightFound] at semanticEq
          have valueEq : leftFirst = rightFirstValue := by
            rcases leftSelected with rfl | rfl <;>
              rcases rightSelected with rfl | rfl
            · rfl
            · by_cases hit : rightFirstValue = leftFirst
              · exact hit.symm
              · exfalso
                simp [hit, Ne.symm hit] at semanticEq
            · by_cases hit : rightFirstValue = leftFirst
              · exact hit.symm
              · exfalso
                simp [hit, Ne.symm hit] at semanticEq
            · rfl
          exact congrArg some valueEq

/-! ## The target oracle -/

/-- Every valid S6_8496 identity has identical ordered square banks in all
aligned globally-simple gaps. -/
theorem valid_canonicalGapOracle
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    CanonicalGapOracle identity.lhs identity.rhs where
  whole := by
    intro leftGap rightGap leftShape rightShape
    have firstOccurrences := valid_firstOccurrenceSequence_eq identity valid
    rw [leftShape, rightShape] at firstOccurrences
    simpa [distinctLetters_eq_firstOccurrenceSequence] using firstOccurrences
  initial := by
    intro leftGap rightGap leftRemainder rightRemainder separator
      leftShape rightShape leftSeparatorSimple rightSeparatorSimple
      leftRepeated rightRepeated
    have support :=
      valid_initialGap_support_iff identity valid
        leftShape rightShape leftSeparatorSimple rightSeparatorSimple
        leftRepeated rightRepeated
    apply distinctLetters_eq_of_support_pairHeads leftGap rightGap support
    exact pairHead_eq_of_initialOrder identity valid
      leftShape rightShape support
  interior := by
    intro leftBefore rightBefore leftGap rightGap leftAfter rightAfter
      previous current leftShape rightShape
      leftPreviousSimple rightPreviousSimple
      leftCurrentSimple rightCurrentSimple leftRepeated rightRepeated
    have support :=
      valid_interiorGap_support_iff identity valid
        leftShape rightShape leftPreviousSimple rightPreviousSimple
        leftCurrentSimple rightCurrentSimple leftRepeated rightRepeated
    apply distinctLetters_eq_of_support_pairHeads leftGap rightGap support
    exact pairHead_eq_of_noninitialOrder identity valid
      leftShape rightShape leftPreviousSimple rightPreviousSimple support
  final := by
    intro leftBefore rightBefore leftGap rightGap separator
      leftShape rightShape leftSeparatorSimple rightSeparatorSimple
      leftRepeated rightRepeated
    have support :=
      valid_finalGap_support_iff identity valid
        leftShape rightShape leftSeparatorSimple rightSeparatorSimple
        leftRepeated rightRepeated
    apply distinctLetters_eq_of_support_pairHeads leftGap rightGap support
    have leftShape' :
        identity.lhs.toList =
          leftBefore ++ separator :: (leftGap ++ []) := by
      simpa using leftShape
    have rightShape' :
        identity.rhs.toList =
          rightBefore ++ separator :: (rightGap ++ []) := by
      simpa using rightShape
    exact pairHead_eq_of_noninitialOrder identity valid
      leftShape' rightShape' leftSeparatorSimple rightSeparatorSimple support

end SemigroupBasis.CoRoots.Order6PublishedMonoid14.S6_8496
