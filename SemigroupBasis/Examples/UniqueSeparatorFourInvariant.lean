import SemigroupBasis.Examples.UniqueSeparatorFourSemantics

namespace SemigroupBasis.Examples

open SemigroupBasis

/-- A concrete occurrence of a globally unique separator whose left and
right supports are disjoint. -/
def UniqueSeparatorFourExactCut
    {α : Type} [DecidableEq α] (letters left : List α)
    (separator : α) (right : List α) : Prop :=
  letters = left ++ separator :: right ∧
    letters.count separator = 1 ∧
    UniqueSeparatorFourSupportsDisjoint left right

/-- Equal term functions in `S4_69` have equal support. -/
theorem uniqueSeparatorFourEqualEval_support_iff
    {α : Type} [DecidableEq α] (left right : Word α)
    (equalEval :
      ∀ valuation : α → Fin 4,
        uniqueSeparatorFour.semigroup.eval valuation left =
          uniqueSeparatorFour.semigroup.eval valuation right)
    (tested : α) :
    tested ∈ left.toList ↔ tested ∈ right.toList := by
  have evaluated :=
    equalEval (uniqueSeparatorFourSupportValuation tested)
  constructor
  · intro member
    have leftZero :
        uniqueSeparatorFour.semigroup.eval
            (uniqueSeparatorFourSupportValuation tested) left =
          (0 : Fin 4) :=
      (uniqueSeparatorFourSupportEval_eq_zero_iff tested left).2 member
    have rightZero :
        uniqueSeparatorFour.semigroup.eval
            (uniqueSeparatorFourSupportValuation tested) right =
          (0 : Fin 4) :=
      evaluated.symm.trans leftZero
    exact
      (uniqueSeparatorFourSupportEval_eq_zero_iff tested right).1
        rightZero
  · intro member
    have rightZero :
        uniqueSeparatorFour.semigroup.eval
            (uniqueSeparatorFourSupportValuation tested) right =
          (0 : Fin 4) :=
      (uniqueSeparatorFourSupportEval_eq_zero_iff tested right).2 member
    have leftZero :
        uniqueSeparatorFour.semigroup.eval
            (uniqueSeparatorFourSupportValuation tested) left =
          (0 : Fin 4) :=
      evaluated.trans rightZero
    exact
      (uniqueSeparatorFourSupportEval_eq_zero_iff tested left).1
        leftZero

/-- Every identity valid in `S4_69` preserves support. -/
theorem uniqueSeparatorFourValid_support_iff
    {α : Type} [DecidableEq α] (identity : Identity α)
    (valid : identity.SatisfiedBy uniqueSeparatorFour.semigroup)
    (tested : α) :
    tested ∈ identity.lhs.toList ↔ tested ∈ identity.rhs.toList :=
  uniqueSeparatorFourEqualEval_support_iff
    identity.lhs identity.rhs valid tested

private theorem exactCut_separator_absent_left
    {α : Type} [DecidableEq α] {letters left right : List α}
    {separator : α}
    (split : letters = left ++ separator :: right)
    (countOne : letters.count separator = 1) :
    separator ∉ left := by
  intro member
  have positive : 0 < left.count separator :=
    List.count_pos_iff.mpr member
  rw [split, List.count_append, List.count_cons_self] at countOne
  omega

private theorem exactCut_separator_absent_right
    {α : Type} [DecidableEq α] {letters left right : List α}
    {separator : α}
    (split : letters = left ++ separator :: right)
    (countOne : letters.count separator = 1) :
    separator ∉ right := by
  intro member
  have positive : 0 < right.count separator :=
    List.count_pos_iff.mpr member
  rw [split, List.count_append, List.count_cons_self] at countOne
  omega

/-- Transport one exact separator cut across two words with equal term
functions.  The transported cut has exactly the same left and right
supports, not merely compatible supports. -/
theorem uniqueSeparatorFourEqualEval_transportExactCut
    {α : Type} [DecidableEq α] (source target : Word α)
    (equalEval :
      ∀ valuation : α → Fin 4,
        uniqueSeparatorFour.semigroup.eval valuation source =
          uniqueSeparatorFour.semigroup.eval valuation target)
    {left right : List α} {separator : α}
    (cut :
      UniqueSeparatorFourExactCut
        source.toList left separator right) :
    ∃ targetLeft targetRight,
      UniqueSeparatorFourExactCut
          target.toList targetLeft separator targetRight ∧
        (∀ letter, letter ∈ targetLeft ↔ letter ∈ left) ∧
        (∀ letter, letter ∈ targetRight ↔ letter ∈ right) := by
  rcases cut with ⟨sourceSplit, sourceCount, sourceDisjoint⟩
  have separatorAbsentLeft :
      separator ∉ left :=
    exactCut_separator_absent_left sourceSplit sourceCount
  have separatorAbsentRight :
      separator ∉ right :=
    exactCut_separator_absent_right sourceSplit sourceCount
  have sourceEvaluatesOne :
      uniqueSeparatorFour.semigroup.eval
          (uniqueSeparatorFourSeparatorValuation left separator)
          source =
        (1 : Fin 4) := by
    apply
      (uniqueSeparatorFourSeparatorEval_eq_one_iff_exact_cut
        left separator source).2
    refine ⟨sourceCount, left, right, sourceSplit, ?_, ?_,
      sourceDisjoint⟩
    · exact
        ⟨separatorAbsentLeft,
          fun letter member => member⟩
    · exact
        ⟨separatorAbsentRight,
          fun letter rightMember leftMember =>
            sourceDisjoint letter leftMember rightMember⟩
  have targetEvaluatesOne :
      uniqueSeparatorFour.semigroup.eval
          (uniqueSeparatorFourSeparatorValuation left separator)
          target =
        (1 : Fin 4) :=
    (equalEval
      (uniqueSeparatorFourSeparatorValuation left separator)).symm.trans
        sourceEvaluatesOne
  obtain
    ⟨targetCount, targetLeft, targetRight, targetSplit,
      targetLeftCompatible, targetRightCompatible, targetDisjoint⟩ :=
    (uniqueSeparatorFourSeparatorEval_eq_one_iff_exact_cut
      left separator target).1 targetEvaluatesOne
  have supportIff :
      ∀ letter,
        letter ∈ source.toList ↔ letter ∈ target.toList :=
    fun letter =>
      uniqueSeparatorFourEqualEval_support_iff
        source target equalEval letter
  have targetLeftSupport :
      ∀ letter, letter ∈ targetLeft ↔ letter ∈ left := by
    intro letter
    constructor
    · exact targetLeftCompatible.2 letter
    · intro leftMember
      have sourceMember : letter ∈ source.toList := by
        rw [sourceSplit]
        exact List.mem_append_left _ leftMember
      have targetMember : letter ∈ target.toList :=
        (supportIff letter).1 sourceMember
      rw [targetSplit] at targetMember
      rcases List.mem_append.mp targetMember with
        targetLeftMember | targetSuffixMember
      · exact targetLeftMember
      · rcases List.mem_cons.mp targetSuffixMember with
          separatorEquality | targetRightMember
        · subst letter
          exact False.elim (separatorAbsentLeft leftMember)
        · exact False.elim <|
            targetRightCompatible.2 letter targetRightMember leftMember
  have targetRightSupport :
      ∀ letter, letter ∈ targetRight ↔ letter ∈ right := by
    intro letter
    constructor
    · intro targetRightMember
      have targetMember : letter ∈ target.toList := by
        rw [targetSplit]
        exact List.mem_append_right _ <|
          List.Mem.tail separator targetRightMember
      have sourceMember : letter ∈ source.toList :=
        (supportIff letter).2 targetMember
      rw [sourceSplit] at sourceMember
      rcases List.mem_append.mp sourceMember with
        sourceLeftMember | sourceSuffixMember
      · exact False.elim <|
          targetRightCompatible.2
            letter targetRightMember sourceLeftMember
      · rcases List.mem_cons.mp sourceSuffixMember with
          separatorEquality | sourceRightMember
        · subst letter
          exact False.elim <|
            targetRightCompatible.1 targetRightMember
        · exact sourceRightMember
    · intro sourceRightMember
      have sourceMember : letter ∈ source.toList := by
        rw [sourceSplit]
        exact List.mem_append_right _ <|
          List.Mem.tail separator sourceRightMember
      have targetMember : letter ∈ target.toList :=
        (supportIff letter).1 sourceMember
      rw [targetSplit] at targetMember
      rcases List.mem_append.mp targetMember with
        targetLeftMember | targetSuffixMember
      · have sourceLeftMember :=
          targetLeftCompatible.2 letter targetLeftMember
        exact False.elim <|
          sourceDisjoint letter sourceLeftMember sourceRightMember
      · rcases List.mem_cons.mp targetSuffixMember with
          separatorEquality | targetRightMember
        · subst letter
          exact False.elim (separatorAbsentRight sourceRightMember)
        · exact targetRightMember
  exact
    ⟨targetLeft, targetRight,
      ⟨targetSplit, targetCount, targetDisjoint⟩,
      targetLeftSupport, targetRightSupport⟩

/-- Exact separator-cut signatures are invariant under equal term
functions. -/
theorem uniqueSeparatorFourEqualEval_exactCut_iff
    {α : Type} [DecidableEq α] (leftWord rightWord : Word α)
    (equalEval :
      ∀ valuation : α → Fin 4,
        uniqueSeparatorFour.semigroup.eval valuation leftWord =
          uniqueSeparatorFour.semigroup.eval valuation rightWord)
    (separator : α) (leftSupport rightSupport : List α) :
    (∃ left right,
        UniqueSeparatorFourExactCut
            leftWord.toList left separator right ∧
          (∀ letter, letter ∈ left ↔ letter ∈ leftSupport) ∧
          (∀ letter, letter ∈ right ↔ letter ∈ rightSupport)) ↔
      ∃ left right,
        UniqueSeparatorFourExactCut
            rightWord.toList left separator right ∧
          (∀ letter, letter ∈ left ↔ letter ∈ leftSupport) ∧
          (∀ letter, letter ∈ right ↔ letter ∈ rightSupport) := by
  constructor
  · rintro ⟨left, right, cut, leftEq, rightEq⟩
    obtain
      ⟨targetLeft, targetRight, targetCut,
        targetLeftEq, targetRightEq⟩ :=
      uniqueSeparatorFourEqualEval_transportExactCut
        leftWord rightWord equalEval cut
    exact
      ⟨targetLeft, targetRight, targetCut,
        fun letter => (targetLeftEq letter).trans (leftEq letter),
        fun letter => (targetRightEq letter).trans (rightEq letter)⟩
  · rintro ⟨left, right, cut, leftEq, rightEq⟩
    obtain
      ⟨targetLeft, targetRight, targetCut,
        targetLeftEq, targetRightEq⟩ :=
      uniqueSeparatorFourEqualEval_transportExactCut
        rightWord leftWord (fun valuation => (equalEval valuation).symm)
        cut
    exact
      ⟨targetLeft, targetRight, targetCut,
        fun letter => (targetLeftEq letter).trans (leftEq letter),
        fun letter => (targetRightEq letter).trans (rightEq letter)⟩

end SemigroupBasis.Examples
