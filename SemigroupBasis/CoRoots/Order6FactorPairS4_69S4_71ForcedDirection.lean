import SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71EventIncomparability

namespace SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71

open SemigroupBasis

/-!
# Forced direction at an uncovered simple/first site

The width-free normalizer only needs one fact about a non-derivable
simple/first crossing.  If no quadratic interval covers an adjacent
`simple, first` site, then the simple letter is an exact `S4_69` separator.
The exact-cut component of `SameJointSignature` transports that separator
to every signature-equal word and therefore fixes the direction of the
crossing.

This module is purely combinatorial.  It does not duplicate the constructive
covered-crossing theorem.
-/

/-- A multiplicity-two letter has one occurrence strictly before the
adjacent site `i, i + 1` and its other occurrence strictly after it. -/
def CoveredAt (letters : List Nat) (i : Nat) : Prop :=
  ∃ g pre post,
    letters.count g = 2 ∧
      pre < i ∧
      i + 1 < post ∧
      post < letters.length ∧
      letters[pre]? = some g ∧
      letters[post]? = some g

/-- Contract consumed by the width-free normalizer.  The current pinned
Lean API calls the first-occurrence operation `List.idxOf`. -/
def ForcedDirection : Prop :=
  ∀ (left right : Word Nat) (i s a : Nat),
    SameJointSignature left right →
    (∀ t, left.toList.count t ≤ 2) →
    (∀ t, right.toList.count t ≤ 2) →
    left.toList.count s = 1 →
    left.toList.count a = 2 →
    left.toList[i]? = some s →
    left.toList[i + 1]? = some a →
    (∀ j, j < i + 1 → left.toList[j]? ≠ some a) →
    ¬ CoveredAt left.toList i →
    right.toList.idxOf s < right.toList.idxOf a

private theorem exactCut_separator_not_left
    {letters left right : List Nat} {separator : Nat}
    (cut :
      SemigroupBasis.Examples.UniqueSeparatorFourExactCut
        letters left separator right) :
    separator ∉ left := by
  intro separatorMember
  have leftPositive : 0 < left.count separator :=
    List.count_pos_iff.mpr separatorMember
  have countOne := cut.2.1
  rw [cut.1, List.count_append, List.count_cons_self] at countOne
  omega

private theorem exactCutAtUncoveredSimpleFirst
    {letters : List Nat} {i s a : Nat}
    (twoLimited : ∀ t, letters.count t ≤ 2)
    (sCount : letters.count s = 1)
    (sAt : letters[i]? = some s)
    (aAt : letters[i + 1]? = some a)
    (aFirst : ∀ j, j < i + 1 → letters[j]? ≠ some a)
    (uncovered : ¬ CoveredAt letters i) :
    SemigroupBasis.Examples.UniqueSeparatorFourExactCut
      letters (letters.take i) s (letters.drop (i + 1)) := by
  obtain ⟨iInBounds, valueAtI⟩ :=
    List.getElem?_eq_some_iff.mp sAt
  obtain ⟨nextInBounds, valueAtNext⟩ :=
    List.getElem?_eq_some_iff.mp aAt
  have splitAtS :
      letters =
        letters.take i ++ s :: letters.drop (i + 1) := by
    calc
      letters = letters.take i ++ letters.drop i :=
        (List.take_append_drop i letters).symm
      _ = letters.take i ++ s :: letters.drop (i + 1) := by
        congr 1
        simpa [valueAtI] using
          List.drop_eq_getElem_cons iInBounds
  have dropAfterS :
      letters.drop (i + 1) =
        a :: letters.drop (i + 2) := by
    simpa [valueAtNext, Nat.add_assoc] using
      (List.drop_eq_getElem_cons nextInBounds)
  have splitAtSite :
      letters =
        letters.take i ++ s :: a :: letters.drop (i + 2) := by
    calc
      letters =
          letters.take i ++ s :: letters.drop (i + 1) :=
        splitAtS
      _ =
          letters.take i ++ s :: a :: letters.drop (i + 2) := by
        rw [dropAfterS]
  refine ⟨splitAtS, sCount, ?_⟩
  intro g beforeMember afterMember
  rw [dropAfterS] at afterMember
  simp only [List.mem_cons] at afterMember
  rcases afterMember with gEqualsA | futureMember
  · subst g
    obtain ⟨pre, preInBounds, valueAtPre⟩ :=
      List.mem_take_iff_getElem.mp beforeMember
    have preValue : letters[pre]? = some a :=
      List.getElem?_eq_some_iff.mpr
        ⟨by omega, valueAtPre⟩
    exact (aFirst pre (by omega)) preValue
  · apply uncovered
    obtain ⟨pre, preInBounds, valueAtPre⟩ :=
      List.mem_take_iff_getElem.mp beforeMember
    obtain ⟨offset, postInBounds, valueAtPost⟩ :=
      List.mem_drop_iff_getElem.mp futureMember
    have beforePositive :
        0 < (letters.take i).count g :=
      List.count_pos_iff.mpr beforeMember
    have afterPositive :
        0 < (letters.drop (i + 2)).count g :=
      List.count_pos_iff.mpr futureMember
    have countTwo : letters.count g = 2 := by
      apply Nat.le_antisymm (twoLimited g)
      rw [splitAtSite, List.count_append]
      simp only [List.count_cons]
      omega
    refine
      ⟨g, pre, i + 2 + offset, countTwo, ?_, ?_, ?_, ?_, ?_⟩
    · omega
    · omega
    · omega
    · exact
        List.getElem?_eq_some_iff.mpr
          ⟨by omega, valueAtPre⟩
    · exact
        List.getElem?_eq_some_iff.mpr
          ⟨by omega, valueAtPost⟩

/-- At an uncovered adjacent simple/first site, every word with the same
joint signature places the simple letter before the first occurrence of the
quadratic letter. -/
theorem forcedDirection : ForcedDirection := by
  intro left right i s a same leftTwo _rightTwo
    sCount aCount sAt aAt aFirst uncovered
  have sourceCut :=
    exactCutAtUncoveredSimpleFirst
      leftTwo sCount sAt aAt aFirst uncovered
  have sourceSignature :
      SemigroupBasis.CoRoots.S5_378.ExactCutSignature
        left s (left.toList.take i) (left.toList.drop (i + 1)) :=
    ⟨left.toList.take i, left.toList.drop (i + 1),
      sourceCut, fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  have targetSignature :
      SemigroupBasis.CoRoots.S5_378.ExactCutSignature
        right s (left.toList.take i) (left.toList.drop (i + 1)) :=
    (same.separator.exactCuts
      s (left.toList.take i) (left.toList.drop (i + 1))).mp
        sourceSignature
  obtain
    ⟨targetLeft, targetRight, targetCut,
      targetLeftSupport, targetRightSupport⟩ :=
    targetSignature
  obtain ⟨nextInBounds, valueAtNext⟩ :=
    List.getElem?_eq_some_iff.mp aAt
  have sourceAOnRight :
      a ∈ left.toList.drop (i + 1) := by
    apply List.mem_drop_iff_getElem.mpr
    refine ⟨0, ?_, ?_⟩
    · omega
    · simpa using valueAtNext
  have targetAOnRight : a ∈ targetRight :=
    (targetRightSupport a).mpr sourceAOnRight
  have targetANotLeft : a ∉ targetLeft := by
    intro targetAOnLeft
    exact targetCut.2.2 a targetAOnLeft targetAOnRight
  have targetSNotLeft : s ∉ targetLeft :=
    exactCut_separator_not_left targetCut
  have different : s ≠ a := by
    intro equality
    have impossible : (1 : Nat) = 2 := by
      calc
        1 = left.toList.count s := sCount.symm
        _ = left.toList.count a := congrArg (left.toList.count) equality
        _ = 2 := aCount
    omega
  rw [targetCut.1]
  simp only [List.idxOf_append]
  rw [if_neg targetSNotLeft, if_neg targetANotLeft]
  simp only [List.idxOf_cons, cond_eq_ite, beq_iff_eq]
  simp only [if_true, if_neg different]
  omega

end SemigroupBasis.CoRoots.Order6FactorPairS4_69S4_71
