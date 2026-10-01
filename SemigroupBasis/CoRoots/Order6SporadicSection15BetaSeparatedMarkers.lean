import SemigroupBasis.CoRoots.Order6SporadicSection15AlphaMoves

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

open SemigroupBasis

/-! ## Swapping separated nonsimple markers

The three placements of (15.1b) connect all six orders of two displayed
copies of `x` and two displayed copies of `y`.  Crucially, the three lists
between the displayed occurrences are left in their physical slots.  After
one additional occurrence of each marker has been selected, this finite
calculation swaps `x` and `y` across an arbitrary middle list.

This module does not use the completeness theorem or any semantic argument.
The multiplicity hypotheses are discharged solely by locating the two extra
displayed occurrences, and every equational step is an instance of (15.1b).
-/

/-- The six possible orders of two `x` markers and two `y` markers. -/
inductive FourMarkerShape where
  | xxyy
  | xyxy
  | xyyx
  | yxxy
  | yxyx
  | yyxx
  deriving DecidableEq

/-- Render four markers while keeping all three intervening lists fixed. -/
def renderFourMarkerShape
    (shape : FourMarkerShape)
    (x y : Nat) (h k t : List Nat) : List Nat :=
  match shape with
  | .xxyy => [x] ++ h ++ [x] ++ k ++ [y] ++ t ++ [y]
  | .xyxy => [x] ++ h ++ [y] ++ k ++ [x] ++ t ++ [y]
  | .xyyx => [x] ++ h ++ [y] ++ k ++ [y] ++ t ++ [x]
  | .yxxy => [y] ++ h ++ [x] ++ k ++ [x] ++ t ++ [y]
  | .yxyx => [y] ++ h ++ [x] ++ k ++ [y] ++ t ++ [x]
  | .yyxx => [y] ++ h ++ [y] ++ k ++ [x] ++ t ++ [x]

/-- Every four-marker order is derivable from the alternating order.  This
is the narrow Section 15 analogue of the attachment-shape calculation used
for `S5_107`, but it depends only on the typed (15.1b) moves. -/
theorem listDerivesFourMarkerFromAlternating
    (shape : FourMarkerShape)
    (x y : Nat) (h k t : List Nat) :
    ListDerives
      (renderFourMarkerShape .xyxy x y h k t)
      (renderFourMarkerShape shape x y h k t) := by
  have toXyyx :
      ListDerives
        (renderFourMarkerShape .xyxy x y h k t)
        (renderFourMarkerShape .xyyx x y h k t) := by
    simpa [renderFourMarkerShape, List.append_assoc] using
      listDerives15_1bRightSwap [] [] x y h k t
  have fromYxyx :
      ListDerives
        (renderFourMarkerShape .yxyx x y h k t)
        (renderFourMarkerShape .xyyx x y h k t) := by
    simpa [renderFourMarkerShape, List.append_assoc] using
      listDerives15_1bLeftSwap [] [] y x h k t
  have toYxyx :
      ListDerives
        (renderFourMarkerShape .xyxy x y h k t)
        (renderFourMarkerShape .yxyx x y h k t) :=
    toXyyx.trans fromYxyx.symm
  cases shape with
  | xyxy =>
      exact S5_107.ListDerives.refl _
  | yxxy =>
      simpa [renderFourMarkerShape, List.append_assoc] using
        listDerives15_1bLeftSwap [] [] x y h k t
  | xxyy =>
      simpa [renderFourMarkerShape, List.append_assoc] using
        listDerives15_1bMiddleSwap [] [] x y h k t
  | xyyx =>
      exact toXyyx
  | yxyx =>
      exact toYxyx
  | yyxx =>
      exact toYxyx.trans (by
        simpa [renderFourMarkerShape, List.append_assoc] using
          listDerives15_1bMiddleSwap [] [] y x h k t)

/-- Any two orders of the same four displayed markers are mutually
derivable without changing the three intervening lists. -/
theorem listDerivesFourMarkerShapes
    (source target : FourMarkerShape)
    (x y : Nat) (h k t : List Nat) :
    ListDerives
      (renderFourMarkerShape source x y h k t)
      (renderFourMarkerShape target x y h k t) :=
  (listDerivesFourMarkerFromAlternating
      source x y h k t).symm.trans
    (listDerivesFourMarkerFromAlternating
      target x y h k t)

/-- If the selected occurrence of `selected` is the only one displayed
outside three regions, global multiplicity forces another occurrence into
one of those regions. -/
private theorem extraFirstMarker_mem_regions
    (before middle after : List Nat)
    (selected other : Nat)
    (different : selected ≠ other)
    (multiple :
      2 <=
        (before ++ [selected] ++ middle ++ [other] ++ after).count
          selected) :
    selected ∈ before ∨ selected ∈ middle ∨ selected ∈ after := by
  apply Decidable.byContradiction
  intro absent
  have beforeAbsent : selected ∉ before := by
    intro member
    exact absent (Or.inl member)
  have middleAbsent : selected ∉ middle := by
    intro member
    exact absent (Or.inr (Or.inl member))
  have afterAbsent : selected ∉ after := by
    intro member
    exact absent (Or.inr (Or.inr member))
  have beforeZero : before.count selected = 0 :=
    List.count_eq_zero.mpr beforeAbsent
  have middleZero : middle.count selected = 0 :=
    List.count_eq_zero.mpr middleAbsent
  have afterZero : after.count selected = 0 :=
    List.count_eq_zero.mpr afterAbsent
  have countOne :
      (before ++ [selected] ++ middle ++ [other] ++ after).count
          selected = 1 := by
    simp [List.count_append, beforeZero, middleZero, afterZero,
      different, Ne.symm different]
  omega

/-- The symmetric count calculation when the selected occurrence is the
second displayed marker rather than the first. -/
private theorem extraSecondMarker_mem_regions
    (before middle after : List Nat)
    (other selected : Nat)
    (different : other ≠ selected)
    (multiple :
      2 <=
        (before ++ [other] ++ middle ++ [selected] ++ after).count
          selected) :
    selected ∈ before ∨ selected ∈ middle ∨ selected ∈ after := by
  apply Decidable.byContradiction
  intro absent
  have beforeAbsent : selected ∉ before := by
    intro member
    exact absent (Or.inl member)
  have middleAbsent : selected ∉ middle := by
    intro member
    exact absent (Or.inr (Or.inl member))
  have afterAbsent : selected ∉ after := by
    intro member
    exact absent (Or.inr (Or.inr member))
  have beforeZero : before.count selected = 0 :=
    List.count_eq_zero.mpr beforeAbsent
  have middleZero : middle.count selected = 0 :=
    List.count_eq_zero.mpr middleAbsent
  have afterZero : after.count selected = 0 :=
    List.count_eq_zero.mpr afterAbsent
  have countOne :
      (before ++ [other] ++ middle ++ [selected] ++ after).count
          selected = 1 := by
    simp [List.count_append, beforeZero, middleZero, afterZero,
      different]
  omega

/-- Swap two displayed nonsimple markers across an arbitrary middle list.
The two count hypotheses refer to the complete source word; the additional
occurrences may lie independently in the prefix, middle, or suffix. -/
theorem listDerivesSwapSeparatedNonsimple
    (stem middle suffix : List Nat) (left right : Nat)
    (leftNonsimple :
      2 <=
        (stem ++ [left] ++ middle ++ [right] ++ suffix).count left)
    (rightNonsimple :
      2 <=
        (stem ++ [left] ++ middle ++ [right] ++ suffix).count right) :
    ListDerives
      (stem ++ [left] ++ middle ++ [right] ++ suffix)
      (stem ++ [right] ++ middle ++ [left] ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact S5_107.ListDerives.refl _
  · have leftRegion :
        left ∈ stem ∨ left ∈ middle ∨ left ∈ suffix :=
      extraFirstMarker_mem_regions
        stem middle suffix left right equal leftNonsimple
    have rightRegion :
        right ∈ stem ∨ right ∈ middle ∨ right ∈ suffix :=
      extraSecondMarker_mem_regions
        stem middle suffix left right equal rightNonsimple
    rcases leftRegion with leftInPrefix | leftInMiddle | leftInSuffix
    · obtain ⟨leftBefore, leftAfter, prefixSplit⟩ :=
        List.mem_iff_append.mp leftInPrefix
      rcases rightRegion with rightInPrefix | rightInMiddle | rightInSuffix
      · have rightInSplit :
            right ∈ leftBefore ∨ right ∈ leftAfter := by
          rw [prefixSplit] at rightInPrefix
          rcases List.mem_append.mp rightInPrefix with
              beforeMember | afterMember
          · exact Or.inl beforeMember
          · rcases List.mem_cons.mp afterMember with atLeft | inAfter
            · exact False.elim (equal atLeft.symm)
            · exact Or.inr inAfter
        rcases rightInSplit with rightBefore | rightAfter
        · obtain ⟨before, between, beforeSplit⟩ :=
            List.mem_iff_append.mp rightBefore
          have core :=
            listDerivesFourMarkerShapes
              .yxxy .yxyx left right between leftAfter middle
          simpa [prefixSplit, beforeSplit, renderFourMarkerShape,
            List.append_assoc] using
              S5_107.ListDerives.context before suffix core
        · obtain ⟨between, after, afterSplit⟩ :=
            List.mem_iff_append.mp rightAfter
          have core :=
            listDerivesFourMarkerShapes
              .xyxy .xyyx left right between after middle
          simpa [prefixSplit, afterSplit, renderFourMarkerShape,
            List.append_assoc] using
              S5_107.ListDerives.context leftBefore suffix core
      · obtain ⟨middleBefore, middleAfter, middleSplit⟩ :=
          List.mem_iff_append.mp rightInMiddle
        have core :=
          listDerivesFourMarkerShapes
            .xxyy .xyyx left right leftAfter middleBefore middleAfter
        simpa [prefixSplit, middleSplit, renderFourMarkerShape,
          List.append_assoc] using
            S5_107.ListDerives.context leftBefore suffix core
      · obtain ⟨suffixBefore, suffixAfter, suffixSplit⟩ :=
          List.mem_iff_append.mp rightInSuffix
        have core :=
          listDerivesFourMarkerShapes
            .xxyy .xyxy left right leftAfter middle suffixBefore
        simpa [prefixSplit, suffixSplit, renderFourMarkerShape,
          List.append_assoc] using
            S5_107.ListDerives.context leftBefore suffixAfter core
    · obtain ⟨leftBefore, leftAfter, middleSplit⟩ :=
        List.mem_iff_append.mp leftInMiddle
      rcases rightRegion with rightInPrefix | rightInMiddle | rightInSuffix
      · obtain ⟨rightBefore, rightAfter, prefixSplit⟩ :=
          List.mem_iff_append.mp rightInPrefix
        have core :=
          listDerivesFourMarkerShapes
            .yxxy .yyxx left right rightAfter leftBefore leftAfter
        simpa [prefixSplit, middleSplit, renderFourMarkerShape,
          List.append_assoc] using
            S5_107.ListDerives.context rightBefore suffix core
      · have rightInSplit :
            right ∈ leftBefore ∨ right ∈ leftAfter := by
          rw [middleSplit] at rightInMiddle
          rcases List.mem_append.mp rightInMiddle with
              beforeMember | afterMember
          · exact Or.inl beforeMember
          · rcases List.mem_cons.mp afterMember with atLeft | inAfter
            · exact False.elim (equal atLeft.symm)
            · exact Or.inr inAfter
        rcases rightInSplit with rightBefore | rightAfter
        · obtain ⟨before, between, beforeSplit⟩ :=
            List.mem_iff_append.mp rightBefore
          have core :=
            listDerivesFourMarkerShapes
              .xyxy .yyxx left right before between leftAfter
          simpa [middleSplit, beforeSplit, renderFourMarkerShape,
            List.append_assoc] using
              S5_107.ListDerives.context stem suffix core
        · obtain ⟨between, after, afterSplit⟩ :=
            List.mem_iff_append.mp rightAfter
          have core :=
            listDerivesFourMarkerShapes
              .xxyy .yxyx left right leftBefore between after
          simpa [middleSplit, afterSplit, renderFourMarkerShape,
            List.append_assoc] using
              S5_107.ListDerives.context stem suffix core
      · obtain ⟨rightBefore, rightAfter, suffixSplit⟩ :=
          List.mem_iff_append.mp rightInSuffix
        have core :=
          listDerivesFourMarkerShapes
            .xxyy .yxxy left right leftBefore leftAfter rightBefore
        simpa [middleSplit, suffixSplit, renderFourMarkerShape,
          List.append_assoc] using
            S5_107.ListDerives.context stem rightAfter core
    · obtain ⟨leftBefore, leftAfter, suffixSplit⟩ :=
        List.mem_iff_append.mp leftInSuffix
      rcases rightRegion with rightInPrefix | rightInMiddle | rightInSuffix
      · obtain ⟨rightBefore, rightAfter, prefixSplit⟩ :=
          List.mem_iff_append.mp rightInPrefix
        have core :=
          listDerivesFourMarkerShapes
            .yxyx .yyxx left right rightAfter middle leftBefore
        simpa [prefixSplit, suffixSplit, renderFourMarkerShape,
          List.append_assoc] using
            S5_107.ListDerives.context rightBefore leftAfter core
      · obtain ⟨rightBefore, rightAfter, middleSplit⟩ :=
          List.mem_iff_append.mp rightInMiddle
        have core :=
          listDerivesFourMarkerShapes
            .xyyx .yyxx left right rightBefore rightAfter leftBefore
        simpa [middleSplit, suffixSplit, renderFourMarkerShape,
          List.append_assoc] using
            S5_107.ListDerives.context stem leftAfter core
      · have rightInSplit :
            right ∈ leftBefore ∨ right ∈ leftAfter := by
          rw [suffixSplit] at rightInSuffix
          rcases List.mem_append.mp rightInSuffix with
              beforeMember | afterMember
          · exact Or.inl beforeMember
          · rcases List.mem_cons.mp afterMember with atLeft | inAfter
            · exact False.elim (equal atLeft.symm)
            · exact Or.inr inAfter
        rcases rightInSplit with rightBefore | rightAfter
        · obtain ⟨before, between, beforeSplit⟩ :=
            List.mem_iff_append.mp rightBefore
          have core :=
            listDerivesFourMarkerShapes
              .xyyx .yxyx left right middle before between
          simpa [suffixSplit, beforeSplit, renderFourMarkerShape,
            List.append_assoc] using
              S5_107.ListDerives.context stem leftAfter core
        · obtain ⟨between, after, afterSplit⟩ :=
            List.mem_iff_append.mp rightAfter
          have core :=
            listDerivesFourMarkerShapes
              .xyxy .yxxy left right middle leftBefore between
          simpa [suffixSplit, afterSplit, renderFourMarkerShape,
            List.append_assoc] using
              S5_107.ListDerives.context stem after core

end SemigroupBasis.CoRoots.Order6SporadicSection15
