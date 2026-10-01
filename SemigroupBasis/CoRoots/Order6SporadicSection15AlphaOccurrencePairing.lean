import SemigroupBasis.CoRoots.Order6SporadicSection15AlphaPairMoves

namespace SemigroupBasis.CoRoots.Order6SporadicSection15

/-! ## Pairing twice-occurring alpha markers

This file isolates the occurrence-pairing step of the alpha argument.  Marker
labels occupy fixed positional slots and arbitrary marker-free gaps occupy the
spaces after those slots.  The three placements of (15.1b) interchange two
adjacent marker slots while leaving their intervening gap fixed.

The terminal theorem recursively exposes the second copy of the first marker,
removes those two marker slots, and continues on the remaining marker list.
It does not sort the resulting pairs, compact simple gaps, or claim alpha
normalization.
-/

namespace AlphaOccurrencePairing

/-- Render marker labels into fixed positional gaps.  A balanced input has one
gap after every marker.  The truncating fallback makes the helper total; every
public derivation theorem below requires balanced lengths. -/
def renderMarkerGaps : List Nat -> List (List Nat) -> List Nat
  | marker :: markers, gap :: gaps =>
      [marker] ++ gap ++ renderMarkerGaps markers gaps
  | _, _ => []

/-- Every marker label is absent from every positional gap.  In the intended
alpha application the gaps are runs of globally simple letters. -/
def MarkerFreeGaps (markers : List Nat) (gaps : List (List Nat)) : Prop :=
  forall marker, marker ∈ markers ->
    forall gap, gap ∈ gaps -> marker ∉ gap

/-- Every displayed marker occurs exactly twice among the marker slots. -/
def TwiceOccurringMarkers (markers : List Nat) : Prop :=
  forall marker, marker ∈ markers -> markers.count marker = 2

/-- A marker list has been paired when it is a concatenation of adjacent
equal pairs.  Distinctness of pair labels follows separately from exact source
multiplicity and permutation preservation. -/
inductive PairedMarkerList : List Nat -> Prop
  | nil : PairedMarkerList []
  | pair (marker : Nat) {rest : List Nat} :
      PairedMarkerList rest ->
        PairedMarkerList (marker :: marker :: rest)

/-- Recursively place the second occurrence of the head marker immediately
after the head.  The absent branch keeps a singleton unchanged, making the
function total outside the exact-twice domain. -/
def pairMarkerOccurrences : List Nat -> List Nat
  | [] => []
  | marker :: rest =>
      if present : marker ∈ rest then
        marker :: marker :: pairMarkerOccurrences (rest.erase marker)
      else
        marker :: pairMarkerOccurrences rest
termination_by markers => markers.length
decreasing_by
  · have eraseLength := List.length_erase_of_mem (by assumption)
    simp only [List.length_cons]
    omega
  · simp

/-- Pairing only permutes marker occurrences. -/
theorem pairMarkerOccurrences_perm :
    forall markers : List Nat,
      markers.Perm (pairMarkerOccurrences markers)
  | [] => by
      simpa only [pairMarkerOccurrences] using
        (List.Perm.nil : ([] : List Nat).Perm [])
  | marker :: rest => by
      rw [pairMarkerOccurrences]
      split
      next present =>
        have expose : rest.Perm (marker :: rest.erase marker) :=
          List.perm_cons_erase present
        have recurse := pairMarkerOccurrences_perm (rest.erase marker)
        exact (List.Perm.cons marker expose).trans
          (List.Perm.cons marker (List.Perm.cons marker recurse))
      next absent =>
        exact List.Perm.cons marker (pairMarkerOccurrences_perm rest)
termination_by markers => markers.length
decreasing_by
  · simp
  · have eraseLength := List.length_erase_of_mem (by assumption)
    simp only [List.length_cons]
    omega

/-- Exact-twice input makes the total pairing function land in adjacent
pairs; the singleton fallback is unreachable. -/
theorem pairMarkerOccurrences_paired :
    forall markers : List Nat,
      TwiceOccurringMarkers markers ->
        PairedMarkerList (pairMarkerOccurrences markers)
  | [], _ => by
      simpa [pairMarkerOccurrences] using PairedMarkerList.nil
  | marker :: rest, twice => by
      have markerCount : (marker :: rest).count marker = 2 :=
        twice marker (by simp)
      have restCount : rest.count marker = 1 := by
        simpa using markerCount
      have present : marker ∈ rest :=
        List.count_pos_iff.mp (by omega)
      have markerGone : marker ∉ rest.erase marker := by
        rw [← List.count_eq_zero]
        rw [List.count_erase_self, restCount]
      have reducedTwice :
          TwiceOccurringMarkers (rest.erase marker) := by
        intro tested testedIn
        have testedInRest : tested ∈ rest :=
          List.mem_of_mem_erase testedIn
        have different : tested ≠ marker := by
          intro equal
          subst tested
          exact markerGone testedIn
        have sourceCount : (marker :: rest).count tested = 2 :=
          twice tested (by simp [testedInRest])
        have restTestedCount : rest.count tested = 2 := by
          simpa [List.count_cons_of_ne (Ne.symm different)] using
            sourceCount
        rw [List.count_erase_of_ne different]
        exact restTestedCount
      rw [pairMarkerOccurrences]
      rw [dif_pos present]
      exact PairedMarkerList.pair marker
        (pairMarkerOccurrences_paired (rest.erase marker) reducedTwice)
termination_by markers _ => markers.length
decreasing_by
  have eraseLength := List.length_erase_of_mem present
  simp only [List.length_cons]
  omega

/-- Flatten the fixed positional gaps without their marker slots. -/
def markerGapLetters (gaps : List (List Nat)) : List Nat :=
  gaps.flatten

/-- The renderer's occurrence count is the sum of the marker-slot count and
the count contributed by the fixed gaps. -/
theorem count_renderMarkerGaps
    (markers : List Nat) (gaps : List (List Nat))
    (balanced : gaps.length = markers.length) (tested : Nat) :
    (renderMarkerGaps markers gaps).count tested =
      markers.count tested + (markerGapLetters gaps).count tested := by
  induction markers generalizing gaps with
  | nil =>
      have gapsEmpty : gaps = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using balanced
      subst gaps
      simp [renderMarkerGaps, markerGapLetters]
  | cons marker markers induction =>
      cases gaps with
      | nil =>
          simp at balanced
      | cons gap gaps =>
          have tailBalanced : gaps.length = markers.length := by
            simpa using balanced
          have tailCount := induction gaps tailBalanced
          simp only [renderMarkerGaps, markerGapLetters,
            List.flatten_cons, List.count_append, List.count_cons,
            List.count_nil, tailCount]
          omega

/-- The marker contribution is bounded by the occurrence count in the full
rendering. -/
theorem marker_count_le_renderMarkerGaps
    (markers : List Nat) (gaps : List (List Nat))
    (balanced : gaps.length = markers.length) (tested : Nat) :
    markers.count tested <= (renderMarkerGaps markers gaps).count tested := by
  rw [count_renderMarkerGaps markers gaps balanced tested]
  omega

/-- Permuting marker labels against fixed balanced gaps preserves every total
rendered occurrence count. -/
theorem renderMarkerGaps_count_eq_of_perm
    (gaps : List (List Nat)) {source target : List Nat}
    (balanced : gaps.length = source.length)
    (permutation : source.Perm target) (tested : Nat) :
    (renderMarkerGaps source gaps).count tested =
      (renderMarkerGaps target gaps).count tested := by
  have targetBalanced : gaps.length = target.length :=
    balanced.trans permutation.length_eq
  rw [count_renderMarkerGaps source gaps balanced tested,
    count_renderMarkerGaps target gaps targetBalanced tested,
    List.perm_iff_count.mp permutation tested]

/-! ### A gap-preserving adjacent marker swap -/

/-- Swap two adjacent marker slots while retaining the complete gap between
them.  Each marker has another occurrence in an outer context; marker-freeness
of the intervening gap is what forces those witnesses outside the selected
interval.  The four witness-location cases use the left, middle, or right
placement of (15.1b). -/
theorem listDerivesSwapSeparatedNonsimpleMarkers
    (stem gap suffix : List Nat) (left right : Nat)
    (leftGapFree : left ∉ gap) (rightGapFree : right ∉ gap)
    (leftNonsimple :
      2 <= (stem ++ [left] ++ gap ++ [right] ++ suffix).count left)
    (rightNonsimple :
      2 <= (stem ++ [left] ++ gap ++ [right] ++ suffix).count right) :
    ListDerives
      (stem ++ [left] ++ gap ++ [right] ++ suffix)
      (stem ++ [right] ++ gap ++ [left] ++ suffix) := by
  by_cases equal : left = right
  · subst right
    exact S5_107.ListDerives.refl _
  · have leftSide : left ∈ stem ∨ left ∈ suffix := by
      by_cases inPrefix : left ∈ stem
      · exact Or.inl inPrefix
      · right
        apply List.count_pos_iff.mp
        have prefixZero : stem.count left = 0 :=
          List.count_eq_zero.mpr inPrefix
        have gapZero : gap.count left = 0 :=
          List.count_eq_zero.mpr leftGapFree
        have countShape :
            (stem ++ [left] ++ gap ++ [right] ++ suffix).count left =
              1 + suffix.count left := by
          simp [List.count_append, prefixZero, gapZero,
            equal, Ne.symm equal, Nat.add_comm]
        rw [countShape] at leftNonsimple
        omega
    have rightSide : right ∈ stem ∨ right ∈ suffix := by
      by_cases inPrefix : right ∈ stem
      · exact Or.inl inPrefix
      · right
        apply List.count_pos_iff.mp
        have prefixZero : stem.count right = 0 :=
          List.count_eq_zero.mpr inPrefix
        have gapZero : gap.count right = 0 :=
          List.count_eq_zero.mpr rightGapFree
        have countShape :
            (stem ++ [left] ++ gap ++ [right] ++ suffix).count right =
              1 + suffix.count right := by
          simp [List.count_append, prefixZero, gapZero,
            equal, Ne.symm equal, Nat.add_comm]
        rw [countShape] at rightNonsimple
        omega
    rcases leftSide with leftInPrefix | leftInSuffix
    · obtain ⟨leftBefore, leftAfter, prefixSplit⟩ :=
        List.mem_iff_append.mp leftInPrefix
      rcases rightSide with rightInPrefix | rightInSuffix
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
        · obtain ⟨before, middle, beforeSplit⟩ :=
            List.mem_iff_append.mp rightBefore
          have displayed :=
            listDerives15_1bRightSwap
              before suffix right left middle leftAfter gap
          simpa [prefixSplit, beforeSplit, List.append_assoc] using
            displayed.symm
        · obtain ⟨middle, tail, afterSplit⟩ :=
            List.mem_iff_append.mp rightAfter
          simpa [prefixSplit, afterSplit, List.append_assoc] using
            listDerives15_1bRightSwap
              leftBefore suffix left right middle tail gap
      · obtain ⟨rightBefore, rightAfter, suffixSplit⟩ :=
          List.mem_iff_append.mp rightInSuffix
        have displayed :=
          listDerives15_1bMiddleSwap
            leftBefore rightAfter left right leftAfter gap rightBefore
        simpa [prefixSplit, suffixSplit, List.append_assoc] using
          displayed.symm
    · obtain ⟨leftBefore, leftAfter, suffixSplit⟩ :=
        List.mem_iff_append.mp leftInSuffix
      rcases rightSide with rightInPrefix | rightInSuffix
      · obtain ⟨rightBefore, rightAfter, prefixSplit⟩ :=
          List.mem_iff_append.mp rightInPrefix
        simpa [prefixSplit, suffixSplit, List.append_assoc] using
          listDerives15_1bMiddleSwap
            rightBefore leftAfter right left rightAfter gap leftBefore
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
        · obtain ⟨before, middle, beforeSplit⟩ :=
            List.mem_iff_append.mp rightBefore
          have displayed :=
            listDerives15_1bLeftSwap
              stem leftAfter right left gap before middle
          simpa [suffixSplit, beforeSplit, List.append_assoc] using
            displayed.symm
        · obtain ⟨middle, after, afterSplit⟩ :=
            List.mem_iff_append.mp rightAfter
          simpa [suffixSplit, afterSplit, List.append_assoc] using
            listDerives15_1bLeftSwap
              stem after left right gap leftBefore middle

/-! ### Permutation closure for fixed marker slots -/

/-- Any permutation of globally nonsimple marker slots is derivable while all
positional gaps remain fixed.  The marker-free predicate is invariant under
the label permutation. -/
theorem listDerivesPermuteMarkerGaps
    (before after : List Nat) (gaps : List (List Nat))
    {source target : List Nat}
    (balanced : gaps.length = source.length)
    (markerFree : MarkerFreeGaps source gaps)
    (nonsimple :
      forall marker, marker ∈ source ->
        2 <= (before ++ renderMarkerGaps source gaps ++ after).count marker)
    (permutation : source.Perm target) :
    ListDerives
      (before ++ renderMarkerGaps source gaps ++ after)
      (before ++ renderMarkerGaps target gaps ++ after) := by
  induction permutation generalizing before gaps with
  | nil =>
      have gapsEmpty : gaps = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using balanced
      subst gaps
      simpa [renderMarkerGaps, pairMarkerOccurrences] using
        (S5_107.ListDerives.refl (before ++ after) :
          ListDerives (before ++ after) (before ++ after))
  | @cons head source target permutation induction =>
      cases gaps with
      | nil =>
          simp at balanced
      | cons gap gaps =>
          have tailBalanced : gaps.length = source.length := by
            simpa using balanced
          have tailMarkerFree : MarkerFreeGaps source gaps := by
            intro marker markerIn currentGap gapIn
            exact markerFree marker (List.Mem.tail head markerIn)
              currentGap (List.Mem.tail gap gapIn)
          have tailNonsimple :
              forall marker, marker ∈ source ->
                2 <=
                  ((before ++ [head] ++ gap) ++
                    renderMarkerGaps source gaps ++ after).count marker := by
            intro marker markerIn
            have bound := nonsimple marker (List.Mem.tail head markerIn)
            simpa [renderMarkerGaps, List.append_assoc] using bound
          have tailDerivation := induction
            (before ++ [head] ++ gap) gaps tailBalanced
            tailMarkerFree tailNonsimple
          simpa [renderMarkerGaps, List.append_assoc] using tailDerivation
  | swap first second rest =>
      cases gaps with
      | nil =>
          simp at balanced
      | cons firstGap remaining =>
          cases remaining with
          | nil =>
              simp at balanced
          | cons secondGap gaps =>
              have firstGapFree : second ∉ firstGap :=
                markerFree second (by simp) firstGap (by simp)
              have secondGapFree : first ∉ firstGap :=
                markerFree first (by simp) firstGap (by simp)
              have secondBound := nonsimple second (by simp)
              have firstBound := nonsimple first (by simp)
              simpa [renderMarkerGaps, List.append_assoc] using
                listDerivesSwapSeparatedNonsimpleMarkers
                  before
                  firstGap
                  (secondGap ++ renderMarkerGaps rest gaps ++ after)
                  second first firstGapFree secondGapFree
                  (by
                    simpa [renderMarkerGaps, List.append_assoc] using
                      secondBound)
                  (by
                    simpa [renderMarkerGaps, List.append_assoc] using
                      firstBound)
  | @trans source middle target firstPermutation secondPermutation
      firstInduction secondInduction =>
      have firstDerivation := firstInduction before gaps balanced
        markerFree nonsimple
      have middleBalanced : gaps.length = middle.length :=
        balanced.trans firstPermutation.length_eq
      have middleMarkerFree : MarkerFreeGaps middle gaps := by
        intro marker markerIn gap gapIn
        have sourceIn : marker ∈ source :=
          (firstPermutation.mem_iff).mpr markerIn
        exact markerFree marker sourceIn gap gapIn
      have middleNonsimple :
          forall marker, marker ∈ middle ->
            2 <=
              (before ++ renderMarkerGaps middle gaps ++ after).count marker := by
        intro marker markerIn
        have sourceIn : marker ∈ source :=
          (firstPermutation.mem_iff).mpr markerIn
        have bound := nonsimple marker sourceIn
        have renderedCount :=
          renderMarkerGaps_count_eq_of_perm gaps balanced
            firstPermutation marker
        simp only [List.count_append] at bound |-
        omega
      exact firstDerivation.trans
        (secondInduction before gaps middleBalanced
          middleMarkerFree middleNonsimple)

/-! ### Recursive occurrence pairing -/

/-- Pair every exact-twice marker sequence against its original positional
gaps.  At each recursive step `perm_cons_erase` exposes the second occurrence
of the first marker; `listDerivesPermuteMarkerGaps` realizes that exposure by
the gap-preserving (15.1b) swaps above.  The recursive call removes the two
newly paired marker slots, so the marker-count measure strictly decreases.
-/
theorem listDerivesPairMarkerOccurrences :
    forall (before after markers : List Nat) (gaps : List (List Nat)),
      gaps.length = markers.length ->
      TwiceOccurringMarkers markers ->
      MarkerFreeGaps markers gaps ->
      ListDerives
        (before ++ renderMarkerGaps markers gaps ++ after)
        (before ++
          renderMarkerGaps (pairMarkerOccurrences markers) gaps ++ after)
  | before, after, [], gaps, balanced, _, _ => by
      have gapsEmpty : gaps = [] := by
        apply List.eq_nil_of_length_eq_zero
        simpa using balanced
      subst gaps
      simpa [renderMarkerGaps, pairMarkerOccurrences] using
        (S5_107.ListDerives.refl (before ++ after) :
          ListDerives (before ++ after) (before ++ after))
  | before, after, marker :: rest, gaps, balanced, twice, markerFree => by
      have markerCount : (marker :: rest).count marker = 2 :=
        twice marker (by simp)
      have restCount : rest.count marker = 1 := by
        simpa using markerCount
      have present : marker ∈ rest :=
        List.count_pos_iff.mp (by omega)
      cases gaps with
      | nil =>
          simp at balanced
      | cons firstGap remainingGaps =>
          cases remainingGaps with
          | nil =>
              have restEmpty : rest = [] := by
                have restLength : rest.length = 0 := by
                  simp only [List.length_cons, List.length_nil] at balanced
                  omega
                apply List.eq_nil_of_length_eq_zero
                exact restLength
              subst rest
              simp at present
          | cons secondGap tailGaps =>
              have eraseLength := List.length_erase_of_mem present
              have tailBalanced :
                  tailGaps.length = (rest.erase marker).length := by
                have balancedLengths := balanced
                simp only [List.length_cons] at balancedLengths
                omega
              have markerGone : marker ∉ rest.erase marker := by
                rw [← List.count_eq_zero]
                rw [List.count_erase_self, restCount]
              have reducedTwice :
                  TwiceOccurringMarkers (rest.erase marker) := by
                intro tested testedIn
                have testedInRest : tested ∈ rest :=
                  List.mem_of_mem_erase testedIn
                have different : tested ≠ marker := by
                  intro equal
                  subst tested
                  exact markerGone testedIn
                have sourceCount :
                    (marker :: rest).count tested = 2 :=
                  twice tested (by simp [testedInRest])
                have restTestedCount : rest.count tested = 2 := by
                  simpa [List.count_cons_of_ne (Ne.symm different)] using
                    sourceCount
                rw [List.count_erase_of_ne different]
                exact restTestedCount
              have reducedMarkerFree :
                  MarkerFreeGaps (rest.erase marker) tailGaps := by
                intro tested testedIn gap gapIn
                exact markerFree tested
                  (List.Mem.tail marker (List.mem_of_mem_erase testedIn))
                  gap (by simp [gapIn])
              have sourceNonsimple :
                  forall tested, tested ∈ marker :: rest ->
                    2 <=
                      (before ++
                        renderMarkerGaps (marker :: rest)
                          (firstGap :: secondGap :: tailGaps) ++
                        after).count tested := by
                intro tested testedIn
                have exactCount := twice tested testedIn
                have renderBound := marker_count_le_renderMarkerGaps
                  (marker :: rest) (firstGap :: secondGap :: tailGaps)
                  balanced tested
                simp only [List.count_append]
                omega
              have exposePermutation :
                  (marker :: rest).Perm
                    (marker :: marker :: rest.erase marker) :=
                List.Perm.cons marker (List.perm_cons_erase present)
              have expose := listDerivesPermuteMarkerGaps
                before after (firstGap :: secondGap :: tailGaps)
                balanced markerFree sourceNonsimple exposePermutation
              have recurse := listDerivesPairMarkerOccurrences
                (before ++ [marker] ++ firstGap ++ [marker] ++ secondGap)
                after (rest.erase marker) tailGaps tailBalanced
                reducedTwice reducedMarkerFree
              have exposed :
                  ListDerives
                    (before ++
                      renderMarkerGaps (marker :: rest)
                        (firstGap :: secondGap :: tailGaps) ++ after)
                    (before ++ [marker] ++ firstGap ++ [marker] ++
                      secondGap ++ renderMarkerGaps (rest.erase marker)
                        tailGaps ++ after) := by
                simpa [renderMarkerGaps, List.append_assoc] using expose
              have combined := exposed.trans recurse
              simpa [renderMarkerGaps, pairMarkerOccurrences, present,
                List.append_assoc] using combined
termination_by _ _ markers _ _ _ _ => markers.length
decreasing_by
  have eraseLength := List.length_erase_of_mem present
  simp only [List.length_cons] at balanced ⊢
  omega

end AlphaOccurrencePairing

end SemigroupBasis.CoRoots.Order6SporadicSection15
