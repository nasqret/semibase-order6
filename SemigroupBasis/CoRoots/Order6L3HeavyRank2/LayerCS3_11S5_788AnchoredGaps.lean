import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_11S5_788NormalForm
import SemigroupBasis.CoRoots.Order6L3HeavyRank2.LayerCS3_11S5_788Condition14Transport

/-!
# Exact C2 anchored-gap moves

The four-step adjacent-envelope merge is witnessed entirely by the frozen
displayed-law macros.  A repeated endpoint also explicitly forbids an exact
separator cut, which is the invariant falsified by the previous C2 render.
-/

namespace SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_11S5_788

open SemigroupBasis
open SemigroupBasis.Examples

private theorem anchor_mem_left_of_split
    (anchor separator : Nat) (tail left right : List Nat)
    (different : anchor ≠ separator)
    (shape : anchor :: tail = left ++ separator :: right) :
    anchor ∈ left := by
  cases left with
  | nil =>
      have same : anchor = separator := by
        simpa using congrArg List.head? shape
      exact False.elim (different same)
  | cons first rest =>
      have same : anchor = first := by
        simpa using congrArg List.head? shape
      rw [same]
      exact List.Mem.head rest

/-- A gap bracketed by the same letter cannot contain an exact unique
separator: every interior split has that letter on both sides. -/
theorem noExactCut_closedAnchor
    (anchor : Nat) (interior : List Nat) :
    ¬ ∃ left separator right,
      UniqueSeparatorFourExactCut
        ([anchor] ++ interior ++ [anchor]) left separator right := by
  rintro ⟨left, separator, right, shape, countOne, disjoint⟩
  by_cases same : anchor = separator
  · subst separator
    simp only [List.count_append, List.count_singleton_self] at countOne
    omega
  · have leftMember : anchor ∈ left :=
      anchor_mem_left_of_split anchor separator
        (interior ++ [anchor]) left right same (by simpa using shape)
    have reversedShape :
        anchor :: (interior.reverse ++ [anchor]) =
          right.reverse ++ separator :: left.reverse := by
      simpa [List.reverse_append, List.append_assoc] using
        congrArg List.reverse shape
    have rightReverseMember : anchor ∈ right.reverse :=
      anchor_mem_left_of_split anchor separator
        (interior.reverse ++ [anchor]) right.reverse left.reverse
        same reversedShape
    have rightMember : anchor ∈ right := by
      simpa using rightReverseMember
    exact disjoint anchor leftMember rightMember

/-- The repaired gap renderer can never create a new exact separator cut,
even when an odd non-anchor letter is rendered only once. -/
theorem noExactCut_renderParitySeparatorInitialGap
    (initials : List Nat) (parity : Nat → Nat)
    (segment : UniqueSeparatorCanonicalSegment) :
    ¬ ∃ left separator right,
      UniqueSeparatorFourExactCut
        (renderParitySeparatorInitialGap initials parity segment)
        left separator right := by
  cases order : initials.filter
      (fun letter => decide (letter ∈ segment.quadratic)) with
  | nil =>
      simp [renderParitySeparatorInitialGap, order,
        UniqueSeparatorFourExactCut]
  | cons anchor remaining =>
      simpa [renderParitySeparatorInitialGap, order,
        List.append_assoc] using
        noExactCut_closedAnchor anchor
          ((if parity anchor = 0 then [] else [anchor]) ++
            remaining.flatMap (parityMultiplicityBlock parity))

/-- The nontrivial adjacent-envelope merge.  Its four typed intermediate
steps were found against the exact eighteen-law basis and then replayed
with arbitrary nonempty word substitutions. -/
theorem derivesMergeClosedEnvelopes
    (anchor leftInterior nextAnchor rightInterior : Word Nat) :
    Derives targetBasis
      (((((anchor ++ leftInterior) ++ anchor) ++ nextAnchor) ++
        rightInterior) ++ nextAnchor)
      (((((anchor ++ leftInterior) ++ nextAnchor) ++ rightInterior) ++
        nextAnchor) ++ anchor) := by
  have first :
      Derives targetBasis
        (((((anchor ++ leftInterior) ++ anchor) ++ nextAnchor) ++
          rightInterior) ++ nextAnchor)
        (((((((anchor ++ anchor) ++ leftInterior) ++ anchor) ++ anchor) ++
          nextAnchor) ++ rightInterior) ++ nextAnchor) := by
    simpa [Word.append_assoc] using
      (((derivesSplitEndpointContraction anchor leftInterior).symm.appendRight
        nextAnchor).appendRight rightInterior).appendRight nextAnchor
  have second :
      Derives targetBasis
        (((((((anchor ++ anchor) ++ leftInterior) ++ anchor) ++ anchor) ++
          nextAnchor) ++ rightInterior) ++ nextAnchor)
        (((((((anchor ++ anchor) ++ leftInterior) ++ anchor) ++ nextAnchor) ++
          rightInterior) ++ nextAnchor) ++ anchor) := by
    simpa [Word.append_assoc] using
      Derives.prepend ((anchor ++ anchor) ++ leftInterior)
        (derivesAttachmentTurn anchor nextAnchor rightInterior)
  have third :
      Derives targetBasis
        (((((((anchor ++ anchor) ++ leftInterior) ++ anchor) ++ nextAnchor) ++
          rightInterior) ++ nextAnchor) ++ anchor)
        (((((((anchor ++ anchor) ++ anchor) ++ leftInterior) ++ nextAnchor) ++
          rightInterior) ++ nextAnchor) ++ anchor) := by
    simpa [Word.append_assoc] using
      (derivesDoubledInitialClosedMove anchor
        (anchor ++ leftInterior)
        ((nextAnchor ++ rightInterior) ++ nextAnchor)).symm
  have fourth :
      Derives targetBasis
        (((((((anchor ++ anchor) ++ anchor) ++ leftInterior) ++ nextAnchor) ++
          rightInterior) ++ nextAnchor) ++ anchor)
        (((((anchor ++ leftInterior) ++ nextAnchor) ++ rightInterior) ++
          nextAnchor) ++ anchor) := by
    simpa [Word.append_assoc] using
      derivesTripleLeftContraction anchor
        (((leftInterior ++ nextAnchor) ++ rightInterior) ++ nextAnchor)
  exact first.trans (second.trans (third.trans fourth))

/-- Merge adjacent closed list envelopes, including all four empty-interior
cases, without introducing an empty semigroup-word substitution. -/
theorem listDerivesMergeClosedEnvelopes
    (anchor nextAnchor : Nat)
    (leftInterior rightInterior : List Nat) :
    SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis
      ([anchor] ++ leftInterior ++ [anchor] ++
        [nextAnchor] ++ rightInterior ++ [nextAnchor])
      ([anchor] ++ leftInterior ++ [nextAnchor] ++
        rightInterior ++ [nextAnchor] ++ [anchor]) := by
  cases leftInterior with
  | nil =>
      cases rightInterior with
      | nil =>
          simpa [Word.singleton, Word.append, Word.toList,
            List.append_assoc] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (derivesSquareFinalSwitch
                (Word.singleton anchor) (Word.singleton nextAnchor))
      | cons rightHead rightTail =>
          simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.singleton, Word.append, Word.toList,
            List.append_assoc] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (derivesAttachmentTurn
                (Word.singleton anchor)
                (Word.singleton nextAnchor)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons
                  rightHead rightTail))
  | cons leftHead leftTail =>
      cases rightInterior with
      | nil =>
          simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.singleton, Word.append, Word.toList,
            List.append_assoc] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (derivesFinalSquareTurn
                (Word.singleton anchor)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons
                  leftHead leftTail)
                (Word.singleton nextAnchor))
      | cons rightHead rightTail =>
          simpa [SemigroupBasis.CoRoots.S5_107.listWordOfCons,
            Word.singleton, Word.append, Word.toList,
            List.append_assoc] using
            SemigroupBasis.CoRoots.S5_107.ListDerives.ofWord
              (derivesMergeClosedEnvelopes
                (Word.singleton anchor)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons
                  leftHead leftTail)
                (Word.singleton nextAnchor)
                (SemigroupBasis.CoRoots.S5_107.listWordOfCons
                  rightHead rightTail))

/-- The old connected-component closing theorem is reused only through the
explicit six-axiom C2 transport bridge. -/
theorem existsClosedHeadDerivation_of_connected
    {head : Nat} {tail : List Nat}
    (connected : ConnectedComponentSupportConnected (head :: tail))
    (tailNonempty : tail ≠ []) :
    ∃ interior,
      SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis
        (head :: tail) ([head] ++ interior ++ [head]) := by
  obtain ⟨interior, derivation⟩ :=
    SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14.existsClosedHeadDerivation
      connected tailNonempty
  exact ⟨interior, transportCondition14ListDerives derivation⟩

private theorem existsClosedAnchor_of_components :
    ∀ (components : List (List Nat)),
      (∀ component ∈ components, 2 ≤ component.length) →
      (∀ component ∈ components,
        ConnectedComponentSupportConnected component) →
      components ≠ [] →
      ∃ anchor interior,
        SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis
          components.flatten ([anchor] ++ interior ++ [anchor]) := by
  intro components
  induction components with
  | nil =>
      intro _ _ nonempty
      exact False.elim (nonempty rfl)
  | cons component rest ih =>
      intro lengths connections _
      have firstLength : 2 ≤ component.length :=
        lengths component (by simp)
      have firstConnected :
          ConnectedComponentSupportConnected component :=
        connections component (by simp)
      cases component with
      | nil =>
          simp at firstLength
      | cons anchor tail =>
          have tailNonempty : tail ≠ [] := by
            intro empty
            simp [empty] at firstLength
          obtain ⟨firstInterior, firstDerivation⟩ :=
            existsClosedHeadDerivation_of_connected
              firstConnected tailNonempty
          cases rest with
          | nil =>
              exact ⟨anchor, firstInterior, by
                simpa using firstDerivation⟩
          | cons next remaining =>
              have restLengths :
                  ∀ candidate ∈ next :: remaining,
                    2 ≤ candidate.length := by
                intro candidate member
                exact lengths candidate (by simp [member])
              have restConnections :
                  ∀ candidate ∈ next :: remaining,
                    ConnectedComponentSupportConnected candidate := by
                intro candidate member
                exact connections candidate (by simp [member])
              obtain ⟨nextAnchor, nextInterior, restDerivation⟩ :=
                ih restLengths restConnections (by simp)
              have firstStep :
                  SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis
                    ((anchor :: tail) ++ (next :: remaining).flatten)
                    (([anchor] ++ firstInterior ++ [anchor]) ++
                      (next :: remaining).flatten) :=
                firstDerivation.append (next :: remaining).flatten
              have secondStep :
                  SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis
                    (([anchor] ++ firstInterior ++ [anchor]) ++
                      (next :: remaining).flatten)
                    (([anchor] ++ firstInterior ++ [anchor]) ++
                      ([nextAnchor] ++ nextInterior ++ [nextAnchor])) :=
                restDerivation.prepend
                  ([anchor] ++ firstInterior ++ [anchor])
              have thirdStep :
                  SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis
                    (([anchor] ++ firstInterior ++ [anchor]) ++
                      ([nextAnchor] ++ nextInterior ++ [nextAnchor]))
                    ([anchor] ++
                      (firstInterior ++ [nextAnchor] ++ nextInterior ++
                        [nextAnchor]) ++
                      [anchor]) := by
                simpa [List.append_assoc] using
                  listDerivesMergeClosedEnvelopes anchor nextAnchor
                    firstInterior nextInterior
              refine
                ⟨anchor,
                  firstInterior ++ [nextAnchor] ++ nextInterior ++
                    [nextAnchor],
                  ?_⟩
              simpa [List.append_assoc] using
                firstStep.trans (secondStep.trans thirdStep)

/-- Every nonempty exact-cut-free gap, including one with several mutually
disjoint support components, derives to one repeated-endpoint envelope. -/
theorem existsClosedAnchor_of_noExactCut
    {gap : List Nat}
    (nonempty : gap ≠ [])
    (noExactCut :
      ¬ ∃ left separator right,
        UniqueSeparatorFourExactCut gap left separator right) :
    ∃ anchor interior,
      SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis
        gap ([anchor] ++ interior ++ [anchor]) := by
  let components := connectedComponentDecomposeList gap
  have flattened : components.flatten = gap :=
    connectedComponentDecomposeList_flatten gap
  have componentsNonempty : components ≠ [] := by
    intro empty
    rw [empty] at flattened
    exact nonempty (by simpa using flattened.symm)
  obtain ⟨anchor, interior, derivation⟩ :=
    existsClosedAnchor_of_components components
      (SemigroupBasis.CoRoots.S5_441.connectedComponentDecomposeList_components_length_ge_two_of_no_exactCut
        noExactCut)
      (fun component member =>
        connectedComponentDecomposeList_supportConnected gap component member)
      componentsNonempty
  exact ⟨anchor, interior, by simpa [flattened] using derivation⟩

private theorem anchor_mem_nonempty_prefix
    {anchor : Nat} {tail left right : List Nat}
    (shape : anchor :: tail = left ++ right)
    (nonempty : left ≠ []) :
    anchor ∈ left := by
  cases left with
  | nil =>
      exact False.elim (nonempty rfl)
  | cons first rest =>
      have same : anchor = first := by
        simpa using congrArg List.head? shape
      rw [same]
      exact List.Mem.head rest

/-- Repeating one anchor at both ends joins every support component. -/
theorem closedAnchor_supportConnected
    (anchor : Nat) (interior : List Nat) :
    ConnectedComponentSupportConnected
      ([anchor] ++ interior ++ [anchor]) := by
  intro left right shape leftNonempty rightNonempty
  have leftMember : anchor ∈ left :=
    anchor_mem_nonempty_prefix
      (by simpa using shape) leftNonempty
  have reversedShape :
      anchor :: (interior.reverse ++ [anchor]) =
        right.reverse ++ left.reverse := by
    simpa [List.reverse_append, List.append_assoc] using
      congrArg List.reverse shape
  have rightReverseNonempty : right.reverse ≠ [] := by
    simpa using rightNonempty
  have rightMember : anchor ∈ right := by
    have reversedMember :=
      anchor_mem_nonempty_prefix reversedShape rightReverseNonempty
    simpa using reversedMember
  exact ⟨anchor, leftMember, rightMember⟩

private theorem firstOccurrenceSequence_filter_sortedSupport
    (letters : List Nat) :
    (firstOccurrenceSequence letters).filter
      (fun selected => decide
        (selected ∈ connectedComponentSortedSupport letters)) =
      firstOccurrenceSequence letters := by
  apply List.filter_eq_self.mpr
  intro selected member
  simp only [decide_eq_true_eq]
  exact
    (connectedComponentSortedSupport_mem_iff selected letters).mpr
      ((mem_firstOccurrenceSequence_iff selected letters).mp member)

private theorem parityPayloadBlocks_eq
    (source closed : List Nat) (anchor : Nat) (remaining : List Nat)
    (anchorAbsent : anchor ∉ remaining)
    (sameParity :
      ∀ letter, source.count letter % 2 = closed.count letter % 2) :
    remaining.flatMap
        (SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14.componentParityBlock
          closed anchor) =
      remaining.flatMap
        (parityMultiplicityBlock (fun letter => source.count letter % 2)) := by
  induction remaining with
  | nil =>
      rfl
  | cons letter rest ih =>
      have different : letter ≠ anchor := by
        intro same
        subst letter
        exact anchorAbsent (by simp)
      have absentRest : anchor ∉ rest := by
        intro member
        exact anchorAbsent (by simp [member])
      rw [List.flatMap_cons, List.flatMap_cons]
      have blockEq :
          SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14.componentParityBlock
              closed anchor letter =
            parityMultiplicityBlock
              (fun selected => source.count selected % 2) letter := by
        simp [SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14.componentParityBlock,
          parityMultiplicityBlock, different, ← sameParity letter]
      rw [blockEq, ih absentRest]

private theorem componentInitialParityRender_eq_gapRender
    (source closed : List Nat)
    (sameInitials :
      firstOccurrenceSequence source = firstOccurrenceSequence closed)
    (sameParity :
      ∀ letter, source.count letter % 2 = closed.count letter % 2)
    (closedLength : 2 ≤ closed.length) :
    SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14.componentInitialParityRender
        closed (firstOccurrenceSequence closed)
        (connectedComponentSignatureOfList closed) =
      renderParitySeparatorInitialGap
        (firstOccurrenceSequence source)
        (fun letter => source.count letter % 2)
        ⟨connectedComponentSortedSupport source, none⟩ := by
  have notSimple :
      ¬ ((connectedComponentSignatureOfList closed).support.length = 1 ∧
        (connectedComponentSignatureOfList closed).repeatedUnary = false) := by
    rintro ⟨supportLength, repeatedFalse⟩
    obtain ⟨letter, supportShape⟩ :=
      List.length_eq_one_iff.mp supportLength
    have sortedShape : connectedComponentSortedSupport closed = [letter] := by
      rw [← connectedComponentSignatureOfList_support]
      exact supportShape
    have lengthDifferent : closed.length ≠ 1 := by
      omega
    have repeatedTrue :
        (connectedComponentSignatureOfList closed).repeatedUnary = true := by
      simp [connectedComponentSignatureOfList, sortedShape,
        lengthDifferent]
    rw [repeatedTrue] at repeatedFalse
    contradiction
  have closedRestriction :
      (firstOccurrenceSequence closed).filter
        (fun letter => decide
          (letter ∈ (connectedComponentSignatureOfList closed).support)) =
        firstOccurrenceSequence closed := by
    rw [connectedComponentSignatureOfList_support]
    exact firstOccurrenceSequence_filter_sortedSupport closed
  have sourceRestriction :=
    firstOccurrenceSequence_filter_sortedSupport source
  unfold
    SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14.componentInitialParityRender
    renderParitySeparatorInitialGap
  rw [if_neg notSimple, closedRestriction, sourceRestriction,
    ← sameInitials]
  cases initialsShape : firstOccurrenceSequence source with
  | nil =>
      rfl
  | cons anchor remaining =>
      have anchorAbsent : anchor ∉ remaining := by
        have nodup := firstOccurrenceSequence_nodup source
        rw [initialsShape] at nodup
        exact (List.nodup_cons.mp nodup).1
      have payload :=
        parityPayloadBlocks_eq source closed anchor remaining
          anchorAbsent sameParity
      simp only [initialsShape]
      rw [payload]
      have sameAnchorParity := sameParity anchor
      by_cases even : source.count anchor % 2 = 0
      · simp [SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14.componentParityBlock,
          ← sameAnchorParity, even, List.append_assoc]
      · simp [SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14.componentParityBlock,
          ← sameAnchorParity, even, List.append_assoc]

/-- Unrestricted local reachability of the exact repaired C2 gap renderer. -/
theorem listDerivesGapToParitySeparatorInitialNormal
    {gap : List Nat}
    (nonempty : gap ≠ [])
    (noExactCut :
      ¬ ∃ left separator right,
        UniqueSeparatorFourExactCut gap left separator right) :
    SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis gap
      (renderParitySeparatorInitialGap
        (firstOccurrenceSequence gap)
        (fun letter => gap.count letter % 2)
        ⟨connectedComponentSortedSupport gap, none⟩) := by
  obtain ⟨anchor, interior, closedDerivation⟩ :=
    existsClosedAnchor_of_noExactCut nonempty noExactCut
  let closed : List Nat := [anchor] ++ interior ++ [anchor]
  have closedNonempty : closed ≠ [] := by
    simp [closed]
  have closedConnected : ConnectedComponentSupportConnected closed :=
    closedAnchor_supportConnected anchor interior
  have normalized :=
    listDerivesComponentInitialParityLocalNormal
      closed closedNonempty closedConnected
  cases gap with
  | nil =>
      contradiction
  | cons head tail =>
      have first :
          SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis
            (head :: tail) (anchor :: (interior ++ [anchor])) := by
        simpa [closed, List.append_assoc] using closedDerivation
      have asWord := SemigroupBasis.CoRoots.S5_107.ListDerives.toWord first
      let identity : Identity Nat :=
        ⟨SemigroupBasis.CoRoots.S5_107.listWordOfCons head tail,
          SemigroupBasis.CoRoots.S5_107.listWordOfCons anchor
            (interior ++ [anchor])⟩
      have same := sameSignature_of_factor_valid identity
        (fun valuation => asWord.sound targetModelsLeft valuation)
        (fun valuation => asWord.sound targetModelsRight valuation)
      have sameInitials :
          firstOccurrenceSequence (head :: tail) =
            firstOccurrenceSequence closed := by
        simpa [identity, SemigroupBasis.CoRoots.S5_107.listWordOfCons,
          closed, Word.toList, List.append_assoc] using same.initials
      have sameParity :
          ∀ letter,
            (head :: tail).count letter % 2 = closed.count letter % 2 := by
        intro letter
        simpa [identity, SemigroupBasis.CoRoots.S5_107.listWordOfCons,
          closed, Word.toList, List.append_assoc] using same.parity letter
      have closedLength : 2 ≤ closed.length := by
        simp [closed, List.length_append]
      have renderEq := componentInitialParityRender_eq_gapRender
        (head :: tail) closed sameInitials sameParity closedLength
      rw [renderEq] at normalized
      exact closedDerivation.trans normalized

end SemigroupBasis.CoRoots.Order6L3HeavyRank2.S3_11S5_788
