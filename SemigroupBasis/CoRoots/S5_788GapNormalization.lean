import SemigroupBasis.CoRoots.S5_441ExactCutAlignment
import SemigroupBasis.CoRoots.S5_788IntervalPlan

namespace SemigroupBasis.CoRoots.S5_788

open SemigroupBasis
open SemigroupBasis.Examples

/-- The local normal form of one separator-free exact-cut gap. -/
def initialGapNormalList (gap : List Nat) : List Nat :=
  match firstOccurrenceSequence gap with
  | [] => []
  | first :: rest => first :: rest ++ [first]

private theorem mem_firstOccurrenceSequence_iff
    (selected : Nat) :
    ∀ letters : List Nat,
      selected ∈ firstOccurrenceSequence letters ↔
        selected ∈ letters
  | [] => by
      simp [firstOccurrenceSequence]
  | letter :: rest => by
      by_cases equal : selected = letter
      · subst letter
        simp [firstOccurrenceSequence]
      · simp [firstOccurrenceSequence, equal,
          mem_firstOccurrenceSequence_iff selected rest]

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
    (dropped : ¬ keep selected)
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

/-- First-occurrence normalization commutes with deleting a fixed collection
of letters. -/
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
          (filter_ne_then_keep_of_drop keep letter kept
            (firstOccurrenceSequence rest)).symm

/-- A connected component normalizes to a closed initial envelope whose
endpoint is the component's first letter. -/
private theorem exists_initialEnvelopeDerivation_of_connected
    {head : Nat} {tail : List Nat}
    (connected :
      ConnectedComponentSupportConnected (head :: tail))
    (lengthAtLeastTwo : 2 ≤ (head :: tail).length)
    (twoLimited :
      UniqueSeparatorTwoLimited (head :: tail)) :
    ∃ interior,
      S5_107.ListDerives basis
          (head :: tail)
          (initialEnvelopeRender head interior []) ∧
        head ∉ interior ∧
        ∀ tested,
          tested ∈ initialEnvelopeRender head interior [] ↔
            tested ∈ head :: tail := by
  let interior :=
    (firstOccurrenceSequence tail).filter
      (fun letter => decide (letter ≠ head))
  have initialShape :
      firstOccurrenceSequence (head :: tail) =
        head :: interior := by
    rfl
  have endpointNotInterior : head ∉ interior := by
    have nodup :=
      firstOccurrenceSequence_nodup (head :: tail)
    rw [initialShape] at nodup
    exact (List.nodup_cons.mp nodup).1
  have componentDerivation :=
    listDerivesConnectedInitialEnvelope
      connected lengthAtLeastTwo twoLimited
  have targetShape :
      firstOccurrenceSequence (head :: tail) ++ [head] =
        initialEnvelopeRender head interior [] := by
    rw [initialShape]
    simp [initialEnvelopeRender, List.append_assoc]
  refine
    ⟨interior, ?_, endpointNotInterior, ?_⟩
  · rw [← targetShape]
    exact componentDerivation
  · intro tested
    rw [← targetShape, List.mem_append,
      mem_firstOccurrenceSequence_iff]
    simp [or_assoc, or_left_comm, or_comm]

/-- Fold a nonempty list of pairwise-disjoint connected components to one
closed initial envelope. The first source letter remains the endpoint. -/
private theorem exists_initialEnvelopeDerivation_of_components
    (components : List (List Nat))
    (componentsNonempty : components ≠ [])
    (supportConnected :
      ∀ component ∈ components,
        ConnectedComponentSupportConnected component)
    (lengthAtLeastTwo :
      ∀ component ∈ components, 2 ≤ component.length)
    (twoLimited :
      ∀ component ∈ components,
        UniqueSeparatorTwoLimited component)
    (pairwiseDisjoint :
      components.Pairwise ConnectedComponentSupportsDisjoint) :
    ∃ endpoint sourceTail finalInterior,
      components.flatten = endpoint :: sourceTail ∧
        S5_107.ListDerives basis
          components.flatten
          (initialEnvelopeRender endpoint finalInterior []) ∧
        endpoint ∉ finalInterior ∧
        ∀ tested,
          tested ∈
              initialEnvelopeRender endpoint finalInterior [] ↔
            tested ∈ components.flatten := by
  induction components with
  | nil =>
      exact False.elim (componentsNonempty rfl)
  | cons component rest induction =>
      rw [List.pairwise_cons] at pairwiseDisjoint
      have componentLengthAtLeastTwo :
          2 ≤ component.length :=
        lengthAtLeastTwo component (by simp)
      have componentNonempty : component ≠ [] := by
        intro componentEmpty
        subst component
        simp at componentLengthAtLeastTwo
      obtain ⟨endpoint, tail, rfl⟩ :=
        List.exists_cons_of_ne_nil componentNonempty
      obtain
        ⟨firstInterior, componentDerivation,
          endpointNotFirstInterior, componentSupport⟩ :=
          exists_initialEnvelopeDerivation_of_connected
            (supportConnected (endpoint :: tail) (by simp))
            componentLengthAtLeastTwo
            (twoLimited (endpoint :: tail) (by simp))
      cases rest with
      | nil =>
          refine
            ⟨endpoint, tail, firstInterior, by simp, ?_,
              endpointNotFirstInterior, ?_⟩
          · simpa using componentDerivation
          · intro tested
            simpa using componentSupport tested
      | cons next remaining =>
          obtain
            ⟨restEndpoint, restSourceTail, restInterior,
              restSourceShape, restDerivation,
              restEndpointAbsent, restSupport⟩ :=
                induction
                  (by simp)
                  (fun current member =>
                    supportConnected current
                      (List.Mem.tail (endpoint :: tail) member))
                  (fun current member =>
                    lengthAtLeastTwo current
                      (List.Mem.tail (endpoint :: tail) member))
                  (fun current member =>
                    twoLimited current
                      (List.Mem.tail (endpoint :: tail) member))
                  pairwiseDisjoint.2
          have endpointNotRestFlatten :
              endpoint ∉ (next :: remaining).flatten := by
            intro endpointMember
            rw [List.mem_flatten] at endpointMember
            rcases endpointMember with
              ⟨candidate, candidateMember, endpointInCandidate⟩
            exact
              (pairwiseDisjoint.1 candidate candidateMember
                endpoint (by simp)) endpointInCandidate
          have endpointNotRestTarget :
              endpoint ∉
                initialEnvelopeRender
                  restEndpoint restInterior [] := by
            intro endpointMember
            exact endpointNotRestFlatten <|
              (restSupport endpoint).mp endpointMember
          have endpointNeRestEndpoint :
              endpoint ≠ restEndpoint := by
            intro equal
            apply endpointNotRestTarget
            subst restEndpoint
            simp [initialEnvelopeRender]
          have endpointNotRestInterior :
              endpoint ∉ restInterior := by
            intro endpointMember
            apply endpointNotRestTarget
            simp [initialEnvelopeRender, endpointMember]
          let finalInterior :=
            firstInterior ++ [restEndpoint] ++ restInterior
          have endpointNotFinal :
              endpoint ∉ finalInterior := by
            simp [finalInterior, endpointNotFirstInterior,
              endpointNeRestEndpoint, endpointNotRestInterior]
          have normalizeFirst :
              S5_107.ListDerives basis
                ((endpoint :: tail) ++
                  (next :: remaining).flatten)
                (initialEnvelopeRender
                    endpoint firstInterior [] ++
                  (next :: remaining).flatten) :=
            componentDerivation.append
              (next :: remaining).flatten
          have normalizeRest :
              S5_107.ListDerives basis
                (initialEnvelopeRender
                    endpoint firstInterior [] ++
                  (next :: remaining).flatten)
                (initialEnvelopeRender
                    endpoint firstInterior [] ++
                  initialEnvelopeRender
                    restEndpoint restInterior []) :=
            restDerivation.prepend
              (initialEnvelopeRender endpoint firstInterior [])
          have combine :
              S5_107.ListDerives basis
                (initialEnvelopeRender
                    endpoint firstInterior [] ++
                  initialEnvelopeRender
                    restEndpoint restInterior [])
                (initialEnvelopeRender
                  endpoint finalInterior []) := by
            simpa [initialEnvelopeRender, finalInterior,
              List.append_assoc] using
                listDerivesAdjacentEnvelopes
                  endpoint restEndpoint
                  firstInterior restInterior
          have combined :
              S5_107.ListDerives basis
                ((endpoint :: tail) ++
                  (next :: remaining).flatten)
                (initialEnvelopeRender
                  endpoint finalInterior []) :=
            normalizeFirst.trans <|
              normalizeRest.trans combine
          refine
            ⟨endpoint,
              tail ++ (next :: remaining).flatten,
              finalInterior, by simp, ?_,
              endpointNotFinal, ?_⟩
          · simpa using combined
          · intro tested
            calc
              tested ∈
                  initialEnvelopeRender
                    endpoint finalInterior [] ↔
                  tested ∈
                      initialEnvelopeRender
                        endpoint firstInterior [] ∨
                    tested ∈
                      initialEnvelopeRender
                        restEndpoint restInterior [] := by
                simp [initialEnvelopeRender, finalInterior,
                  List.mem_append, or_assoc, or_left_comm, or_comm]
              _ ↔
                  tested ∈ endpoint :: tail ∨
                    tested ∈ (next :: remaining).flatten := by
                rw [componentSupport tested, restSupport tested]
              _ ↔
                  tested ∈
                    ((endpoint :: tail) ::
                      next :: remaining).flatten := by
                simp [or_assoc, or_left_comm, or_comm]

/-- Endpoint capping cannot create an exact cut because every derivation
preserves the complete exact-cut signature. -/
private theorem endpointCap_no_exactCut
    {gap : List Nat}
    (gapNonempty : gap ≠ [])
    (noExactCut :
      ¬ ∃ left separator right,
        UniqueSeparatorFourExactCut
          gap left separator right) :
    ¬ ∃ left separator right,
      UniqueSeparatorFourExactCut
        (uniqueSeparatorEndpointCap gap)
        left separator right := by
  obtain ⟨head, tail, gapShape⟩ :=
    List.exists_cons_of_ne_nil gapNonempty
  subst gap
  rintro ⟨left, separator, right, cut⟩
  have capDerivation :=
    listDerivesEndpointCap (head :: tail)
  obtain
    ⟨targetHead, targetTail, targetShape, wordDerivation⟩ :=
      capDerivation.from_cons
  rw [targetShape] at cut
  have same := derives_sameSignature wordDerivation
  obtain
    ⟨sourceLeft, sourceRight, sourceCut,
      _leftSupport, _rightSupport⟩ :=
      S5_441Invariant.SameExactCutSignature.transport
        (S5_441Invariant.SameExactCutSignature.symm
          same.exactCuts)
        cut
  apply noExactCut
  exact
    ⟨sourceLeft, separator, sourceRight, by
      simpa [S5_107.listWordOfCons] using sourceCut⟩

/-- Every exact-cut-free gap, after endpoint capping, derives to its local
first-occurrence envelope. -/
theorem listDerivesEndpointCapToInitialGapNormal_of_noExactCut
    {gap : List Nat}
    (noExactCut :
      ¬ ∃ left separator right,
        UniqueSeparatorFourExactCut
          gap left separator right) :
    S5_107.ListDerives basis
      (uniqueSeparatorEndpointCap gap)
      (initialGapNormalList gap) := by
  by_cases gapEmpty : gap = []
  · subst gap
    simpa [initialGapNormalList, uniqueSeparatorEndpointCap] using
      S5_107.ListDerives.refl (basis := basis) []
  · have cappedNonempty :
        uniqueSeparatorEndpointCap gap ≠ [] := by
      obtain ⟨head, tail, gapShape⟩ :=
        List.exists_cons_of_ne_nil gapEmpty
      intro cappedEmpty
      have headMember :
          head ∈ uniqueSeparatorEndpointCap gap :=
        (uniqueSeparatorEndpointCap_mem_iff head gap).2 <| by
          rw [gapShape]
          simp
      rw [cappedEmpty] at headMember
      simp at headMember
    have cappedNoExactCut :=
      endpointCap_no_exactCut gapEmpty noExactCut
    let capped := uniqueSeparatorEndpointCap gap
    obtain
      ⟨endpoint, sourceTail, finalInterior,
        cappedShape, envelopeDerivation,
        endpointNotInterior, _envelopeSupport⟩ :=
        exists_initialEnvelopeDerivation_of_components
          (connectedComponentDecomposeList capped)
          (connectedComponentDecomposeList_nonempty <| by
            simpa [capped] using cappedNonempty)
          (connectedComponentDecomposeList_supportConnected capped)
          (S5_441.connectedComponentDecomposeList_components_length_ge_two_of_no_exactCut
            (by simpa [capped] using cappedNoExactCut))
          (fun component componentMember tested => by
            have componentSublist :
                component.Sublist capped := by
              have sublist :=
                List.sublist_flatten_of_mem componentMember
              rw [connectedComponentDecomposeList_flatten capped]
                at sublist
              exact sublist
            exact
              Nat.le_trans
                (componentSublist.count_le tested)
                (uniqueSeparatorEndpointCap_twoLimited gap tested))
          (connectedComponentDecomposeList_pairwiseDisjoint capped)
    rw [connectedComponentDecomposeList_flatten capped]
      at cappedShape envelopeDerivation
    have closedDerivation :=
      listDerivesClosedInitialEnvelope
        endpoint finalInterior endpointNotInterior
    have shapedEnvelopeDerivation := envelopeDerivation
    rw [cappedShape] at shapedEnvelopeDerivation
    have wordDerivation :=
      S5_107.ListDerives.toWord shapedEnvelopeDerivation
    have initialSequence :
        firstOccurrenceSequence capped =
          firstOccurrenceSequence
            (initialEnvelopeRender
              endpoint finalInterior []) := by
      rw [cappedShape]
      simpa [S5_107.listWordOfCons,
        initialEnvelopeRender] using
          (derives_sameSignature wordDerivation).initials
    have combined :=
      envelopeDerivation.trans closedDerivation
    rw [← initialSequence] at combined
    have capInitials :
        firstOccurrenceSequence capped =
          firstOccurrenceSequence gap := by
      simpa [capped] using
        firstOccurrenceSequence_endpointCap gap
    rw [capInitials] at combined
    have gapInitialShape :
        firstOccurrenceSequence gap =
          endpoint ::
            (firstOccurrenceSequence sourceTail).filter
              (fun letter => decide (letter ≠ endpoint)) := by
      calc
        firstOccurrenceSequence gap =
            firstOccurrenceSequence capped :=
          capInitials.symm
        _ =
            endpoint ::
              (firstOccurrenceSequence sourceTail).filter
                (fun letter => decide (letter ≠ endpoint)) := by
          rw [cappedShape]
          rfl
    simpa [capped, initialGapNormalList,
      gapInitialShape] using combined

/-- Restricting the global first-occurrence order to one exact-cut support
segment gives exactly the first-occurrence order of that segment's gap. -/
theorem firstOccurrenceSequence_restrict_exactCutGap
    (word : Word Nat) (segment : S5_441.ExactCutSegment)
    (segmentMember :
      segment ∈
        S5_441.exactCutDecomposition word.toList) :
    (firstOccurrenceSequence word.toList).filter
        (fun letter =>
          decide
            (letter ∈
              (S5_441.exactCutSupportSegment segment).quadratic)) =
      firstOccurrenceSequence segment.gap := by
  obtain ⟨before, after, decompositionShape⟩ :=
    List.mem_iff_append.mp segmentMember
  have pairwise :=
    S5_441.exactCutDecomposition_renders_pairwise_disjoint
      word.toList
  rw [decompositionShape] at pairwise
  have splitPairwise :=
    List.pairwise_append.mp pairwise
  have beforeToSuffix := splitPairwise.2.2
  have suffixPairwise := splitPairwise.2.1
  have segmentToAfter :=
    (List.pairwise_cons.mp suffixPairwise).1
  have beforeFilter :
      (S5_441.renderExactCutSegments before).filter
          (fun letter => decide (letter ∈ segment.gap)) =
        [] := by
    apply List.filter_eq_nil_iff.mpr
    intro tested testedBefore
    simp only [decide_eq_true_eq]
    intro testedGap
    change
      tested ∈
        before.flatMap S5_441.ExactCutSegment.render
      at testedBefore
    rw [List.mem_flatMap] at testedBefore
    rcases testedBefore with
      ⟨candidate, candidateMember, testedCandidate⟩
    have testedSegment : tested ∈ segment.render := by
      change tested ∈ segment.gap ++ segment.separator.toList
      exact List.mem_append_left _ testedGap
    exact
      (beforeToSuffix candidate candidateMember
        segment (by simp) tested testedCandidate)
        testedSegment
  have afterFilter :
      (S5_441.renderExactCutSegments after).filter
          (fun letter => decide (letter ∈ segment.gap)) =
        [] := by
    apply List.filter_eq_nil_iff.mpr
    intro tested testedAfter
    simp only [decide_eq_true_eq]
    intro testedGap
    change
      tested ∈
        after.flatMap S5_441.ExactCutSegment.render
      at testedAfter
    rw [List.mem_flatMap] at testedAfter
    rcases testedAfter with
      ⟨candidate, candidateMember, testedCandidate⟩
    have testedSegment : tested ∈ segment.render := by
      change tested ∈ segment.gap ++ segment.separator.toList
      exact List.mem_append_left _ testedGap
    exact
      (segmentToAfter candidate candidateMember
        tested testedSegment) testedCandidate
  have separatorFilter :
      segment.separator.toList.filter
          (fun letter => decide (letter ∈ segment.gap)) =
        [] := by
    cases separatorShape : segment.separator with
    | none =>
        simp [separatorShape]
    | some separator =>
        apply List.filter_eq_nil_iff.mpr
        intro tested testedSeparator
        have testedEq : tested = separator := by
          simpa [separatorShape] using testedSeparator
        subst tested
        simp only [decide_eq_true_eq]
        intro separatorGap
        have separatorMember :
            separator ∈
              S5_441.exactCutSeparators
                (S5_441.exactCutDecomposition word.toList) := by
          unfold S5_441.exactCutSeparators
          rw [List.mem_filterMap]
          exact ⟨segment, segmentMember, separatorShape⟩
        exact
          (S5_441.exactCutDecomposition_gap_letter_not_separator
            segmentMember separatorGap) separatorMember
  have gapFilter :
      segment.gap.filter
          (fun letter => decide (letter ∈ segment.gap)) =
        segment.gap := by
    apply List.filter_eq_self.mpr
    intro tested testedGap
    exact decide_eq_true testedGap
  have wholeShape :
      word.toList =
        S5_441.renderExactCutSegments before ++
          segment.gap ++ segment.separator.toList ++
            S5_441.renderExactCutSegments after := by
    calc
      word.toList =
          S5_441.renderExactCutSegments
            (S5_441.exactCutDecomposition word.toList) :=
        (S5_441.render_exactCutDecomposition word.toList).symm
      _ =
          S5_441.renderExactCutSegments
            (before ++ segment :: after) := by
        rw [decompositionShape]
      _ =
          S5_441.renderExactCutSegments before ++
            segment.gap ++ segment.separator.toList ++
              S5_441.renderExactCutSegments after := by
        simp [S5_441.renderExactCutSegments,
          S5_441.ExactCutSegment.render, List.append_assoc]
  have wholeFilter :
      word.toList.filter
          (fun letter => decide (letter ∈ segment.gap)) =
        segment.gap := by
    rw [wholeShape]
    simp only [List.filter_append]
    rw [beforeFilter, gapFilter, separatorFilter, afterFilter]
    simp
  have supportFilter :
      (firstOccurrenceSequence word.toList).filter
          (fun letter =>
            decide
              (letter ∈
                (S5_441.exactCutSupportSegment segment).quadratic)) =
        (firstOccurrenceSequence word.toList).filter
          (fun letter => decide (letter ∈ segment.gap)) := by
    apply List.filter_congr
    intro tested _
    simp [S5_441.exactCutSupportSegment,
      connectedComponentSortedSupport_mem_iff]
  calc
    (firstOccurrenceSequence word.toList).filter
          (fun letter =>
            decide
              (letter ∈
                (S5_441.exactCutSupportSegment segment).quadratic)) =
        (firstOccurrenceSequence word.toList).filter
          (fun letter => decide (letter ∈ segment.gap)) :=
      supportFilter
    _ =
        firstOccurrenceSequence
          (word.toList.filter
            (fun letter => decide (letter ∈ segment.gap))) :=
      (firstOccurrenceSequence_filter
        (fun letter => decide (letter ∈ segment.gap))
        word.toList).symm
    _ = firstOccurrenceSequence segment.gap := by
      rw [wholeFilter]

/-- The exact-cut scanner supplies the no-cut premise needed by the local
gap normalizer. -/
theorem listDerivesEndpointCapToInitialGapNormal
    (word : Word Nat) (segment : S5_441.ExactCutSegment)
    (segmentMember :
      segment ∈
        S5_441.exactCutDecomposition word.toList) :
    S5_107.ListDerives basis
      (uniqueSeparatorEndpointCap segment.gap)
      (initialGapNormalList segment.gap) :=
  listDerivesEndpointCapToInitialGapNormal_of_noExactCut
    (S5_441.exactCutDecomposition_gap_no_exactCut segmentMember)

end SemigroupBasis.CoRoots.S5_788
