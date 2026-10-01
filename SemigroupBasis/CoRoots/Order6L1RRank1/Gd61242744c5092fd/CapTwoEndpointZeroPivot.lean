import SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.CapTwoEndpointSemanticTransport

/-!
# Zero-measure component pivots and component assembly

This module carries the strict endpoint progress theorem through a genuine
well-founded induction.  The result is an existential zero-measure endpoint
for every connected cap-two component, together with its exact frozen route,
literal permutation, semantic transport, and preserved component hypotheses.

The endpoint is intentionally not identified with a canonical search result.
The separate zero-endpoint uniqueness bridge is recorded outside Lean as the
only remaining theorem needed to identify two independently reached pivots.

Static off-tree source; not locally elaborated.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
namespace CapTwoRTCRoute

open SemigroupBasis
open SemigroupBasis.Examples

/-! Lean 4.28 no longer exports the former core pointwise list relation.
Keep its compatibility declaration route-local so unrelated S5 certificates
may retain their independent global compatibility declaration. -/
namespace List

inductive Forall₂ {alpha beta : Type}
    (relation : alpha → beta → Prop) :
    _root_.List alpha → _root_.List beta → Prop
  | nil : Forall₂ relation [] []
  | cons {left right leftRest rightRest} :
      relation left right →
      Forall₂ relation leftRest rightRest →
        Forall₂ relation (left :: leftRest) (right :: rightRest)

end List

/-! ## Exact zero form -/

/-- The literal structural information supplied by the three zero
coordinates. -/
structure EndpointZeroForm (letters : List Nat) : Prop where
  separated :
    ∃ firsts events : List Nat,
      tagEndpoints letters =
        firsts.map EndpointTag.first ++ events.map EndpointTag.event
  firstOrdered :
    (firstProjection (tagEndpoints letters)).Pairwise (· ≤ ·)
  eventNormal : eventGapInversions (tagEndpoints letters) = 0

theorem endpointZeroForm_of_measure_eq_zero
    {letters : List Nat}
    (zero : endpointMeasure letters = ⟨0, 0, 0⟩) :
    EndpointZeroForm letters := by
  have separationZero := congrArg EndpointMeasure.separation zero
  have firstZero := congrArg EndpointMeasure.firstOrder zero
  have eventZero := congrArg EndpointMeasure.eventOrder zero
  change endpointSeparation letters = 0 at separationZero
  change
    ascendingInversions (firstProjection (tagEndpoints letters)) = 0
      at firstZero
  change eventGapInversions (tagEndpoints letters) = 0 at eventZero
  refine ⟨?_,
    (ascendingInversions_eq_zero_iff_pairwise
      (firstProjection (tagEndpoints letters))).mp firstZero,
    eventZero⟩
  exact endpointTags_separated_of_zero
    (tagEndpoints letters) separationZero

/-! ## Component-signature transport of connectedness -/

private theorem connectedDecomposition_eq_singleton
    {letters : List Nat}
    (nonempty : letters ≠ [])
    (connected : ConnectedComponentSupportConnected letters) :
    connectedComponentDecomposeList letters = [letters] := by
  have decompositionNonempty :=
    connectedComponentDecomposeList_nonempty nonempty
  obtain ⟨first, rest, decompositionShape⟩ :=
    List.exists_cons_of_ne_nil decompositionNonempty
  cases rest with
  | nil =>
      have flattened := connectedComponentDecomposeList_flatten letters
      rw [decompositionShape] at flattened
      have firstEq : first = letters := by
        simpa using flattened
      simpa [firstEq] using decompositionShape
  | cons second remaining =>
      have firstNonempty : first ≠ [] :=
        connectedComponentDecomposeList_nonempty_components letters
          first (by rw [decompositionShape]; simp)
      have suffixNonempty : (second :: remaining).flatten ≠ [] := by
        have secondNonempty : second ≠ [] :=
          connectedComponentDecomposeList_nonempty_components letters
            second (by rw [decompositionShape]; simp)
        intro flattenedEmpty
        have appendedEmpty : second ++ remaining.flatten = [] := by
          simpa using flattenedEmpty
        exact secondNonempty
          (List.append_eq_nil_iff.mp appendedEmpty).1
      have pairwise :=
        connectedComponentDecomposeList_pairwiseDisjoint letters
      rw [decompositionShape] at pairwise
      have firstToSuffix := (List.pairwise_cons.mp pairwise).1
      have disjoint :
          ConnectedComponentSupportsDisjoint
            first (second :: remaining).flatten := by
        intro letter firstMember suffixMember
        rw [List.mem_flatten] at suffixMember
        rcases suffixMember with
          ⟨candidate, candidateMember, letterMember⟩
        exact
          (firstToSuffix candidate candidateMember
            letter firstMember) letterMember
      have flattened := connectedComponentDecomposeList_flatten letters
      rw [decompositionShape] at flattened
      have sourceShape :
          letters = first ++ (second :: remaining).flatten := by
        simpa using flattened.symm
      obtain ⟨letter, firstMember, suffixMember⟩ :=
        connected first (second :: remaining).flatten
          sourceShape firstNonempty suffixNonempty
      exact False.elim
        (disjoint letter firstMember suffixMember)

private theorem connected_of_same_component_signatures
    {source target : List Nat}
    (sourceNonempty : source ≠ [])
    (sourceConnected : ConnectedComponentSupportConnected source)
    (same :
      connectedComponentSignaturesList source =
        connectedComponentSignaturesList target) :
    ConnectedComponentSupportConnected target := by
  have sourceDecomposition :=
    connectedDecomposition_eq_singleton
      sourceNonempty sourceConnected
  have sourceSignatures :
      connectedComponentSignaturesList source =
        [connectedComponentSignatureOfList source] := by
    simp [connectedComponentSignaturesList, sourceDecomposition]
  have targetSignatures :
      connectedComponentSignaturesList target =
        [connectedComponentSignatureOfList source] := by
    rw [← same, sourceSignatures]
  have targetDecompositionLength :
      (connectedComponentDecomposeList target).length = 1 := by
    have lengths := congrArg List.length targetSignatures
    simpa [connectedComponentSignaturesList] using lengths
  obtain ⟨only, targetDecomposition⟩ :=
    List.length_eq_one_iff.mp targetDecompositionLength
  have onlyConnected :=
    connectedComponentDecomposeList_supportConnected target
      only (by rw [targetDecomposition]; simp)
  have flattened := connectedComponentDecomposeList_flatten target
  rw [targetDecomposition] at flattened
  have onlyEq : only = target := by
    simpa using flattened
  simpa [onlyEq] using onlyConnected

theorem EndpointSemanticAgreement.connected_right
    {source target : List Nat}
    (same : EndpointSemanticAgreement source target)
    (sourceNonempty : source ≠ [])
    (targetNonempty : target ≠ [])
    (sourceConnected : ConnectedComponentSupportConnected source) :
    ConnectedComponentSupportConnected target := by
  obtain ⟨sourceHead, sourceTail, sourceShape⟩ :=
    List.exists_cons_of_ne_nil sourceNonempty
  obtain ⟨targetHead, targetTail, targetShape⟩ :=
    List.exists_cons_of_ne_nil targetNonempty
  have wordComponents := same.componentTheory
    sourceHead sourceTail targetHead targetTail
    sourceShape targetShape
  have listComponents :
      connectedComponentSignaturesList source =
        connectedComponentSignaturesList target := by
    rw [sourceShape, targetShape]
    simpa [connectedComponentSignaturesWord,
      S5_107.listWordOfCons, Word.toList] using wordComponents
  exact connected_of_same_component_signatures
    sourceNonempty sourceConnected listComponents

/-! ## Well-founded zero-pivot induction -/

/-- A named target is a zero-measure pivot of one source component. -/
structure IsComponentZeroPivot
    (source pivot : List Nat) : Prop where
  reachable : ContextualFrozenRTC source pivot
  permutation : source.Perm pivot
  semantic : EndpointSemanticAgreement source pivot
  zeroMeasure : endpointMeasure pivot = ⟨0, 0, 0⟩
  zeroForm : EndpointZeroForm pivot
  connected : ConnectedComponentSupportConnected pivot
  twoLimited : ∀ tested, pivot.count tested ≤ 2

private theorem connectedCapTwo_reaches_zero_of_acc
    (measure : EndpointMeasure)
    (accessible : Acc EndpointMeasure.Lt measure) :
    ∀ letters : List Nat,
      endpointMeasure letters = measure →
      (∀ tested, letters.count tested ≤ 2) →
      ConnectedComponentSupportConnected letters →
      ∃ pivot, IsComponentZeroPivot letters pivot := by
  induction accessible with
  | intro measure smaller inductionHypothesis =>
      intro letters measureEq twoLimited connected
      by_cases zero : endpointMeasure letters = ⟨0, 0, 0⟩
      · exact ⟨letters,
          ContextualFrozenRTC.refl letters,
          List.Perm.refl letters,
          EndpointSemanticAgreement.refl letters,
          zero,
          endpointZeroForm_of_measure_eq_zero zero,
          connected,
          twoLimited⟩
      · have positive : (endpointMeasure letters).Positive :=
          (endpointMeasure_positive_iff_ne_zero letters).mpr zero
        obtain ⟨next, reachable, permutation, changed, decrease,
            semantic⟩ :=
          endpointDisorder_progress_semantic
            twoLimited connected positive
        have nextLimited : ∀ tested, next.count tested ≤ 2 := by
          intro tested
          rw [← permutation.count tested]
          exact twoLimited tested
        have sourceNonempty : letters ≠ [] := by
          intro empty
          apply zero
          rw [empty]
          rfl
        have nextNonempty : next ≠ [] := by
          intro empty
          rw [empty] at permutation
          exact sourceNonempty permutation.symm.nil_eq.symm
        have nextConnected :
            ConnectedComponentSupportConnected next :=
          semantic.connected_right sourceNonempty nextNonempty connected
        have lower : EndpointMeasure.Lt (endpointMeasure next) measure := by
          simpa [measureEq] using decrease
        obtain ⟨pivot, pivotData⟩ :=
          inductionHypothesis (endpointMeasure next) lower
            next rfl nextLimited nextConnected
        rcases pivotData with
          ⟨nextReachable, nextPermutation, nextSemantic,
            pivotZero, pivotForm, pivotConnected, pivotLimited⟩
        exact ⟨pivot,
          reachable.trans nextReachable,
          permutation.trans nextPermutation,
          semantic.trans nextSemantic,
          pivotZero, pivotForm, pivotConnected, pivotLimited⟩

/-- Every connected cap-two list reaches an honest zero-measure endpoint by
strict lexicographic induction. -/
theorem connectedCapTwo_reaches_zero
    {letters : List Nat}
    (twoLimited : ∀ tested, letters.count tested ≤ 2)
    (connected : ConnectedComponentSupportConnected letters) :
    ∃ pivot, IsComponentZeroPivot letters pivot := by
  exact connectedCapTwo_reaches_zero_of_acc
    (endpointMeasure letters)
    (endpointMeasure_lt_wellFounded.apply (endpointMeasure letters))
    letters rfl twoLimited connected

/-! ## Literal component assembly -/

/-- Independent component routes concatenate without any extra generating
step. -/
theorem contextualFrozenRTC_flatten_of_forall₂
    {sources pivots : List (List Nat)}
    (aligned :
      List.Forall₂ ContextualFrozenRTC sources pivots) :
    ContextualFrozenRTC sources.flatten pivots.flatten := by
  induction aligned with
  | nil => exact ContextualFrozenRTC.refl []
  | @cons source pivot sourceRest pivotRest
      componentRoute restRoutes inductionHypothesis =>
      have normalizeHead :
          ContextualFrozenRTC
            (source ++ sourceRest.flatten)
            (pivot ++ sourceRest.flatten) := by
        simpa using componentRoute.context [] sourceRest.flatten
      have normalizeRest :
          ContextualFrozenRTC
            (pivot ++ sourceRest.flatten)
            (pivot ++ pivotRest.flatten) := by
        simpa using inductionHypothesis.context pivot []
      simpa [List.flatten_cons, List.append_assoc] using
        normalizeHead.trans normalizeRest

/-- Given a zero-pivot witness for every displayed component, choose aligned
pivots and assemble their frozen routes.  This is the exact whole-list
component induction boundary. -/
theorem assemble_component_zero_pivots
    (components : List (List Nat))
    (each :
      ∀ component, component ∈ components →
        ∃ pivot, IsComponentZeroPivot component pivot) :
    ∃ pivots,
      List.Forall₂ IsComponentZeroPivot components pivots ∧
      ContextualFrozenRTC components.flatten pivots.flatten := by
  induction components with
  | nil =>
      exact ⟨[], List.Forall₂.nil,
        ContextualFrozenRTC.refl []⟩
  | cons component rest inductionHypothesis =>
      obtain ⟨pivot, pivotData⟩ :=
        each component (by simp)
      have tailEach :
          ∀ candidate, candidate ∈ rest →
            ∃ target, IsComponentZeroPivot candidate target := by
        intro candidate member
        exact each candidate (by simp [member])
      obtain ⟨pivots, aligned, assembled⟩ :=
        inductionHypothesis tailEach
      have allAligned :
          List.Forall₂ IsComponentZeroPivot
            (component :: rest) (pivot :: pivots) :=
        List.Forall₂.cons pivotData aligned
      have normalizeHead :
          ContextualFrozenRTC
            (component ++ rest.flatten)
            (pivot ++ rest.flatten) := by
        simpa using pivotData.reachable.context [] rest.flatten
      have normalizeRest :
          ContextualFrozenRTC
            (pivot ++ rest.flatten)
            (pivot ++ pivots.flatten) := by
        simpa using assembled.context pivot []
      exact ⟨pivot :: pivots, allAligned,
        by
          simpa [List.flatten_cons, List.append_assoc] using
            normalizeHead.trans normalizeRest⟩

/-- Normalize an arbitrary displayed list of connected cap-two components and
assemble the resulting routes on its flattening. -/
theorem connectedCapTwo_components_reach_zero
    (components : List (List Nat))
    (twoLimited :
      ∀ component, component ∈ components →
        ∀ tested, component.count tested ≤ 2)
    (connected :
      ∀ component, component ∈ components →
        ConnectedComponentSupportConnected component) :
    ∃ pivots,
      List.Forall₂ IsComponentZeroPivot components pivots ∧
      ContextualFrozenRTC components.flatten pivots.flatten := by
  apply assemble_component_zero_pivots components
  intro component member
  exact connectedCapTwo_reaches_zero
    (twoLimited component member) (connected component member)

end CapTwoRTCRoute
end SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
