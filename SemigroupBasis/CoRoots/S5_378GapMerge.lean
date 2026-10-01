import SemigroupBasis.CoRoots.S5_379Envelope
import SemigroupBasis.Examples.ConnectedComponentFourComponents

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_378

open SemigroupBasis
open SemigroupBasis.Examples

/-- List-level derivability for the seven-law B378 basis. -/
abbrev ListDerives : List Nat → List Nat → Prop :=
  S5_107.ListDerives basis

/-- A closed envelope with two displayed copies of its endpoint. -/
def gapEnvelopeRender
    (endpoint : Nat) (interior : List Nat) : List Nat :=
  endpoint :: interior ++ [endpoint]

namespace ListDerives

/-- Transport an S5_379 list derivation through the explicit proof that every
S5_379 basis law follows from the stronger B378 basis. -/
theorem ofS5_379 {left right : List Nat}
    (derivation :
      SemigroupBasis.CoRoots.S5_379.ListDerives left right) :
    ListDerives left right := by
  cases derivation with
  | empty =>
      exact S5_107.ListDerives.empty
  | words wordDerivation =>
      exact S5_107.ListDerives.words <|
        wordDerivation.transport
          SemigroupBasis.CoRoots.S5_379.strongerBasisDerives

end ListDerives

/-- The connected-component envelope normalizer from S5_379 transports to
B378. The transport is only derivational; all shape and count conclusions
are inherited unchanged from the authored component theorem. -/
theorem existsConnectedComponentEnvelopeNormal
    {component : List Nat}
    (lengthAtLeastTwo : 2 ≤ component.length)
    (connected : ConnectedComponentSupportConnected component) :
    ∃ endpoint interior,
      ListDerives component (gapEnvelopeRender endpoint interior) ∧
      endpoint ∉ interior ∧
      interior.Pairwise (· ≤ ·) ∧
      UniqueSeparatorTwoLimited
        (gapEnvelopeRender endpoint interior) ∧
      (∀ tested,
        (gapEnvelopeRender endpoint interior).count tested =
          min (component.count tested) 2) := by
  cases component with
  | nil =>
      simp at lengthAtLeastTwo
  | cons head tail =>
      cases tail with
      | nil =>
          simp at lengthAtLeastTwo
      | cons next rest =>
          obtain
            ⟨interior, derivation, endpointAbsent, sorted,
              twoLimited, capped⟩ :=
            SemigroupBasis.CoRoots.S5_379.existsConnectedComponentEnvelopeNormal
                head next rest connected
          refine
            ⟨head, interior, ListDerives.ofS5_379 derivation,
              endpointAbsent, sorted, ?_, ?_⟩
          · simpa [gapEnvelopeRender] using twoLimited
          · intro tested
            simpa [gapEnvelopeRender] using capped tested

/-- Merge two adjacent B378 envelopes in all four empty/nonempty interior
cases:

`x A x y B y  ->  x A y y B x`.

The proof selects the matching recorded finite chain without using an empty
word substitution. -/
theorem listDerivesAdjacentEnvelopeMerge
    (x y : Nat) (leftInterior rightInterior : List Nat) :
    ListDerives
      (gapEnvelopeRender x leftInterior ++
        gapEnvelopeRender y rightInterior)
      (gapEnvelopeRender x
        (leftInterior ++ [y, y] ++ rightInterior)) := by
  cases leftInterior with
  | nil =>
      cases rightInterior with
      | nil =>
          simpa [gapEnvelopeRender, Word.toList_append,
            List.append_assoc] using
              (S5_107.ListDerives.ofWord
                (derivesMergeBothEmptyFiniteChain
                  (Word.singleton x) (Word.singleton y)))
      | cons rightHead rightTail =>
          let rightWord :=
            S5_107.listWordOfCons rightHead rightTail
          simpa [gapEnvelopeRender, rightWord,
            S5_107.listWordOfCons, Word.toList,
            Word.toList_append, List.append_assoc] using
              (S5_107.ListDerives.ofWord
                (derivesMergeLeftEmptyFiniteChain
                  (Word.singleton x) (Word.singleton y) rightWord))
  | cons leftHead leftTail =>
      let leftWord :=
        S5_107.listWordOfCons leftHead leftTail
      cases rightInterior with
      | nil =>
          simpa [gapEnvelopeRender, leftWord,
            S5_107.listWordOfCons, Word.toList,
            Word.toList_append, List.append_assoc] using
              (S5_107.ListDerives.ofWord
                (derivesMergeRightEmptyFiniteChain
                  (Word.singleton x) leftWord (Word.singleton y)))
      | cons rightHead rightTail =>
          let rightWord :=
            S5_107.listWordOfCons rightHead rightTail
          simpa [gapEnvelopeRender, leftWord, rightWord,
            S5_107.listWordOfCons, Word.toList,
            Word.toList_append, List.append_assoc] using
              (S5_107.ListDerives.ofWord
                (derivesMergeBothNonemptyFiniteChain
                  (Word.singleton x) leftWord
                  (Word.singleton y) rightWord))

/-- The merge target is an exact permutation of the two source envelopes. -/
theorem adjacentEnvelopeMerge_perm
    (x y : Nat) (leftInterior rightInterior : List Nat) :
    (gapEnvelopeRender x leftInterior ++
        gapEnvelopeRender y rightInterior).Perm
      (gapEnvelopeRender x
        (leftInterior ++ [y, y] ++ rightInterior)) := by
  rw [List.perm_iff_count]
  intro tested
  simp only [gapEnvelopeRender, List.count_cons,
    List.count_append, List.count_nil]
  omega

private theorem supportsDisjoint_flatten
    {component : List Nat} {components : List (List Nat)}
    (disjoint :
      ∀ other ∈ components,
        ConnectedComponentSupportsDisjoint component other) :
    ConnectedComponentSupportsDisjoint component components.flatten := by
  intro tested testedInComponent testedInFlatten
  rw [List.mem_flatten] at testedInFlatten
  obtain ⟨other, otherMember, testedInOther⟩ := testedInFlatten
  exact disjoint other otherMember tested testedInComponent testedInOther

/-- Fold an arbitrary nonempty list of pairwise support-disjoint connected
components, each of length at least two, into one B378 envelope. The target
has exactly every source multiplicity capped at two. -/
theorem existsGapEnvelopeNormalOfComponents
    (components : List (List Nat))
    (componentsNonempty : components ≠ [])
    (pairwiseDisjoint :
      components.Pairwise ConnectedComponentSupportsDisjoint)
    (supportConnected :
      ∀ component ∈ components,
        ConnectedComponentSupportConnected component)
    (lengthAtLeastTwo :
      ∀ component ∈ components, 2 ≤ component.length) :
    ∃ endpoint interior,
      ListDerives components.flatten
        (gapEnvelopeRender endpoint interior) ∧
      endpoint ∉ interior ∧
      UniqueSeparatorTwoLimited
        (gapEnvelopeRender endpoint interior) ∧
      (∀ tested,
        (gapEnvelopeRender endpoint interior).count tested =
          min (components.flatten.count tested) 2) := by
  induction components with
  | nil =>
      exact False.elim (componentsNonempty rfl)
  | cons component rest induction =>
      obtain
        ⟨componentEndpoint, componentInterior,
          componentDerivation, _componentEndpointAbsent,
          _componentSorted, _componentLimited, componentCount⟩ :=
        existsConnectedComponentEnvelopeNormal
          (lengthAtLeastTwo component (by simp))
          (supportConnected component (by simp))
      cases rest with
      | nil =>
          refine
            ⟨componentEndpoint, componentInterior,
              ?_, _componentEndpointAbsent, _componentLimited, ?_⟩
          · simpa using componentDerivation
          · intro tested
            simpa using componentCount tested
      | cons next remaining =>
          have pairwiseTail :
              (next :: remaining).Pairwise
                ConnectedComponentSupportsDisjoint :=
            (List.pairwise_cons.mp pairwiseDisjoint).2
          obtain
            ⟨restEndpoint, restInterior, restDerivation,
              _restEndpointAbsent, _restLimited, restCount⟩ :=
            induction
              (by simp)
              pairwiseTail
              (fun current member =>
                supportConnected current
                  (List.Mem.tail component member))
              (fun current member =>
                lengthAtLeastTwo current
                  (List.Mem.tail component member))
          let mergedInterior :=
            componentInterior ++
              [restEndpoint, restEndpoint] ++ restInterior
          have normalizeFirst :
              ListDerives
                (component ++ (next :: remaining).flatten)
                (gapEnvelopeRender componentEndpoint componentInterior ++
                  (next :: remaining).flatten) :=
            S5_107.ListDerives.append componentDerivation
              (next :: remaining).flatten
          have normalizeRest :
              ListDerives
                (gapEnvelopeRender componentEndpoint componentInterior ++
                  (next :: remaining).flatten)
                (gapEnvelopeRender componentEndpoint componentInterior ++
                  gapEnvelopeRender restEndpoint restInterior) :=
            S5_107.ListDerives.prepend
              (gapEnvelopeRender componentEndpoint componentInterior)
              restDerivation
          have merge :
              ListDerives
                (gapEnvelopeRender componentEndpoint componentInterior ++
                  gapEnvelopeRender restEndpoint restInterior)
                (gapEnvelopeRender componentEndpoint mergedInterior) := by
            simpa [mergedInterior] using
              listDerivesAdjacentEnvelopeMerge
                componentEndpoint restEndpoint
                componentInterior restInterior
          have combined :
              ListDerives
                (component :: next :: remaining).flatten
                (gapEnvelopeRender componentEndpoint mergedInterior) := by
            simpa using
              normalizeFirst.trans (normalizeRest.trans merge)
          have mergePermutation :
              (gapEnvelopeRender componentEndpoint componentInterior ++
                  gapEnvelopeRender restEndpoint restInterior).Perm
                (gapEnvelopeRender componentEndpoint mergedInterior) := by
            simpa [mergedInterior] using
              adjacentEnvelopeMerge_perm
                componentEndpoint restEndpoint
                componentInterior restInterior
          have componentRestDisjoint :
              ConnectedComponentSupportsDisjoint
                component (next :: remaining).flatten :=
            supportsDisjoint_flatten
              (List.pairwise_cons.mp pairwiseDisjoint).1
          have mergedCount :
              ∀ tested,
                (gapEnvelopeRender componentEndpoint mergedInterior).count
                    tested =
                  min
                    ((component :: next :: remaining).flatten.count tested)
                    2 := by
            intro tested
            have permutationCount :=
              List.perm_iff_count.mp mergePermutation tested
            have oneSideZero :
                component.count tested = 0 ∨
                  (next :: remaining).flatten.count tested = 0 := by
              by_cases inComponent : tested ∈ component
              · right
                apply List.count_eq_zero.mpr
                intro inRest
                exact componentRestDisjoint tested inComponent inRest
              · left
                exact List.count_eq_zero.mpr inComponent
            rw [List.count_append, componentCount, restCount]
              at permutationCount
            simp only [List.flatten_cons, List.count_append]
            rcases oneSideZero with componentZero | restZero
            · simp [componentZero] at permutationCount ⊢
              exact permutationCount.symm
            · have restZeroExpanded :
                  next.count tested + remaining.flatten.count tested = 0 := by
                simpa only [List.flatten_cons, List.count_append] using
                  restZero
              simp [restZeroExpanded] at permutationCount ⊢
              exact permutationCount.symm
          have mergedLimited :
              UniqueSeparatorTwoLimited
                (gapEnvelopeRender componentEndpoint mergedInterior) := by
            intro tested
            rw [mergedCount tested]
            exact Nat.min_le_right _ _
          have mergedEndpointAbsent :
              componentEndpoint ∉ mergedInterior := by
            apply List.count_eq_zero.mp
            have endpointBound := mergedLimited componentEndpoint
            simp only [gapEnvelopeRender, List.count_cons_self,
              List.count_append, List.count_nil] at endpointBound
            omega
          exact
            ⟨componentEndpoint, mergedInterior, combined,
              mergedEndpointAbsent, mergedLimited, mergedCount⟩

private theorem pairwiseFlattenDisjoint
    {before after : List (List Nat)}
    (pairwise :
      (before ++ after).Pairwise
        ConnectedComponentSupportsDisjoint) :
    ConnectedComponentSupportsDisjoint
      before.flatten after.flatten := by
  have cross := (List.pairwise_append.mp pairwise).2.2
  intro tested testedInBefore testedInAfter
  rw [List.mem_flatten] at testedInBefore testedInAfter
  obtain ⟨left, leftMember, testedInLeft⟩ := testedInBefore
  obtain ⟨right, rightMember, testedInRight⟩ := testedInAfter
  exact
    (cross left leftMember right rightMember)
      tested testedInLeft testedInRight

private theorem singletonComponentExactCut
    {gap : List Nat} {before after : List (List Nat)}
    {separator : Nat}
    (decompositionEq :
      connectedComponentDecomposeList gap =
        before ++ [separator] :: after) :
    UniqueSeparatorFourExactCut gap
      before.flatten separator after.flatten := by
  have flattenEq := connectedComponentDecomposeList_flatten gap
  rw [decompositionEq] at flattenEq
  have gapShape :
      gap = before.flatten ++ separator :: after.flatten := by
    simpa [List.append_assoc] using flattenEq.symm
  have pairwise := connectedComponentDecomposeList_pairwiseDisjoint gap
  rw [decompositionEq] at pairwise
  have beforeSuffixDisjoint :
      ConnectedComponentSupportsDisjoint
        before.flatten ([separator] :: after).flatten :=
    pairwiseFlattenDisjoint
      (before := before) (after := [separator] :: after) pairwise
  have tailPairwise :
      ([separator] :: after).Pairwise
        ConnectedComponentSupportsDisjoint :=
    (List.pairwise_append.mp pairwise).2.1
  have singletonAfterDisjoint :
      ConnectedComponentSupportsDisjoint
        [[separator]].flatten after.flatten :=
    pairwiseFlattenDisjoint
      (before := [[separator]]) (after := after) (by
        simpa using tailPairwise)
  have separatorNotBefore : separator ∉ before.flatten := by
    intro separatorBefore
    apply beforeSuffixDisjoint separator separatorBefore
    change separator ∈ [separator] ++ after.flatten
    simp
  have separatorNotAfter : separator ∉ after.flatten := by
    exact singletonAfterDisjoint separator (by simp)
  have beforeCountZero : before.flatten.count separator = 0 :=
    List.count_eq_zero.mpr separatorNotBefore
  have afterCountZero : after.flatten.count separator = 0 :=
    List.count_eq_zero.mpr separatorNotAfter
  have countOne : gap.count separator = 1 := by
    rw [gapShape, List.count_append, List.count_cons_self,
      beforeCountZero, afterCountZero]
  have disjoint :
      UniqueSeparatorFourSupportsDisjoint
        before.flatten after.flatten := by
    intro tested testedInBefore testedInAfter
    apply beforeSuffixDisjoint tested testedInBefore
    change tested ∈ [separator] ++ after.flatten
    exact List.mem_append_right _ testedInAfter
  exact ⟨gapShape, countOne, disjoint⟩

private theorem componentLengthAtLeastTwoOfNoExactCut
    {gap component : List Nat}
    (noExactCut :
      ¬ ∃ left separator right,
        UniqueSeparatorFourExactCut gap left separator right)
    (componentMember :
      component ∈ connectedComponentDecomposeList gap) :
    2 ≤ component.length := by
  by_cases lengthAtLeastTwo : 2 ≤ component.length
  · exact lengthAtLeastTwo
  · have componentNonempty : component ≠ [] :=
      connectedComponentDecomposeList_nonempty_components
        gap component componentMember
    have componentPositive : 0 < component.length :=
      List.length_pos_iff.mpr componentNonempty
    have componentLengthOne : component.length = 1 := by
      omega
    obtain ⟨separator, componentEq⟩ :=
      List.length_eq_one_iff.mp componentLengthOne
    obtain ⟨before, after, decompositionEq⟩ :=
      List.mem_iff_append.mp componentMember
    have localCut :
        UniqueSeparatorFourExactCut gap
          before.flatten separator after.flatten := by
      apply singletonComponentExactCut
      simpa [componentEq] using decompositionEq
    exact False.elim <|
      noExactCut
        ⟨before.flatten, separator, after.flatten, localCut⟩

/-- Every nonempty exact-cut-free gap folds through all of its deterministic
support components to one cap-two envelope. This closes the arbitrary-length
gap-merge induction, but does not select a canonical endpoint or globally
sort the merged interior. -/
theorem existsGapEnvelopeNormalOfNoExactCut
    {gap : List Nat}
    (gapNonempty : gap ≠ [])
    (noExactCut :
      ¬ ∃ left separator right,
        UniqueSeparatorFourExactCut gap left separator right) :
    ∃ endpoint interior,
      ListDerives gap (gapEnvelopeRender endpoint interior) ∧
      endpoint ∉ interior ∧
      UniqueSeparatorTwoLimited
        (gapEnvelopeRender endpoint interior) ∧
      (∀ tested,
        (gapEnvelopeRender endpoint interior).count tested =
          min (gap.count tested) 2) := by
  obtain ⟨endpoint, interior, derivation,
      endpointAbsent, twoLimited, capped⟩ :=
    existsGapEnvelopeNormalOfComponents
      (connectedComponentDecomposeList gap)
      (connectedComponentDecomposeList_nonempty gapNonempty)
      (connectedComponentDecomposeList_pairwiseDisjoint gap)
      (connectedComponentDecomposeList_supportConnected gap)
      (fun component member =>
        componentLengthAtLeastTwoOfNoExactCut noExactCut member)
  rw [connectedComponentDecomposeList_flatten gap]
    at derivation capped
  exact
    ⟨endpoint, interior, derivation,
      endpointAbsent, twoLimited, capped⟩

/-- The canonical refinement still required after gap merging: choose the
least multiple endpoint and globally sort the cap-two interior. No inhabitant
of this proposition is asserted in the partial packet. -/
def CanonicalGapRefinementObligation : Prop :=
  ∀ (source : List Nat) (endpoint : Nat) (interior : List Nat),
    endpoint ∉ interior →
      UniqueSeparatorTwoLimited
        (gapEnvelopeRender endpoint interior) →
      (∀ tested,
        (gapEnvelopeRender endpoint interior).count tested =
          min (source.count tested) 2) →
      ∃ canonicalEndpoint canonicalInterior,
        ListDerives
          (gapEnvelopeRender endpoint interior)
          (gapEnvelopeRender canonicalEndpoint canonicalInterior) ∧
        canonicalEndpoint ∉ canonicalInterior ∧
        canonicalInterior.Pairwise (· ≤ ·) ∧
        (∀ tested,
          (gapEnvelopeRender
              canonicalEndpoint canonicalInterior).count tested =
            min (source.count tested) 2) ∧
        (∀ tested,
          2 ≤ source.count tested → canonicalEndpoint ≤ tested)

end SemigroupBasis.CoRoots.S5_378
