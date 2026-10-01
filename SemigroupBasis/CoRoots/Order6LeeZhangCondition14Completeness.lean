import SemigroupBasis.CoRoots.Order6LeeZhangCondition14EndpointNormal

/-!
# Lee--Zhang Condition 14: unrestricted completeness

The connected-component normalizer is local: it selects parity blocks using
the component itself.  This file assembles those local derivations globally.
Pairwise disjointness of the canonical component decomposition identifies
both the restricted first-occurrence order and every relevant occurrence
count with their whole-word counterparts.  Consequently every word derives
to `componentInitialParityNormalList`, and equality of the exact product
signature gives an unrestricted derivation.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeZhangCondition14Completeness

open SemigroupBasis
open SemigroupBasis.Examples
open SemigroupBasis.CoRoots.Order6LeeZhangAmbientConditions.Condition14

private abbrev ListDerives : List Nat -> List Nat -> Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives basis

private theorem mem_firstOccurrenceSequence_iff
    (selected : Nat) :
    forall letters : List Nat,
      selected ∈ firstOccurrenceSequence letters ↔ selected ∈ letters
  | [] => by
      simp [firstOccurrenceSequence]
  | letter :: remaining => by
      by_cases equal : selected = letter
      · subst letter
        simp [firstOccurrenceSequence]
      · simp [firstOccurrenceSequence, equal,
          mem_firstOccurrenceSequence_iff selected remaining]

private theorem filter_filter_ne_comm
    (keep : Nat -> Bool) (selected : Nat) (letters : List Nat) :
    (letters.filter keep).filter
        (fun letter => decide (letter ≠ selected)) =
      (letters.filter
        (fun letter => decide (letter ≠ selected))).filter keep := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro letter _
  exact Bool.and_comm _ _

private theorem filter_ne_then_keep_of_drop
    (keep : Nat -> Bool) (selected : Nat)
    (dropped : ¬keep selected) (letters : List Nat) :
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

/-- First-occurrence normalization commutes with a support restriction. -/
private theorem firstOccurrenceSequence_filter
    (keep : Nat -> Bool) :
    forall letters : List Nat,
      firstOccurrenceSequence (letters.filter keep) =
        (firstOccurrenceSequence letters).filter keep
  | [] => rfl
  | letter :: remaining => by
      by_cases kept : keep letter
      · rw [List.filter_cons, if_pos kept,
          firstOccurrenceSequence, firstOccurrenceSequence,
          firstOccurrenceSequence_filter keep remaining,
          List.filter_cons, if_pos kept]
        exact congrArg (List.cons letter) <|
          filter_filter_ne_comm keep letter
            (firstOccurrenceSequence remaining)
      · rw [List.filter_cons, if_neg kept,
          firstOccurrenceSequence_filter keep remaining,
          firstOccurrenceSequence, List.filter_cons, if_neg kept]
        exact
          (filter_ne_then_keep_of_drop keep letter kept
            (firstOccurrenceSequence remaining)).symm

/-- Restricting the flattened canonical decomposition to one of its pairwise
disjoint components recovers that component exactly. -/
private theorem filter_component_of_pairwise :
    forall (components : List (List Nat)) (component : List Nat),
      components.Pairwise ConnectedComponentSupportsDisjoint ->
      component ∈ components →
      components.flatten.filter
          (fun letter => decide (letter ∈ component)) =
        component
  | [], component, _, member => by
      simp at member
  | current :: remaining, component, pairwise, member => by
      rw [List.pairwise_cons] at pairwise
      rcases List.mem_cons.mp member with componentEq | componentMember
      · subst component
        have currentFilter :
            current.filter
                (fun letter => decide (letter ∈ current)) =
              current := by
          apply List.filter_eq_self.mpr
          intro letter letterMember
          exact decide_eq_true letterMember
        have remainingFilter :
            remaining.flatten.filter
                (fun letter => decide (letter ∈ current)) =
              [] := by
          apply List.filter_eq_nil_iff.mpr
          intro letter flattenedMember
          simp only [decide_eq_true_eq]
          intro currentMember
          rw [List.mem_flatten] at flattenedMember
          rcases flattenedMember with
            ⟨candidate, candidateMember, candidateContains⟩
          exact
            (pairwise.1 candidate candidateMember
              letter currentMember) candidateContains
        simp [currentFilter, remainingFilter]
      · have currentFilter :
            current.filter
                (fun letter => decide (letter ∈ component)) =
              [] := by
          apply List.filter_eq_nil_iff.mpr
          intro letter currentMember
          simp only [decide_eq_true_eq]
          intro componentContains
          exact
            (pairwise.1 component componentMember
              letter currentMember) componentContains
        rw [List.flatten_cons, List.filter_append,
          currentFilter, List.nil_append]
        exact
          filter_component_of_pairwise
            remaining component pairwise.2 componentMember

/-- The global first-occurrence sequence restricted to one canonical
component is its local first-occurrence sequence. -/
private theorem firstOccurrenceSequence_restrict_component
    (word : Word Nat) {component : List Nat}
    (componentMember :
      component ∈ connectedComponentDecomposeList word.toList) :
    (firstOccurrenceSequence word.toList).filter
        (fun letter => decide
          (letter ∈
            (connectedComponentSignatureOfList component).support)) =
      firstOccurrenceSequence component := by
  have supportFilter :
      (firstOccurrenceSequence word.toList).filter
          (fun letter => decide
            (letter ∈
              (connectedComponentSignatureOfList component).support)) =
        (firstOccurrenceSequence word.toList).filter
          (fun letter => decide (letter ∈ component)) := by
    apply List.filter_congr
    intro letter _
    simp [connectedComponentSignatureOfList_support,
      connectedComponentSortedSupport_mem_iff]
  have wholeFilter :
      word.toList.filter
          (fun letter => decide (letter ∈ component)) =
        component := by
    rw [← connectedComponentDecomposeList_flatten word.toList]
    exact
      filter_component_of_pairwise
        (connectedComponentDecomposeList word.toList)
        component
        (connectedComponentDecomposeList_pairwiseDisjoint word.toList)
        componentMember
  calc
    (firstOccurrenceSequence word.toList).filter
          (fun letter => decide
            (letter ∈
              (connectedComponentSignatureOfList component).support)) =
        (firstOccurrenceSequence word.toList).filter
          (fun letter => decide (letter ∈ component)) :=
      supportFilter
    _ = firstOccurrenceSequence
          (word.toList.filter
            (fun letter => decide (letter ∈ component))) :=
      (firstOccurrenceSequence_filter
        (fun letter => decide (letter ∈ component))
        word.toList).symm
    _ = firstOccurrenceSequence component := by
      rw [wholeFilter]

private theorem firstOccurrenceSequence_restrict_ownSupport
    (component : List Nat) :
    (firstOccurrenceSequence component).filter
        (fun letter => decide
          (letter ∈
            (connectedComponentSignatureOfList component).support)) =
      firstOccurrenceSequence component := by
  apply List.filter_eq_self.mpr
  intro letter member
  simp only [decide_eq_true_eq]
  rw [connectedComponentSignatureOfList_support,
    connectedComponentSortedSupport_mem_iff]
  exact (mem_firstOccurrenceSequence_iff letter component).1 member

private theorem count_filter_of_keep
    (keep : Nat -> Bool) {selected : Nat} (kept : keep selected) :
    forall letters : List Nat,
      (letters.filter keep).count selected = letters.count selected
  | [] => rfl
  | letter :: remaining => by
      by_cases letterKept : keep letter
      · rw [List.filter_cons, if_pos letterKept]
        simp only [List.count_cons]
        rw [count_filter_of_keep keep kept remaining]
      · rw [List.filter_cons, if_neg letterKept]
        have different : selected ≠ letter := by
          intro equal
          subst letter
          exact letterKept kept
        rw [List.count_cons_of_ne (Ne.symm different)]
        exact count_filter_of_keep keep kept remaining

/-- Every letter belonging to a canonical component has the same exact count
in that component as in the whole word. -/
private theorem count_eq_count_component
    (word : Word Nat) {component : List Nat}
    (componentMember :
      component ∈ connectedComponentDecomposeList word.toList)
    {letter : Nat} (letterMember : letter ∈ component) :
    word.toList.count letter = component.count letter := by
  have wholeFilter :
      word.toList.filter
          (fun candidate => decide (candidate ∈ component)) =
        component := by
    rw [← connectedComponentDecomposeList_flatten word.toList]
    exact
      filter_component_of_pairwise
        (connectedComponentDecomposeList word.toList)
        component
        (connectedComponentDecomposeList_pairwiseDisjoint word.toList)
        componentMember
  have restrictedCount :=
    count_filter_of_keep
      (fun candidate => decide (candidate ∈ component))
      (selected := letter) (by simpa using letterMember) word.toList
  rw [wholeFilter] at restrictedCount
  exact restrictedCount.symm

/-- The local and global sources select the same parity for every letter of a
canonical component. -/
private theorem count_mod_two_eq_component
    (word : Word Nat) {component : List Nat}
    (componentMember :
      component ∈ connectedComponentDecomposeList word.toList)
    {letter : Nat} (letterMember : letter ∈ component) :
    word.toList.count letter % 2 = component.count letter % 2 := by
  rw [count_eq_count_component word componentMember letterMember]

private theorem componentParityBlock_eq_global
    (word : Word Nat) {component : List Nat}
    (componentMember :
      component ∈ connectedComponentDecomposeList word.toList)
    (anchor letter : Nat) (letterMember : letter ∈ component) :
    componentParityBlock component anchor letter =
      componentParityBlock word.toList anchor letter := by
  unfold componentParityBlock
  rw [← count_mod_two_eq_component
    word componentMember letterMember]

private theorem flatMap_congr_of_mem
    {alpha beta : Type} (left right : alpha -> List beta) :
    forall letters : List alpha,
      (∀ letter, letter ∈ letters → left letter = right letter) →
      letters.flatMap left = letters.flatMap right
  | [], _ => rfl
  | letter :: remaining, same => by
      rw [List.flatMap_cons, List.flatMap_cons,
        same letter (by simp)]
      exact congrArg (fun suffix => right letter ++ suffix) <|
        flatMap_congr_of_mem left right remaining <| by
          intro selected member
          exact same selected (by simp [member])

private def componentInitialParityLocalNormalList
    (component : List Nat) : List Nat :=
  componentInitialParityRender component
    (firstOccurrenceSequence component)
    (connectedComponentSignatureOfList component)

/-- A component-local parity renderer is literally the corresponding block
of the whole-word canonical renderer. -/
private theorem componentInitialParityLocalNormal_eq_globalRender
    (word : Word Nat) {component : List Nat}
    (componentMember :
      component ∈ connectedComponentDecomposeList word.toList) :
    componentInitialParityLocalNormalList component =
      componentInitialParityRender word.toList
        (firstOccurrenceSequence word.toList)
        (connectedComponentSignatureOfList component) := by
  have localRestriction :=
    firstOccurrenceSequence_restrict_ownSupport component
  have globalRestriction :=
    firstOccurrenceSequence_restrict_component word componentMember
  unfold componentInitialParityLocalNormalList
    componentInitialParityRender
  rw [localRestriction, globalRestriction]
  by_cases simple :
      (connectedComponentSignatureOfList component).support.length = 1 ∧
        (connectedComponentSignatureOfList component).repeatedUnary = false
  · simp [simple]
  · simp only [simple, ↓reduceIte]
    cases initialsShape : firstOccurrenceSequence component with
    | nil =>
        simp
    | cons anchor remaining =>
        have anchorMember : anchor ∈ component := by
          exact (mem_firstOccurrenceSequence_iff anchor component).1 <| by
            rw [initialsShape]
            simp
        have anchorBlock :
            componentParityBlock component anchor anchor =
              componentParityBlock
                word.toList anchor anchor :=
          componentParityBlock_eq_global
            word componentMember anchor anchor anchorMember
        have remainingBlocks :
            remaining.flatMap
                (componentParityBlock component anchor) =
              remaining.flatMap
                (componentParityBlock word.toList anchor) := by
          apply flatMap_congr_of_mem
          intro letter letterMember
          have inInitials :
              letter ∈ firstOccurrenceSequence component := by
            rw [initialsShape]
            simp [letterMember]
          exact
            componentParityBlock_eq_global
              word componentMember anchor letter
              ((mem_firstOccurrenceSequence_iff letter component).1
                inInitials)
        change
          componentParityBlock component anchor anchor ++
                remaining.flatMap
                  (componentParityBlock component anchor) ++ [anchor] =
            componentParityBlock word.toList anchor anchor ++
                remaining.flatMap
                  (componentParityBlock word.toList anchor) ++ [anchor]
        rw [anchorBlock, remainingBlocks]

private theorem componentLocalNormals_eq_normalList
    (word : Word Nat) :
    (connectedComponentDecomposeList word.toList).flatMap
        componentInitialParityLocalNormalList =
      componentInitialParityNormalList word := by
  unfold componentInitialParityNormalList
    connectedComponentSignaturesWord
    connectedComponentSignaturesList
  rw [List.flatMap_map]
  apply flatMap_congr_of_mem
  intro component componentMember
  exact
    componentInitialParityLocalNormal_eq_globalRender
      word componentMember

private theorem listDerivesComponentsLocalNormal :
    forall components : List (List Nat),
      (∀ component, component ∈ components → component ≠ []) →
      (∀ component, component ∈ components →
        ConnectedComponentSupportConnected component) ->
      ListDerives components.flatten
        (components.flatMap componentInitialParityLocalNormalList)
  | [], _, _ =>
      SemigroupBasis.CoRoots.S5_107.ListDerives.empty
  | component :: remaining, componentNonempty,
      componentConnected => by
      have headDerivation :
          ListDerives component
            (componentInitialParityLocalNormalList component) := by
        simpa [componentInitialParityLocalNormalList] using
          listDerivesComponentInitialParityLocalNormal
            component
            (componentNonempty component (by simp))
            (componentConnected component (by simp))
      have tailNonempty :
          ∀ candidate, candidate ∈ remaining → candidate ≠ [] := by
        intro candidate member
        exact componentNonempty candidate (by simp [member])
      have tailConnected :
          ∀ candidate, candidate ∈ remaining →
            ConnectedComponentSupportConnected candidate := by
        intro candidate member
        exact componentConnected candidate (by simp [member])
      have tailDerivation :=
        listDerivesComponentsLocalNormal
          remaining tailNonempty tailConnected
      have first := headDerivation.append remaining.flatten
      have second :=
        tailDerivation.prepend
          (componentInitialParityLocalNormalList component)
      simpa [List.flatMap_cons, List.append_assoc] using
        first.trans second

/-- Every word derives to its deterministic component/initial/parity normal
form. -/
theorem listDerivesComponentInitialParityNormal
    (word : Word Nat) :
    SemigroupBasis.CoRoots.S5_107.ListDerives basis
      word.toList (componentInitialParityNormalList word) := by
  have derivation :=
    listDerivesComponentsLocalNormal
      (connectedComponentDecomposeList word.toList)
      (connectedComponentDecomposeList_nonempty_components word.toList)
      (connectedComponentDecomposeList_supportConnected word.toList)
  rw [connectedComponentDecomposeList_flatten word.toList] at derivation
  rw [componentLocalNormals_eq_normalList word] at derivation
  exact derivation

/-- Equality of the exact product-factor signature is sufficient for a
derivation from the six Condition 14 laws. -/
theorem derives_of_sameComponentInitialParitySignature
    {left right : Word Nat}
    (same :
      SameComponentInitialParitySignature left right) :
    Derives basis left right := by
  have leftNormal :=
    listDerivesComponentInitialParityNormal left
  have rightNormal :=
    listDerivesComponentInitialParityNormal right
  have normalEqual :=
    componentInitialParityNormalList_eq_of_sameSignature same
  rw [normalEqual] at leftNormal
  have combined := leftNormal.trans rightNormal.symm
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          exact SemigroupBasis.CoRoots.S5_107.ListDerives.toWord combined

/-- Unconditional unrestricted completeness for Lee--Zhang Condition 14. -/
theorem complete : DerivationalObligation := by
  intro identity cyclicValid coreValid
  exact
    derives_of_sameComponentInitialParitySignature
      (valid_sameComponentInitialParitySignature
        identity cyclicValid coreValid)

end SemigroupBasis.CoRoots.Order6LeeZhangCondition14Completeness
