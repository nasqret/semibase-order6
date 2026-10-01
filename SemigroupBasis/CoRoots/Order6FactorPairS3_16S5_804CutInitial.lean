import SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitialFixedFinalReplay
import SemigroupBasis.Subdirect

/-!
# Global cut/initial normalization for the d024 B10 root

Endpoint capping first makes every connected component two-limited.  The
pending-aware fixed-final replay then normalizes that capped component to the
deterministic renderer of its exact cut/initial signature.  Pairwise-disjoint
component assembly identifies every local first-occurrence order with the
restriction of the global order, yielding one common normal word for the
literal `S3_16 x S5_804` factor intersection.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## Connected-component endpoint-cap bridge -/

/-- A nonempty support-connected list is one canonical component. -/
private theorem connectedComponentDecomposeList_eq_singleton
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
      have flattened :=
        connectedComponentDecomposeList_flatten letters
      rw [decompositionShape] at flattened
      have firstEq : first = letters := by
        simpa using flattened
      simpa [firstEq] using decompositionShape
  | cons second remaining =>
      have firstNonempty : first ≠ [] :=
        connectedComponentDecomposeList_nonempty_components letters
          first (by rw [decompositionShape]; simp)
      have suffixNonempty :
          (second :: remaining).flatten ≠ [] := by
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
      have flattened :=
        connectedComponentDecomposeList_flatten letters
      rw [decompositionShape] at flattened
      have sourceShape :
          letters = first ++ (second :: remaining).flatten := by
        simpa using flattened.symm
      obtain ⟨letter, firstMember, suffixMember⟩ :=
        connected first (second :: remaining).flatten
          sourceShape firstNonempty suffixNonempty
      exact False.elim <|
        disjoint letter firstMember suffixMember

/-- Endpoint capping preserves the exact signature of a connected component,
including its unary repetition bit and literal final letter. -/
private theorem connectedCutComponentSignature_endpointCap
    {head : Nat} {tail : List Nat}
    (connected :
      ConnectedComponentSupportConnected (head :: tail)) :
    S5_804.connectedCutComponentSignatureOfList
        (uniqueSeparatorEndpointCap (head :: tail)) =
      S5_804.connectedCutComponentSignatureOfList (head :: tail) := by
  have sourceDecomposition :=
    connectedComponentDecomposeList_eq_singleton
      (letters := head :: tail) (by simp) connected
  have cappedNonempty :
      uniqueSeparatorEndpointCap (head :: tail) ≠ [] := by
    apply List.ne_nil_of_mem
    exact
      (endpointCap_mem_iff head (head :: tail)).2 (by simp)
  have cappedConnected := endpointCap_supportConnected connected
  have cappedDecomposition :=
    connectedComponentDecomposeList_eq_singleton
      cappedNonempty cappedConnected
  have signatures :=
    connectedCutSignatures_endpointCap (head :: tail)
  simpa [S5_804.connectedCutSignaturesList,
    sourceDecomposition, cappedDecomposition] using signatures

/-! ## One connected component -/

/-- The component-local deterministic cut/initial normal list. -/
def cutInitialLocalNormalList (component : List Nat) : List Nat :=
  renderCutInitialComponent
    (firstOccurrenceSequence component)
    (S5_804.connectedCutComponentSignatureOfList component)

/-- Every nonempty support-connected component derives to its local
cut/initial normal list.  The only derivational steps are endpoint capping
and the kernel-checked pending-aware fixed-final replay. -/
theorem listDerivesCutInitialLocalNormal
    (component : List Nat)
    (nonempty : component ≠ [])
    (connected : ConnectedComponentSupportConnected component) :
    B10ListDerives component (cutInitialLocalNormalList component) := by
  obtain ⟨head, tail, rfl⟩ :=
    List.exists_cons_of_ne_nil nonempty
  let capped := uniqueSeparatorEndpointCap (head :: tail)
  have capDerivation :
      B10ListDerives (head :: tail) capped := by
    exact listDerivesEndpointCap (head :: tail)
  have cappedNonempty : capped ≠ [] := by
    apply List.ne_nil_of_mem
    exact
      (endpointCap_mem_iff head (head :: tail)).2 (by simp)
  have cappedConnected :
      ConnectedComponentSupportConnected capped := by
    exact endpointCap_supportConnected connected
  have cappedTwoLimited : UniqueSeparatorTwoLimited capped := by
    exact endpointCap_twoLimited (head :: tail)
  have fixedFinalDerivation :
      B10ListDerives capped
        (renderCutInitialComponent
          (firstOccurrenceSequence capped)
          (S5_804.connectedCutComponentSignatureOfList capped)) :=
    listDerivesConnectedTwoLimitedCutInitial
      capped cappedNonempty cappedConnected cappedTwoLimited
  have combined := capDerivation.trans fixedFinalDerivation
  have initialsEq :
      firstOccurrenceSequence capped =
        firstOccurrenceSequence (head :: tail) := by
    exact firstOccurrenceSequence_endpointCap (head :: tail)
  have signatureEq :
      S5_804.connectedCutComponentSignatureOfList capped =
        S5_804.connectedCutComponentSignatureOfList (head :: tail) := by
    exact connectedCutComponentSignature_endpointCap connected
  rw [initialsEq, signatureEq] at combined
  simpa [cutInitialLocalNormalList] using combined

/-! ## Local/global renderer identification -/

/-- Restricting a pairwise-disjoint component decomposition to one member
recovers that component exactly. -/
private theorem filter_component_of_pairwise :
    ∀ (components : List (List Nat)) (component : List Nat),
      components.Pairwise ConnectedComponentSupportsDisjoint →
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
            (S5_804.connectedCutComponentSignatureOfList
              component).base.support)) =
      firstOccurrenceSequence component := by
  have supportFilter :
      (firstOccurrenceSequence word.toList).filter
          (fun letter => decide
            (letter ∈
              (S5_804.connectedCutComponentSignatureOfList
                component).base.support)) =
        (firstOccurrenceSequence word.toList).filter
          (fun letter => decide (letter ∈ component)) := by
    apply List.filter_congr
    intro letter _
    simp [S5_804.connectedCutComponentSignatureOfList,
      connectedComponentSignatureOfList_support,
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
              (S5_804.connectedCutComponentSignatureOfList
                component).base.support)) =
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

/-- Restricting a component's own first-occurrence sequence to its exact
support changes nothing. -/
private theorem firstOccurrenceSequence_restrict_ownSupport
    (component : List Nat) :
    (firstOccurrenceSequence component).filter
        (fun letter => decide
          (letter ∈
            (S5_804.connectedCutComponentSignatureOfList
              component).base.support)) =
      firstOccurrenceSequence component := by
  apply List.filter_eq_self.mpr
  intro letter member
  simp only [decide_eq_true_eq]
  change
    letter ∈ (connectedComponentSignatureOfList component).support
  rw [connectedComponentSignatureOfList_support,
    connectedComponentSortedSupport_mem_iff]
  exact (mem_firstOccurrenceSequence_iff letter component).1 member

/-- A component-local renderer is literally its block in the global
deterministic renderer. -/
private theorem cutInitialLocalNormalList_eq_globalRender
    (word : Word Nat) {component : List Nat}
    (componentMember :
      component ∈ connectedComponentDecomposeList word.toList) :
    cutInitialLocalNormalList component =
      renderCutInitialComponent
        (firstOccurrenceSequence word.toList)
        (S5_804.connectedCutComponentSignatureOfList component) := by
  have localRestriction :=
    firstOccurrenceSequence_restrict_ownSupport component
  have globalRestriction :=
    firstOccurrenceSequence_restrict_component word componentMember
  unfold cutInitialLocalNormalList renderCutInitialComponent
  rw [localRestriction, globalRestriction]

private theorem flatMap_congr_of_mem
    {α β : Type} (left right : α → List β) :
    ∀ letters : List α,
      (∀ letter ∈ letters, left letter = right letter) →
      letters.flatMap left = letters.flatMap right
  | [], _ => rfl
  | letter :: rest, same => by
      rw [List.flatMap_cons, List.flatMap_cons,
        same letter (by simp)]
      exact congrArg (fun suffix => right letter ++ suffix) <|
        flatMap_congr_of_mem left right rest <| by
          intro selected member
          exact same selected (by simp [member])

/-- Flat-mapping the component-local normal lists is the global deterministic
normal list defined by the exact joint signature. -/
private theorem componentLocalNormals_eq_normalList
    (word : Word Nat) :
    (connectedComponentDecomposeList word.toList).flatMap
        cutInitialLocalNormalList =
      cutInitialNormalList word := by
  unfold cutInitialNormalList
    S5_804.connectedCutSignaturesWord
    S5_804.connectedCutSignaturesList
  rw [List.flatMap_map]
  apply flatMap_congr_of_mem
  intro component componentMember
  exact
    cutInitialLocalNormalList_eq_globalRender
      word componentMember

/-! ## Global component assembly -/

private theorem listDerivesComponentsLocalNormal :
    ∀ components : List (List Nat),
      (∀ component ∈ components, component ≠ []) →
      (∀ component ∈ components,
        ConnectedComponentSupportConnected component) →
      B10ListDerives components.flatten
        (components.flatMap cutInitialLocalNormalList)
  | [], _, _ =>
      S5_107.ListDerives.empty
  | component :: remaining, componentNonempty,
      componentConnected => by
      have headDerivation :=
        listDerivesCutInitialLocalNormal
          component
          (componentNonempty component (by simp))
          (componentConnected component (by simp))
      have tailNonempty :
          ∀ candidate ∈ remaining, candidate ≠ [] := by
        intro candidate member
        exact componentNonempty candidate (by simp [member])
      have tailConnected :
          ∀ candidate ∈ remaining,
            ConnectedComponentSupportConnected candidate := by
        intro candidate member
        exact componentConnected candidate (by simp [member])
      have tailDerivation :=
        listDerivesComponentsLocalNormal
          remaining tailNonempty tailConnected
      have first := headDerivation.append remaining.flatten
      have second :=
        tailDerivation.prepend
          (cutInitialLocalNormalList component)
      simpa [List.flatMap_cons, List.append_assoc] using
        first.trans second

/-- Every word's underlying list derives to the deterministic global
cut/initial normal list. -/
theorem listDerivesCutInitialNormal
    (word : Word Nat) :
    B10ListDerives word.toList (cutInitialNormalList word) := by
  have derivation :=
    listDerivesComponentsLocalNormal
      (connectedComponentDecomposeList word.toList)
      (connectedComponentDecomposeList_nonempty_components word.toList)
      (connectedComponentDecomposeList_supportConnected word.toList)
  rw [connectedComponentDecomposeList_flatten word.toList]
    at derivation
  rw [componentLocalNormals_eq_normalList word] at derivation
  exact derivation

/-! ## Word wrapper and unrestricted completeness -/

private def wordOfList : List Nat → Word Nat
  | [] => Word.singleton 0
  | head :: tail => ⟨head, tail⟩

/-- The deterministic global cut/initial normal word. -/
def cutInitialNormal (word : Word Nat) : Word Nat :=
  wordOfList (cutInitialNormalList word)

private theorem cutInitialNormalList_ne_nil (word : Word Nat) :
    cutInitialNormalList word ≠ [] := by
  cases word with
  | mk head tail =>
      exact S5_107.ListDerives.target_ne_nil
        (listDerivesCutInitialNormal ⟨head, tail⟩)

private theorem wordOfList_toList
    {letters : List Nat} (nonempty : letters ≠ []) :
    (wordOfList letters).toList = letters := by
  cases letters with
  | nil => contradiction
  | cons head tail => rfl

@[simp]
theorem cutInitialNormal_toList (word : Word Nat) :
    (cutInitialNormal word).toList = cutInitialNormalList word := by
  exact wordOfList_toList (cutInitialNormalList_ne_nil word)

/-- Every word derives to its deterministic global normal word. -/
theorem derivesCutInitialNormal (word : Word Nat) :
    Derives B10 word (cutInitialNormal word) := by
  cases word with
  | mk head tail =>
      have listDerivation :=
        listDerivesCutInitialNormal ⟨head, tail⟩
      obtain ⟨targetHead, targetTail, targetShape, wordDerivation⟩ :=
        S5_107.ListDerives.from_cons listDerivation
      simpa [cutInitialNormal, wordOfList, Word.toList,
        targetShape] using wordDerivation

/-- Equal exact joint signatures give equal deterministic normal words. -/
theorem cutInitialNormal_eq_of_sameSignature
    {left right : Word Nat}
    (same : SameCutInitialSignature left right) :
    cutInitialNormal left = cutInitialNormal right := by
  apply Word.toList_injective
  rw [cutInitialNormal_toList, cutInitialNormal_toList,
    cutInitialNormalList_eq_of_sameSignature same]

/-- The exact cut/initial signature is sufficient for a literal B10
derivation, with no bounded-search or factor-basis retargeting. -/
theorem derivesOfSameCutInitialSignature
    {left right : Word Nat}
    (same : SameCutInitialSignature left right) :
    Derives B10 left right := by
  have leftNormal := derivesCutInitialNormal left
  have rightNormal := derivesCutInitialNormal right
  have normalEqual := cutInitialNormal_eq_of_sameSignature same
  rw [normalEqual] at leftNormal
  exact leftNormal.trans rightNormal.symm

/-- Joint validity in the two selected direct factors is derivationally
complete for literal B10. -/
theorem derivesOfFactorValidity
    (identity : Identity Nat)
    (leftValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.S3_16.table.semigroup)
    (rightValid :
      identity.SatisfiedBy
        SemigroupBasis.Generated.Catalogue.S5_804.table.semigroup) :
    Derives B10 identity.lhs identity.rhs :=
  derivesOfSameCutInitialSignature <|
    sameCutInitialSignature_of_factor_valid
      identity leftValid rightValid

/-- The exact unrestricted direct factor-intersection root for d024. -/
def intersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_16.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_804.table.semigroup
      B10 where
  leftModels := s3_16_models
  rightModels := s5_804_models
  complete := derivesOfFactorValidity

/-- Descriptive compatibility name for downstream d024 target modules. -/
abbrev intersectionBasisS3_16S5_804 := intersectionBasis

end SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_804CutInitial
