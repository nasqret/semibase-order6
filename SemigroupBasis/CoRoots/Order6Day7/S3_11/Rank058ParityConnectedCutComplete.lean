import SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank058ParityComponentReplay
import SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank058ParityConnectedCutDiagnostic

/-!
# Unrestricted owner completeness for the actual rank-058 opposite cut

The opposite detector already decomposes the REVERSED source word.  Aligning
those actual reversed component streams directly avoids any guessed
`decompose(reverse)` theorem.  Equal final coordinates in the detector's
component signature become equal FIRST endpoints after each component is
reversed back; the component module then supplies the frozen-owner proof.

No lower-factor derivation is replayed, no finite-table separation is assumed,
and quotient normalization is introduced only after the owner intersection is
constructed.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 15000000

namespace SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank058.ParityConnectedCutComplete

open SemigroupBasis
open SemigroupBasis.Examples

private abbrev targetBasis : List (Identity Nat) := Rank058.basis

abbrev ListDerives : List Nat → List Nat → Prop :=
  SemigroupBasis.CoRoots.S5_107.ListDerives targetBasis

private abbrev componentSignature (component : List Nat) :=
  S5_804.connectedCutComponentSignatureOfList component

private theorem componentSignature_mem_of_mem
    {component : List Nat} {tested : Nat}
    (member : tested ∈ component) :
    tested ∈ (componentSignature component).base.support := by
  change tested ∈ (connectedComponentSignatureOfList component).support
  rw [connectedComponentSignatureOfList_support,
    connectedComponentSortedSupport_mem_iff]
  exact member

private theorem component_mem_of_signature_mem
    {component : List Nat} {tested : Nat}
    (member : tested ∈ (componentSignature component).base.support) :
    tested ∈ component := by
  change tested ∈ (connectedComponentSignatureOfList component).support at member
  rwa [connectedComponentSignatureOfList_support,
    connectedComponentSortedSupport_mem_iff] at member

private theorem componentSupport_iff_of_signature_eq
    {left right : List Nat}
    (same : componentSignature left = componentSignature right)
    (tested : Nat) :
    tested ∈ left ↔ tested ∈ right := by
  constructor
  · intro member
    apply component_mem_of_signature_mem
    rw [← same]
    exact componentSignature_mem_of_mem member
  · intro member
    apply component_mem_of_signature_mem
    rw [same]
    exact componentSignature_mem_of_mem member

private theorem length_eq_one_of_signature_eq
    {left right : List Nat}
    (same : componentSignature left = componentSignature right)
    (leftLength : left.length = 1) :
    right.length = 1 := by
  have baseSame :
      connectedComponentSignatureOfList left =
        connectedComponentSignatureOfList right :=
    congrArg S5_804.ConnectedCutComponentSignature.base same
  obtain ⟨letter, rfl⟩ := List.length_eq_one_iff.mp leftLength
  have leftSignature :
      connectedComponentSignatureOfList [letter] =
        ⟨[letter], false⟩ := by
    simp [connectedComponentSignatureOfList,
      connectedComponentSortedSupport,
      connectedComponentDistinctSupport]
  have rightSignature :
      connectedComponentSignatureOfList right =
        ⟨[letter], false⟩ := by
    rw [← baseSame, leftSignature]
  have rightSupport :
      connectedComponentSortedSupport right = [letter] := by
    rw [← connectedComponentSignatureOfList_support]
    exact congrArg connectedComponentSignature.support rightSignature
  have repeatedFalse :
      decide (right.length ≠ 1) = false := by
    simpa [connectedComponentSignatureOfList, rightSupport] using
      congrArg connectedComponentSignature.repeatedUnary rightSignature
  by_cases lengthOne : right.length = 1
  · exact lengthOne
  · exact False.elim ((of_decide_eq_false repeatedFalse) lengthOne)

private theorem getLastD_append
    (left right : List Nat) (fallback : Nat) :
    (left ++ right).getLastD fallback =
      right.getLastD (left.getLastD fallback) := by
  induction left generalizing fallback with
  | nil => rfl
  | cons head tail induction =>
      simp only [List.cons_append, List.getLastD_cons]
      exact induction head

private theorem componentFinal_append_singleton
    (initial : List Nat) (last : Nat) :
    S5_804.componentFinal (initial ++ [last]) = last := by
  cases initial with
  | nil => rfl
  | cons head tail =>
      simp only [List.cons_append, S5_804.componentFinal]
      rw [getLastD_append]
      rfl

private theorem componentFinal_of_reverse_cons
    {letters : List Nat} {head : Nat} {tail : List Nat}
    (shape : letters.reverse = head :: tail) :
    S5_804.componentFinal letters = head := by
  have reconstruction := congrArg List.reverse shape
  have split : letters = tail.reverse ++ [head] := by
    simpa [List.reverse_cons] using reconstruction
  rw [split]
  exact componentFinal_append_singleton tail.reverse head

/-- An opposite signature fixes support, unary stratum, and ACTUAL first. -/
theorem listDerivesReversedConnectedComponents
    {left right : List Nat}
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (leftConnected : ConnectedComponentSupportConnected left)
    (rightConnected : ConnectedComponentSupportConnected right)
    (sameSignature : componentSignature left = componentSignature right)
    (sameParity : ∀ tested,
      left.count tested % 2 = right.count tested % 2) :
    ListDerives left.reverse right.reverse := by
  by_cases leftLengthOne : left.length = 1
  · have rightLengthOne :=
      length_eq_one_of_signature_eq sameSignature leftLengthOne
    obtain ⟨leftLetter, rfl⟩ := List.length_eq_one_iff.mp leftLengthOne
    obtain ⟨rightLetter, rfl⟩ := List.length_eq_one_iff.mp rightLengthOne
    have lettersEqual : leftLetter = rightLetter := by
      have support :=
        componentSupport_iff_of_signature_eq sameSignature leftLetter
      exact by simpa using support.mp (by simp)
    subst rightLetter
    exact S5_107.ListDerives.refl _
  · have rightLengthNotOne : right.length ≠ 1 := by
      intro rightLengthOne
      exact leftLengthOne
        (length_eq_one_of_signature_eq sameSignature.symm rightLengthOne)
    have leftAtLeastTwo : 2 ≤ left.reverse.length := by
      have positive : 0 < left.length :=
        List.length_pos_iff.mpr leftNonempty
      simp only [List.length_reverse]
      omega
    have rightAtLeastTwo : 2 ≤ right.reverse.length := by
      have positive : 0 < right.length :=
        List.length_pos_iff.mpr rightNonempty
      simp only [List.length_reverse]
      omega
    have leftReverseNonempty : left.reverse ≠ [] := by
      simpa using leftNonempty
    have rightReverseNonempty : right.reverse ≠ [] := by
      simpa using rightNonempty
    obtain ⟨leftHead, leftTail, leftShape⟩ :=
      List.exists_cons_of_ne_nil leftReverseNonempty
    obtain ⟨rightHead, rightTail, rightShape⟩ :=
      List.exists_cons_of_ne_nil rightReverseNonempty
    have sameFirst : leftHead = rightHead := by
      calc
        leftHead = S5_804.componentFinal left :=
          (componentFinal_of_reverse_cons leftShape).symm
        _ = S5_804.componentFinal right :=
          congrArg S5_804.ConnectedCutComponentSignature.final sameSignature
        _ = rightHead := componentFinal_of_reverse_cons rightShape
    subst rightHead
    have leftConnected' :
        ConnectedComponentSupportConnected (leftHead :: leftTail) := by
      rw [← leftShape]
      exact S5_804.connectedComponentSupportConnected_reverse leftConnected
    have rightConnected' :
        ConnectedComponentSupportConnected (leftHead :: rightTail) := by
      rw [← rightShape]
      exact S5_804.connectedComponentSupportConnected_reverse rightConnected
    have leftLength : 2 ≤ (leftHead :: leftTail).length := by
      rw [← leftShape]
      exact leftAtLeastTwo
    have rightLength : 2 ≤ (leftHead :: rightTail).length := by
      rw [← rightShape]
      exact rightAtLeastTwo
    have support : ∀ tested,
        tested ∈ leftHead :: leftTail ↔
          tested ∈ leftHead :: rightTail := by
      intro tested
      have original := componentSupport_iff_of_signature_eq sameSignature tested
      simpa [← leftShape, ← rightShape] using original
    have parity : ∀ tested,
        (leftHead :: leftTail).count tested % 2 =
          (leftHead :: rightTail).count tested % 2 := by
      intro tested
      simpa [← leftShape, ← rightShape] using sameParity tested
    have closed :=
      ParityComponentReplay.listDerivesConnectedComponentsOfSameHeadSupportParity
        leftConnected' rightConnected' leftLength rightLength support parity
    simpa [leftShape, rightShape] using closed

private theorem flatten_mem_of_signatures_eq
    {left right : List (List Nat)} {tested : Nat}
    (same : left.map componentSignature = right.map componentSignature)
    (member : tested ∈ left.flatten) :
    tested ∈ right.flatten := by
  rcases List.mem_flatten.mp member with
    ⟨component, componentMember, testedMember⟩
  have signatureMember : componentSignature component ∈
      right.map componentSignature := by
    rw [← same]
    exact List.mem_map.mpr ⟨component, componentMember, rfl⟩
  rcases List.mem_map.mp signatureMember with
    ⟨target, targetMember, signatureEq⟩
  apply List.mem_flatten_of_mem targetMember
  apply component_mem_of_signature_mem
  rw [signatureEq]
  exact componentSignature_mem_of_mem testedMember

private theorem flatten_mem_iff_of_signatures_eq
    {left right : List (List Nat)}
    (same : left.map componentSignature = right.map componentSignature)
    (tested : Nat) :
    tested ∈ left.flatten ↔ tested ∈ right.flatten :=
  ⟨fun member => flatten_mem_of_signatures_eq same member,
    fun member => flatten_mem_of_signatures_eq same.symm member⟩

private theorem count_flatten_eq_component
    {components : List (List Nat)} {component : List Nat} {tested : Nat}
    (pairwise : components.Pairwise ConnectedComponentSupportsDisjoint)
    (componentMember : component ∈ components)
    (testedMember : tested ∈ component) :
    components.flatten.count tested = component.count tested := by
  induction components with
  | nil => simp at componentMember
  | cons current remaining induction =>
      rw [List.pairwise_cons] at pairwise
      rcases List.mem_cons.mp componentMember with rfl | componentMember
      · have remainingAbsent : tested ∉ remaining.flatten := by
          intro remainingMember
          rcases List.mem_flatten.mp remainingMember with
            ⟨candidate, candidateMember, candidateContains⟩
          exact
            (pairwise.1 candidate candidateMember tested testedMember)
              candidateContains
        simp [List.count_eq_zero.mpr remainingAbsent]
      · have currentAbsent : tested ∉ current := by
          intro currentMember
          exact
            (pairwise.1 component componentMember tested currentMember)
              testedMember
        rw [List.flatten_cons, List.count_append,
          List.count_eq_zero.mpr currentAbsent,
          induction pairwise.2 componentMember]
        simp

private theorem head_disjoint_flatten
    {head : List Nat} {tail : List (List Nat)}
    (disjoint : ∀ component, component ∈ tail →
      ConnectedComponentSupportsDisjoint head component) :
    ConnectedComponentSupportsDisjoint head tail.flatten := by
  intro tested headMember tailMember
  rcases List.mem_flatten.mp tailMember with
    ⟨component, componentMember, componentContains⟩
  exact
    (disjoint component componentMember tested headMember)
      componentContains

/-- Align the detector's REVERSED component stream directly. -/
theorem listDerivesReverseAlignedComponents :
    ∀ (leftComponents rightComponents : List (List Nat)),
      (∀ component, component ∈ leftComponents → component ≠ []) →
      (∀ component, component ∈ rightComponents → component ≠ []) →
      leftComponents.Pairwise ConnectedComponentSupportsDisjoint →
      rightComponents.Pairwise ConnectedComponentSupportsDisjoint →
      (∀ component, component ∈ leftComponents →
        ConnectedComponentSupportConnected component) →
      (∀ component, component ∈ rightComponents →
        ConnectedComponentSupportConnected component) →
      leftComponents.map componentSignature =
        rightComponents.map componentSignature →
      (∀ tested,
        leftComponents.flatten.count tested % 2 =
          rightComponents.flatten.count tested % 2) →
      ListDerives leftComponents.flatten.reverse
        rightComponents.flatten.reverse
  | [], rightComponents, _, _, _, _, _, _, signaturesEqual, _ => by
      cases rightComponents with
      | nil => exact S5_107.ListDerives.empty
      | cons rightHead rightTail => simp at signaturesEqual
  | leftHead :: leftTail, rightComponents,
      leftNonempty, rightNonempty,
      leftPairwise, rightPairwise,
      leftConnected, rightConnected,
      signaturesEqual, wholeParity => by
      cases rightComponents with
      | nil => simp at signaturesEqual
      | cons rightHead rightTail =>
          have leftPairwiseAll := leftPairwise
          have rightPairwiseAll := rightPairwise
          rw [List.pairwise_cons] at leftPairwise rightPairwise
          simp only [List.map_cons, List.cons.injEq] at signaturesEqual
          have headParity : ∀ tested,
              leftHead.count tested % 2 =
                rightHead.count tested % 2 := by
            intro tested
            by_cases leftMember : tested ∈ leftHead
            · have leftSupport := componentSignature_mem_of_mem leftMember
              have rightSupport :
                  tested ∈ (componentSignature rightHead).base.support := by
                rw [← signaturesEqual.1]
                exact leftSupport
              have rightMember :=
                component_mem_of_signature_mem rightSupport
              have leftWholeCount :=
                count_flatten_eq_component
                  leftPairwiseAll (by simp) leftMember
              have rightWholeCount :=
                count_flatten_eq_component
                  rightPairwiseAll (by simp) rightMember
              rw [← leftWholeCount, ← rightWholeCount]
              exact wholeParity tested
            · have rightAbsent : tested ∉ rightHead := by
                intro rightMember
                have rightSupport :=
                  componentSignature_mem_of_mem rightMember
                have leftSupport :
                    tested ∈ (componentSignature leftHead).base.support := by
                  rw [signaturesEqual.1]
                  exact rightSupport
                exact leftMember
                  (component_mem_of_signature_mem leftSupport)
              rw [List.count_eq_zero.mpr leftMember,
                List.count_eq_zero.mpr rightAbsent]
          have headDerivation : ListDerives leftHead.reverse rightHead.reverse :=
            listDerivesReversedConnectedComponents
              (leftNonempty leftHead (by simp))
              (rightNonempty rightHead (by simp))
              (leftConnected leftHead (by simp))
              (rightConnected rightHead (by simp))
              signaturesEqual.1 headParity
          have tailParity : ∀ tested,
              leftTail.flatten.count tested % 2 =
                rightTail.flatten.count tested % 2 := by
            intro tested
            by_cases leftTailMember : tested ∈ leftTail.flatten
            · have rightTailMember : tested ∈ rightTail.flatten :=
                (flatten_mem_iff_of_signatures_eq
                  signaturesEqual.2 tested).mp leftTailMember
              have leftHeadAbsent : tested ∉ leftHead := by
                intro leftHeadMember
                exact
                  (head_disjoint_flatten leftPairwise.1
                    tested leftHeadMember) leftTailMember
              have rightHeadAbsent : tested ∉ rightHead := by
                intro rightHeadMember
                exact
                  (head_disjoint_flatten rightPairwise.1
                    tested rightHeadMember) rightTailMember
              have parity := wholeParity tested
              simp only [List.flatten_cons, List.count_append] at parity
              rw [List.count_eq_zero.mpr leftHeadAbsent,
                List.count_eq_zero.mpr rightHeadAbsent] at parity
              simpa using parity
            · have rightTailAbsent : tested ∉ rightTail.flatten := by
                intro rightTailMember
                exact leftTailMember
                  ((flatten_mem_iff_of_signatures_eq
                    signaturesEqual.2 tested).mpr rightTailMember)
              rw [List.count_eq_zero.mpr leftTailMember,
                List.count_eq_zero.mpr rightTailAbsent]
          have tailDerivation :=
            listDerivesReverseAlignedComponents leftTail rightTail
              (fun component member =>
                leftNonempty component (by simp [member]))
              (fun component member =>
                rightNonempty component (by simp [member]))
              leftPairwise.2 rightPairwise.2
              (fun component member =>
                leftConnected component (by simp [member]))
              (fun component member =>
                rightConnected component (by simp [member]))
              signaturesEqual.2 tailParity
          have first := tailDerivation.append leftHead.reverse
          have second := headDerivation.prepend rightTail.flatten.reverse
          simpa [List.reverse_append, List.append_assoc] using
            first.trans second

/-- Exact unrestricted Nat-level reachability from the TRUE owner signature. -/
theorem derivesOfSameParityOppositeConnectedCutSignature
    {left right : Word Nat}
    (same :
      ParityConnectedCutDiagnostic.SameParityOppositeConnectedCutSignature
        left right) :
    Derives targetBasis left right := by
  let leftComponents := connectedComponentDecomposeWord left.reverse
  let rightComponents := connectedComponentDecomposeWord right.reverse
  have signaturesEqual :
      leftComponents.map componentSignature =
        rightComponents.map componentSignature := by
    simpa [leftComponents, rightComponents, componentSignature,
      S5_804.SameConnectedCutSignature,
      S5_804.connectedCutSignaturesWord,
      S5_804.connectedCutSignaturesList,
      connectedComponentDecomposeWord] using same.cuts
  have wholeParity : ∀ tested,
      leftComponents.flatten.count tested % 2 =
        rightComponents.flatten.count tested % 2 := by
    intro tested
    change
      (connectedComponentDecomposeWord left.reverse).flatten.count tested % 2 =
        (connectedComponentDecomposeWord right.reverse).flatten.count tested % 2
    rw [connectedComponentDecomposeWord_flatten,
      connectedComponentDecomposeWord_flatten]
    simpa [Word.toList_reverse] using same.parity tested
  have aligned :=
    listDerivesReverseAlignedComponents leftComponents rightComponents
      (connectedComponentDecomposeWord_nonempty_components left.reverse)
      (connectedComponentDecomposeWord_nonempty_components right.reverse)
      (connectedComponentDecomposeWord_pairwiseDisjoint left.reverse)
      (connectedComponentDecomposeWord_pairwiseDisjoint right.reverse)
      (connectedComponentDecomposeWord_supportConnected left.reverse)
      (connectedComponentDecomposeWord_supportConnected right.reverse)
      signaturesEqual wholeParity
  have listed : ListDerives left.toList right.toList := by
    simpa [leftComponents, rightComponents,
      connectedComponentDecomposeWord_flatten,
      Word.toList_reverse] using aligned
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          exact S5_107.ListDerives.toWord listed

/-- The missing full parity-preserving opposite-connected-cut lift. -/
theorem parityPreservingOppositeConnectedCutLift :
    ParityConnectedCutDiagnostic.ParityPreservingOppositeConnectedCutLift := by
  apply ParityConnectedCutDiagnostic.lift_iff_jointSignatureReach.mpr
  intro left right same
  exact derivesOfSameParityOppositeConnectedCutSignature same

/-- Actual independent owner intersection; constructed ONLY after completeness. -/
noncomputable def intersectionBasis :
    IntersectionBasis leftTable.semigroup rightTable.semigroup basis :=
  ParityConnectedCutDiagnostic.intersectionBasis_of_connectedCutLift
    parityPreservingOppositeConnectedCutLift

/-- The representative endpoint is unconditional at SOURCE level. -/
theorem s6_11229_representative_basis :
    BasisFor S6_11229.table.semigroup basis :=
  (ParityConnectedCutDiagnostic.both_orientations_of_connectedCutLift
    parityPreservingOppositeConnectedCutLift).1

/-- The opposite endpoint is unconditional at SOURCE level. -/
theorem s6_11229_opposite_basis :
    BasisFor S6_11229.table.semigroup.opposite (reversedBasis basis) :=
  (ParityConnectedCutDiagnostic.both_orientations_of_connectedCutLift
    parityPreservingOppositeConnectedCutLift).2

end SemigroupBasis.CoRoots.Order6Day7.S3_11.Rank058.ParityConnectedCutComplete
