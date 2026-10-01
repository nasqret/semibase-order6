import SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16Retarget

/-!
# Unconditional literal-B16 normalization for d029

Each connected component is replayed to an exact-count envelope, reduced
modulo three, and (when necessary) retargeted to the endpoint selected by
the matching component.  Component derivations are then assembled in their
ordered decomposition.  All syntactic steps derive from the literal B16
basis.
-/

namespace SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16

open SemigroupBasis
open SemigroupBasis.Examples

private theorem componentSignature_mem_of_mem
    {component : List Nat} {tested : Nat}
    (member : tested ∈ component) :
    tested ∈ (connectedComponentSignatureOfList component).support := by
  rw [connectedComponentSignatureOfList_support,
    connectedComponentSortedSupport_mem_iff]
  exact member

private theorem component_mem_of_signature_mem
    {component : List Nat} {tested : Nat}
    (member :
      tested ∈ (connectedComponentSignatureOfList component).support) :
    tested ∈ component := by
  rwa [connectedComponentSignatureOfList_support,
    connectedComponentSortedSupport_mem_iff] at member

private theorem sameSupport_of_componentSignature_eq
    {left right : List Nat}
    (same :
      connectedComponentSignatureOfList left =
        connectedComponentSignatureOfList right) :
    ∀ tested, tested ∈ left ↔ tested ∈ right := by
  intro tested
  constructor
  · intro member
    apply component_mem_of_signature_mem
    rw [← same]
    exact componentSignature_mem_of_mem member
  · intro member
    apply component_mem_of_signature_mem
    rw [same]
    exact componentSignature_mem_of_mem member

private theorem length_eq_one_of_componentSignature_eq
    {left right : List Nat}
    (same :
      connectedComponentSignatureOfList left =
        connectedComponentSignatureOfList right)
    (leftLength : left.length = 1) :
    right.length = 1 := by
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
    rw [← same, leftSignature]
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

private theorem listDerives_support_iff
    {left right : List Nat}
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (derivation : B16ListDerives left right) :
    ∀ tested, tested ∈ left ↔ tested ∈ right := by
  obtain ⟨leftHead, leftTail, rfl⟩ :=
    List.exists_cons_of_ne_nil leftNonempty
  obtain ⟨rightHead, rightTail, rfl⟩ :=
    List.exists_cons_of_ne_nil rightNonempty
  have same :=
    derives_sameModThreeComponentSignature
      (S5_107.ListDerives.toWord derivation)
  intro tested
  simpa [S5_107.listWordOfCons, Word.toList] using
    sameSupport_of_sameComponentSignature same.components tested

private theorem listDerives_modThree_eq
    {left right : List Nat}
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (derivation : B16ListDerives left right) :
    ∀ tested,
      left.count tested % 3 = right.count tested % 3 := by
  obtain ⟨leftHead, leftTail, rfl⟩ :=
    List.exists_cons_of_ne_nil leftNonempty
  obtain ⟨rightHead, rightTail, rfl⟩ :=
    List.exists_cons_of_ne_nil rightNonempty
  have same :=
    derives_sameModThreeComponentSignature
      (S5_107.ListDerives.toWord derivation)
  intro tested
  simpa [S5_107.listWordOfCons, Word.toList] using
    same.modThree tested

/-- Two nonempty support-connected components with the same ordered
component signature and coordinatewise multiplicities modulo three derive
from the literal B16 basis. -/
theorem listDerivesConnectedComponents_of_sameSignatureModThree
    {left right : List Nat}
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (leftConnected : ConnectedComponentSupportConnected left)
    (rightConnected : ConnectedComponentSupportConnected right)
    (sameSignature :
      connectedComponentSignatureOfList left =
        connectedComponentSignatureOfList right)
    (sameModThree :
      ∀ tested,
        left.count tested % 3 = right.count tested % 3) :
    B16ListDerives left right := by
  by_cases leftLengthOne : left.length = 1
  · have rightLengthOne :=
      length_eq_one_of_componentSignature_eq
        sameSignature leftLengthOne
    obtain ⟨leftLetter, rfl⟩ :=
      List.length_eq_one_iff.mp leftLengthOne
    obtain ⟨rightLetter, rfl⟩ :=
      List.length_eq_one_iff.mp rightLengthOne
    have lettersEqual : leftLetter = rightLetter := by
      have supportEq :=
        sameSupport_of_componentSignature_eq sameSignature leftLetter
      exact by simpa using supportEq.mp (by simp)
    subst rightLetter
    exact B16ListDerives.refl _
  · have rightLengthNotOne : right.length ≠ 1 := by
      intro rightLengthOne
      exact leftLengthOne <|
        length_eq_one_of_componentSignature_eq
          sameSignature.symm rightLengthOne
    have leftLengthAtLeastTwo : 2 ≤ left.length := by
      have positive : 0 < left.length := by
        cases left with
        | nil => contradiction
        | cons _ _ => simp
      omega
    have rightLengthAtLeastTwo : 2 ≤ right.length := by
      have positive : 0 < right.length := by
        cases right with
        | nil => contradiction
        | cons _ _ => simp
      omega
    obtain ⟨leftHead, leftTail, rfl⟩ :=
      List.exists_cons_of_ne_nil leftNonempty
    obtain ⟨rightHead, rightTail, rfl⟩ :=
      List.exists_cons_of_ne_nil rightNonempty
    obtain ⟨leftInterior, leftDerivation, leftPermutation⟩ :=
      exists_envelopeDerivation_of_connected
        leftConnected leftLengthAtLeastTwo
    obtain ⟨rightInterior, rightDerivation, rightPermutation⟩ :=
      exists_envelopeDerivation_of_connected
        rightConnected rightLengthAtLeastTwo
    have componentSupport :=
      sameSupport_of_componentSignature_eq sameSignature
    have envelopeSupport :
        ∀ tested,
          tested ∈ modThreeEnvelopeRender leftHead leftInterior [] ↔
            tested ∈
              modThreeEnvelopeRender rightHead rightInterior [] := by
      intro tested
      exact (leftPermutation.mem_iff).symm.trans <|
        (componentSupport tested).trans rightPermutation.mem_iff
    have envelopeModThree :
        ∀ tested,
          (modThreeEnvelopeRender leftHead leftInterior []).count
                tested % 3 =
            (modThreeEnvelopeRender rightHead rightInterior []).count
                tested % 3 := by
      intro tested
      have leftCount :=
        (List.perm_iff_count.mp leftPermutation) tested
      have rightCount :=
        (List.perm_iff_count.mp rightPermutation) tested
      exact
        (congrArg (fun count => count % 3) leftCount).symm.trans <|
          (sameModThree tested).trans <|
            congrArg (fun count => count % 3) rightCount
    by_cases endpointsEqual : leftHead = rightHead
    · subst rightHead
      have middle :=
        listDerivesEnvelopeInteriorNormalizeOfRenderedInvariants
          leftHead envelopeSupport envelopeModThree
      exact B16ListDerives.trans leftDerivation <|
        B16ListDerives.trans middle <|
          B16ListDerives.symm rightDerivation
    · let reducedInterior :=
        fixedEndpointModThreeReduce leftHead leftInterior
      have reduceDerivation :
          B16ListDerives
            (modThreeEnvelopeRender leftHead leftInterior [])
            (modThreeEnvelopeRender leftHead reducedInterior []) :=
        listDerivesEnvelopeFixedEndpointReduce
          leftHead leftInterior []
      have rightHeadInLeft : rightHead ∈ leftHead :: leftTail :=
        (componentSupport rightHead).mpr (by simp)
      have rightHeadInLeftEnvelope :
          rightHead ∈ modThreeEnvelopeRender leftHead leftInterior [] :=
        (leftPermutation.mem_iff).mp rightHeadInLeft
      have reductionSupport :=
        listDerives_support_iff
          (by simp [modThreeEnvelopeRender,
            S5_441.parityEnvelopeRender])
          (by simp [modThreeEnvelopeRender,
            S5_441.parityEnvelopeRender])
          reduceDerivation rightHead
      have rightHeadInReducedEnvelope :=
        reductionSupport.mp rightHeadInLeftEnvelope
      have rightHeadInReduced : rightHead ∈ reducedInterior := by
        simpa [modThreeEnvelopeRender,
          S5_441.parityEnvelopeRender, endpointsEqual,
          Ne.symm endpointsEqual] using rightHeadInReducedEnvelope
      obtain
        ⟨targetInterior, retargetDerivation,
          _profilePermutation, _targetReduced⟩ :=
          exists_reducedModThreeEnvelopeRetarget
            endpointsEqual rightHeadInReduced
            (fixedEndpointModThreeReduce_reduced
              leftHead leftInterior)
      have leftEnvelopeToTarget :
          B16ListDerives
            (modThreeEnvelopeRender leftHead leftInterior [])
            (modThreeEnvelopeRender rightHead targetInterior []) :=
        B16ListDerives.trans reduceDerivation retargetDerivation
      have pathSupport :=
        listDerives_support_iff
          (by simp [modThreeEnvelopeRender,
            S5_441.parityEnvelopeRender])
          (by simp [modThreeEnvelopeRender,
            S5_441.parityEnvelopeRender])
          leftEnvelopeToTarget
      have pathModThree :=
        listDerives_modThree_eq
          (by simp [modThreeEnvelopeRender,
            S5_441.parityEnvelopeRender])
          (by simp [modThreeEnvelopeRender,
            S5_441.parityEnvelopeRender])
          leftEnvelopeToTarget
      have targetSupport :
          ∀ tested,
            tested ∈ modThreeEnvelopeRender rightHead targetInterior [] ↔
              tested ∈
                modThreeEnvelopeRender rightHead rightInterior [] := by
        intro tested
        exact (pathSupport tested).symm.trans (envelopeSupport tested)
      have targetModThree :
          ∀ tested,
            (modThreeEnvelopeRender rightHead targetInterior []).count
                  tested % 3 =
              (modThreeEnvelopeRender rightHead rightInterior []).count
                  tested % 3 := by
        intro tested
        exact
          (pathModThree tested).symm.trans (envelopeModThree tested)
      have finish :=
        listDerivesEnvelopeInteriorNormalizeOfRenderedInvariants
          rightHead targetSupport targetModThree
      exact B16ListDerives.trans leftDerivation <|
        B16ListDerives.trans leftEnvelopeToTarget <|
          B16ListDerives.trans finish <|
            B16ListDerives.symm rightDerivation

private theorem flatten_mem_of_componentSignatures_eq
    {left right : List (List Nat)} {tested : Nat}
    (same :
      left.map connectedComponentSignatureOfList =
        right.map connectedComponentSignatureOfList)
    (member : tested ∈ left.flatten) :
    tested ∈ right.flatten := by
  rcases List.mem_flatten.mp member with
    ⟨component, componentMember, testedMember⟩
  have signatureMember :
      connectedComponentSignatureOfList component ∈
        right.map connectedComponentSignatureOfList := by
    rw [← same]
    exact List.mem_map.mpr ⟨component, componentMember, rfl⟩
  rcases List.mem_map.mp signatureMember with
    ⟨target, targetMember, signatureEq⟩
  apply List.mem_flatten_of_mem targetMember
  apply component_mem_of_signature_mem
  rw [signatureEq]
  exact componentSignature_mem_of_mem testedMember

private theorem flatten_mem_iff_of_componentSignatures_eq
    {left right : List (List Nat)}
    (same :
      left.map connectedComponentSignatureOfList =
        right.map connectedComponentSignatureOfList)
    (tested : Nat) :
    tested ∈ left.flatten ↔ tested ∈ right.flatten :=
  ⟨fun member => flatten_mem_of_componentSignatures_eq same member,
    fun member =>
      flatten_mem_of_componentSignatures_eq same.symm member⟩

private theorem count_flatten_eq_component
    {components : List (List Nat)} {component : List Nat}
    {tested : Nat}
    (pairwise :
      components.Pairwise ConnectedComponentSupportsDisjoint)
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
    (disjoint :
      ∀ component, component ∈ tail →
        ConnectedComponentSupportsDisjoint head component) :
    ConnectedComponentSupportsDisjoint head tail.flatten := by
  intro tested headMember tailMember
  rcases List.mem_flatten.mp tailMember with
    ⟨component, componentMember, componentContains⟩
  exact
    (disjoint component componentMember tested headMember)
      componentContains

private theorem listDerivesAlignedComponents :
    ∀ (leftComponents rightComponents : List (List Nat)),
      (∀ component, component ∈ leftComponents → component ≠ []) →
      (∀ component, component ∈ rightComponents → component ≠ []) →
      leftComponents.Pairwise ConnectedComponentSupportsDisjoint →
      rightComponents.Pairwise ConnectedComponentSupportsDisjoint →
      (∀ component, component ∈ leftComponents →
        ConnectedComponentSupportConnected component) →
      (∀ component, component ∈ rightComponents →
        ConnectedComponentSupportConnected component) →
      leftComponents.map connectedComponentSignatureOfList =
        rightComponents.map connectedComponentSignatureOfList →
      (∀ tested,
        leftComponents.flatten.count tested % 3 =
          rightComponents.flatten.count tested % 3) →
      B16ListDerives leftComponents.flatten rightComponents.flatten
  | [], rightComponents, _, _, _, _, _, _, signaturesEqual, _ => by
      cases rightComponents with
      | nil => exact S5_107.ListDerives.empty
      | cons rightHead rightTail => simp at signaturesEqual
  | leftHead :: leftTail, rightComponents,
      leftNonempty, rightNonempty,
      leftPairwise, rightPairwise,
      leftConnected, rightConnected,
      signaturesEqual, wholeModThree => by
      cases rightComponents with
      | nil => simp at signaturesEqual
      | cons rightHead rightTail =>
          have leftPairwiseAll := leftPairwise
          have rightPairwiseAll := rightPairwise
          rw [List.pairwise_cons] at leftPairwise rightPairwise
          simp only [List.map_cons, List.cons.injEq] at signaturesEqual
          have headModThree :
              ∀ tested,
                leftHead.count tested % 3 =
                  rightHead.count tested % 3 := by
            intro tested
            by_cases leftMember : tested ∈ leftHead
            · have leftSupport :=
                componentSignature_mem_of_mem leftMember
              have rightSupport :
                  tested ∈
                    (connectedComponentSignatureOfList rightHead).support := by
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
              exact wholeModThree tested
            · have rightAbsent : tested ∉ rightHead := by
                intro rightMember
                have rightSupport :=
                  componentSignature_mem_of_mem rightMember
                have leftSupport :
                    tested ∈
                      (connectedComponentSignatureOfList leftHead).support := by
                  rw [signaturesEqual.1]
                  exact rightSupport
                exact leftMember <|
                  component_mem_of_signature_mem leftSupport
              rw [List.count_eq_zero.mpr leftMember,
                List.count_eq_zero.mpr rightAbsent]
          have headDerivation : B16ListDerives leftHead rightHead :=
            listDerivesConnectedComponents_of_sameSignatureModThree
              (leftNonempty leftHead (by simp))
              (rightNonempty rightHead (by simp))
              (leftConnected leftHead (by simp))
              (rightConnected rightHead (by simp))
              signaturesEqual.1 headModThree
          have tailModThree :
              ∀ tested,
                leftTail.flatten.count tested % 3 =
                  rightTail.flatten.count tested % 3 := by
            intro tested
            by_cases leftTailMember : tested ∈ leftTail.flatten
            · have rightTailMember : tested ∈ rightTail.flatten :=
                (flatten_mem_iff_of_componentSignatures_eq
                  signaturesEqual.2 tested).1 leftTailMember
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
              have residue := wholeModThree tested
              simp only [List.flatten_cons, List.count_append] at residue
              rw [List.count_eq_zero.mpr leftHeadAbsent,
                List.count_eq_zero.mpr rightHeadAbsent] at residue
              simpa using residue
            · have rightTailAbsent : tested ∉ rightTail.flatten := by
                intro rightTailMember
                exact leftTailMember <|
                  (flatten_mem_iff_of_componentSignatures_eq
                    signaturesEqual.2 tested).2 rightTailMember
              rw [List.count_eq_zero.mpr leftTailMember,
                List.count_eq_zero.mpr rightTailAbsent]
          have tailDerivation :=
            listDerivesAlignedComponents
              leftTail rightTail
              (fun component member =>
                leftNonempty component (by simp [member]))
              (fun component member =>
                rightNonempty component (by simp [member]))
              leftPairwise.2 rightPairwise.2
              (fun component member =>
                leftConnected component (by simp [member]))
              (fun component member =>
                rightConnected component (by simp [member]))
              signaturesEqual.2 tailModThree
          have first :=
            B16ListDerives.append headDerivation leftTail.flatten
          have second :=
            B16ListDerives.prepend rightHead tailDerivation
          simpa [List.append_assoc] using
            B16ListDerives.trans first second

/-- Unrestricted syntactic completeness of the ordered connected-component
signature together with every occurrence count modulo three. -/
theorem derivesOfSameModThreeComponentSignature
    {left right : Word Nat}
    (same : SameModThreeComponentSignature left right) :
    Derives B16 left right := by
  let leftComponents := connectedComponentDecomposeWord left
  let rightComponents := connectedComponentDecomposeWord right
  have signaturesEqual :
      leftComponents.map connectedComponentSignatureOfList =
        rightComponents.map connectedComponentSignatureOfList := by
    simpa [leftComponents, rightComponents,
      SameComponentSignature, connectedComponentSignaturesWord,
      connectedComponentSignaturesList,
      connectedComponentDecomposeWord] using same.components
  have wholeModThree :
      ∀ tested,
        leftComponents.flatten.count tested % 3 =
          rightComponents.flatten.count tested % 3 := by
    intro tested
    change
      (connectedComponentDecomposeWord left).flatten.count tested % 3 =
        (connectedComponentDecomposeWord right).flatten.count tested % 3
    rw [connectedComponentDecomposeWord_flatten left,
      connectedComponentDecomposeWord_flatten right]
    exact same.modThree tested
  have componentDerivation :=
    listDerivesAlignedComponents
      leftComponents rightComponents
      (connectedComponentDecomposeWord_nonempty_components left)
      (connectedComponentDecomposeWord_nonempty_components right)
      (connectedComponentDecomposeWord_pairwiseDisjoint left)
      (connectedComponentDecomposeWord_pairwiseDisjoint right)
      (connectedComponentDecomposeWord_supportConnected left)
      (connectedComponentDecomposeWord_supportConnected right)
      signaturesEqual wholeModThree
  have listDerivation : B16ListDerives left.toList right.toList := by
    change
      B16ListDerives
        (connectedComponentDecomposeWord left).flatten
        (connectedComponentDecomposeWord right).flatten
      at componentDerivation
    rw [connectedComponentDecomposeWord_flatten left,
      connectedComponentDecomposeWord_flatten right]
      at componentDerivation
    exact componentDerivation
  cases left with
  | mk leftHead leftTail =>
      cases right with
      | mk rightHead rightTail =>
          exact S5_107.ListDerives.toWord listDerivation

end SemigroupBasis.CoRoots.Order6L2DD029ModThreeComponentB16
