import SemigroupBasis.CoRoots.S5_442Invariant
import SemigroupBasis.CoRoots.S5_442ParityEnvelopeRetarget

namespace SemigroupBasis.CoRoots.S5_442

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
    (derivation : ListDerives left right) :
    ∀ tested, tested ∈ left ↔ tested ∈ right := by
  obtain ⟨leftHead, leftTail, rfl⟩ :=
    List.exists_cons_of_ne_nil leftNonempty
  obtain ⟨rightHead, rightTail, rfl⟩ :=
    List.exists_cons_of_ne_nil rightNonempty
  have same :=
    derives_sameParityComponentSignature
      (S5_107.ListDerives.toWord derivation)
  intro tested
  simpa [S5_107.listWordOfCons, Word.toList] using
    (S5_442Invariant.sameSupport_of_sameComponentSignature
      same.components tested)

private theorem listDerives_parity_eq
    {left right : List Nat}
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (derivation : ListDerives left right) :
    ∀ tested,
      left.count tested % 2 = right.count tested % 2 := by
  obtain ⟨leftHead, leftTail, rfl⟩ :=
    List.exists_cons_of_ne_nil leftNonempty
  obtain ⟨rightHead, rightTail, rfl⟩ :=
    List.exists_cons_of_ne_nil rightNonempty
  have same :=
    derives_sameParityComponentSignature
      (S5_107.ListDerives.toWord derivation)
  intro tested
  simpa [S5_107.listWordOfCons, Word.toList] using
    same.parity tested

private theorem fixedEndpointParityReduce_reduced
    (endpoint : Nat) (interior : List Nat) :
    ParityEnvelopeInteriorReduced endpoint
      (fixedEndpointParityReduce endpoint interior) := by
  refine
    { endpoint_count_le_one := ?_
      other_count_le_two := ?_ }
  · rw [fixedEndpointParityReduce_count_endpoint]
    omega
  · intro tested different
    rw [fixedEndpointParityReduce_count_of_ne
      endpoint tested interior different]
    exact positiveParityReduce_count_le_two tested interior

/-- Two support-connected components with the same S4_70 signature and the
same coordinate parity vector are derivable from the 20-law basis. -/
theorem listDerivesConnectedComponents_of_sameSignatureParity
    {left right : List Nat}
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (leftConnected : ConnectedComponentSupportConnected left)
    (rightConnected : ConnectedComponentSupportConnected right)
    (sameSignature :
      connectedComponentSignatureOfList left =
        connectedComponentSignatureOfList right)
    (sameParity :
      ∀ tested,
        left.count tested % 2 = right.count tested % 2) :
    ListDerives left right := by
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
    exact ListDerives.refl _
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
    obtain
      ⟨leftInterior, leftDerivation, leftPermutation⟩ :=
        exists_parityEnvelopeDerivation_of_connected
          leftConnected leftLengthAtLeastTwo
    obtain
      ⟨rightInterior, rightDerivation, rightPermutation⟩ :=
        exists_parityEnvelopeDerivation_of_connected
          rightConnected rightLengthAtLeastTwo
    have componentSupport :=
      sameSupport_of_componentSignature_eq sameSignature
    have envelopeSupport :
        ∀ tested,
          tested ∈ parityEnvelopeRender leftHead leftInterior [] ↔
            tested ∈ parityEnvelopeRender rightHead rightInterior [] := by
      intro tested
      exact (leftPermutation.mem_iff).symm.trans <|
        (componentSupport tested).trans rightPermutation.mem_iff
    have envelopeParity :
        ∀ tested,
          (parityEnvelopeRender leftHead leftInterior []).count tested % 2 =
            (parityEnvelopeRender rightHead rightInterior []).count tested % 2 := by
      intro tested
      have leftCount :=
        (List.perm_iff_count.mp leftPermutation) tested
      have rightCount :=
        (List.perm_iff_count.mp rightPermutation) tested
      exact
        (congrArg (fun count => count % 2) leftCount).symm.trans <|
          (sameParity tested).trans <|
            congrArg (fun count => count % 2) rightCount
    by_cases endpointsEqual : leftHead = rightHead
    · subst rightHead
      have middle :=
        listDerivesParityEnvelopeInteriorNormalizeOfRenderedInvariants
          leftHead envelopeSupport envelopeParity
      exact ListDerives.trans leftDerivation <|
        ListDerives.trans middle (ListDerives.symm rightDerivation)
    · let reducedInterior :=
        fixedEndpointParityReduce leftHead leftInterior
      have reduceDerivation :
          ListDerives
            (parityEnvelopeRender leftHead leftInterior [])
            (parityEnvelopeRender leftHead reducedInterior []) := by
        exact
          listDerivesParityEnvelopeFixedEndpointReduce
            leftHead leftInterior []
      have rightHeadInLeft :
          rightHead ∈ leftHead :: leftTail :=
        (componentSupport rightHead).mpr (by simp)
      have rightHeadInLeftEnvelope :
          rightHead ∈
            parityEnvelopeRender leftHead leftInterior [] :=
        (leftPermutation.mem_iff).mp rightHeadInLeft
      have reductionSupport :=
        listDerives_support_iff
          (by simp [parityEnvelopeRender, S5_441.parityEnvelopeRender])
          (by simp [parityEnvelopeRender, S5_441.parityEnvelopeRender])
          reduceDerivation rightHead
      have rightHeadInReducedEnvelope :=
        reductionSupport.mp rightHeadInLeftEnvelope
      have rightHeadInReduced : rightHead ∈ reducedInterior := by
        simpa [parityEnvelopeRender, S5_441.parityEnvelopeRender,
          endpointsEqual, Ne.symm endpointsEqual] using
          rightHeadInReducedEnvelope
      obtain
        ⟨targetInterior, retargetDerivation,
          _profilePermutation, _targetReduced⟩ :=
          exists_reducedParityEnvelopeRetarget
            endpointsEqual rightHeadInReduced
            (fixedEndpointParityReduce_reduced
              leftHead leftInterior)
      have leftEnvelopeToTarget :
          ListDerives
            (parityEnvelopeRender leftHead leftInterior [])
            (parityEnvelopeRender rightHead targetInterior []) :=
        ListDerives.trans reduceDerivation retargetDerivation
      have pathSupport :=
        listDerives_support_iff
          (by simp [parityEnvelopeRender, S5_441.parityEnvelopeRender])
          (by simp [parityEnvelopeRender, S5_441.parityEnvelopeRender])
          leftEnvelopeToTarget
      have pathParity :=
        listDerives_parity_eq
          (by simp [parityEnvelopeRender, S5_441.parityEnvelopeRender])
          (by simp [parityEnvelopeRender, S5_441.parityEnvelopeRender])
          leftEnvelopeToTarget
      have targetSupport :
          ∀ tested,
            tested ∈ parityEnvelopeRender rightHead targetInterior [] ↔
              tested ∈ parityEnvelopeRender rightHead rightInterior [] := by
        intro tested
        exact (pathSupport tested).symm.trans (envelopeSupport tested)
      have targetParity :
          ∀ tested,
            (parityEnvelopeRender rightHead targetInterior []).count tested % 2 =
              (parityEnvelopeRender rightHead rightInterior []).count tested % 2 := by
        intro tested
        exact (pathParity tested).symm.trans (envelopeParity tested)
      have finish :=
        listDerivesParityEnvelopeInteriorNormalizeOfRenderedInvariants
          rightHead targetSupport targetParity
      exact ListDerives.trans leftDerivation <|
        ListDerives.trans leftEnvelopeToTarget <|
          ListDerives.trans finish (ListDerives.symm rightDerivation)

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
        leftComponents.flatten.count tested % 2 =
          rightComponents.flatten.count tested % 2) →
      ListDerives leftComponents.flatten rightComponents.flatten
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
          have headParity :
              ∀ tested,
                leftHead.count tested % 2 =
                  rightHead.count tested % 2 := by
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
              exact wholeParity tested
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
          have headDerivation : ListDerives leftHead rightHead :=
            listDerivesConnectedComponents_of_sameSignatureParity
              (leftNonempty leftHead (by simp))
              (rightNonempty rightHead (by simp))
              (leftConnected leftHead (by simp))
              (rightConnected rightHead (by simp))
              signaturesEqual.1 headParity
          have tailParity :
              ∀ tested,
                leftTail.flatten.count tested % 2 =
                  rightTail.flatten.count tested % 2 := by
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
              have parity := wholeParity tested
              simp only [List.flatten_cons, List.count_append] at parity
              rw [List.count_eq_zero.mpr leftHeadAbsent,
                List.count_eq_zero.mpr rightHeadAbsent] at parity
              simpa using parity
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
              signaturesEqual.2 tailParity
          have first := ListDerives.append headDerivation leftTail.flatten
          have second := ListDerives.prepend rightHead tailDerivation
          simpa [List.append_assoc] using
            ListDerives.trans first second

/-- Unrestricted syntactic completeness of the ordered component signature
together with coordinatewise occurrence parity. -/
theorem derives_of_sameParityComponentSignature
    {left right : Word Nat}
    (same :
      S5_442Invariant.SameParityComponentSignature left right) :
    Derives basis left right := by
  let leftComponents := connectedComponentDecomposeWord left
  let rightComponents := connectedComponentDecomposeWord right
  have signaturesEqual :
      leftComponents.map connectedComponentSignatureOfList =
        rightComponents.map connectedComponentSignatureOfList := by
    simpa [leftComponents, rightComponents,
      connectedComponentSignaturesWord,
      connectedComponentSignaturesList,
      connectedComponentDecomposeWord] using same.components
  have wholeParity :
      ∀ tested,
        leftComponents.flatten.count tested % 2 =
          rightComponents.flatten.count tested % 2 := by
    intro tested
    change
      (connectedComponentDecomposeWord left).flatten.count tested % 2 =
        (connectedComponentDecomposeWord right).flatten.count tested % 2
    rw [connectedComponentDecomposeWord_flatten left,
      connectedComponentDecomposeWord_flatten right]
    exact same.parity tested
  have componentDerivation :=
    listDerivesAlignedComponents
      leftComponents rightComponents
      (connectedComponentDecomposeWord_nonempty_components left)
      (connectedComponentDecomposeWord_nonempty_components right)
      (connectedComponentDecomposeWord_pairwiseDisjoint left)
      (connectedComponentDecomposeWord_pairwiseDisjoint right)
      (connectedComponentDecomposeWord_supportConnected left)
      (connectedComponentDecomposeWord_supportConnected right)
      signaturesEqual wholeParity
  have listDerivation : ListDerives left.toList right.toList := by
    change
      ListDerives
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

end SemigroupBasis.CoRoots.S5_442
