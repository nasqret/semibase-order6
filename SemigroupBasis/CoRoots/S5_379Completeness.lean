import SemigroupBasis.CoRoots.S5_379Envelope
import SemigroupBasis.Examples.ConnectedComponentFourFinal

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.S5_379

open SemigroupBasis
open SemigroupBasis.Examples

/-! ## Exact factor signature -/

/-- Equality of the `S4_70` term functions determines the exact ordered
connected-component signatures. -/
theorem sameComponentSignatures_of_sameComponentSimpleSignature
    {left right : Word Nat}
    (same : SameComponentSimpleSignature left right) :
    connectedComponentSignaturesWord left =
      connectedComponentSignaturesWord right := by
  have leftDerivation := connectedComponentFour_derivesCanonical left
  have rightDerivation := connectedComponentFour_derivesCanonical right
  have normalizedEval :
      ∀ valuation : Nat → Fin 4,
        connectedComponentFour.semigroup.eval valuation
            (connectedComponentCanonicalRender left) =
          connectedComponentFour.semigroup.eval valuation
            (connectedComponentCanonicalRender right) := by
    intro valuation
    have leftSound :=
      leftDerivation.sound connectedComponentFourBasis_models valuation
    have rightSound :=
      rightDerivation.sound connectedComponentFourBasis_models valuation
    exact leftSound.symm.trans <|
      (same.component valuation).trans rightSound
  exact
    connectedComponentCanonical_eq_of_equalEval
      (connectedComponentFourSignaturesWord_canonical left)
      (connectedComponentFourSignaturesWord_canonical right)
      (connectedComponentCanonicalRender left)
      (connectedComponentCanonicalRender right)
      (connectedComponentCanonicalRender_toList left)
      (connectedComponentCanonicalRender_toList right)
      normalizedEval

/-- Support and global simplicity determine every multiplicity after capping
at two. -/
theorem cappedCounts_eq_of_sameComponentSimpleSignature
    {left right : Word Nat}
    (same : SameComponentSimpleSignature left right)
    (tested : Nat) :
    min (left.toList.count tested) 2 =
      min (right.toList.count tested) 2 := by
  by_cases leftMember : tested ∈ left.toList
  · have rightMember : tested ∈ right.toList :=
      (same.support tested).1 leftMember
    have leftPositive : 0 < left.toList.count tested :=
      List.count_pos_iff.mpr leftMember
    have rightPositive : 0 < right.toList.count tested :=
      List.count_pos_iff.mpr rightMember
    by_cases leftSimple : left.toList.count tested = 1
    · have rightSimple : right.toList.count tested = 1 :=
        (same.globallySimple tested).1 leftSimple
      omega
    · have rightNotSimple : right.toList.count tested ≠ 1 := by
        intro rightSimple
        exact leftSimple ((same.globallySimple tested).2 rightSimple)
      omega
  · have rightAbsent : tested ∉ right.toList := by
      intro rightMember
      exact leftMember ((same.support tested).2 rightMember)
    rw [List.count_eq_zero.mpr leftMember,
      List.count_eq_zero.mpr rightAbsent]

/-! ## Endpoint retargeting -/

private theorem envelopeSwitch_perm
    (oldEndpoint newEndpoint : Nat) (trailing : List Nat) :
    (oldEndpoint :: newEndpoint :: newEndpoint :: trailing ++
        [oldEndpoint]).Perm
      (newEndpoint :: oldEndpoint :: oldEndpoint :: trailing ++
        [newEndpoint]) := by
  rw [List.perm_iff_count]
  intro tested
  simp only [List.count_cons, List.count_append, List.count_nil]
  omega

/-- Switch a closed cap-two envelope to a different repeated endpoint. The
new interior contains the two old endpoints and all untouched trailing
letters, so the complete rendered lists are permutations. -/
theorem existsEnvelopeRetarget
    {oldEndpoint newEndpoint : Nat} {interior : List Nat}
    (different : oldEndpoint ≠ newEndpoint)
    (newCount : interior.count newEndpoint = 2) :
    ∃ targetInterior,
      ListDerives
          (oldEndpoint :: interior ++ [oldEndpoint])
          (newEndpoint :: targetInterior ++ [newEndpoint]) /\
        (oldEndpoint :: interior ++ [oldEndpoint]).Perm
          (newEndpoint :: targetInterior ++ [newEndpoint]) := by
  have firstMember : newEndpoint ∈ interior :=
    List.count_pos_iff.mp (by omega)
  have countAfterFirst :
      (interior.erase newEndpoint).count newEndpoint = 1 := by
    rw [List.count_erase_self, newCount]
  have secondMember : newEndpoint ∈ interior.erase newEndpoint :=
    List.count_pos_iff.mp (by omega)
  let trailing := (interior.erase newEndpoint).erase newEndpoint
  have arrange :
      interior.Perm (newEndpoint :: newEndpoint :: trailing) :=
    (List.perm_cons_erase firstMember).trans <|
      List.Perm.cons newEndpoint <| by
        simpa [trailing] using List.perm_cons_erase secondMember
  have arrangeSource :
      ListDerives
        (oldEndpoint :: interior ++ [oldEndpoint])
        (oldEndpoint :: newEndpoint :: newEndpoint :: trailing ++
          [oldEndpoint]) := by
    simpa [List.append_assoc] using
      listDerivesInteriorPermutation oldEndpoint [] arrange
  have switch :
      ListDerives
        (oldEndpoint :: newEndpoint :: newEndpoint :: trailing ++
          [oldEndpoint])
        (newEndpoint :: oldEndpoint :: oldEndpoint :: trailing ++
          [newEndpoint]) := by
    cases trailing with
    | nil =>
        exact S5_107.ListDerives.words <| by
          have core :=
            (derivesCrossingFinal
              (Word.singleton oldEndpoint)
              (Word.singleton newEndpoint)).symm.trans
              (derivesCrossingInitial
                (Word.singleton oldEndpoint)
                (Word.singleton newEndpoint))
          simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using core
    | cons head tail =>
        exact S5_107.ListDerives.words <| by
          simpa [S5_107.listWordOfCons, Word.singleton, Word.append,
            Word.append_assoc, List.append_assoc] using
              derivesEnvelopeSwitch
                (Word.singleton oldEndpoint)
                (Word.singleton newEndpoint)
                (S5_107.listWordOfCons head tail)
  have arrangeWhole :
      (oldEndpoint :: interior ++ [oldEndpoint]).Perm
        (oldEndpoint :: newEndpoint :: newEndpoint :: trailing ++
          [oldEndpoint]) :=
    List.Perm.cons oldEndpoint (arrange.append_right [oldEndpoint])
  let targetInterior := oldEndpoint :: oldEndpoint :: trailing
  refine
    ⟨targetInterior, arrangeSource.trans switch, ?_⟩
  exact arrangeWhole.trans <| by
    simpa [targetInterior] using
      envelopeSwitch_perm oldEndpoint newEndpoint trailing

private theorem interior_perm_of_closed_envelope_perm
    (endpoint : Nat) {left right : List Nat}
    (permutation :
      (endpoint :: left ++ [endpoint]).Perm
        (endpoint :: right ++ [endpoint])) :
    left.Perm right := by
  rw [List.perm_iff_count]
  intro tested
  have counts := (List.perm_iff_count.mp permutation) tested
  simp only [List.count_cons, List.count_append, List.count_nil] at counts
  omega

/-- Any two support-connected components with the same cap-two multiplicity
vector are joined by the six S5_379 laws. -/
theorem listDerivesConnectedComponents_of_cappedCounts
    {left right : List Nat}
    (leftNonempty : left ≠ []) (rightNonempty : right ≠ [])
    (leftConnected : ConnectedComponentSupportConnected left)
    (rightConnected : ConnectedComponentSupportConnected right)
    (sameCounts : ∀ tested,
      min (left.count tested) 2 = min (right.count tested) 2) :
    ListDerives left right := by
  obtain ⟨leftTarget, leftDerivation, leftLimited,
      leftCounts, leftShape⟩ :=
    existsConnectedComponentNormal leftNonempty leftConnected
  obtain ⟨rightTarget, rightDerivation, rightLimited,
      rightCounts, rightShape⟩ :=
    existsConnectedComponentNormal rightNonempty rightConnected
  have targetsPerm : leftTarget.Perm rightTarget := by
    rw [List.perm_iff_count]
    intro tested
    exact (leftCounts tested).trans <|
      (sameCounts tested).trans (rightCounts tested).symm
  by_cases leftSingleton : leftTarget.length = 1
  · obtain ⟨letter, leftTargetEq⟩ :=
      List.length_eq_one_iff.mp leftSingleton
    have rightTargetEq : rightTarget = [letter] :=
      List.perm_singleton.mp <| by
        simpa [leftTargetEq] using targetsPerm.symm
    rw [leftTargetEq] at leftDerivation
    rw [rightTargetEq] at rightDerivation
    exact leftDerivation.trans rightDerivation.symm
  · by_cases rightSingleton : rightTarget.length = 1
    · obtain ⟨letter, rightTargetEq⟩ :=
        List.length_eq_one_iff.mp rightSingleton
      have leftTargetEq : leftTarget = [letter] :=
        List.perm_singleton.mp <| by
          simpa [rightTargetEq] using targetsPerm
      rw [leftTargetEq] at leftDerivation
      rw [rightTargetEq] at rightDerivation
      exact leftDerivation.trans rightDerivation.symm
    · rcases leftShape with leftLength | leftEnvelope
      · exact False.elim (leftSingleton leftLength)
      · rcases rightShape with rightLength | rightEnvelope
        · exact False.elim (rightSingleton rightLength)
        · obtain
            ⟨oldEndpoint, leftInterior, leftTargetEq,
              _oldAbsent, _leftSorted⟩ := leftEnvelope
          obtain
            ⟨newEndpoint, rightInterior, rightTargetEq,
              _newAbsent, _rightSorted⟩ := rightEnvelope
          rw [leftTargetEq] at leftDerivation leftLimited targetsPerm
          rw [rightTargetEq] at rightDerivation rightLimited targetsPerm
          by_cases sameEndpoint : oldEndpoint = newEndpoint
          · subst newEndpoint
            have interiorPerm : leftInterior.Perm rightInterior :=
              interior_perm_of_closed_envelope_perm
                oldEndpoint targetsPerm
            have middle :=
              listDerivesInteriorPermutation
                oldEndpoint [] interiorPerm
            have middle' :
                ListDerives
                  (oldEndpoint :: leftInterior ++ [oldEndpoint])
                  (oldEndpoint :: rightInterior ++ [oldEndpoint]) := by
              simpa [List.append_assoc] using middle
            exact leftDerivation.trans <|
              middle'.trans rightDerivation.symm
          · have newInteriorCount :
                leftInterior.count newEndpoint = 2 := by
              have bound := leftLimited newEndpoint
              have counts :=
                (List.perm_iff_count.mp targetsPerm) newEndpoint
              simp only [List.count_cons, List.count_append,
                List.count_nil] at bound counts
              simp [sameEndpoint, Ne.symm sameEndpoint] at bound counts
              omega
            obtain ⟨switchedInterior, retarget, retargetPerm⟩ :=
              existsEnvelopeRetarget sameEndpoint newInteriorCount
            have switchedPerm :
                (newEndpoint :: switchedInterior ++ [newEndpoint]).Perm
                  (newEndpoint :: rightInterior ++ [newEndpoint]) :=
              retargetPerm.symm.trans targetsPerm
            have interiorPerm :
                switchedInterior.Perm rightInterior :=
              interior_perm_of_closed_envelope_perm
                newEndpoint switchedPerm
            have finish :=
              listDerivesInteriorPermutation
                newEndpoint [] interiorPerm
            have finish' :
                ListDerives
                  (newEndpoint :: switchedInterior ++ [newEndpoint])
                  (newEndpoint :: rightInterior ++ [newEndpoint]) := by
              simpa [List.append_assoc] using finish
            exact leftDerivation.trans <|
              retarget.trans <|
                finish'.trans rightDerivation.symm

/-! ## Ordered component concatenation -/

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
  ⟨fun member =>
      flatten_mem_of_componentSignatures_eq same member,
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
  | nil =>
      simp at componentMember
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
        min (leftComponents.flatten.count tested) 2 =
          min (rightComponents.flatten.count tested) 2) →
      ListDerives leftComponents.flatten rightComponents.flatten
  | [], rightComponents, _, _, _, _, _, _, signaturesEqual, _ => by
      cases rightComponents with
      | nil => exact S5_107.ListDerives.empty
      | cons rightHead rightTail =>
          simp at signaturesEqual
  | leftHead :: leftTail, rightComponents,
      leftNonempty, rightNonempty,
      leftPairwise, rightPairwise,
      leftConnected, rightConnected,
      signaturesEqual, wholeCounts => by
      cases rightComponents with
      | nil =>
          simp at signaturesEqual
      | cons rightHead rightTail =>
          have leftPairwiseAll := leftPairwise
          have rightPairwiseAll := rightPairwise
          rw [List.pairwise_cons] at leftPairwise rightPairwise
          simp only [List.map_cons, List.cons.injEq] at signaturesEqual
          have headCounts : ∀ tested,
              min (leftHead.count tested) 2 =
                min (rightHead.count tested) 2 := by
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
              exact wholeCounts tested
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
            listDerivesConnectedComponents_of_cappedCounts
              (leftNonempty leftHead (by simp))
              (rightNonempty rightHead (by simp))
              (leftConnected leftHead (by simp))
              (rightConnected rightHead (by simp))
              headCounts
          have tailCounts : ∀ tested,
              min (leftTail.flatten.count tested) 2 =
                min (rightTail.flatten.count tested) 2 := by
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
              have counts := wholeCounts tested
              simp only [List.flatten_cons, List.count_append] at counts
              rw [List.count_eq_zero.mpr leftHeadAbsent,
                List.count_eq_zero.mpr rightHeadAbsent] at counts
              simpa using counts
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
              signaturesEqual.2 tailCounts
          have first := headDerivation.append leftTail.flatten
          have second := tailDerivation.prepend rightHead
          simpa [List.append_assoc] using first.trans second

/-- Unrestricted completeness of the component/simple signature. -/
theorem derives_of_sameComponentSimpleSignature
    {left right : Word Nat}
    (same : SameComponentSimpleSignature left right) :
    Derives basis left right := by
  let leftComponents := connectedComponentDecomposeWord left
  let rightComponents := connectedComponentDecomposeWord right
  have signaturesEqual :
      leftComponents.map connectedComponentSignatureOfList =
        rightComponents.map connectedComponentSignatureOfList := by
    simpa [leftComponents, rightComponents,
      connectedComponentSignaturesWord,
      connectedComponentSignaturesList,
      connectedComponentDecomposeWord] using
        sameComponentSignatures_of_sameComponentSimpleSignature same
  have leftFlatten : leftComponents.flatten = left.toList := by
    simpa [leftComponents] using
      connectedComponentDecomposeWord_flatten left
  have rightFlatten : rightComponents.flatten = right.toList := by
    simpa [rightComponents] using
      connectedComponentDecomposeWord_flatten right
  have flattenedCounts :
      ∀ tested,
        min (leftComponents.flatten.count tested) 2 =
          min (rightComponents.flatten.count tested) 2 := by
    intro tested
    rw [leftFlatten, rightFlatten]
    exact cappedCounts_eq_of_sameComponentSimpleSignature same tested
  have componentDerivation :=
    listDerivesAlignedComponents
      leftComponents rightComponents
      (connectedComponentDecomposeWord_nonempty_components left)
      (connectedComponentDecomposeWord_nonempty_components right)
      (connectedComponentDecomposeWord_pairwiseDisjoint left)
      (connectedComponentDecomposeWord_pairwiseDisjoint right)
      (connectedComponentDecomposeWord_supportConnected left)
      (connectedComponentDecomposeWord_supportConnected right)
      signaturesEqual
      flattenedCounts
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

end SemigroupBasis.CoRoots.S5_379
