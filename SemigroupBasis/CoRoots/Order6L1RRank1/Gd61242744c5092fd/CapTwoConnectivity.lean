import SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd.CapTwoEndpointZeroUnique

/-!
# Gd cap-two whole-word contextual connectivity

This module closes the route-local endpoint-separation argument.  It aligns
the literal connected-component decompositions using the public `S4_70`
signature, isolates the selected `S4_71` block probe with the table identity,
normalizes each paired cap-two component by the lexicographic endpoint
measure, identifies the two zero endpoints, and concatenates the resulting
contextual frozen routes.

No component envelope, generated `S4_71` module, joint signature, canonical
search equality, or bounded path-coverage theorem is imported or used.
-/

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
namespace CapTwoRTCRoute

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6L1RRank1
open SemigroupBasis.Examples

/-! ## The route-local factor relation -/

/-- The two forward semantic facts used by the cap-two route. -/
structure SameFactor (left right : Word Nat) : Prop where
  components :
    connectedComponentSignaturesWord left =
      connectedComponentSignaturesWord right
  blockTheory :
    (Identity.mk left right).SatisfiedBy
      SemanticBlockSignature.table.semigroup

namespace SameFactor

theorem refl (word : Word Nat) : SameFactor word word := by
  refine ⟨rfl, ?_⟩
  intro valuation
  rfl

theorem symm {left right : Word Nat}
    (same : SameFactor left right) : SameFactor right left := by
  refine ⟨same.components.symm, ?_⟩
  intro valuation
  exact (same.blockTheory valuation).symm

theorem trans {left middle right : Word Nat}
    (first : SameFactor left middle)
    (second : SameFactor middle right) : SameFactor left right := by
  refine ⟨first.components.trans second.components, ?_⟩
  intro valuation
  exact (first.blockTheory valuation).trans
    (second.blockTheory valuation)

end SameFactor

/-- Public left-factor model certificate for the route-local basis. -/
theorem left_models :
    Models Generated.S4_70.table.semigroup basis :=
  routeLeftModels

/-- Public right-factor model certificate for the route-local basis. -/
theorem right_models :
    Models SemanticBlockSignature.table.semigroup basis :=
  routeRightModels

theorem sameFactor_of_factor_valid
    (identity : Identity Nat)
    (leftValid : identity.SatisfiedBy
      Generated.S4_70.table.semigroup)
    (rightValid : identity.SatisfiedBy
      SemanticBlockSignature.table.semigroup) :
    SameFactor identity.lhs identity.rhs := by
  refine ⟨?_, rightValid⟩
  exact
    SemigroupBasis.CoRoots.S5_790Invariant.sameComponents_of_s4_70_valid
      identity leftValid

theorem sameFactor_of_derives
    {left right : Word Nat}
    (derived : Derives basis left right) : SameFactor left right := by
  exact sameFactor_of_factor_valid (Identity.mk left right)
    (fun valuation => derived.sound routeLeftModels valuation)
    (fun valuation => derived.sound routeRightModels valuation)

/-! ## Literal component facts -/

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

private theorem componentMembers_of_signature_eq
    {left right : List Nat}
    (same :
      connectedComponentSignatureOfList left =
        connectedComponentSignatureOfList right) :
    ∀ letter, letter ∈ left ↔ letter ∈ right := by
  have supportEqual := congrArg connectedComponentSignature.support same
  rw [connectedComponentSignatureOfList_support,
    connectedComponentSignatureOfList_support] at supportEqual
  intro letter
  rw [← connectedComponentSortedSupport_mem_iff letter left,
    ← connectedComponentSortedSupport_mem_iff letter right,
    supportEqual]

private theorem componentWordSignatures_eq
    {left right : List Nat}
    (leftNonempty : left ≠ [])
    (rightNonempty : right ≠ [])
    (leftConnected : ConnectedComponentSupportConnected left)
    (rightConnected : ConnectedComponentSupportConnected right)
    (same :
      connectedComponentSignatureOfList left =
        connectedComponentSignatureOfList right) :
    ∀ leftHead leftTail rightHead rightTail,
      left = leftHead :: leftTail →
      right = rightHead :: rightTail →
      connectedComponentSignaturesWord
          (S5_107.listWordOfCons leftHead leftTail) =
        connectedComponentSignaturesWord
          (S5_107.listWordOfCons rightHead rightTail) := by
  have leftDecomposition :=
    connectedDecomposition_eq_singleton leftNonempty leftConnected
  have rightDecomposition :=
    connectedDecomposition_eq_singleton rightNonempty rightConnected
  intro leftHead leftTail rightHead rightTail leftShape rightShape
  unfold connectedComponentSignaturesWord
    connectedComponentSignaturesList
  simp only [S5_107.listWordOfCons, Word.toList]
  rw [← leftShape, ← rightShape,
    leftDecomposition, rightDecomposition]
  exact congrArg List.singleton same

private theorem componentCount_le_flattenCount
    {components : List (List Nat)}
    {component : List Nat}
    (member : component ∈ components)
    (letter : Nat) :
    component.count letter ≤ components.flatten.count letter := by
  induction components with
  | nil => simp at member
  | cons head tail inductionHypothesis =>
      rw [List.flatten_cons, List.count_append]
      rcases List.mem_cons.mp member with equal | tailMember
      · subst component
        omega
      · have lower := inductionHypothesis tailMember
        omega

/-! ## Isolating one component in the selected block table -/

private def routeBlockListEval
    (valuation : Nat → Fin 4) (letters : List Nat) : Fin 4 :=
  letters.foldl
    (fun value letter =>
      SemanticBlockSignature.table.mul value (valuation letter))
    (3 : Fin 4)

private theorem routeTable_left_identity (value : Fin 4) :
    SemanticBlockSignature.table.mul (3 : Fin 4) value = value := by
  apply Fin.ext
  revert value
  decide

private theorem routeTable_right_identity (value : Fin 4) :
    SemanticBlockSignature.table.mul value (3 : Fin 4) = value := by
  apply Fin.ext
  revert value
  decide

private theorem routeBlockFold_eq_mul
    (valuation : Nat → Fin 4) :
    ∀ (letters : List Nat) (initial : Fin 4),
      letters.foldl
          (fun value letter =>
            SemanticBlockSignature.table.mul value (valuation letter))
          initial =
        SemanticBlockSignature.table.mul initial
          (routeBlockListEval valuation letters)
  | [], initial => by
      unfold routeBlockListEval
      simp only [List.foldl_nil]
      exact (routeTable_right_identity initial).symm
  | letter :: rest, initial => by
      change
        rest.foldl
            (fun value tested =>
              SemanticBlockSignature.table.mul value
                (valuation tested))
            (SemanticBlockSignature.table.mul initial
              (valuation letter)) =
          SemanticBlockSignature.table.mul initial
            (rest.foldl
              (fun value tested =>
                SemanticBlockSignature.table.mul value
                  (valuation tested))
              (SemanticBlockSignature.table.mul
                (3 : Fin 4) (valuation letter)))
      rw [routeTable_left_identity]
      rw [routeBlockFold_eq_mul valuation rest
        (SemanticBlockSignature.table.mul initial (valuation letter))]
      rw [routeBlockFold_eq_mul valuation rest (valuation letter)]
      exact SemanticBlockSignature.table.semigroup.assoc
        initial (valuation letter) (routeBlockListEval valuation rest)

private theorem routeBlockListEval_append
    (valuation : Nat → Fin 4)
    (left right : List Nat) :
    routeBlockListEval valuation (left ++ right) =
      SemanticBlockSignature.table.mul
        (routeBlockListEval valuation left)
        (routeBlockListEval valuation right) := by
  unfold routeBlockListEval
  rw [List.foldl_append]
  exact routeBlockFold_eq_mul valuation right
    (left.foldl
      (fun value letter =>
        SemanticBlockSignature.table.mul value (valuation letter))
      (3 : Fin 4))

private theorem routeBlockFold_congr
    (leftValuation rightValuation : Nat → Fin 4) :
    ∀ (letters : List Nat) (initial : Fin 4),
      (∀ letter, letter ∈ letters →
        leftValuation letter = rightValuation letter) →
      letters.foldl
          (fun value letter =>
            SemanticBlockSignature.table.mul value
              (leftValuation letter)) initial =
        letters.foldl
          (fun value letter =>
            SemanticBlockSignature.table.mul value
              (rightValuation letter)) initial
  | [], _, _ => rfl
  | letter :: rest, initial, agree => by
      simp only [List.foldl_cons]
      rw [agree letter (List.Mem.head rest)]
      apply routeBlockFold_congr leftValuation rightValuation rest
      intro tested member
      exact agree tested (List.Mem.tail letter member)

private theorem routeBlockListEval_congr
    {leftValuation rightValuation : Nat → Fin 4}
    {letters : List Nat}
    (agree : ∀ letter, letter ∈ letters →
      leftValuation letter = rightValuation letter) :
    routeBlockListEval leftValuation letters =
      routeBlockListEval rightValuation letters := by
  unfold routeBlockListEval
  exact routeBlockFold_congr leftValuation rightValuation
    letters (3 : Fin 4) agree

private theorem routeBlockFold_identity
    (valuation : Nat → Fin 4) :
    ∀ (letters : List Nat) (initial : Fin 4),
      (∀ letter, letter ∈ letters →
        valuation letter = (3 : Fin 4)) →
      letters.foldl
          (fun value letter =>
            SemanticBlockSignature.table.mul value
              (valuation letter)) initial = initial
  | [], _, _ => rfl
  | letter :: rest, initial, identityOn => by
      simp only [List.foldl_cons]
      rw [identityOn letter (List.Mem.head rest),
        routeTable_right_identity]
      apply routeBlockFold_identity valuation rest initial
      intro tested member
      exact identityOn tested (List.Mem.tail letter member)

private theorem routeBlockListEval_identity
    {valuation : Nat → Fin 4}
    {letters : List Nat}
    (identityOn : ∀ letter, letter ∈ letters →
      valuation letter = (3 : Fin 4)) :
    routeBlockListEval valuation letters = (3 : Fin 4) := by
  unfold routeBlockListEval
  exact routeBlockFold_identity valuation letters (3 : Fin 4)
    identityOn

private def isolatedValuation
    (selected : List Nat) (valuation : Nat → Fin 4) : Nat → Fin 4 :=
  fun letter => if letter ∈ selected then valuation letter else 3

private theorem isolatedComponent_eval
    (valuation : Nat → Fin 4) :
    ∀ (components : List (List Nat)) (selected : List Nat),
      components.Pairwise ConnectedComponentSupportsDisjoint →
      selected ∈ components →
      routeBlockListEval (isolatedValuation selected valuation)
          components.flatten =
        routeBlockListEval valuation selected
  | [], selected, _, member => by simp at member
  | head :: tail, selected, pairwise, member => by
      have headToTail := (List.pairwise_cons.mp pairwise).1
      have tailPairwise := (List.pairwise_cons.mp pairwise).2
      rcases List.mem_cons.mp member with equal | tailMember
      · subst selected
        have headEval :
            routeBlockListEval (isolatedValuation head valuation) head =
              routeBlockListEval valuation head := by
          apply routeBlockListEval_congr
          intro letter letterMember
          simp [isolatedValuation, letterMember]
        have tailEval :
            routeBlockListEval (isolatedValuation head valuation)
                tail.flatten = (3 : Fin 4) := by
          apply routeBlockListEval_identity
          intro letter letterMember
          have absent : letter ∉ head := by
            intro headMember
            rw [List.mem_flatten] at letterMember
            rcases letterMember with
              ⟨component, componentMember, componentLetter⟩
            exact
              (headToTail component componentMember
                letter headMember) componentLetter
          simp [isolatedValuation, absent]
        rw [List.flatten_cons,
          routeBlockListEval_append, headEval, tailEval,
          routeTable_right_identity]
      · have headEval :
            routeBlockListEval (isolatedValuation selected valuation)
                head = (3 : Fin 4) := by
          apply routeBlockListEval_identity
          intro letter letterMember
          have absent : letter ∉ selected :=
            headToTail selected tailMember letter letterMember
          simp [isolatedValuation, absent]
        have tailEval :=
          isolatedComponent_eval valuation tail selected
            tailPairwise tailMember
        rw [List.flatten_cons,
          routeBlockListEval_append, headEval, tailEval,
          routeTable_left_identity]

private theorem routeBlock_eval_eq_listEval
    (valuation : Nat → Fin 4) (word : Word Nat) :
    SemanticBlockSignature.table.semigroup.eval valuation word =
      routeBlockListEval valuation word.toList := by
  cases word with
  | mk head tail =>
      change
        tail.foldl
            (fun value letter =>
              SemanticBlockSignature.table.mul value
                (valuation letter))
            (valuation head) =
          tail.foldl
            (fun value letter =>
              SemanticBlockSignature.table.mul value
                (valuation letter))
            (SemanticBlockSignature.table.mul
              (3 : Fin 4) (valuation head))
      rw [routeTable_left_identity]

private theorem componentBlockTheory_of_whole
    {left right : Word Nat}
    {leftComponent rightComponent : List Nat}
    (leftMember :
      leftComponent ∈ connectedComponentDecomposeWord left)
    (rightMember :
      rightComponent ∈ connectedComponentDecomposeWord right)
    (sameMembers : ∀ letter,
      letter ∈ leftComponent ↔ letter ∈ rightComponent)
    (whole :
      (Identity.mk left right).SatisfiedBy
        SemanticBlockSignature.table.semigroup) :
    ∀ leftHead leftTail rightHead rightTail,
      leftComponent = leftHead :: leftTail →
      rightComponent = rightHead :: rightTail →
      (Identity.mk
        (S5_107.listWordOfCons leftHead leftTail)
        (S5_107.listWordOfCons rightHead rightTail)).SatisfiedBy
          SemanticBlockSignature.table.semigroup := by
  have leftPairwise :=
    connectedComponentDecomposeWord_pairwiseDisjoint left
  have rightPairwise :=
    connectedComponentDecomposeWord_pairwiseDisjoint right
  intro leftHead leftTail rightHead rightTail leftShape rightShape
  intro valuation
  have isolatedEqual :
      isolatedValuation leftComponent valuation =
        isolatedValuation rightComponent valuation := by
    funext letter
    unfold isolatedValuation
    by_cases leftPresent : letter ∈ leftComponent
    · have rightPresent := (sameMembers letter).mp leftPresent
      rw [if_pos leftPresent, if_pos rightPresent]
    · have rightAbsent : letter ∉ rightComponent := by
        intro rightPresent
        exact leftPresent ((sameMembers letter).mpr rightPresent)
      rw [if_neg leftPresent, if_neg rightAbsent]
  have leftIsolated :=
    isolatedComponent_eval valuation
      (connectedComponentDecomposeWord left) leftComponent
      leftPairwise leftMember
  have rightIsolated :=
    isolatedComponent_eval valuation
      (connectedComponentDecomposeWord right) rightComponent
      rightPairwise rightMember
  have rightIsolatedWithLeft :
      routeBlockListEval (isolatedValuation leftComponent valuation)
          (connectedComponentDecomposeWord right).flatten =
        routeBlockListEval valuation rightComponent := by
    rw [isolatedEqual]
    exact rightIsolated
  have evaluated := whole (isolatedValuation leftComponent valuation)
  rw [routeBlock_eval_eq_listEval,
    routeBlock_eval_eq_listEval,
    ← connectedComponentDecomposeWord_flatten left,
    ← connectedComponentDecomposeWord_flatten right,
    leftIsolated, rightIsolatedWithLeft] at evaluated
  rw [routeBlock_eval_eq_listEval, routeBlock_eval_eq_listEval]
  simpa [S5_107.listWordOfCons, Word.toList,
    ← leftShape, ← rightShape] using evaluated

/-! ## One paired component and the whole-word assembly -/

private theorem pairedComponent_rtc
    {left right : Word Nat}
    {leftComponent rightComponent : List Nat}
    (leftLimited : ∀ letter, left.toList.count letter ≤ 2)
    (rightLimited : ∀ letter, right.toList.count letter ≤ 2)
    (wholeBlockTheory :
      (Identity.mk left right).SatisfiedBy
        SemanticBlockSignature.table.semigroup)
    (leftMember :
      leftComponent ∈ connectedComponentDecomposeWord left)
    (rightMember :
      rightComponent ∈ connectedComponentDecomposeWord right)
    (sameSignature :
      connectedComponentSignatureOfList leftComponent =
        connectedComponentSignatureOfList rightComponent) :
    ContextualFrozenRTC leftComponent rightComponent := by
  have leftNonempty : leftComponent ≠ [] :=
    connectedComponentDecomposeWord_nonempty_components left
      leftComponent leftMember
  have rightNonempty : rightComponent ≠ [] :=
    connectedComponentDecomposeWord_nonempty_components right
      rightComponent rightMember
  have leftConnected :
      ConnectedComponentSupportConnected leftComponent :=
    connectedComponentDecomposeWord_supportConnected left
      leftComponent leftMember
  have rightConnected :
      ConnectedComponentSupportConnected rightComponent :=
    connectedComponentDecomposeWord_supportConnected right
      rightComponent rightMember
  have leftComponentLimited :
      ∀ letter, leftComponent.count letter ≤ 2 := by
    intro letter
    have lower := componentCount_le_flattenCount leftMember letter
    rw [connectedComponentDecomposeWord_flatten] at lower
    have upper := leftLimited letter
    omega
  have rightComponentLimited :
      ∀ letter, rightComponent.count letter ≤ 2 := by
    intro letter
    have lower := componentCount_le_flattenCount rightMember letter
    rw [connectedComponentDecomposeWord_flatten] at lower
    have upper := rightLimited letter
    omega
  have sameMembers := componentMembers_of_signature_eq sameSignature
  have componentAgreement :
      EndpointSemanticAgreement leftComponent rightComponent := by
    refine ⟨sortedSupport_eq_of_mem_iff sameMembers, ?_, ?_⟩
    · exact componentWordSignatures_eq
        leftNonempty rightNonempty leftConnected rightConnected
        sameSignature
    · exact componentBlockTheory_of_whole
        leftMember rightMember sameMembers wholeBlockTheory
  obtain ⟨leftPivot, leftPivotData⟩ :=
    connectedCapTwo_reaches_zero
      leftComponentLimited leftConnected
  obtain ⟨rightPivot, rightPivotData⟩ :=
    connectedCapTwo_reaches_zero
      rightComponentLimited rightConnected
  have leftPivotNonempty : leftPivot ≠ [] := by
    intro empty
    have permutation := leftPivotData.permutation
    rw [empty] at permutation
    exact leftNonempty permutation.symm.nil_eq.symm
  have rightPivotNonempty : rightPivot ≠ [] := by
    intro empty
    have permutation := rightPivotData.permutation
    rw [empty] at permutation
    exact rightNonempty permutation.symm.nil_eq.symm
  have pivotAgreement :
      EndpointSemanticAgreement leftPivot rightPivot :=
    leftPivotData.semantic.symm.trans
      (componentAgreement.trans rightPivotData.semantic)
  have pivotsEqual : leftPivot = rightPivot :=
    zeroEndpoint_unique
      leftPivotNonempty rightPivotNonempty
      leftPivotData.twoLimited rightPivotData.twoLimited
      leftPivotData.connected rightPivotData.connected
      leftPivotData.zeroMeasure rightPivotData.zeroMeasure
      pivotAgreement
  have rightReturn :
      ContextualFrozenRTC leftPivot rightComponent := by
    simpa [pivotsEqual] using rightPivotData.reachable.symm
  exact leftPivotData.reachable.trans rightReturn

private theorem componentRoutes_of_signature_eq
    {left right : Word Nat}
    (leftLimited : ∀ letter, left.toList.count letter ≤ 2)
    (rightLimited : ∀ letter, right.toList.count letter ≤ 2)
    (wholeBlockTheory :
      (Identity.mk left right).SatisfiedBy
        SemanticBlockSignature.table.semigroup) :
    ∀ (leftComponents rightComponents : List (List Nat)),
      (∀ component, component ∈ leftComponents →
        component ∈ connectedComponentDecomposeWord left) →
      (∀ component, component ∈ rightComponents →
        component ∈ connectedComponentDecomposeWord right) →
      leftComponents.map connectedComponentSignatureOfList =
        rightComponents.map connectedComponentSignatureOfList →
      List.Forall₂ ContextualFrozenRTC
        leftComponents rightComponents := by
  intro leftComponents
  induction leftComponents with
  | nil =>
      intro rightComponents _ _ same
      cases rightComponents with
      | nil => exact List.Forall₂.nil
      | cons head tail => simp at same
  | cons leftHead leftTail inductionHypothesis =>
      intro rightComponents leftIn rightIn same
      cases rightComponents with
      | nil => simp at same
      | cons rightHead rightTail =>
          simp only [List.map_cons, List.cons.injEq] at same
          have headRoute := pairedComponent_rtc
            leftLimited rightLimited wholeBlockTheory
            (leftIn leftHead (List.Mem.head leftTail))
            (rightIn rightHead (List.Mem.head rightTail))
            same.1
          have tailRoutes := inductionHypothesis rightTail
            (fun component member =>
              leftIn component (List.Mem.tail leftHead member))
            (fun component member =>
              rightIn component (List.Mem.tail rightHead member))
            same.2
          exact List.Forall₂.cons headRoute tailRoutes

/-- Unbounded cap-two endpoint connectivity under exactly the 198 frozen
displayed-law paths. -/
theorem capTwo_sameFactor_rtc
    {left right : Word Nat}
    (leftLimited : ∀ letter, left.toList.count letter ≤ 2)
    (rightLimited : ∀ letter, right.toList.count letter ≤ 2)
    (same : SameFactor left right) :
    ContextualFrozenRTC left.toList right.toList := by
  let leftComponents := connectedComponentDecomposeWord left
  let rightComponents := connectedComponentDecomposeWord right
  have signatureEqual :
      leftComponents.map connectedComponentSignatureOfList =
        rightComponents.map connectedComponentSignatureOfList := by
    simpa [leftComponents, rightComponents,
      connectedComponentSignaturesWord,
      connectedComponentSignaturesList,
      connectedComponentDecomposeWord] using same.components
  have componentRoutes :
      List.Forall₂ ContextualFrozenRTC
        leftComponents rightComponents :=
    componentRoutes_of_signature_eq
      leftLimited rightLimited same.blockTheory
      leftComponents rightComponents
      (by
        intro component member
        simpa [leftComponents] using member)
      (by
        intro component member
        simpa [rightComponents] using member)
      signatureEqual
  have assembled :=
    contextualFrozenRTC_flatten_of_forall₂ componentRoutes
  simpa [leftComponents, rightComponents,
    connectedComponentDecomposeWord_flatten] using assembled

end CapTwoRTCRoute
end SemigroupBasis.CoRoots.Order6L1RRank1.Gd61242744c5092fd
