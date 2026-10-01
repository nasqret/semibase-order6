import SemigroupBasis.CoRoots.Order6SporadicSection25ComponentIsolation

/-! The arbitrary-word F4 converse. Actual factor validity supplies both
the ordered component signature and the restricted affine comparisons. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection25
open SemigroupBasis

theorem componentSignature_singleton_injective (letters : List Nat) (head : Nat)
    (same : Examples.connectedComponentSignatureOfList letters =
      Examples.connectedComponentSignatureOfList [head]) : letters = [head] := by
  have supports := congrArg Examples.connectedComponentSignature.support same
  rw [Examples.connectedComponentSignatureOfList_support,
    Examples.connectedComponentSignatureOfList_support] at supports
  have sortedSingleton : Examples.connectedComponentSortedSupport [head] = [head] := by
    simp [Examples.connectedComponentSortedSupport, Examples.connectedComponentDistinctSupport]
  rw [sortedSingleton] at supports
  have flags := congrArg Examples.connectedComponentSignature.repeatedUnary same
  have flag : decide (letters.length ≠ 1) = false := by
    simpa only [Examples.connectedComponentSignatureOfList, supports, sortedSingleton] using flags
  have length : letters.length = 1 := by
    by_cases equal : letters.length = 1
    · exact equal
    · have impossible : (true : Bool) = false := by
        simpa only [decide_eq_true equal] using flag
      cases impossible
  rcases List.length_eq_one_iff.mp length with ⟨found, rfl⟩
  have equal : found = head := List.mem_singleton.mp
    ((sameComponentSignature_support same found).1 (List.Mem.head _))
  exact congrArg (fun letter => [letter]) equal

theorem actualComponentPair_derives (withB0 : Bool) (identity : Identity Nat)
    (valid : identity.SatisfiedBy Generated.Catalogue.S4_96.table.semigroup.opposite)
    (left right : List Nat)
    (leftMember : left ∈ Examples.connectedComponentDecomposeWord identity.lhs)
    (rightMember : right ∈ Examples.connectedComponentDecomposeWord identity.rhs)
    (same : Examples.connectedComponentSignatureOfList left =
      Examples.connectedComponentSignatureOfList right) :
    ListDerives withB0 left right := by
  have leftNonempty := Examples.connectedComponentDecomposeWord_nonempty_components
    identity.lhs left leftMember
  have rightNonempty := Examples.connectedComponentDecomposeWord_nonempty_components
    identity.rhs right rightMember
  have leftConnected := actualDecomposition_supportConnected identity.lhs left leftMember
  have rightConnected := actualDecomposition_supportConnected identity.rhs right rightMember
  cases left with
  | nil => exact False.elim (leftNonempty rfl)
  | cons leftHead leftTail =>
      cases right with
      | nil => exact False.elim (rightNonempty rfl)
      | cons rightHead rightTail =>
          by_cases leftSingleton : leftTail = []
          · subst leftTail
            have equal := componentSignature_singleton_injective (rightHead :: rightTail) leftHead same.symm
            rw [equal]
            exact S5_107.ListDerives.refl _
          · by_cases rightSingleton : rightTail = []
            · subst rightTail
              have equal := componentSignature_singleton_injective (leftHead :: leftTail) rightHead same
              have tailEqual : leftTail = [] := by
                have tails := congrArg List.tail equal
                simpa only [List.tail_cons] using tails
              exact False.elim (leftSingleton tailEqual)
            · let leftWord : Word Nat := ⟨leftHead,leftTail⟩
              let rightWord : Word Nat := ⟨rightHead,rightTail⟩
              have localValid := actualAffineValid_componentPair identity valid leftWord rightWord
                leftMember rightMember same
              have derived := connected_affineCompare withB0 leftWord rightWord
                leftSingleton rightSingleton leftConnected rightConnected localValid
              exact S5_107.ListDerives.ofWord derived

theorem flattenedComponents_derive (withB0 : Bool) (left right : List (List Nat))
    (same : left.map Examples.connectedComponentSignatureOfList =
      right.map Examples.connectedComponentSignatureOfList)
    (pairDerives : ∀ l ∈ left, ∀ r ∈ right,
      Examples.connectedComponentSignatureOfList l = Examples.connectedComponentSignatureOfList r →
        ListDerives withB0 l r) :
    ListDerives withB0 left.flatten right.flatten := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact S5_107.ListDerives.refl _
      | cons first rest => cases same
  | cons first rest ih =>
      cases right with
      | nil => cases same
      | cons other remaining =>
          have separated := List.cons.inj same
          have firstDerives := pairDerives first (List.Mem.head _) other (List.Mem.head _) separated.1
          have restDerives := ih remaining separated.2 (fun l lm r rm equal =>
            pairDerives l (List.Mem.tail _ lm) r (List.Mem.tail _ rm) equal)
          simpa only [List.flatten_cons] using
            (firstDerives.append rest.flatten).trans (restDerives.prepend other)

theorem F4_derives_of_actual_factors (identity : Identity Nat)
    (affineValid : identity.SatisfiedBy Generated.Catalogue.S4_96.table.semigroup.opposite)
    (componentValid : identity.SatisfiedBy Generated.Catalogue.S4_70.table.semigroup) :
    Derives (basis false) identity.lhs identity.rhs := by
  have signatures := actualF4Valid_componentSignatures identity componentValid
  change (Examples.connectedComponentDecomposeWord identity.lhs).map
      Examples.connectedComponentSignatureOfList =
    (Examples.connectedComponentDecomposeWord identity.rhs).map
      Examples.connectedComponentSignatureOfList at signatures
  have derived := flattenedComponents_derive false
    (Examples.connectedComponentDecomposeWord identity.lhs)
    (Examples.connectedComponentDecomposeWord identity.rhs) signatures
    (fun left lm right rm same => actualComponentPair_derives false identity affineValid
      left right lm rm same)
  have listDerived : ListDerives false identity.lhs.toList identity.rhs.toList := by
    simpa only [Examples.connectedComponentDecomposeWord_flatten] using derived
  exact S5_107.ListDerives.toWord listDerived

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.componentSignature_singleton_injective
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.actualComponentPair_derives
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.flattenedComponents_derive
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F4_derives_of_actual_factors

end SemigroupBasis.CoRoots.Order6SporadicSection25
