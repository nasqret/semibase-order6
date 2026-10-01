import SemigroupBasis.CoRoots.Order6SporadicSection25UnitRestriction
import SemigroupBasis.CoRoots.Order6SporadicSection25ComponentSemantics

/-! Actual support-disjoint components are isolated by a Boolean filter.
These are generic list facts, with no bound or assumed normal-form field. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection25
open SemigroupBasis

theorem filter_all_kept (keep : Nat → Bool) (letters : List Nat)
    (kept : ∀ letter ∈ letters, keep letter = true) : letters.filter keep = letters := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      have first := kept letter (List.Mem.head _)
      have tail := ih (fun x member => kept x (List.Mem.tail _ member))
      simp [first, tail]

theorem filter_none_kept (keep : Nat → Bool) (letters : List Nat)
    (discarded : ∀ letter ∈ letters, keep letter = false) : letters.filter keep = [] := by
  induction letters with
  | nil => rfl
  | cons letter rest ih =>
      have first := discarded letter (List.Mem.head _)
      have tail := ih (fun x member => discarded x (List.Mem.tail _ member))
      simp [first, tail]

theorem filter_to_own_support (letters : List Nat) :
    letters.filter (fun x => decide (x ∈ letters)) = letters := by
  apply filter_all_kept
  intro letter member
  exact decide_eq_true member

theorem filter_disjoint_support (left right : List Nat)
    (disjoint : Examples.ConnectedComponentSupportsDisjoint left right) :
    left.filter (fun x => decide (x ∈ right)) = [] := by
  apply filter_none_kept
  intro letter member
  exact decide_eq_false (disjoint letter member)

theorem filter_flatten_component (components : List (List Nat)) (component : List Nat)
    (member : component ∈ components)
    (disjoint : components.Pairwise Examples.ConnectedComponentSupportsDisjoint) :
    components.flatten.filter (fun x => decide (x ∈ component)) = component := by
  induction components with
  | nil => cases member
  | cons first rest ih =>
      have relations := List.pairwise_cons.mp disjoint
      rcases List.mem_cons.mp member with equal | inRest
      · subst component
        have restEmpty : rest.flatten.filter (fun x => decide (x ∈ first)) = [] := by
          apply filter_none_kept
          intro letter letterMember
          rcases List.mem_flatten.mp letterMember with ⟨other, otherMember, inOther⟩
          apply decide_eq_false
          intro inFirst
          exact relations.1 other otherMember letter inFirst inOther
        simp only [List.flatten_cons, List.filter_append, filter_to_own_support,
          restEmpty, List.append_nil]
      · have firstEmpty := filter_disjoint_support first component (relations.1 component inRest)
        have remainder := ih inRest relations.2
        simp only [List.flatten_cons, List.filter_append, firstEmpty, remainder, List.nil_append]

theorem sameComponentSignature_support {left right : List Nat}
    (same : Examples.connectedComponentSignatureOfList left =
      Examples.connectedComponentSignatureOfList right) :
    ∀ letter, letter ∈ left ↔ letter ∈ right := by
  have supports := congrArg Examples.connectedComponentSignature.support same
  rw [Examples.connectedComponentSignatureOfList_support,
    Examples.connectedComponentSignatureOfList_support] at supports
  intro letter
  calc
    letter ∈ left ↔ letter ∈ Examples.connectedComponentSortedSupport left :=
      (Examples.connectedComponentSortedSupport_mem_iff letter left).symm
    _ ↔ letter ∈ Examples.connectedComponentSortedSupport right := by rw [supports]
    _ ↔ letter ∈ right := Examples.connectedComponentSortedSupport_mem_iff letter right

theorem actualComponent_filter (word : Word Nat) (component : List Nat)
    (member : component ∈ Examples.connectedComponentDecomposeWord word) :
    word.toList.filter (fun x => decide (x ∈ component)) = component := by
  have filtered := filter_flatten_component (Examples.connectedComponentDecomposeWord word)
    component member (Examples.connectedComponentDecomposeWord_pairwiseDisjoint word)
  simpa only [Examples.connectedComponentDecomposeWord_flatten] using filtered

theorem actualAffineValid_componentPair (identity : Identity Nat)
    (valid : identity.SatisfiedBy Generated.Catalogue.S4_96.table.semigroup.opposite)
    (left right : Word Nat)
    (leftMember : left.toList ∈ Examples.connectedComponentDecomposeWord identity.lhs)
    (rightMember : right.toList ∈ Examples.connectedComponentDecomposeWord identity.rhs)
    (same : Examples.connectedComponentSignatureOfList left.toList =
      Examples.connectedComponentSignatureOfList right.toList) :
    (⟨left,right⟩ : Identity Nat).SatisfiedBy Generated.Catalogue.S4_96.table.semigroup.opposite := by
  have supports := sameComponentSignature_support same
  have masks : (fun x => decide (x ∈ left.toList)) = (fun x => decide (x ∈ right.toList)) := by
    funext letter
    by_cases member : letter ∈ left.toList
    · have other := (supports letter).1 member
      simp [member, other]
    · have other : letter ∉ right.toList := fun present => member ((supports letter).2 present)
      simp [member, other]
  apply actualAffineValid_restrict_filter identity valid
    (fun x => decide (x ∈ left.toList)) left right
  · exact actualComponent_filter identity.lhs left.toList leftMember
  · rw [masks]
    exact actualComponent_filter identity.rhs right.toList rightMember

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.filter_all_kept
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.filter_none_kept
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.filter_to_own_support
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.filter_disjoint_support
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.filter_flatten_component
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.sameComponentSignature_support
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.actualComponent_filter
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.actualAffineValid_componentPair

end SemigroupBasis.CoRoots.Order6SporadicSection25
