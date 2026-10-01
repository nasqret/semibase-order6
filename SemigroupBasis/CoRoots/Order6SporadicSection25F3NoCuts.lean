import SemigroupBasis.CoRoots.Order6SporadicSection25F3BlockMerge
import SemigroupBasis.CoRoots.Order6SporadicSection25F3LocalUnits
import SemigroupBasis.Examples.ConnectedComponentFourComponents

/-! Absence of an actual B0 exact separator forces every maximal support
component to be nontrivial; the constructed F3 merge then applies. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator
open SemigroupBasis

def NoExactSeparator (letters : List Nat) : Prop :=
  ∀ left separator right, ¬Examples.UniqueSeparatorFourExactCut letters left separator right

theorem singleton_component_exactCut (parts before after : List (List Nat)) (separator : Nat)
    (shape : parts = before ++ [separator] :: after)
    (pairwise : parts.Pairwise Examples.ConnectedComponentSupportsDisjoint) :
    Examples.UniqueSeparatorFourExactCut parts.flatten before.flatten separator after.flatten := by
  subst parts
  have outer := List.pairwise_append.mp pairwise
  have middle := List.pairwise_cons.mp outer.2.1
  have absentLeft : separator ∉ before.flatten := by
    intro member
    rcases List.mem_flatten.mp member with ⟨component, inBefore, inComponent⟩
    exact outer.2.2 component inBefore [separator] (List.Mem.head _) separator inComponent (by simp)
  have absentRight : separator ∉ after.flatten := by
    intro member
    rcases List.mem_flatten.mp member with ⟨component, inAfter, inComponent⟩
    exact middle.1 component inAfter separator (by simp) inComponent
  have disjoint : Examples.UniqueSeparatorFourSupportsDisjoint before.flatten after.flatten := by
    intro letter inLeft inRight
    rcases List.mem_flatten.mp inLeft with ⟨leftPart, leftMember, inLeftPart⟩
    rcases List.mem_flatten.mp inRight with ⟨rightPart, rightMember, inRightPart⟩
    exact outer.2.2 leftPart leftMember rightPart
      (List.mem_cons_of_mem [separator] rightMember) letter inLeftPart inRightPart
  have flattened : (before ++ [separator] :: after).flatten =
      before.flatten ++ separator :: after.flatten := by
    simp only [List.flatten_append, List.flatten_cons, List.singleton_append]
  refine ⟨flattened, ?_, disjoint⟩
  have leftZero : before.flatten.count separator = 0 := List.count_eq_zero.mpr absentLeft
  have rightZero : after.flatten.count separator = 0 := List.count_eq_zero.mpr absentRight
  rw [flattened, List.count_append, List.count_cons_self, leftZero, rightZero]

theorem noSeparator_components_nontrivial (word : Word Nat)
    (noSeparator : NoExactSeparator word.toList) :
    ∀ component, component ∈ Examples.connectedComponentDecomposeWord word →
      NontrivialConnected component := by
  intro component member
  have nonempty := Examples.connectedComponentDecomposeWord_nonempty_components word component member
  have connected := Examples.connectedComponentDecomposeWord_supportConnected word component member
  rcases component with _ | ⟨head, tail⟩
  · exact False.elim (nonempty rfl)
  · have tailNonempty : tail ≠ [] := by
      intro empty
      have singletonMember : [head] ∈ Examples.connectedComponentDecomposeWord word := by
        simpa only [empty] using member
      rcases List.mem_iff_append.mp singletonMember with ⟨before, after, partsShape⟩
      have cut := singleton_component_exactCut (Examples.connectedComponentDecomposeWord word)
        before after head partsShape (Examples.connectedComponentDecomposeWord_pairwiseDisjoint word)
      rw [Examples.connectedComponentDecomposeWord_flatten] at cut
      exact noSeparator before.flatten head after.flatten cut
    refine ⟨?_, connected⟩
    rcases tail with _ | ⟨next, rest⟩
    · exact False.elim (tailNonempty rfl)
    · simp only [List.length_cons]
      omega

theorem separatorFree_connectedWord (word : Word Nat)
    (noSeparator : NoExactSeparator word.toList) :
    ∃ merged : Word Nat, NontrivialConnected merged.toList ∧
      ListDerives true word.toList merged.toList ∧
      ∀ letter, letter ∈ merged.toList ↔ letter ∈ word.toList := by
  rcases mergeConnectedList (Examples.connectedComponentDecomposeWord word)
      (noSeparator_components_nontrivial word noSeparator)
      (Examples.connectedComponentDecomposeWord_nonempty word) with
    ⟨merged, connected, derives, support⟩
  rw [Examples.connectedComponentDecomposeWord_flatten] at derives support
  rcases merged with _ | ⟨head, tail⟩
  · have lengthBound := connected.1
    simp only [List.length_nil] at lengthBound
    omega
  · exact ⟨⟨head, tail⟩, connected, derives, support⟩

theorem noSeparator_transport (identity : Identity Nat)
    (valid : identity.SatisfiedBy semigroup)
    (noSeparator : NoExactSeparator identity.lhs.toList) :
    NoExactSeparator identity.rhs.toList := by
  intro left separator right cut
  rcases Examples.uniqueSeparatorFourEqualEval_transportExactCut
      identity.rhs identity.lhs (fun valuation => (valid valuation).symm) cut with
    ⟨before, after, transported, _, _⟩
  exact noSeparator before separator after transported

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.singleton_component_exactCut
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.noSeparator_components_nontrivial
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.separatorFree_connectedWord
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.noSeparator_transport

end SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator
