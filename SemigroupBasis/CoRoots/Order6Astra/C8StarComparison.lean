import SemigroupBasis.CoRoots.Order6Astra.C8BranchKeys
import SemigroupBasis.CoRoots.Order6Astra.C8ChainComparison

namespace SemigroupBasis.CoRoots.Order6Astra.C8StarComparison

open Order6SporadicSection19.Published
open C8Star C8TailCuts C8SemanticKey C8ListDerives C8BranchKeys C8StarKeyFacts
open C8ChainComparison C8BranchAlgebra

def Smaller (alphabet : List Nat) : Prop :=
  ∀ smaller : List Nat, smaller.length < alphabet.length → ∀ u v : List Nat,
    (∀ x ∈ u, x ∈ smaller) → Key u v → Rel u v

theorem branch_derived (alphabet : List Nat) (recursive : Smaller alphabet)
    (left right : Star) (key : Key left.word.toList right.word.toList)
    (covered : ∀ x ∈ left.word.toList, x ∈ alphabet)
    (branch : Word Nat) (member : branch ∈ left.branches) :
    ∃ other ∈ right.branches, Derives basis branch other := by
  obtain ⟨p, t, literal, fresh⟩ := left.marked branch member
  obtain ⟨other, otherMember, q, target, _, nextKey⟩ :=
    matching_prefix_key left right key branch member p t literal fresh
  have headPresent := covered left.root.head left.root_head_present
  have shorter := erase_shorter alphabet left.root.head headPresent
  have prefixCovered : ∀ x ∈ p, x ∈ alphabet.erase left.root.head := by
    intro x hx
    apply left.branch_erase alphabet covered branch member x
    rw [literal]
    exact List.mem_append.mpr (Or.inl hx)
  have next := recursive (alphabet.erase left.root.head) shorter p q prefixCovered nextKey
  refine ⟨other, otherMember, ?_⟩
  apply to_words
  rw [literal, target]
  exact C8ListDerives.append next (C8ListDerives.refl [t])

/-- The entire connected recursive comparison, assuming only strictly smaller
alphabet cases of the same statement. No same-size completeness assumption. -/
theorem compare_stars (alphabet : List Nat) (recursive : Smaller alphabet)
    (left right : Star) (key : Key left.word.toList right.word.toList)
    (covered : ∀ x ∈ left.word.toList, x ∈ alphabet) : Derives basis left.word right.word := by
  have targetCovered : ∀ x ∈ right.word.toList, x ∈ alphabet :=
    fun x hx => covered x ((key.support x).mpr hx)
  have roots := matching_roots left right key
  have paired := compare_chains (left.root ++ left.root) left.branches right.branches
    left.pairwise right.pairwise
    (branch_derived alphabet recursive left right key covered)
    (branch_derived alphabet recursive right left key.symm targetCovered)
  simpa only [Star.word, roots] using paired

end SemigroupBasis.CoRoots.Order6Astra.C8StarComparison

#print axioms SemigroupBasis.CoRoots.Order6Astra.C8StarComparison.branch_derived
#print axioms SemigroupBasis.CoRoots.Order6Astra.C8StarComparison.compare_stars
