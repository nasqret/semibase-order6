import SemigroupBasis.CoRoots.Order6SporadicSection18ConnectedEnds

/-! Close the entire simple-free identity branch of C7 using Corollary18.3.
The only remaining completeness input at this assembly boundary concerns
valid identities of pairwise-disjoint connected products WITH a simple letter. -/

namespace SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6SporadicSection12

theorem simpleFree_complete (identity : Identity Nat)
    (valid : identity.SatisfiedBy Actual.table.semigroup)
    (simpleFree : ¬ Canonical.HasSimple identity.lhs.toList) :
    Derives basis identity.lhs identity.rhs := by
  have same := Actual.sameEval_valid identity valid
  have leftNonsimple : ∀ x ∈ identity.lhs.toList, identity.lhs.toList.count x ≠ 1 := by
    intro x _ one
    exact simpleFree ⟨x, one⟩
  have rightNonsimple : ∀ x ∈ identity.rhs.toList, identity.rhs.toList.count x ≠ 1 := by
    intro x _ one
    exact simpleFree ⟨x, (same.countOne x).mpr one⟩
  have lists : ListDerives identity.lhs.toList identity.rhs.toList :=
    corollary18_3 identity.lhs.toList identity.rhs.toList
      leftNonsimple rightNonsimple (fun x => same.mem x)
  exact S5_107.ListDerives.toWord lists

/-- This implication preserves the full unrestricted target and identifies
the still-unproved simple-letter branch precisely. -/
theorem basisFor_of_simplePairwiseConnected
    (complete : ∀ identity : Identity Nat,
      identity.SatisfiedBy Actual.table.semigroup →
      PairwiseDisjointConnectedProduct identity.lhs →
      PairwiseDisjointConnectedProduct identity.rhs →
      Canonical.HasSimple identity.lhs.toList →
      Derives basis identity.lhs identity.rhs) :
    BasisFor Actual.table.semigroup basis := by
  apply basisFor_of_pairwiseConnected
  intro identity valid leftProduct rightProduct
  by_cases simple : Canonical.HasSimple identity.lhs.toList
  · exact complete identity valid leftProduct rightProduct simple
  · exact simpleFree_complete identity valid simple

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.simpleFree_complete
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction.basisFor_of_simplePairwiseConnected

end SemigroupBasis.CoRoots.Order6SporadicSection18.Reduction
