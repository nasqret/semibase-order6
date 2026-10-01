import SemigroupBasis.CoRoots.Order6SporadicSection25F3NoCuts
import SemigroupBasis.CoRoots.Order6SporadicSection25F3AffineModel
import SemigroupBasis.CoRoots.Order6SporadicSection25HeadDetection

namespace SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator
open SemigroupBasis

theorem nontrivialConnected_tail_ne_nil (word : Word Nat)
    (connected : NontrivialConnected word.toList) : word.tail ≠ [] := by
  intro empty
  have lengthBound := connected.1
  simp only [Word.toList, empty, List.length_cons, List.length_nil] at lengthBound
  omega

theorem separatorFree_compare (identity : Identity Nat)
    (separatorValid : identity.SatisfiedBy semigroup)
    (affineValid : identity.SatisfiedBy Generated.Catalogue.S4_96.table.semigroup.opposite)
    (noSeparator : NoExactSeparator identity.lhs.toList) :
    Derives (basis true) identity.lhs identity.rhs := by
  rcases separatorFree_connectedWord identity.lhs noSeparator with
    ⟨left, leftConnected, leftListDerives, _⟩
  rcases separatorFree_connectedWord identity.rhs
      (noSeparator_transport identity separatorValid noSeparator) with
    ⟨right, rightConnected, rightListDerives, _⟩
  have leftDerives : Derives (basis true) identity.lhs left :=
    S5_107.ListDerives.toWord leftListDerives
  have rightDerives : Derives (basis true) identity.rhs right :=
    S5_107.ListDerives.toWord rightListDerives
  have mergedValid : (⟨left,right⟩ : Identity Nat).SatisfiedBy
      Generated.Catalogue.S4_96.table.semigroup.opposite := by
    intro valuation
    exact (leftDerives.sound basis_true_models_affine valuation).symm.trans
      ((affineValid valuation).trans (rightDerives.sound basis_true_models_affine valuation))
  have compared := connected_affineCompare true left right
    (nontrivialConnected_tail_ne_nil left leftConnected)
    (nontrivialConnected_tail_ne_nil right rightConnected)
    leftConnected.2 rightConnected.2 mergedValid
  exact leftDerives.trans (compared.trans rightDerives.symm)

#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.nontrivialConnected_tail_ne_nil
#print axioms SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator.separatorFree_compare

end SemigroupBasis.CoRoots.Order6SporadicSection25.F3Separator
