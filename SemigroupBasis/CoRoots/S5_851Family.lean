import SemigroupBasis.CoRoots.S5_851SupportCompletion

namespace SemigroupBasis.CoRoots.S5_851

open SemigroupBasis

/-- Unconditional representative endpoint after closing the support-order
normalization obligation. -/
theorem basisFor : BasisFor table.semigroup basis :=
  representative_basis_of_headSupportFinalDerivationalCompleteness
    headSupportFinalDerivationalCompleteness

/-- Unconditional opposite endpoint for the non-self-dual representative. -/
theorem oppositeBasisFor :
    BasisFor table.semigroup.opposite expectedOppositeBasis :=
  opposite_basis_of_headSupportFinalDerivationalCompleteness
    headSupportFinalDerivationalCompleteness

end SemigroupBasis.CoRoots.S5_851

namespace SemigroupBasis.CoRoots.S5_867

open SemigroupBasis
open SemigroupBasis.CoRoots.S5_851

theorem basisFor : BasisFor table.semigroup basis :=
  representative_basis_of_headSupportFinalDerivationalCompleteness
    headSupportFinalDerivationalCompleteness

theorem oppositeBasisFor :
    BasisFor table.semigroup.opposite expectedOppositeBasis :=
  opposite_basis_of_headSupportFinalDerivationalCompleteness
    headSupportFinalDerivationalCompleteness

end SemigroupBasis.CoRoots.S5_867
