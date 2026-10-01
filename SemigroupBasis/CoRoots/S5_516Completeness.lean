import SemigroupBasis.CoRoots.S5_516Semantics

namespace SemigroupBasis.CoRoots.S5_516

open SemigroupBasis

/-- Unconditional exact-basis theorem for the stored `S5_516`
representative. -/
theorem representative_basis :
    BasisFor table.semigroup basis :=
  basis_complete_of_exact table models valid_exactBasisClass

/-- Unconditional endpoint for the literal reverse-word basis on the
opposite table. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite expectedOppositeBasis := by
  rw [← oppositeBasis_eq_expected]
  exact representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.S5_516
