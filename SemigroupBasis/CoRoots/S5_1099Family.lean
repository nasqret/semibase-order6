import SemigroupBasis.CoRoots.S5_1099Semantics

namespace SemigroupBasis.CoRoots.S5_1099

open SemigroupBasis

/-- Unconditional exact basis endpoint for the canonical representative. -/
theorem basis_complete : BasisFor table.semigroup basis := by
  refine ⟨models, ?_⟩
  intro identity valid
  exact derives_of_sameTraceSignature
    (valid_sameTraceSignature identity valid)

theorem representative_basis :
    BasisFor table.semigroup basis :=
  basis_complete

/-- Unconditional endpoint for the anti-isomorphism orientation. -/
theorem opposite_basis_complete :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using basis_complete.oppositeReversed

theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis :=
  opposite_basis_complete

theorem derives_iff_sameTraceSignature
    {left right : Word Nat} :
    Derives basis left right ↔ SameTraceSignature left right := by
  constructor
  · intro derivation
    have valid :
        (Identity.mk left right).SatisfiedBy table.semigroup :=
      fun valuation => derivation.sound models valuation
    exact valid_sameTraceSignature (Identity.mk left right) valid
  · exact derives_of_sameTraceSignature

end SemigroupBasis.CoRoots.S5_1099
