import SemigroupBasis.CoRoots.Order6S6_15646Semantics
import SemigroupBasis.Opposite

namespace SemigroupBasis.CoRoots.Order6FennemoreR3Band

open SemigroupBasis

/-- Equal recursive `i3` invariants derive equal words. -/
theorem derivesOfInvariantEq
    (left right : Word Nat)
    (equalInvariant :
      r3Invariant left.toList = r3Invariant right.toList) :
    Derives basis left right :=
  r3_derives_of_invariant_eq left right equalInvariant

/-- The unconditional exact endpoint for the direct Smallsemi representative
`S6_15646`. -/
theorem representative_basis :
    BasisFor table.semigroup basis := by
  refine ⟨basis_models, ?_⟩
  intro identity valid
  exact derivesOfInvariantEq identity.lhs identity.rhs
    (r3_invariant_eq_of_valid identity.lhs identity.rhs valid)

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

/-- The opposite endpoint follows from the established reversal API. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.Order6FennemoreR3Band
