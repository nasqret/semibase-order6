import SemigroupBasis.CoRoots.Order6S6_14921SingletonShortBlockPeriod3Completeness

/-!
# Exact endpoint for S6_14921

The three recorded laws normalize every word by first-occurrence order.  The
initial block has threshold two and period three; every later block has its
positive multiplicity modulo three because `xyyyy = xy` is available in a
nonempty left context.
-/

namespace SemigroupBasis.Order6.S6_14921

open SemigroupBasis

abbrev table : FiniteTable :=
  SemigroupBasis.CoRoots.Order6S6_14921SingletonShortBlockPeriod3.table

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6S6_14921SingletonShortBlockPeriod3.basis

def oppositeBasis : List (Identity Nat) := reversedBasis basis

def tableSHA256 : String :=
  "37a1f3815f54b1a9a663244fa565c43a98fbf0e5566d6005128168bd1e7e5c37"

def tableRowsOneBased : List (List Nat) :=
  SemigroupBasis.CoRoots.Order6S6_14921SingletonShortBlockPeriod3.tableOneBased

/-- The endpoint table is exactly the committed Smallsemi representative. -/
theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1],
       [1, 1, 1, 2, 2, 2],
       [3, 3, 3, 3, 3, 3],
       [1, 1, 3, 4, 5, 6],
       [1, 1, 3, 5, 6, 4],
       [1, 1, 3, 6, 4, 5]] :=
  SemigroupBasis.CoRoots.Order6S6_14921SingletonShortBlockPeriod3.tableOneBased_certificate

/-- Unconditional complete basis theorem for the exact `S6_14921` table. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6S6_14921SingletonShortBlockPeriod3.basis_complete_aristotle

/-- Reversal gives the corresponding endpoint for the opposite table. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end SemigroupBasis.Order6.S6_14921
