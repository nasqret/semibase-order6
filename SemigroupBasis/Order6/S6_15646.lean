import SemigroupBasis.CoRoots.Order6S6_15646

/-!
# Exact endpoint for S6_15646

The two Fennemore band laws `x = xx` and `xyz = xyzxzyz` normalize words to
the recursive `i3` invariant.  The exact six-element table separates unequal
invariants, yielding the unrestricted completeness theorem.
-/

namespace SemigroupBasis.Order6.S6_15646

open SemigroupBasis

abbrev table : FiniteTable :=
  SemigroupBasis.CoRoots.Order6FennemoreR3Band.table

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6FennemoreR3Band.basis

def oppositeBasis : List (Identity Nat) :=
  reversedBasis basis

def tableSHA256 : String :=
  "e6d1891b7fabf499ef037f1568b959f775b05dc5c62d735597186275db6dfe9e"

def tableRowsOneBased : List (List Nat) :=
  SemigroupBasis.CoRoots.Order6FennemoreR3Band.tableOneBased

/-- The endpoint table is exactly the committed Smallsemi representative. -/
theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1],
       [1, 2, 1, 2, 5, 6],
       [3, 3, 3, 3, 3, 3],
       [1, 2, 3, 4, 5, 6],
       [1, 2, 6, 5, 5, 6],
       [6, 6, 6, 6, 6, 6]] :=
  SemigroupBasis.CoRoots.Order6FennemoreR3Band.tableOneBased_certificate

/-- Unconditional complete basis theorem for the exact `S6_15646` table. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FennemoreR3Band.representative_basis

/-- Reversal gives the corresponding endpoint for the opposite table. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end SemigroupBasis.Order6.S6_15646
