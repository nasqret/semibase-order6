import SemigroupBasis.CoRoots.Order6S6_3372CorrectedNormalization

/-!
# Exact endpoint for S6_3372

The corrected four-law basis combines the content/endpoint signature of
`S5_303` with the terminal unique-suffix signature of `S5_83`.  The two
literal embeddings into the exact six-element table make those signatures
necessary, and the corrected normalizer proves that they are sufficient.
-/

namespace SemigroupBasis.Order6.S6_3372

open SemigroupBasis

abbrev table : FiniteTable :=
  SemigroupBasis.CoRoots.Order6S6_3372CorrectedBasis.Recorded.table

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6S6_3372CorrectedBasis.basis

def oppositeBasis : List (Identity Nat) := reversedBasis basis

def tableSHA256 : String :=
  "8b04861c1d5afb3dff18ff93f48806c01ef463bd86c80b63775e1965a6e2c4ba"

def tableRowsOneBased : List (List Nat) :=
  SemigroupBasis.CoRoots.Order6S6_3372FinalRepeatedSupportV2.tableOneBased

/-- The endpoint table is exactly the committed Smallsemi representative. -/
theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1],
       [1, 1, 1, 1, 1, 1],
       [1, 1, 1, 1, 1, 1],
       [1, 1, 2, 1, 1, 1],
       [1, 2, 1, 4, 5, 6],
       [1, 2, 2, 4, 5, 6]] :=
  SemigroupBasis.CoRoots.Order6S6_3372FinalRepeatedSupportV2.tableOneBased_certificate

/-- Unconditional complete basis theorem for the exact `S6_3372` table. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6S6_3372CorrectedBasis.basis_complete

/-- Reversal gives the corresponding endpoint for the opposite table. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end SemigroupBasis.Order6.S6_3372
