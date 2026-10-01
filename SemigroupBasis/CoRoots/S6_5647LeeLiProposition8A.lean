import SemigroupBasis.CoRoots.Order6LeeLiProposition8AAssembly

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeLiProposition8A.S6_5647

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6LeeLiProposition8A

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact zero-based multiplication for catalogue representative `S6_5647`.
Its one-based rows are
`111111/111112/111213/111214/123355/123456`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 1 right else
      if left = 2 then row6 0 0 0 1 0 2 right else
        if left = 3 then row6 0 0 0 1 0 3 right else
          if left = 4 then row6 0 1 2 2 4 4 right else
            row6 0 1 2 3 4 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "69e15ffa52a29d501f7965b17a0116e1081b81ba2b5af615f1dbb28c33a87535"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 2],
        [1, 1, 1, 2, 1, 3], [1, 1, 1, 2, 1, 4],
        [1, 2, 3, 3, 5, 5], [1, 2, 3, 4, 5, 6]] := by
  decide

theorem identityElement_certificate :
    (∀ value : Fin 6, mul 5 value = value) ∧
      (∀ value : Fin 6, mul value 5 = value) := by
  decide

/-! ## Exact target soundness -/

set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  models_of_individual_fused_checks table
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

/-! ## Published A to catalogue relabelling -/

/-- The audited zero-based relabelling `[0,1,2,4,3,5]`, equivalently
`[1,2,3,5,4,6]` in the one-based source packet. -/
def publishedToCatalogueRelabel (value : Fin 6) : Fin 6 :=
  if value = 0 then 0 else
    if value = 1 then 1 else
      if value = 2 then 2 else
        if value = 3 then 4 else
          if value = 4 then 3 else 5

def publishedToCatalogueZeroBased : List Nat :=
  List.ofFn fun value : Fin 6 =>
    (publishedToCatalogueRelabel value).val

theorem publishedToCatalogueZeroBased_certificate :
    publishedToCatalogueZeroBased = [0, 1, 2, 4, 3, 5] := by
  decide

def publishedToCatalogueOneBased : List Nat :=
  List.ofFn fun value : Fin 6 =>
    (publishedToCatalogueRelabel value).val + 1

theorem publishedToCatalogueOneBased_certificate :
    publishedToCatalogueOneBased = [1, 2, 3, 5, 4, 6] := by
  decide

/-- Certified copy of published Lee--Li monoid A inside the exact catalogue
representative.  Since both carriers have order six, this injective relabelling
is the audited table isomorphism in the direction required by
`BasisFor.inheritAlongEmbedding`. -/
def publishedToCatalogueEmbedding :
    Embedding publishedTable.semigroup table.semigroup where
  toFun := publishedToCatalogueRelabel
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

/-! ## Unconditional representative endpoints -/

/-- `S6_5647` inherits the unrestricted Proposition 8.1/A identity theory
through the exact published-to-catalogue relabelling. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  published_basis.inheritAlongEmbedding
    publishedToCatalogueEmbedding models

/-- The reversed Proposition 8.1/A system is a basis for the opposite
catalogue representative. -/
theorem opposite_representative_basis :
    BasisFor table.semigroup.opposite oppositeBasis := by
  simpa [oppositeBasis] using representative_basis.oppositeReversed

end SemigroupBasis.CoRoots.Order6LeeLiProposition8A.S6_5647
