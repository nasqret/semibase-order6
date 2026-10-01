import SemigroupBasis.CoRoots.Order6LeeLiProposition8ASyntax
import SemigroupBasis.Examples.CommutativeExponentFour
import SemigroupBasis.Transfer

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6LeeLiProposition8A

open SemigroupBasis
open SemigroupBasis.Examples

/-!
# Lee--Li Proposition 8.1/A semantic scaffold

This file fixes the published monoid, its exact finite semantic certificates,
and the exponent-four subsemigroup used by the eventual completeness proof.
Canonicalization and completeness begin below this scaffold in a later
materialization step.
-/

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- The exact zero-based multiplication of the monoid labelled `A` in
Lee--Li Proposition 8.1.  Its one-based rows are
`111111/111112/111123/123434/111125/123456`. -/
def publishedMul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 1 right else
      if left = 2 then row6 0 0 0 0 1 2 right else
        if left = 3 then row6 0 1 2 3 2 3 right else
          if left = 4 then row6 0 0 0 0 1 4 right else
            row6 0 1 2 3 4 5 right

def publishedTable : FiniteTable where
  order := 6
  mul := publishedMul
  assoc := by decide

def publishedTableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 =>
      (publishedTable.mul left right).val + 1

theorem publishedTableRowsOneBased_certificate :
    publishedTableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 1, 2],
        [1, 1, 1, 1, 2, 3], [1, 2, 3, 4, 3, 4],
        [1, 1, 1, 1, 2, 5], [1, 2, 3, 4, 5, 6]] := by
  decide

/-- One-based table element `6` is the identity of published monoid `A`. -/
def publishedIdentityElement : Fin 6 := 5

theorem publishedIdentityElement_certificate :
    (forall value : Fin 6,
        publishedMul publishedIdentityElement value = value) ∧
      (forall value : Fin 6,
        publishedMul value publishedIdentityElement = value) := by
  decide

/-! ## Frozen source and semantic commitments -/

def publishedContractSourceSHA256 : String :=
  "f8cdaf4b0fa01127736556b31ef7819b7ac38259621c10fb0873267ae823a919"

def publishedSystemSemanticSHA256 : String :=
  "7e5b81a7c453a84fdaf611cc27815d3488147235ea46138e3209a809a9890d28"

def publishedRowsSemanticSHA256 : String :=
  "ca608b86859cc61724914a9957d96dc1e096a8b56fc1afb25a9912fcc23b12e9"

def publishedNumericTableSemanticSHA256 : String :=
  "fe0cef0ac7cb6aa4da2d67ea143e5a3a1a641449ef899cb41fdd95ae19ccbd01"

def directBasisSemanticSHA256 : String :=
  "c386a312374667336b5e2c685660da84e33f9863ad5b5bc491ca0cd3667e4e55"

/-! ## Exact finite soundness -/

set_option maxHeartbeats 0 in
theorem publishedModels : Models publishedTable.semigroup basis :=
  models_of_individual_fused_checks publishedTable
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ## The exponent-four semantic subsemigroup -/

/-- The four capped-multiplicity states embed with zero-based image
`[0,1,4,5]` in published monoid `A`. -/
def exponentFourToPublished (value : Fin 4) : Fin 6 :=
  if value = 0 then 0 else
    if value = 1 then 1 else
      if value = 2 then 4 else 5

def exponentFourEmbeddingZeroBased : List Nat :=
  List.ofFn fun value : Fin 4 =>
    (exponentFourToPublished value).val

theorem exponentFourEmbeddingZeroBased_certificate :
    exponentFourEmbeddingZeroBased = [0, 1, 4, 5] := by
  decide

def exponentFourEmbedding :
    Embedding commutativeExponentFour.semigroup publishedTable.semigroup where
  toFun := exponentFourToPublished
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right equal
    apply Fin.ext
    revert left right
    decide

/-- Every identity of published monoid `A` preserves each variable's
multiplicity after capping at three. -/
theorem valid_cappedCount_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy publishedTable.semigroup) :
    forall letter,
      min (identity.lhs.toList.count letter) 3 =
        min (identity.rhs.toList.count letter) 3 :=
  exponentFourValid_capped_count_eq identity <|
    exponentFourEmbedding.pullback_identity identity valid

end SemigroupBasis.CoRoots.Order6LeeLiProposition8A
