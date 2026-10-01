import SemigroupBasis.CoRoots.Order6PublishedMonoid14Normalization
import SemigroupBasis.CoRoots.S5_345Factors
import SemigroupBasis.Generated.S3_8
import SemigroupBasis.Generated.S3_16

set_option maxRecDepth 100000

namespace SemigroupBasis.CoRoots.Order6PublishedMonoid14.S6_8496

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6PublishedMonoid14

private def row6
    (c0 c1 c2 c3 c4 c5 column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact catalogue table for Lee--Li's monoid I:
`[[1,1,1,1,1,1],[1,1,1,1,2,3],[1,1,1,3,3,3],
  [1,2,3,4,4,4],[1,2,3,4,5,6],[1,2,3,6,6,6]]`. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 1 2 right else
      if left = 2 then row6 0 0 0 2 2 2 right else
        if left = 3 then row6 0 1 2 3 3 3 right else
          if left = 4 then row6 0 1 2 3 4 5 right else
            row6 0 1 2 5 5 5 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "017c491c13ca9a18432ac9c13f8309b3ed16f41a3ab4b6295f902a050d647adb"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1], [1, 1, 1, 1, 2, 3],
        [1, 1, 1, 3, 3, 3], [1, 2, 3, 4, 4, 4],
        [1, 2, 3, 4, 5, 6], [1, 2, 3, 6, 6, 6]] := by
  decide

theorem identityElement_certificate :
    (∀ value : Fin 6, mul 4 value = value) ∧
      (∀ value : Fin 6, mul value 4 = value) := by
  decide

set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  modelsOfFiniteChecks table (by decide)

theorem oppositeModels :
    Models table.semigroup.opposite oppositeBasis :=
  models.oppositeReversed

/-! ## Published lower-order detectors -/

/-- The literal submonoid on one-based elements `[1,2,5]` is `N₂¹`. -/
def n_2_1Embedding :
    Embedding Generated.S3_8.table.semigroup table.semigroup where
  toFun := fun value : Fin 3 =>
    if value = 0 then (0 : Fin 6)
    else if value = 1 then (1 : Fin 6)
    else (4 : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem valid_n_2_1
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy Generated.S3_8.table.semigroup :=
  n_2_1Embedding.pullback_identity identity valid

/-- Every identity of monoid I preserves absent/simple/multiple status. -/
theorem valid_cappedMultiplicity_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    ∀ letter,
      S5_107.cappedMultiplicity identity.lhs letter =
        S5_107.cappedMultiplicity identity.rhs letter := by
  have factorValid := valid_n_2_1 identity valid
  rw [Generated.S3_8.table_eq_catalogue_model] at factorValid
  intro letter
  simpa [S5_107.cappedMultiplicity, Nat.min_comm] using
    SemigroupBasis.Examples.exponentValid_capped_count_eq
      identity factorValid letter

/-- The literal submonoid on one-based elements `[4,5,6]` is `L₂¹`. -/
def l_2_1Embedding :
    Embedding Generated.S3_16.table.semigroup table.semigroup where
  toFun := fun value : Fin 3 =>
    if value = 0 then (3 : Fin 6)
    else if value = 1 then (4 : Fin 6)
    else (5 : Fin 6)
  map_mul := by
    intro left right
    apply Fin.ext
    revert left right
    decide
  injective := by
    intro left right
    revert left right
    decide

theorem valid_l_2_1
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    identity.SatisfiedBy Generated.S3_16.table.semigroup :=
  l_2_1Embedding.pullback_identity identity valid

/-- Every identity of monoid I preserves the sequence of first occurrences. -/
theorem valid_firstOccurrenceSequence_eq
    (identity : Identity Nat)
    (valid : identity.SatisfiedBy table.semigroup) :
    SemigroupBasis.Examples.firstOccurrenceSequence identity.lhs.toList =
      SemigroupBasis.Examples.firstOccurrenceSequence identity.rhs.toList := by
  have factorValid := valid_l_2_1 identity valid
  rw [Generated.S3_16.table_eq_catalogue_model] at factorValid
  exact
    S5_345Factors.leftRegularBandThreeValid_firstOccurrenceSequence_eq
      identity factorValid

end SemigroupBasis.CoRoots.Order6PublishedMonoid14.S6_8496
