import SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin

/-!
# Exact endpoint for S6_5421

The catalogue representative is subdirect over `S3_8^op` and `S4_9^op`.
Reversing the complete short-word/multiplicity intersection basis therefore
gives the recorded six-law basis for `S6_5421`.
-/

namespace SemigroupBasis.Order6.S6_5421

open SemigroupBasis

def targetBasis : List (Identity Nat) :=
  reversedBasis
    SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin.basis

/-- Exact zero-based multiplication for catalogue representative `S6_5421`. -/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 2, 4 => 2
  | 2, 5 => 2
  | 3, 3 => 1
  | 4, 2 => 2
  | 4, 4 => 4
  | 4, 5 => 4
  | 5, 2 => 2
  | 5, 3 => 1
  | 5, 4 => 4
  | 5, 5 => 4
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "582880c1f4ed530b7fcc201ce9aaa725f6a14f4af34fd9bf814407a5c64dc7a6"

def catalogueRowsOneBased : List (List Nat) :=
  [[1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1],
   [1, 1, 1, 1, 3, 3],
   [1, 1, 1, 2, 1, 1],
   [1, 1, 3, 1, 5, 5],
   [1, 1, 3, 2, 5, 5]]

/-- The hand-written finite table is exactly the committed Smallsemi row. -/
theorem table_matches_catalogue :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val + 1) =
        catalogueRowsOneBased := by
  decide

def multiplicityMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 2 => 1
  | 4 => 2
  | 5 => 2
  | _ => 0

def multiplicitySection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 1 => 2
  | 2 => 4
  | _ => 0

def ontoMultiplicity :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_8.table.semigroup.opposite where
  toFun := multiplicityMap
  map_mul := by decide
  preimage := multiplicitySection
  right_inverse := by decide

def shortWordMap (value : Fin 6) : Fin 4 :=
  match value.val with
  | 1 => 1
  | 3 => 3
  | 5 => 2
  | _ => 0

def shortWordSection (value : Fin 4) : Fin 6 :=
  match value.val with
  | 1 => 1
  | 2 => 5
  | 3 => 3
  | _ => 0

def ontoShortWord :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := shortWordMap
  map_mul := by decide
  preimage := shortWordSection
  right_inverse := by decide

private def valuesOneBased {n m : Nat} (map : Fin n -> Fin m) : List Nat :=
  List.ofFn fun value => (map value).val + 1

def multiplicityMapValuesOneBased := valuesOneBased multiplicityMap
def shortWordMapValuesOneBased := valuesOneBased shortWordMap
def multiplicitySectionValuesOneBased := valuesOneBased multiplicitySection
def shortWordSectionValuesOneBased := valuesOneBased shortWordSection

def multiplicityFactorId : String := "S3_8"
def multiplicityFactorOrientation : String := "opposite"
def shortWordFactorId : String := "S4_9"
def shortWordFactorOrientation : String := "opposite"

theorem factor_binding_certificate :
    multiplicityFactorId = "S3_8" /\
    multiplicityFactorOrientation = "opposite" /\
    shortWordFactorId = "S4_9" /\
    shortWordFactorOrientation = "opposite" /\
    multiplicityMapValuesOneBased = [1, 1, 2, 1, 3, 3] /\
    shortWordMapValuesOneBased = [1, 2, 1, 4, 1, 3] /\
    multiplicitySectionValuesOneBased = [1, 3, 5] /\
    shortWordSectionValuesOneBased = [1, 2, 6, 4] := by
  decide

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_8.table.semigroup.opposite
      SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  left := ontoMultiplicity
  right := ontoShortWord
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

private theorem oppositeIntersectionBasis :
    IntersectionBasis
      SemigroupBasis.Generated.S3_8.table.semigroup.opposite
      SemigroupBasis.Generated.S4_9.table.semigroup.opposite
      (reversedBasis
        SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin.basis) where
  leftModels :=
    SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin.s3_8_models.oppositeReversed
  rightModels :=
    SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin.s4_9_models.oppositeReversed
  complete := by
    intro identity multiplicityValid shortWordValid
    have multiplicityReversed :
        identity.reversed.SatisfiedBy
          SemigroupBasis.Generated.S3_8.table.semigroup :=
      (Identity.satisfiedBy_opposite_iff_reversed identity
        SemigroupBasis.Generated.S3_8.table.semigroup).mp multiplicityValid
    have shortWordReversed :
        identity.reversed.SatisfiedBy
          SemigroupBasis.Generated.S4_9.table.semigroup :=
      (Identity.satisfiedBy_opposite_iff_reversed identity
        SemigroupBasis.Generated.S4_9.table.semigroup).mp shortWordValid
    have derivation :=
      SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin.intersectionBasis.complete
        identity.reversed multiplicityReversed shortWordReversed
    have reversedDerivation := derivation.reverse
    cases identity
    simpa [Identity.reversed] using reversedDerivation

/-- Unconditional complete basis theorem for the exact `S6_5421` table. -/
theorem representative_basis : BasisFor table.semigroup targetBasis := by
  simpa [targetBasis] using
    oppositeIntersectionBasis.basisFor subdirectPair

end SemigroupBasis.Order6.S6_5421
