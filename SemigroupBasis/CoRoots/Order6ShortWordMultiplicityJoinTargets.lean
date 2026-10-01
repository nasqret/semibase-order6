import SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin

/-!
# Order-six short-word/multiplicity join targets

This module instantiates the unrestricted normal-form theorem for the exact
catalogue representatives `S6_2612` and `S6_5158`.  Each table is exhibited as
a subdirect product of the capped-multiplicity factor `S3_8` and the appropriate
three-nilpotent short-word factor.
-/

namespace SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin

open SemigroupBasis

private def toFinThree : Nat → Fin 3
  | 0 => 0
  | 1 => 1
  | _ => 2

private def valuesOneBased {n m : Nat} (map : Fin n → Fin m) : List Nat :=
  List.ofFn fun value => (map value).val + 1

namespace S6_2612

/-- Exact zero-based multiplication for catalogue representative `S6_2612`.
Its one-based table has SHA-256
`638d145917b711270364177f38c1a4a1e08b07648737131c6dbb903ab380088b`.
-/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 3, 5 => 3
  | 4, 2 => 1
  | 4, 4 => 1
  | 5, 3 => 3
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "638d145917b711270364177f38c1a4a1e08b07648737131c6dbb903ab380088b"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 3],
   [0, 0, 1, 0, 1, 0],
   [0, 0, 0, 3, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
        publishedRows := by
  decide

/- Direct finite verification that the exact target table satisfies all six
displayed laws. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

def multiplicityMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 3 => 1
  | 5 => 2
  | _ => 0

def multiplicitySection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => 0
  | 1 => 3
  | _ => 5

def ontoMultiplicity :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_8.table.semigroup where
  toFun := multiplicityMap
  map_mul := by decide
  preimage := multiplicitySection
  right_inverse := by decide

def shortWordMap (value : Fin 6) : Fin 4 :=
  match value.val with
  | 1 => 1
  | 2 => 2
  | 4 => 3
  | _ => 0

def shortWordSection (value : Fin 4) : Fin 6 :=
  match value.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 4

def ontoShortWord :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := shortWordMap
  map_mul := by decide
  preimage := shortWordSection
  right_inverse := by decide

def multiplicityMapValuesOneBased := valuesOneBased multiplicityMap
def shortWordMapValuesOneBased := valuesOneBased shortWordMap
def multiplicitySectionValuesOneBased := valuesOneBased multiplicitySection
def shortWordSectionValuesOneBased := valuesOneBased shortWordSection

theorem mapValuesOneBased_certificate :
    multiplicityMapValuesOneBased = [1, 1, 1, 2, 1, 3] ∧
    shortWordMapValuesOneBased = [1, 2, 3, 1, 4, 1] ∧
    multiplicitySectionValuesOneBased = [1, 4, 6] ∧
    shortWordSectionValuesOneBased = [1, 2, 3, 5] := by
  decide

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.S4_9.table.semigroup where
  left := ontoMultiplicity
  right := ontoShortWord
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

/-- Unconditional complete basis theorem for the exact `S6_2612` catalogue
table. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor subdirectPair

/-- The explicitly recorded opposite orientation of the catalogue result. -/
theorem recorded_opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_2612

namespace S6_5158

/-- Exact zero-based multiplication for catalogue representative `S6_5158`.
Its one-based table has SHA-256
`686180291863cd88a487cf1325b3d7b2bb59c6d8d1ce2f4b28c6d19a62394354`.
-/
def mul (left right : Fin 6) : Fin 6 :=
  match left.val, right.val with
  | 2, 5 => 2
  | 3, 3 => 1
  | 4, 3 => 1
  | 4, 4 => 1
  | 5, 2 => 2
  | 5, 5 => 5
  | _, _ => 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "686180291863cd88a487cf1325b3d7b2bb59c6d8d1ce2f4b28c6d19a62394354"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 0],
   [0, 0, 0, 0, 0, 2],
   [0, 0, 0, 1, 0, 0],
   [0, 0, 0, 1, 1, 0],
   [0, 0, 2, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
        publishedRows := by
  decide

/- Direct finite verification that the exact target table satisfies all six
displayed laws. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem models : Models table.semigroup basis :=
  FiniteCertificate.checkModels_sound table basis toFinThree (by decide)

def multiplicityMap (value : Fin 6) : Fin 3 :=
  match value.val with
  | 2 => 1
  | 5 => 2
  | _ => 0

def multiplicitySection (value : Fin 3) : Fin 6 :=
  match value.val with
  | 0 => 0
  | 1 => 2
  | _ => 5

def ontoMultiplicity :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_8.table.semigroup where
  toFun := multiplicityMap
  map_mul := by decide
  preimage := multiplicitySection
  right_inverse := by decide

def shortWordMap (value : Fin 6) : Fin 4 :=
  match value.val with
  | 1 => 1
  | 3 => 2
  | 4 => 3
  | _ => 0

def shortWordSection (value : Fin 4) : Fin 6 :=
  match value.val with
  | 0 => 0
  | 1 => 1
  | 2 => 3
  | _ => 4

def ontoShortWord :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S4_35.table.semigroup where
  toFun := shortWordMap
  map_mul := by decide
  preimage := shortWordSection
  right_inverse := by decide

def multiplicityMapValuesOneBased := valuesOneBased multiplicityMap
def shortWordMapValuesOneBased := valuesOneBased shortWordMap
def multiplicitySectionValuesOneBased := valuesOneBased multiplicitySection
def shortWordSectionValuesOneBased := valuesOneBased shortWordSection

theorem mapValuesOneBased_certificate :
    multiplicityMapValuesOneBased = [1, 1, 2, 1, 1, 3] ∧
    shortWordMapValuesOneBased = [1, 2, 1, 3, 4, 1] ∧
    multiplicitySectionValuesOneBased = [1, 3, 6] ∧
    shortWordSectionValuesOneBased = [1, 2, 4, 5] := by
  decide

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_8.table.semigroup
      SemigroupBasis.Generated.S4_35.table.semigroup where
  left := ontoMultiplicity
  right := ontoShortWord
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

/-- Unconditional complete basis theorem for the exact `S6_5158` catalogue
table. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  intersectionBasisS4_35.basisFor subdirectPair

/-- The explicitly recorded opposite orientation of the catalogue result. -/
theorem recorded_opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5158

end SemigroupBasis.CoRoots.Order6ShortWordMultiplicityJoin
