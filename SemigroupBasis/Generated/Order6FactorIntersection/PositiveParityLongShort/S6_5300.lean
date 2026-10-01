import SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort

namespace SemigroupBasis.Generated.Order6FactorIntersection.PositiveParityLongShort.S6_5300

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort

def mul (left right : Fin 6) : Fin 6 :=
  if left = 2 then
    if right = 2 then 0 else 2
  else if left = 3 ∧ right = 3 then 1
  else if left = 4 ∧ (right = 3 ∨ right = 4) then 1
  else if left = 5 ∧ right = 5 then 5
  else if right = 2 then 2
  else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 3, 1, 1, 1],
       [1, 1, 3, 1, 1, 1],
       [3, 3, 1, 3, 3, 3],
       [1, 1, 3, 2, 1, 1],
       [1, 1, 3, 2, 2, 1],
       [1, 1, 3, 1, 1, 6]] := by
  decide

def tableSHA256 : String :=
  "d4832e7b788173743b0c0b9d704f86e6462027a08f34a4d9edf64ebe34a085ab"

def componentSHA256 : String :=
  "6370baad5e8c11929d859ea110b980c11a01b09aab81522d516ae28639b4e49e"

def stateFactorID : String := "S3_10"
def shortFactorID : String := "S4_35"
def basisOrientation : String := "direct"
def memberCount : Nat := 2

def stateMap (value : Fin 6) : Fin 3 :=
  if value = 2 then 1 else if value = 5 then 2 else 0

def stateMapValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 6 => (stateMap value).val + 1

theorem stateMapValuesOneBased_certificate :
    stateMapValuesOneBased = [1, 1, 2, 1, 1, 3] := by
  decide

def stateSection (value : Fin 3) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then 2 else 5

def stateSectionValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 3 => (stateSection value).val + 1

theorem stateSectionValuesOneBased_certificate :
    stateSectionValuesOneBased = [1, 3, 6] := by
  decide

def stateQuotient : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S3_10.table.semigroup where
  toFun := stateMap
  map_mul := by decide
  preimage := stateSection
  right_inverse := by decide

def shortMap (value : Fin 6) : Fin 4 :=
  if value = 1 then 1
  else if value = 3 then 2
  else if value = 4 then 3
  else 0

def shortMapValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 6 => (shortMap value).val + 1

theorem shortMapValuesOneBased_certificate :
    shortMapValuesOneBased = [1, 2, 1, 3, 4, 1] := by
  decide

def shortSection (value : Fin 4) : Fin 6 :=
  if value = 0 then 0
  else if value = 1 then 1
  else if value = 2 then 3
  else 4

def shortSectionValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 4 => (shortSection value).val + 1

theorem shortSectionValuesOneBased_certificate :
    shortSectionValuesOneBased = [1, 2, 4, 5] := by
  decide

def shortQuotient : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S4_35.table.semigroup where
  toFun := shortMap
  map_mul := by decide
  preimage := shortSection
  right_inverse := by decide

def coordinateSignaturesOneBased : List (Nat × Nat) :=
  List.ofFn fun value : Fin 6 =>
    ((stateMap value).val + 1, (shortMap value).val + 1)

theorem coordinateSignaturesOneBased_certificate :
    coordinateSignaturesOneBased =
      [(1, 1), (1, 2), (2, 1), (1, 3), (1, 4), (3, 1)] := by
  decide

def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.S3_10.table.semigroup
    SemigroupBasis.Generated.S4_35.table.semigroup where
  left := stateQuotient
  right := shortQuotient
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis :
    BasisFor table.semigroup basis :=
  s3_10_s4_35_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6FactorIntersection.PositiveParityLongShort.S6_5300
