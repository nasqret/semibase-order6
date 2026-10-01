import SemigroupBasis.CoRoots.Order6Head3Tail2

namespace SemigroupBasis.Generated.Order6FactorIntersection.Head3Tail2.S6_5640

open SemigroupBasis
open SemigroupBasis.CoRoots.Order6Head3Tail2

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then 0 else
    if left = 1 then
      if right = 5 then 1 else 0
    else if left = 2 then
      if right = 5 then 2 else 0
    else if left = 3 then
      if right = 2 then 1 else
        if right = 3 then 1 else
          if right = 5 then 3 else 0
    else if left = 4 then 4
    else if right = 2 then 2 else
      if right = 3 then 2 else
        if right = 5 then 5 else 0

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "9d3b1534d48eff92b44e8991e20f3fe9e4546cab7940ae77f4ee0717bfce7215"

def componentSHA256 : String :=
  "092b7ffe1e570ad354db09348ae363e7a25f2ef04e492138f523fe8a90853601"

def contentFactorID : String := "S3_13"
def multiplicityFactorID : String := "S5_207"
def multiplicityFactorOrientation : String := "opposite"
def basisOrientation : String := "direct"

def contentMap (value : Fin 6) : Fin 3 :=
  if value = 0 then 0 else
    if value = 1 then 0 else
      if value = 2 then 0 else
        if value = 3 then 0 else
          if value = 4 then 2 else 1

def contentMapValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 6 => (contentMap value).val + 1

theorem contentMapValuesOneBased_certificate :
    contentMapValuesOneBased = [1, 1, 1, 1, 3, 2] := by
  decide

def contentPreimage (value : Fin 3) : Fin 6 :=
  if value = 0 then 0 else if value = 1 then 5 else 4

def contentPreimageValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 3 => (contentPreimage value).val + 1

theorem contentPreimageValuesOneBased_certificate :
    contentPreimageValuesOneBased = [1, 6, 5] := by
  decide

def contentQuotient :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S3_13.table.semigroup where
  toFun := contentMap
  map_mul := by decide
  preimage := contentPreimage
  right_inverse := by decide

def multiplicityMap (value : Fin 6) : Fin 5 :=
  if value = 0 then 0 else
    if value = 1 then 1 else
      if value = 2 then 2 else
        if value = 3 then 3 else
          if value = 4 then 0 else 4

def multiplicityMapValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 6 => (multiplicityMap value).val + 1

theorem multiplicityMapValuesOneBased_certificate :
    multiplicityMapValuesOneBased = [1, 2, 3, 4, 1, 5] := by
  decide

def multiplicityPreimage (value : Fin 5) : Fin 6 :=
  if value = 0 then 0 else
    if value = 1 then 1 else
      if value = 2 then 2 else
        if value = 3 then 3 else 5

def multiplicityPreimageValuesOneBased : List Nat :=
  List.ofFn fun value : Fin 5 =>
    (multiplicityPreimage value).val + 1

theorem multiplicityPreimageValuesOneBased_certificate :
    multiplicityPreimageValuesOneBased = [1, 2, 3, 4, 6] := by
  decide

def multiplicityQuotient :
    SplitSurjection table.semigroup
      SemigroupBasis.CoRoots.S5_207.table.semigroup.opposite where
  toFun := multiplicityMap
  map_mul := by decide
  preimage := multiplicityPreimage
  right_inverse := by decide

def coordinateSignaturesOneBased : List (Nat × Nat) :=
  List.ofFn fun value : Fin 6 =>
    ((contentMap value).val + 1, (multiplicityMap value).val + 1)

theorem coordinateSignaturesOneBased_certificate :
    coordinateSignaturesOneBased =
      [(1, 1), (1, 2), (1, 3), (1, 4), (3, 1), (2, 5)] := by
  decide

def subdirectPair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S3_13.table.semigroup
      SemigroupBasis.CoRoots.S5_207.table.semigroup.opposite where
  left := contentQuotient
  right := multiplicityQuotient
  jointlyInjective := by
    intro left right equality
    revert left right
    decide

theorem representative_basis : BasisFor table.semigroup basis :=
  intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6FactorIntersection.Head3Tail2.S6_5640
