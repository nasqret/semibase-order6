import SemigroupBasis.CoRoots.Order6FactorIntersectionFirstSequenceShortLong
import SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort
import SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorIntersectionIdentification

open SemigroupBasis

namespace S6_5314

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (0 : Fin 6) else if left = 2 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (2 : Fin 6) else if left = 3 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (0 : Fin 6) else (2 : Fin 6) else if left = 4 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (1 : Fin 6) else (2 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "44390da7c2008d94c668bbd7eab702699aafd715c04320d43d6bfe12c604c100"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (1 : Fin 3) else if value = 3 then (1 : Fin 3) else if value = 4 then (1 : Fin 3) else (2 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else (5 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_10.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 4 :=
  if value = 0 then (0 : Fin 4) else if value = 1 then (1 : Fin 4) else if value = 2 then (0 : Fin 4) else if value = 3 then (2 : Fin 4) else if value = 4 then (3 : Fin 4) else (0 : Fin 4)

def rightFactorSection (value : Fin 4) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (3 : Fin 6) else (4 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_35.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_10.table.semigroup SemigroupBasis.Generated.S4_35.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.s3_10_s4_35_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5314

namespace S6_5329

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (1 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (1 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (4 : Fin 6) else if right = 4 then (3 : Fin 6) else (1 : Fin 6) else if left = 2 then if right = 0 then (1 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (4 : Fin 6) else if right = 4 then (3 : Fin 6) else (1 : Fin 6) else if left = 3 then if right = 0 then (3 : Fin 6) else if right = 1 then (4 : Fin 6) else if right = 2 then (4 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (0 : Fin 6) else (3 : Fin 6) else if left = 4 then if right = 0 then (4 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (1 : Fin 6) else (4 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "192234d4d466dcb3ea1d4215cdebd8b0474e8ff252cddc183f2045bf09d1de7d"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (1 : Fin 3) else if value = 3 then (0 : Fin 3) else if value = 4 then (0 : Fin 3) else (2 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else (5 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Examples.finalMarkerThree.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (1 : Fin 5) else if value = 2 then (1 : Fin 5) else if value = 3 then (2 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def rightFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (3 : Fin 6) else if value = 3 then (4 : Fin 6) else (5 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_505Family.S5_505.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Examples.finalMarkerThree.semigroup SemigroupBasis.CoRoots.S5_505Family.S5_505.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.PrefixResidueFour.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.PrefixResidueFour.intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5329

namespace S6_5921

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 3 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (5 : Fin 6) else if left = 4 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (1 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (5 : Fin 6) else if right = 0 then (5 : Fin 6) else if right = 1 then (5 : Fin 6) else if right = 2 then (5 : Fin 6) else if right = 3 then (5 : Fin 6) else if right = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "d1b7d6c0f8afc41c973d699e5d58919b8a741041bf7591091887fb56d88f94cf"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (0 : Fin 3) else if value = 3 then (1 : Fin 3) else if value = 4 then (1 : Fin 3) else (2 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (3 : Fin 6) else (5 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 4 :=
  if value = 0 then (0 : Fin 4) else if value = 1 then (1 : Fin 4) else if value = 2 then (2 : Fin 4) else if value = 3 then (0 : Fin 4) else if value = 4 then (3 : Fin 4) else (0 : Fin 4)

def rightFactorSection (value : Fin 4) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (2 : Fin 6) else (4 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_2.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.Generated.S4_2.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionFirstSequenceShortLong.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionFirstSequenceShortLong.s3_16_s4_2_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5921

namespace S6_6161

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (1 : Fin 6) else (0 : Fin 6) else if left = 3 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (5 : Fin 6) else if left = 4 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (5 : Fin 6) else if right = 0 then (5 : Fin 6) else if right = 1 then (5 : Fin 6) else if right = 2 then (5 : Fin 6) else if right = 3 then (5 : Fin 6) else if right = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "b836a561f95bc73ba9d180711060638de05004dc9a4c789d04971317f8dc2e7d"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (0 : Fin 3) else if value = 3 then (1 : Fin 3) else if value = 4 then (1 : Fin 3) else (2 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (3 : Fin 6) else (5 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 4 :=
  if value = 0 then (0 : Fin 4) else if value = 1 then (1 : Fin 4) else if value = 2 then (3 : Fin 4) else if value = 3 then (0 : Fin 4) else if value = 4 then (2 : Fin 4) else (0 : Fin 4)

def rightFactorSection (value : Fin 4) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (4 : Fin 6) else (2 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_2.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.Generated.S4_2.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionFirstSequenceShortLong.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionFirstSequenceShortLong.s3_16_s4_2_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_6161

namespace S6_6163

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (1 : Fin 6) else (0 : Fin 6) else if left = 3 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (5 : Fin 6) else if left = 4 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (1 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (5 : Fin 6) else if right = 0 then (5 : Fin 6) else if right = 1 then (5 : Fin 6) else if right = 2 then (5 : Fin 6) else if right = 3 then (5 : Fin 6) else if right = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "27f60396b44b5f8cbd3cb1eca69ede5adf70bcd3a6245cd6861ad4853c953da7"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (0 : Fin 3) else if value = 3 then (1 : Fin 3) else if value = 4 then (1 : Fin 3) else (2 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (3 : Fin 6) else (5 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 4 :=
  if value = 0 then (0 : Fin 4) else if value = 1 then (1 : Fin 4) else if value = 2 then (2 : Fin 4) else if value = 3 then (0 : Fin 4) else if value = 4 then (3 : Fin 4) else (0 : Fin 4)

def rightFactorSection (value : Fin 4) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (2 : Fin 6) else (4 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_3.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.Generated.S4_3.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionFirstSequenceShortLong.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionFirstSequenceShortLong.s3_16_s4_3_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_6163

end SemigroupBasis.Generated.Order6FactorIntersectionIdentification
