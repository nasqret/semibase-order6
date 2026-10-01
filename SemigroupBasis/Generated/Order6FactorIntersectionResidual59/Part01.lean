import SemigroupBasis.Generated.Order6FactorIntersectionResidual59.Common

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorIntersectionResidual59

open SemigroupBasis

namespace S6_5322

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (5 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (5 : Fin 6) else if left = 2 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (5 : Fin 6) else if left = 3 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (0 : Fin 6) else (5 : Fin 6) else if left = 4 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (1 : Fin 6) else (5 : Fin 6) else if right = 0 then (5 : Fin 6) else if right = 1 then (5 : Fin 6) else if right = 2 then (5 : Fin 6) else if right = 3 then (5 : Fin 6) else if right = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "24b3eb28ee9fe5f91da18e4830e28fd7ada6d709b19ef83599c878c9ad5c96f7"

def proofRoute : String := "coordinatewise-common-basis"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (1 : Fin 3) else if value = 3 then (1 : Fin 3) else if value = 4 then (1 : Fin 3) else (2 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else (5 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_11.table.semigroup where
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

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_11.table.semigroup SemigroupBasis.Generated.S4_35.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorIntersectionResidual59.Common.positiveParityS3_11S4_35IntersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5322

namespace S6_5490

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 2 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (2 : Fin 6) else if left = 3 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 4 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "2c9119a142bfb8ef7688d5e371ac1641509f190cb2a47c0d02c4c6b53d4bea31"

def proofRoute : String := "opposite-intersection-retarget"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (1 : Fin 3) else if value = 3 then (0 : Fin 3) else if value = 4 then (2 : Fin 3) else (2 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else (4 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_10.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 4 :=
  if value = 0 then (0 : Fin 4) else if value = 1 then (1 : Fin 4) else if value = 2 then (0 : Fin 4) else if value = 3 then (3 : Fin 4) else if value = 4 then (0 : Fin 4) else (2 : Fin 4)

def rightFactorSection (value : Fin 4) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (5 : Fin 6) else (3 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_10.table.semigroup SemigroupBasis.Generated.S4_9.table.semigroup.opposite where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorIntersectionResidual59.Common.positiveParityS3_10S4_9OppositeIntersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5490

namespace S6_5875

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6) else if left = 2 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6) else if left = 3 then if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6) else if left = 4 then if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6) else if right = 0 then (3 : Fin 6) else if right = 1 then (4 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "cff2e361d6cc24b200a83770a700533401a7dcd2033fe8a433f620288901bdae"

def proofRoute : String := "coordinatewise-common-basis"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (1 : Fin 3) else if value = 3 then (2 : Fin 3) else if value = 4 then (2 : Fin 3) else (2 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else (3 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_11.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 4 :=
  if value = 0 then (0 : Fin 4) else if value = 1 then (2 : Fin 4) else if value = 2 then (0 : Fin 4) else if value = 3 then (0 : Fin 4) else if value = 4 then (1 : Fin 4) else (3 : Fin 4)

def rightFactorSection (value : Fin 4) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (4 : Fin 6) else if value = 2 then (1 : Fin 6) else (5 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_11.table.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorIntersectionResidual59.Common.positiveParityS3_11S4_9IntersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5875

namespace S6_5882

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (1 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6) else if left = 1 then if right = 0 then (1 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6) else if left = 2 then if right = 0 then (1 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6) else if left = 3 then if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6) else if left = 4 then if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6) else if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (4 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "b462ad188cc66d160f3b49ec5625bfec5cd837335ae792c7a645e34ebc3300a4"

def proofRoute : String := "coordinatewise-common-basis"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else if value = 2 then (1 : Fin 3) else if value = 3 then (2 : Fin 3) else if value = 4 then (2 : Fin 3) else (2 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else (3 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_11.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 4 :=
  if value = 0 then (0 : Fin 4) else if value = 1 then (0 : Fin 4) else if value = 2 then (2 : Fin 4) else if value = 3 then (0 : Fin 4) else if value = 4 then (1 : Fin 4) else (3 : Fin 4)

def rightFactorSection (value : Fin 4) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (4 : Fin 6) else if value = 2 then (2 : Fin 6) else (5 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_11.table.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorIntersectionResidual59.Common.positiveParityS3_11S4_9IntersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5882

end SemigroupBasis.Generated.Order6FactorIntersectionResidual59
