import SemigroupBasis.Generated.Order6FactorIntersectionResidual59.Common

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorIntersectionResidual59

open SemigroupBasis

namespace S6_2865

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (0 : Fin 6) else (5 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (0 : Fin 6) else (5 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (0 : Fin 6) else (5 : Fin 6) else if left = 3 then if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (3 : Fin 6) else (5 : Fin 6) else if left = 4 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (1 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (1 : Fin 6) else (5 : Fin 6) else if right = 0 then (5 : Fin 6) else if right = 1 then (5 : Fin 6) else if right = 2 then (5 : Fin 6) else if right = 3 then (5 : Fin 6) else if right = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "2331e7c62fb293892e60c8ec00f7766388a44dc41a3dacc5f34aaee3d027168a"

def proofRoute : String := "coordinatewise-common-basis"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (0 : Fin 3) else if value = 3 then (1 : Fin 3) else if value = 4 then (0 : Fin 3) else (2 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (3 : Fin 6) else (5 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_11.table.semigroup where
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

end S6_2865

namespace S6_2901

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (5 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (5 : Fin 6) else if left = 2 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (5 : Fin 6) else if left = 3 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (5 : Fin 6) else if left = 4 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (1 : Fin 6) else (5 : Fin 6) else if right = 0 then (5 : Fin 6) else if right = 1 then (5 : Fin 6) else if right = 2 then (5 : Fin 6) else if right = 3 then (5 : Fin 6) else if right = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "5909a3b16d13b2f49ac001f90a2c04bcc4e1d50ebaeb90a9050f63a72e21df7b"

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

end S6_2901

namespace S6_2917

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 3 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 4 then if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (1 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (1 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "549afb9ea039a7748ac30e85168267e90aa64a33dc8e20e2f88b38db23f21ef6"

def proofRoute : String := "exact-embedding-then-theory-transport"

def leftFactorMap (value : Fin 6) : Fin 4 :=
  if value = 0 then (0 : Fin 4) else if value = 1 then (1 : Fin 4) else if value = 2 then (1 : Fin 4) else if value = 3 then (1 : Fin 4) else if value = 4 then (2 : Fin 4) else (3 : Fin 4)

def leftFactorSection (value : Fin 4) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (4 : Fin 6) else (5 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S4_44.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 4 :=
  if value = 0 then (0 : Fin 4) else if value = 1 then (0 : Fin 4) else if value = 2 then (1 : Fin 4) else if value = 3 then (2 : Fin 4) else if value = 4 then (0 : Fin 4) else (3 : Fin 4)

def rightFactorSection (value : Fin 4) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else if value = 2 then (3 : Fin 6) else (5 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_2.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S4_44.table.semigroup SemigroupBasis.Generated.S4_2.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionFinalMarkerShortLong.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorIntersectionResidual59.Common.finalMarkerS4_44S4_2IntersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_2917

namespace S6_5308

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (5 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (5 : Fin 6) else if left = 2 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (5 : Fin 6) else if left = 3 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (0 : Fin 6) else (5 : Fin 6) else if left = 4 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (1 : Fin 6) else (5 : Fin 6) else if right = 0 then (5 : Fin 6) else if right = 1 then (5 : Fin 6) else if right = 2 then (5 : Fin 6) else if right = 3 then (5 : Fin 6) else if right = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "d2fe48fddb2fc20fc1ac7d1478142b44d75529903ebd219dff7e9f93f3c2be07"

def proofRoute : String := "coordinatewise-common-basis"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (1 : Fin 3) else if value = 3 then (0 : Fin 3) else if value = 4 then (0 : Fin 3) else (2 : Fin 3)

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

end S6_5308

end SemigroupBasis.Generated.Order6FactorIntersectionResidual59
