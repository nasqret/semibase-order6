import SemigroupBasis.CoRoots.Order6FactorIntersectionFinalMarkerShortLong
import SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorIntersectionIdentification

open SemigroupBasis

namespace S6_2887

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (0 : Fin 6) else if left = 2 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (2 : Fin 6) else if left = 3 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (2 : Fin 6) else if left = 4 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (1 : Fin 6) else (2 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "a5cf01812c008dc00c53a1446f10d27d9b67df5748ab3f343183e964140aaaa6"

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

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_10.table.semigroup SemigroupBasis.Generated.S4_9.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionPositiveParityLongShort.s3_10_s4_9_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_2887

namespace S6_2909

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 3 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 4 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (1 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "d95cda8e50fb08f6ef50c9e7e4e1c7fcf33c23c89ad3cba5eb3bdf8840e88b0e"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (0 : Fin 3) else if value = 3 then (1 : Fin 3) else if value = 4 then (2 : Fin 3) else (2 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (3 : Fin 6) else (4 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 4 :=
  if value = 0 then (0 : Fin 4) else if value = 1 then (1 : Fin 4) else if value = 2 then (2 : Fin 4) else if value = 3 then (0 : Fin 4) else if value = 4 then (0 : Fin 4) else (3 : Fin 4)

def rightFactorSection (value : Fin 4) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (2 : Fin 6) else (5 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_2.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup SemigroupBasis.Generated.S4_2.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionFinalMarkerShortLong.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionFinalMarkerShortLong.s3_6_s4_2_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_2909

namespace S6_2930

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 3 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (1 : Fin 6) else if left = 4 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "b612089a45e85fc0c4b13b5e91d386aa61e52f519b528761447b4fb1b2b34b67"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (1 : Fin 3) else if value = 3 then (0 : Fin 3) else if value = 4 then (2 : Fin 3) else (2 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else (4 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup where
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

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_2.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup SemigroupBasis.Generated.S4_2.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionFinalMarkerShortLong.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionFinalMarkerShortLong.s3_6_s4_2_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_2930

namespace S6_2931

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 3 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (1 : Fin 6) else if left = 4 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "067a5b933fdb0b68e28ccb7d6aa8403b705a8d228840e8081717dab313f95a96"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (1 : Fin 3) else if value = 3 then (0 : Fin 3) else if value = 4 then (2 : Fin 3) else (2 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else (4 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 4 :=
  if value = 0 then (0 : Fin 4) else if value = 1 then (1 : Fin 4) else if value = 2 then (0 : Fin 4) else if value = 3 then (2 : Fin 4) else if value = 4 then (0 : Fin 4) else (3 : Fin 4)

def rightFactorSection (value : Fin 4) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (3 : Fin 6) else (5 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_3.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup SemigroupBasis.Generated.S4_3.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionFinalMarkerShortLong.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionFinalMarkerShortLong.s3_6_s4_3_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_2931

namespace S6_2932

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 3 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (1 : Fin 6) else if left = 4 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "3c86550c615f275feedb78b9d1a1c80ce31c52a771e204a9e10162a2b76ce154"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (1 : Fin 3) else if value = 3 then (1 : Fin 3) else if value = 4 then (2 : Fin 3) else (2 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else (4 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup where
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

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S4_2.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup SemigroupBasis.Generated.S4_2.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionFinalMarkerShortLong.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionFinalMarkerShortLong.s3_6_s4_2_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_2932

end SemigroupBasis.Generated.Order6FactorIntersectionIdentification
