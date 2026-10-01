import SemigroupBasis.Generated.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.Common

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock

open SemigroupBasis

namespace S6_2881

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (0 : Fin 6) else (1 : Fin 6) else if left = 2 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (2 : Fin 6) else (2 : Fin 6) else if left = 3 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (2 : Fin 6) else (2 : Fin 6) else if left = 4 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (1 : Fin 6) else (4 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "e8ba7cdd656378dc943aea076167c46752e1a7498d5c9a638385fbf1b5eeca0d"

def proofRoute : String := "order6-factor-intersection-period-two-from-three-multiple-block-v1"

def leftFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (0 : Fin 5) else if value = 2 then (2 : Fin 5) else if value = 3 then (3 : Fin 5) else if value = 4 then (1 : Fin 5) else (4 : Fin 5)

def leftFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (4 : Fin 6) else if value = 2 then (2 : Fin 6) else if value = 3 then (3 : Fin 6) else (5 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_134.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (1 : Fin 5) else if value = 2 then (2 : Fin 5) else if value = 3 then (2 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def rightFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (2 : Fin 6) else if value = 3 then (4 : Fin 6) else (5 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_223.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S5_134.table.semigroup SemigroupBasis.Generated.Catalogue.S5_223.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.representativeBasis

theorem representative_basis :
    BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.Common.s5_134_s5_223_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_2881

namespace S6_2894

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (1 : Fin 6) else if left = 2 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (2 : Fin 6) else if left = 3 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (2 : Fin 6) else if left = 4 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (1 : Fin 6) else (4 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "31ad9295cf3c50563d9d25308a23fb003a4e5eb0b2eedbf9c2a55ff952c4001b"

def proofRoute : String := "order6-factor-intersection-period-two-from-three-multiple-block-v1"

def leftFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (0 : Fin 5) else if value = 2 then (1 : Fin 5) else if value = 3 then (2 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def leftFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else if value = 2 then (3 : Fin 6) else if value = 3 then (4 : Fin 6) else (5 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_143.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (1 : Fin 5) else if value = 2 then (2 : Fin 5) else if value = 3 then (2 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def rightFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (2 : Fin 6) else if value = 3 then (4 : Fin 6) else (5 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_226.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S5_143.table.semigroup SemigroupBasis.Generated.Catalogue.S5_226.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.representativeBasis

theorem representative_basis :
    BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.Common.s5_143_s5_226_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_2894

namespace S6_5305

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (1 : Fin 6) else if left = 2 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (2 : Fin 6) else if left = 3 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (1 : Fin 6) else (3 : Fin 6) else if left = 4 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (1 : Fin 6) else (3 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "581e050c928f86b9782ee39800f06a4e3872cf0f953d46bba0f60617dda8cdf3"

def proofRoute : String := "order6-factor-intersection-period-two-from-three-multiple-block-v1"

def leftFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (0 : Fin 5) else if value = 2 then (3 : Fin 5) else if value = 3 then (1 : Fin 5) else if value = 4 then (2 : Fin 5) else (4 : Fin 5)

def leftFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (3 : Fin 6) else if value = 2 then (4 : Fin 6) else if value = 3 then (2 : Fin 6) else (5 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_123.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (1 : Fin 5) else if value = 2 then (2 : Fin 5) else if value = 3 then (3 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def rightFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (2 : Fin 6) else if value = 3 then (3 : Fin 6) else (5 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_223.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S5_123.table.semigroup SemigroupBasis.Generated.Catalogue.S5_223.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.representativeBasis

theorem representative_basis :
    BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.Common.s5_123_s5_223_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5305

namespace S6_5319

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (2 : Fin 6) else (1 : Fin 6) else if left = 2 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (2 : Fin 6) else if left = 3 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (1 : Fin 6) else (3 : Fin 6) else if left = 4 then if right = 0 then (2 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (1 : Fin 6) else (3 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "36d23c624314baa7499d5f41388dce488f6f16350cdaaff20d46e505dd9c86ff"

def proofRoute : String := "order6-factor-intersection-period-two-from-three-multiple-block-v1"

def leftFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (0 : Fin 5) else if value = 2 then (1 : Fin 5) else if value = 3 then (2 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def leftFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else if value = 2 then (3 : Fin 6) else if value = 3 then (4 : Fin 6) else (5 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_145.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (1 : Fin 5) else if value = 2 then (2 : Fin 5) else if value = 3 then (3 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def rightFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (2 : Fin 6) else if value = 3 then (3 : Fin 6) else (5 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_226.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S5_145.table.semigroup SemigroupBasis.Generated.Catalogue.S5_226.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.representativeBasis

theorem representative_basis :
    BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.Common.s5_145_s5_226_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5319

end SemigroupBasis.Generated.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock
