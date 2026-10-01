import SemigroupBasis.Generated.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.Common

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock

open SemigroupBasis

namespace S6_2856

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (0 : Fin 6) else (1 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 3 then if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6) else if left = 4 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (1 : Fin 6) else (4 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "c54f1884fc8bb63850dcc83eeb98ca3aec009bfd11b77bb14fe28c3696b7c2b1"

def proofRoute : String := "order6-factor-intersection-period-two-from-three-multiple-block-v1"

def leftFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (0 : Fin 5) else if value = 2 then (1 : Fin 5) else if value = 3 then (3 : Fin 5) else if value = 4 then (2 : Fin 5) else (4 : Fin 5)

def leftFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else if value = 2 then (4 : Fin 6) else if value = 3 then (3 : Fin 6) else (5 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S5_121.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (1 : Fin 5) else if value = 2 then (0 : Fin 5) else if value = 3 then (2 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def rightFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (3 : Fin 6) else if value = 3 then (4 : Fin 6) else (5 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_223.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup SemigroupBasis.Generated.S5_121.table.semigroup SemigroupBasis.Generated.Catalogue.S5_223.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.representativeBasis

theorem representative_basis :
    BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.Common.s5_121_s5_223_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_2856

namespace S6_2858

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (0 : Fin 6) else (1 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (0 : Fin 6) else (1 : Fin 6) else if left = 3 then if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6) else if left = 4 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (1 : Fin 6) else (4 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "a80cdb4c7b3f1a35afafbb2edeac1d77984e9713d387f080ebb10f062bf49e86"

def proofRoute : String := "order6-factor-intersection-period-two-from-three-multiple-block-v1"

def leftFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (0 : Fin 5) else if value = 2 then (1 : Fin 5) else if value = 3 then (3 : Fin 5) else if value = 4 then (2 : Fin 5) else (4 : Fin 5)

def leftFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else if value = 2 then (4 : Fin 6) else if value = 3 then (3 : Fin 6) else (5 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S5_121.table.semigroup where
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

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_223.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup SemigroupBasis.Generated.S5_121.table.semigroup SemigroupBasis.Generated.Catalogue.S5_223.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.representativeBasis

theorem representative_basis :
    BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.Common.s5_121_s5_223_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_2858

namespace S6_2872

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (1 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (0 : Fin 6) else if left = 3 then if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (3 : Fin 6) else if left = 4 then if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (1 : Fin 6) else (4 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "d7784386705fbc2e695a7a3da146d04190f39e463d131a593b321782968e7e7a"

def proofRoute : String := "order6-factor-intersection-period-two-from-three-multiple-block-v1"

def leftFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (0 : Fin 5) else if value = 2 then (1 : Fin 5) else if value = 3 then (2 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def leftFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else if value = 2 then (3 : Fin 6) else if value = 3 then (4 : Fin 6) else (5 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_132.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (1 : Fin 5) else if value = 2 then (0 : Fin 5) else if value = 3 then (2 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def rightFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (3 : Fin 6) else if value = 3 then (4 : Fin 6) else (5 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_226.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S5_132.table.semigroup SemigroupBasis.Generated.Catalogue.S5_226.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.representativeBasis

theorem representative_basis :
    BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.Common.s5_132_s5_226_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_2872

namespace S6_2874

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (1 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (1 : Fin 6) else if left = 3 then if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (3 : Fin 6) else if left = 4 then if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (1 : Fin 6) else (4 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "f7bef01251aa52618aa375744ba37830c6fd3b61b23117dc3857c154ffdf567d"

def proofRoute : String := "order6-factor-intersection-period-two-from-three-multiple-block-v1"

def leftFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (0 : Fin 5) else if value = 2 then (1 : Fin 5) else if value = 3 then (2 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def leftFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else if value = 2 then (3 : Fin 6) else if value = 3 then (4 : Fin 6) else (5 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_132.table.semigroup where
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

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_226.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair :
    SubdirectPair table.semigroup SemigroupBasis.Generated.Catalogue.S5_132.table.semigroup SemigroupBasis.Generated.Catalogue.S5_226.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.representativeBasis

theorem representative_basis :
    BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock.Common.s5_132_s5_226_intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_2874

end SemigroupBasis.Generated.Order6FactorIntersectionPeriodTwoFromThreeMultipleBlock
