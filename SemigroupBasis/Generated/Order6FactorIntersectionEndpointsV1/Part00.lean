import SemigroupBasis.Generated.Order6FactorIntersectionEndpointsV1.Common

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorIntersectionEndpointsV1

open SemigroupBasis

namespace S6_5570

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (2 : Fin 6) else (2 : Fin 6) else if left = 3 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 4 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "7688967d499f6a7365a9ed747cbb08d8aad401dab2c9bc26cb527912c92d4029"

def tableRowsOneBased : List (List Nat) :=
  List.ofFn fun left : Fin 6 =>
    List.ofFn fun right : Fin 6 => (mul left right).val + 1

/-- The endpoint table is exactly the committed Smallsemi representative. -/
theorem tableRowsOneBased_certificate :
    tableRowsOneBased =
      [[1, 1, 1, 1, 1, 1],
       [1, 1, 1, 1, 1, 1],
       [1, 1, 1, 1, 3, 3],
       [1, 1, 1, 2, 1, 1],
       [1, 1, 3, 1, 5, 5],
       [1, 1, 3, 1, 6, 6]] := by
  decide

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (0 : Fin 3) else if value = 3 then (0 : Fin 3) else if value = 4 then (1 : Fin 3) else (2 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (4 : Fin 6) else (5 : Fin 6)

def leftFactor : SplitSurjection table.semigroup
    SemigroupBasis.Generated.S3_15.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (1 : Fin 5) else if value = 2 then (2 : Fin 5) else if value = 3 then (3 : Fin 5) else if value = 4 then (4 : Fin 5) else (4 : Fin 5)

def rightFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (2 : Fin 6) else if value = 3 then (3 : Fin 6) else (4 : Fin 6)

def rightFactor : SplitSurjection table.semigroup
    SemigroupBasis.Examples.commutativeCappedSupportFive.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup
    SemigroupBasis.Generated.S3_15.table.semigroup
    SemigroupBasis.Examples.commutativeCappedSupportFive.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) :=
  SemigroupBasis.CoRoots.Order6HeadSupportCap.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorIntersectionEndpointsV1.Common.s3_15S5_201IntersectionBasis.basisFor
    subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5570

end SemigroupBasis.Generated.Order6FactorIntersectionEndpointsV1
