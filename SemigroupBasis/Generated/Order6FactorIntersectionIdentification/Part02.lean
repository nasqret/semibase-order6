import SemigroupBasis.CoRoots.Order6FactorIntersectionFirstSequenceShortLong
import SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots
import SemigroupBasis.CoRoots.Order6Head3Tail2
import SemigroupBasis.Subdirect

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorIntersectionIdentification

open SemigroupBasis

namespace S6_6174

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (1 : Fin 6) else (0 : Fin 6) else if left = 3 then if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6) else if left = 4 then if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "77a90014ecfe64573190ab229ea89329fbf10cddf7952b3f976a63f4806ce9e1"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (0 : Fin 3) else if value = 3 then (2 : Fin 3) else if value = 4 then (2 : Fin 3) else (1 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (5 : Fin 6) else (3 : Fin 6)

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

end S6_6174

namespace S6_9098

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (1 : Fin 6) else (1 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (1 : Fin 6) else (1 : Fin 6) else if left = 3 then if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6) else if left = 4 then if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (4 : Fin 6) else if right = 4 then (5 : Fin 6) else (3 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (5 : Fin 6) else if right = 4 then (3 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "ed8b06aebbdf5448e2b28684b7f68fc0a4dd64f4567234e1ce056491820646f7"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (1 : Fin 3) else if value = 3 then (2 : Fin 3) else if value = 4 then (2 : Fin 3) else (2 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else (3 : Fin 6)

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

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Examples.s5_1001.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Examples.finalMarkerThree.semigroup SemigroupBasis.Examples.s5_1001.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.IndexTwoPeriodThree.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.IndexTwoPeriodThree.intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_9098

namespace S6_9117

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (1 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (1 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (1 : Fin 6) else (1 : Fin 6) else if left = 2 then if right = 0 then (1 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (1 : Fin 6) else (1 : Fin 6) else if left = 3 then if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6) else if left = 4 then if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (4 : Fin 6) else if right = 4 then (5 : Fin 6) else (3 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (5 : Fin 6) else if right = 4 then (3 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "9f65f7d1309dc1bea1cf28489fce8c7df3c270c76f9179fdbb160dfa28196bf9"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (1 : Fin 3) else if value = 3 then (2 : Fin 3) else if value = 4 then (2 : Fin 3) else (2 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else (3 : Fin 6)

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

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_1007Family.S5_1007.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Examples.finalMarkerThree.semigroup SemigroupBasis.CoRoots.S5_1007Family.S5_1007.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.PrefixResidueSix.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.PrefixResidueSix.intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_9117

namespace S6_9336

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (4 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (1 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (4 : Fin 6) else if right = 3 then (4 : Fin 6) else if right = 4 then (2 : Fin 6) else (1 : Fin 6) else if left = 2 then if right = 0 then (2 : Fin 6) else if right = 1 then (4 : Fin 6) else if right = 2 then (1 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (0 : Fin 6) else (2 : Fin 6) else if left = 3 then if right = 0 then (2 : Fin 6) else if right = 1 then (4 : Fin 6) else if right = 2 then (1 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (0 : Fin 6) else (2 : Fin 6) else if left = 4 then if right = 0 then (4 : Fin 6) else if right = 1 then (2 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (1 : Fin 6) else (4 : Fin 6) else if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "a77826f31e0aa3c69d75a073b9fbdb8e1c45f955820992ed44126c8b084a1726"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (0 : Fin 3) else if value = 3 then (1 : Fin 3) else if value = 4 then (0 : Fin 3) else (2 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (3 : Fin 6) else (5 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Examples.finalMarkerThree.semigroup where
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

end S6_9336

namespace S6_9589

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (0 : Fin 6) else (1 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (1 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (1 : Fin 6) else (2 : Fin 6) else if left = 3 then if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6) else if left = 4 then if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (3 : Fin 6) else (4 : Fin 6) else if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (4 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "8c8c3f83a4bc32ce46bedcfbc99c8f034a00a878a2cb29e76443f8db226d0106"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (2 : Fin 3) else if value = 1 then (2 : Fin 3) else if value = 2 then (2 : Fin 3) else if value = 3 then (0 : Fin 3) else if value = 4 then (0 : Fin 3) else (1 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (3 : Fin 6) else if value = 1 then (5 : Fin 6) else (0 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_13.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (1 : Fin 5) else if value = 2 then (3 : Fin 5) else if value = 3 then (0 : Fin 5) else if value = 4 then (2 : Fin 5) else (4 : Fin 5)

def rightFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else if value = 2 then (4 : Fin 6) else if value = 3 then (2 : Fin 6) else (5 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_207.table.semigroup.opposite where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_13.table.semigroup SemigroupBasis.CoRoots.S5_207.table.semigroup.opposite where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6Head3Tail2.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6Head3Tail2.intersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_9589

end SemigroupBasis.Generated.Order6FactorIntersectionIdentification
