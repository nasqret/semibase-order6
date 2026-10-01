import SemigroupBasis.Generated.Order6FactorIntersectionResidual59.Common

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorIntersectionResidual59

open SemigroupBasis

namespace S6_9106

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6) else if left = 3 then if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6) else if left = 4 then if right = 0 then (4 : Fin 6) else if right = 1 then (4 : Fin 6) else if right = 2 then (4 : Fin 6) else if right = 3 then (4 : Fin 6) else if right = 4 then (5 : Fin 6) else (0 : Fin 6) else if right = 0 then (5 : Fin 6) else if right = 1 then (5 : Fin 6) else if right = 2 then (5 : Fin 6) else if right = 3 then (5 : Fin 6) else if right = 4 then (0 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "ce731fee549cc3784920abf045d7df5d4a5d805ea39bbe3fe89d275104d19c56"

def proofRoute : String := "coordinatewise-common-basis"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else if value = 2 then (0 : Fin 3) else if value = 3 then (2 : Fin 3) else if value = 4 then (0 : Fin 3) else (0 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else (3 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (0 : Fin 5) else if value = 2 then (1 : Fin 5) else if value = 3 then (2 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def rightFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else if value = 2 then (3 : Fin 6) else if value = 3 then (4 : Fin 6) else (5 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_1004.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup SemigroupBasis.Generated.Catalogue.S5_1004.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.IndexTwoPeriodThree.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorIntersectionResidual59.Common.indexTwoPeriodThreeS3_6S5_1004IntersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_9106

namespace S6_9108

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (1 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6) else if left = 3 then if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6) else if left = 4 then if right = 0 then (4 : Fin 6) else if right = 1 then (4 : Fin 6) else if right = 2 then (4 : Fin 6) else if right = 3 then (4 : Fin 6) else if right = 4 then (5 : Fin 6) else (0 : Fin 6) else if right = 0 then (5 : Fin 6) else if right = 1 then (5 : Fin 6) else if right = 2 then (5 : Fin 6) else if right = 3 then (5 : Fin 6) else if right = 4 then (0 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "af975c4496e783c7bd0b38bcac5ffbdbe69904882cd5071528f605f0b6108f43"

def proofRoute : String := "coordinatewise-common-basis"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (0 : Fin 3) else if value = 2 then (1 : Fin 3) else if value = 3 then (2 : Fin 3) else if value = 4 then (0 : Fin 3) else (0 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else (3 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup where
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

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_1004.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup SemigroupBasis.Generated.Catalogue.S5_1004.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.IndexTwoPeriodThree.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorIntersectionResidual59.Common.indexTwoPeriodThreeS3_6S5_1004IntersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_9108

namespace S6_11933

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6) else if left = 3 then if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (2 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6) else if left = 4 then if right = 0 then (4 : Fin 6) else if right = 1 then (4 : Fin 6) else if right = 2 then (4 : Fin 6) else if right = 3 then (4 : Fin 6) else if right = 4 then (5 : Fin 6) else (0 : Fin 6) else if right = 0 then (5 : Fin 6) else if right = 1 then (5 : Fin 6) else if right = 2 then (5 : Fin 6) else if right = 3 then (5 : Fin 6) else if right = 4 then (0 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "baafafb65d08c684be1fe269e6f526ff746575ced68e3efe2dd0f48cba644413"

def proofRoute : String := "coordinatewise-common-basis"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else if value = 2 then (2 : Fin 3) else if value = 3 then (2 : Fin 3) else if value = 4 then (0 : Fin 3) else (0 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else (2 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (2 : Fin 5) else if value = 1 then (2 : Fin 5) else if value = 2 then (0 : Fin 5) else if value = 3 then (1 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def rightFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (2 : Fin 6) else if value = 1 then (3 : Fin 6) else if value = 2 then (0 : Fin 6) else if value = 3 then (4 : Fin 6) else (5 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup SemigroupBasis.CoRoots.S5_1007Family.S5_1008.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.PrefixResidueSix.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorIntersectionResidual59.Common.prefixResidueSixS3_6S5_1008IntersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_11933

namespace S6_14978

def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6) else if left = 1 then if right = 0 then (0 : Fin 6) else if right = 1 then (0 : Fin 6) else if right = 2 then (0 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (4 : Fin 6) else if left = 2 then if right = 0 then (0 : Fin 6) else if right = 1 then (1 : Fin 6) else if right = 2 then (2 : Fin 6) else if right = 3 then (3 : Fin 6) else if right = 4 then (4 : Fin 6) else (5 : Fin 6) else if left = 3 then if right = 0 then (3 : Fin 6) else if right = 1 then (3 : Fin 6) else if right = 2 then (3 : Fin 6) else if right = 3 then (4 : Fin 6) else if right = 4 then (0 : Fin 6) else (0 : Fin 6) else if left = 4 then if right = 0 then (4 : Fin 6) else if right = 1 then (4 : Fin 6) else if right = 2 then (4 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6) else if right = 0 then (4 : Fin 6) else if right = 1 then (4 : Fin 6) else if right = 2 then (5 : Fin 6) else if right = 3 then (0 : Fin 6) else if right = 4 then (3 : Fin 6) else (3 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "a30a70a0b70acc0417ac37268e1edb76248af9c28b7f76a2b75458ec0e4cbca2"

def proofRoute : String := "coordinatewise-common-basis"

def leftFactorMap (value : Fin 6) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else if value = 2 then (2 : Fin 3) else if value = 3 then (0 : Fin 3) else if value = 4 then (0 : Fin 3) else (0 : Fin 3)

def leftFactorSection (value : Fin 3) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (1 : Fin 6) else (2 : Fin 6)

def leftFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup where
  toFun := leftFactorMap
  map_mul := by decide
  preimage := leftFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightFactorMap (value : Fin 6) : Fin 5 :=
  if value = 0 then (0 : Fin 5) else if value = 1 then (0 : Fin 5) else if value = 2 then (1 : Fin 5) else if value = 3 then (2 : Fin 5) else if value = 4 then (3 : Fin 5) else (4 : Fin 5)

def rightFactorSection (value : Fin 5) : Fin 6 :=
  if value = 0 then (0 : Fin 6) else if value = 1 then (2 : Fin 6) else if value = 2 then (3 : Fin 6) else if value = 3 then (4 : Fin 6) else (5 : Fin 6)

def rightFactor : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_1156.table.semigroup where
  toFun := rightFactorMap
  map_mul := by decide
  preimage := rightFactorSection
  right_inverse := by
    intro value
    exact by decide +revert

def subdirectPair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_6.table.semigroup SemigroupBasis.Generated.Catalogue.S5_1156.table.semigroup where
  left := leftFactor
  right := rightFactor
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorIntersectionSpecialRoots.IndexTwoPeriodThree.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.Generated.Order6FactorIntersectionResidual59.Common.indexTwoPeriodThreeS3_6S5_1156IntersectionBasis.basisFor subdirectPair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_14978

end SemigroupBasis.Generated.Order6FactorIntersectionResidual59
