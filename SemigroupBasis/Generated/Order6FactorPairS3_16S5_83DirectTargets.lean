import SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83DirectNormal
import SemigroupBasis.FiniteReflection

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorPairS3_16S5_83DirectTargets

open SemigroupBasis

namespace S6_3373

/-- Authenticated order-six table, SHA-256 `4005ee46be39b7c3acffd7b78bae6345e6e262418787933ddcbc988ac87291ee`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "4005ee46be39b7c3acffd7b78bae6345e6e262418787933ddcbc988ac87291ee"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 1, 0, 3, 4, 5], [5, 5, 5, 5, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun rightValue =>
        (mul left rightValue).val) =
      publishedRows := by
  decide

def ontoS3_16Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (1 : Fin 3) else (2 : Fin 3)

def ontoS3_16Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)

def ontoS3_16 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := ontoS3_16Map
  map_mul := by decide
  preimage := ontoS3_16Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5_83Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (4 : Fin 5) else (0 : Fin 5)

def ontoS5_83Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (4 : Fin 6)

def ontoS5_83 : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup where
  toFun := ontoS5_83Map
  map_mul := by decide
  preimage := ontoS5_83Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup where
  left := ontoS3_16
  right := ontoS5_83
  jointlyInjective := by
    intro left rightValue
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Direct.basis

/-- Complete direct basis obtained from the authenticated subdirect pair. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Direct.intersectionBasisS5_83.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_3373

namespace S6_3378

/-- Authenticated order-six table, SHA-256 `b1619d5160f8cad33f7a534e2f619635252b9946b20cb3d6116f35b173e5e409`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "b1619d5160f8cad33f7a534e2f619635252b9946b20cb3d6116f35b173e5e409"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0], [0, 1, 1, 3, 4, 5], [5, 5, 5, 5, 5, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun rightValue =>
        (mul left rightValue).val) =
      publishedRows := by
  decide

def ontoS3_16Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (1 : Fin 3) else (2 : Fin 3)

def ontoS3_16Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (4 : Fin 6) else (5 : Fin 6)

def ontoS3_16 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := ontoS3_16Map
  map_mul := by decide
  preimage := ontoS3_16Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5_84Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (4 : Fin 5) else (0 : Fin 5)

def ontoS5_84Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (4 : Fin 6)

def ontoS5_84 : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup where
  toFun := ontoS5_84Map
  map_mul := by decide
  preimage := ontoS5_84Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup where
  left := ontoS3_16
  right := ontoS5_84
  jointlyInjective := by
    intro left rightValue
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Direct.basis

/-- Complete direct basis obtained from the authenticated subdirect pair. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Direct.intersectionBasisS5_84.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_3378

namespace S6_6177

/-- Authenticated order-six table, SHA-256 `9586ee4b00556306e965e3955b84625ce8535ff53fc48f8510a9e2a80ea18518`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "9586ee4b00556306e965e3955b84625ce8535ff53fc48f8510a9e2a80ea18518"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0], [3, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 3], [0, 1, 2, 3, 3, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun rightValue =>
        (mul left rightValue).val) =
      publishedRows := by
  decide

def ontoS3_16Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (2 : Fin 3) else if a = 4 then (2 : Fin 3) else (1 : Fin 3)

def ontoS3_16Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (5 : Fin 6) else (3 : Fin 6)

def ontoS3_16 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := ontoS3_16Map
  map_mul := by decide
  preimage := ontoS3_16Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5_83Map (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (2 : Fin 5) else (4 : Fin 5)

def ontoS5_83Section (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (2 : Fin 6) else (5 : Fin 6)

def ontoS5_83 : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup where
  toFun := ontoS5_83Map
  map_mul := by decide
  preimage := ontoS5_83Section
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup where
  left := ontoS3_16
  right := ontoS5_83
  jointlyInjective := by
    intro left rightValue
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Direct.basis

/-- Complete direct basis obtained from the authenticated subdirect pair. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Direct.intersectionBasisS5_83.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_6177

end SemigroupBasis.Generated.Order6FactorPairS3_16S5_83DirectTargets
