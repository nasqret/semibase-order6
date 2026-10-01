import SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83OppositeTransport
import SemigroupBasis.FiniteReflection

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorPairS3_16S5_83OppositeTargets

open SemigroupBasis

namespace S6_3811

/-- Authenticated order-six table, SHA-256 `dd0898d783ac842143f6b49d5d98c6720a2281e34fb31141e596e7f84c85c297`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "dd0898d783ac842143f6b49d5d98c6720a2281e34fb31141e596e7f84c85c297"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2], [0, 0, 1, 0, 0, 0], [4, 4, 4, 4, 4, 4], [0, 0, 0, 0, 4, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun rightValue =>
        (mul left rightValue).val) =
      publishedRows := by
  decide

def ontoS3_16Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (2 : Fin 3) else (1 : Fin 3)

def ontoS3_16Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (5 : Fin 6) else (4 : Fin 6)

def ontoS3_16 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := ontoS3_16Map
  map_mul := by decide
  preimage := ontoS3_16Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5_83OppositeMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (0 : Fin 5) else (4 : Fin 5)

def ontoS5_83OppositeSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (2 : Fin 6) else (5 : Fin 6)

def ontoS5_83Opposite : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite where
  toFun := ontoS5_83OppositeMap
  map_mul := by decide
  preimage := ontoS5_83OppositeSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite where
  left := ontoS3_16
  right := ontoS5_83Opposite
  jointlyInjective := by
    intro left rightValue
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Opposite.basis

/-- Complete direct basis obtained from the authenticated subdirect pair. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Opposite.intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_3811

namespace S6_3824

/-- Authenticated order-six table, SHA-256 `ea9b1d54b97c18ed9be8d6af6ef7a7fe5d4c29f7bfe12637fbc6127b98455641`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "ea9b1d54b97c18ed9be8d6af6ef7a7fe5d4c29f7bfe12637fbc6127b98455641"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2], [0, 0, 1, 0, 0, 1], [4, 4, 4, 4, 4, 4], [0, 0, 0, 0, 4, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun rightValue =>
        (mul left rightValue).val) =
      publishedRows := by
  decide

def ontoS3_16Map (a : Fin 6) : Fin 3 :=
  if a = 0 then (0 : Fin 3) else if a = 1 then (0 : Fin 3) else if a = 2 then (0 : Fin 3) else if a = 3 then (0 : Fin 3) else if a = 4 then (2 : Fin 3) else (1 : Fin 3)

def ontoS3_16Section (a : Fin 3) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (5 : Fin 6) else (4 : Fin 6)

def ontoS3_16 : SplitSurjection table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup where
  toFun := ontoS3_16Map
  map_mul := by decide
  preimage := ontoS3_16Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5_84OppositeMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (0 : Fin 5) else (4 : Fin 5)

def ontoS5_84OppositeSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (2 : Fin 6) else (5 : Fin 6)

def ontoS5_84Opposite : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup.opposite where
  toFun := ontoS5_84OppositeMap
  map_mul := by decide
  preimage := ontoS5_84OppositeSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup.opposite where
  left := ontoS3_16
  right := ontoS5_84Opposite
  jointlyInjective := by
    intro left rightValue
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Opposite.basis

/-- Complete direct basis obtained from the authenticated subdirect pair. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83OppositeTransport.intersectionBasisS5_84Opposite.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_3824

namespace S6_6434

/-- Authenticated order-six table, SHA-256 `1de3b655292d9b1ffeb42f9cc657e8242c8d00d4c3995cf6e290c7c677f0a7f6`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "1de3b655292d9b1ffeb42f9cc657e8242c8d00d4c3995cf6e290c7c677f0a7f6"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 0], [3, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 4], [0, 0, 0, 3, 3, 5]]

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

def ontoS5_83OppositeMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoS5_83OppositeSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoS5_83Opposite : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite where
  toFun := ontoS5_83OppositeMap
  map_mul := by decide
  preimage := ontoS5_83OppositeSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.Generated.Catalogue.S5_83.table.semigroup.opposite where
  left := ontoS3_16
  right := ontoS5_83Opposite
  jointlyInjective := by
    intro left rightValue
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Opposite.basis

/-- Complete direct basis obtained from the authenticated subdirect pair. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Opposite.intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_6434

namespace S6_6441

/-- Authenticated order-six table, SHA-256 `d7203480132d0bf500c4d7a43e08569108df3f01413e99ced6328aeff38a5e7b`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "d7203480132d0bf500c4d7a43e08569108df3f01413e99ced6328aeff38a5e7b"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1], [3, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 4], [0, 0, 0, 3, 3, 5]]

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

def ontoS5_84OppositeMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoS5_84OppositeSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoS5_84Opposite : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup.opposite where
  toFun := ontoS5_84OppositeMap
  map_mul := by decide
  preimage := ontoS5_84OppositeSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S3_16.table.semigroup SemigroupBasis.Generated.Catalogue.S5_84.table.semigroup.opposite where
  left := ontoS3_16
  right := ontoS5_84Opposite
  jointlyInjective := by
    intro left rightValue
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83Opposite.basis

/-- Complete direct basis obtained from the authenticated subdirect pair. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS3_16S5_83OppositeTransport.intersectionBasisS5_84Opposite.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_6441

end SemigroupBasis.Generated.Order6FactorPairS3_16S5_83OppositeTargets
