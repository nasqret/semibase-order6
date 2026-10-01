import SemigroupBasis.CoRoots.Order6S5_108OppositeInitialIntersection
import SemigroupBasis.FiniteReflection

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6S5_108OppositeInitialIntersectionTargets

open SemigroupBasis

namespace S6_3825

/-- Authenticated order-six table, SHA-256 `9b326084e738850e9e17a7db4d8e57a8f35de53e5bcfaab58ba9fd84bd2e3799`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "9b326084e738850e9e17a7db4d8e57a8f35de53e5bcfaab58ba9fd84bd2e3799"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 2], [0, 0, 1, 0, 0, 1], [4, 4, 4, 4, 4, 4], [0, 1, 0, 3, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoInitialMap (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2) else if a = 1 then (0 : Fin 2) else if a = 2 then (0 : Fin 2) else if a = 3 then (0 : Fin 2) else if a = 4 then (1 : Fin 2) else (0 : Fin 2)

def ontoInitialSection (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (4 : Fin 6)

def ontoInitial : SplitSurjection table.semigroup SemigroupBasis.Generated.S2_4.table.semigroup where
  toFun := ontoInitialMap
  map_mul := by decide
  preimage := ontoInitialSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5_108OppositeMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (0 : Fin 5) else (4 : Fin 5)

def ontoS5_108OppositeSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (2 : Fin 6) else (5 : Fin 6)

def ontoS5_108Opposite : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup.opposite where
  toFun := ontoS5_108OppositeMap
  map_mul := by decide
  preimage := ontoS5_108OppositeSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S2_4.table.semigroup SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup.opposite where
  left := ontoInitial
  right := ontoS5_108Opposite
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6S5_108OppositeInitialIntersection.basis

/-- Complete direct basis obtained from the authenticated subdirect pair. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6S5_108OppositeInitialIntersection.intersectionS2_4S5_108Opposite.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_3825

namespace S6_6442

/-- Authenticated order-six table, SHA-256 `542296867b63ca0ff3c7852b36095a5b7d5204ae828b41e7ff1f701a451f5ba9`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "542296867b63ca0ff3c7852b36095a5b7d5204ae828b41e7ff1f701a451f5ba9"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 1, 1], [3, 3, 3, 3, 3, 3], [3, 3, 3, 3, 3, 4], [0, 1, 2, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoInitialMap (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2) else if a = 1 then (0 : Fin 2) else if a = 2 then (0 : Fin 2) else if a = 3 then (1 : Fin 2) else if a = 4 then (1 : Fin 2) else (0 : Fin 2)

def ontoInitialSection (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (3 : Fin 6)

def ontoInitial : SplitSurjection table.semigroup SemigroupBasis.Generated.S2_4.table.semigroup where
  toFun := ontoInitialMap
  map_mul := by decide
  preimage := ontoInitialSection
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5_108OppositeMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (3 : Fin 5) else (4 : Fin 5)

def ontoS5_108OppositeSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)

def ontoS5_108Opposite : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup.opposite where
  toFun := ontoS5_108OppositeMap
  map_mul := by decide
  preimage := ontoS5_108OppositeSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S2_4.table.semigroup SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup.opposite where
  left := ontoInitial
  right := ontoS5_108Opposite
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6S5_108OppositeInitialIntersection.basis

/-- Complete direct basis obtained from the authenticated subdirect pair. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6S5_108OppositeInitialIntersection.intersectionS2_4S5_108Opposite.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_6442

end SemigroupBasis.Generated.Order6S5_108OppositeInitialIntersectionTargets
