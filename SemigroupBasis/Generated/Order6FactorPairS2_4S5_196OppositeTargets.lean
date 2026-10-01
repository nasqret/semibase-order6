import SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196OppositeNormal
import SemigroupBasis.FiniteReflection

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6FactorPairS2_4S5_196OppositeTargets

open SemigroupBasis

namespace S6_5550

/-- Authenticated order-six table, SHA-256 `0ead28ee361cd46242269c93444370cb827d3d79d3cc403ccec22861c5514d00`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "0ead28ee361cd46242269c93444370cb827d3d79d3cc403ccec22861c5514d00"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2], [0, 0, 0, 1, 0, 0], [4, 4, 4, 4, 4, 4], [0, 0, 0, 0, 0, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS2_4Map (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2) else if a = 1 then (0 : Fin 2) else if a = 2 then (0 : Fin 2) else if a = 3 then (0 : Fin 2) else if a = 4 then (1 : Fin 2) else (0 : Fin 2)

def ontoS2_4Section (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (4 : Fin 6)

def ontoS2_4 : SplitSurjection table.semigroup SemigroupBasis.Generated.S2_4.table.semigroup where
  toFun := ontoS2_4Map
  map_mul := by decide
  preimage := ontoS2_4Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5_196OppositeMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (0 : Fin 5) else (4 : Fin 5)

def ontoS5_196OppositeSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)

def ontoS5_196Opposite : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup.opposite where
  toFun := ontoS5_196OppositeMap
  map_mul := by decide
  preimage := ontoS5_196OppositeSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S2_4.table.semigroup SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup.opposite where
  left := ontoS2_4
  right := ontoS5_196Opposite
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite.basis

/-- Endpoint conditional only on the shared factor-pair completeness theorem. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite.intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5550

namespace S6_5554

/-- Authenticated order-six table, SHA-256 `cc1c40770a544c772dc2a75bfef35ac9eb565caf2245fb888d2791e94d9ee83d`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "cc1c40770a544c772dc2a75bfef35ac9eb565caf2245fb888d2791e94d9ee83d"

def publishedRows : List (List Nat) :=
  [[0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 2], [0, 0, 0, 1, 0, 0], [4, 4, 4, 4, 4, 4], [4, 4, 4, 4, 4, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def ontoS2_4Map (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2) else if a = 1 then (0 : Fin 2) else if a = 2 then (0 : Fin 2) else if a = 3 then (0 : Fin 2) else if a = 4 then (1 : Fin 2) else (1 : Fin 2)

def ontoS2_4Section (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else (4 : Fin 6)

def ontoS2_4 : SplitSurjection table.semigroup SemigroupBasis.Generated.S2_4.table.semigroup where
  toFun := ontoS2_4Map
  map_mul := by decide
  preimage := ontoS2_4Section
  right_inverse := by
    intro value
    exact by decide +revert

def ontoS5_196OppositeMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (0 : Fin 5) else (4 : Fin 5)

def ontoS5_196OppositeSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else (5 : Fin 6)

def ontoS5_196Opposite : SplitSurjection table.semigroup SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup.opposite where
  toFun := ontoS5_196OppositeMap
  map_mul := by decide
  preimage := ontoS5_196OppositeSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair : SubdirectPair table.semigroup SemigroupBasis.Generated.S2_4.table.semigroup SemigroupBasis.Generated.Catalogue.S5_196.table.semigroup.opposite where
  left := ontoS2_4
  right := ontoS5_196Opposite
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite.basis

/-- Endpoint conditional only on the shared factor-pair completeness theorem. -/
theorem representative_basis : BasisFor table.semigroup basis :=
  SemigroupBasis.CoRoots.Order6FactorPairS2_4S5_196Opposite.intersectionBasis.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end S6_5554

end SemigroupBasis.Generated.Order6FactorPairS2_4S5_196OppositeTargets
