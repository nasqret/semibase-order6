import SemigroupBasis.Generated.Order6Level2TierBHash86393.Shared

namespace SemigroupBasis.Generated.Order6Level2TierBHash86393.S6_1352

open SemigroupBasis
open SemigroupBasis.Generated.Order6Level2TierBHash86393.Shared

/-- Authenticated order-six table, SHA-256 `11b477ec447d817661187cf832fc38e95b280f68523d15c9b7d0c17844fa12c0`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (2 : Fin 6)
    else if b = 3 then (2 : Fin 6)
    else if b = 4 then (2 : Fin 6)
    else (0 : Fin 6)
  else if a = 1 then
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (2 : Fin 6)
    else if b = 3 then (2 : Fin 6)
    else if b = 4 then (2 : Fin 6)
    else (1 : Fin 6)
  else if a = 2 then
    if b = 0 then (2 : Fin 6)
    else if b = 1 then (2 : Fin 6)
    else if b = 2 then (0 : Fin 6)
    else if b = 3 then (0 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (2 : Fin 6)
  else if a = 3 then
    if b = 0 then (2 : Fin 6)
    else if b = 1 then (2 : Fin 6)
    else if b = 2 then (0 : Fin 6)
    else if b = 3 then (0 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (3 : Fin 6)
  else if a = 4 then
    if b = 0 then (2 : Fin 6)
    else if b = 1 then (3 : Fin 6)
    else if b = 2 then (0 : Fin 6)
    else if b = 3 then (0 : Fin 6)
    else if b = 4 then (0 : Fin 6)
    else (3 : Fin 6)
  else
    if b = 0 then (0 : Fin 6)
    else if b = 1 then (0 : Fin 6)
    else if b = 2 then (2 : Fin 6)
    else if b = 3 then (3 : Fin 6)
    else if b = 4 then (4 : Fin 6)
    else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String := "11b477ec447d817661187cf832fc38e95b280f68523d15c9b7d0c17844fa12c0"

def publishedRows : List (List Nat) :=
  [[0, 0, 2, 2, 2, 0], [0, 0, 2, 2, 2, 1], [2, 2, 0, 0, 0, 2], [2, 2, 0, 0, 0, 3], [2, 3, 0, 0, 0, 3], [0, 0, 2, 3, 4, 5]]

theorem mul_matches_published :
    (List.finRange 6).map (fun left =>
      (List.finRange 6).map fun right => (mul left right).val) =
      publishedRows := by
  decide

def leftMap (a : Fin 6) : Fin 2 :=
  if a = 0 then (0 : Fin 2)
  else if a = 1 then (0 : Fin 2)
  else if a = 2 then (1 : Fin 2)
  else if a = 3 then (1 : Fin 2)
  else if a = 4 then (1 : Fin 2)
  else (0 : Fin 2)

def leftSection (a : Fin 2) : Fin 6 :=
  if a = 0 then (0 : Fin 6)
  else (2 : Fin 6)

def leftQuotient :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.S2_2.table.semigroup where
  toFun := leftMap
  map_mul := by decide
  preimage := leftSection
  right_inverse := by
    intro value
    exact by decide +revert

def rightMap (a : Fin 6) : Fin 5 :=
  if a = 0 then (0 : Fin 5)
  else if a = 1 then (3 : Fin 5)
  else if a = 2 then (0 : Fin 5)
  else if a = 3 then (1 : Fin 5)
  else if a = 4 then (2 : Fin 5)
  else (4 : Fin 5)

def rightSection (a : Fin 5) : Fin 6 :=
  if a = 0 then (0 : Fin 6)
  else if a = 1 then (3 : Fin 6)
  else if a = 2 then (4 : Fin 6)
  else if a = 3 then (1 : Fin 6)
  else (5 : Fin 6)

def rightQuotient :
    SplitSurjection table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup.opposite where
  toFun := rightMap
  map_mul := by decide
  preimage := rightSection
  right_inverse := by
    intro value
    exact by decide +revert

def pair :
    SubdirectPair table.semigroup
      SemigroupBasis.Generated.S2_2.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_108.table.semigroup.opposite where
  left := leftQuotient
  right := rightQuotient
  jointlyInjective := by
    intro left right
    exact by decide +revert

abbrev basis : List (Identity Nat) := Shared.basis

theorem representative_basis : BasisFor table.semigroup basis :=
  Shared.intersectionBasisS2_2S5_108Opposite.basisFor pair

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6Level2TierBHash86393.S6_1352
