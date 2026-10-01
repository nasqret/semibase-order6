import SemigroupBasis.CoRoots.S5_831Completeness
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.S5_831Transfers

open SemigroupBasis

namespace S5_832

/-- Multiplication on the recorded carrier, in certificate order:
`(0,0),(0,1),(0,2),(2,2),(2,4),(3,3)`. -/
def divisorSubMul (left right : Fin 6) : Fin 6 :=
  if left = 0 then
    0
  else if left = 1 then
    if right = 4 then 2 else 0
  else if left = 2 then
    2
  else if left = 3 then
    3
  else if left = 4 then
    4
  else if right = 0 then
    0
  else if right = 1 then
    1
  else if right = 2 then
    2
  else if right = 3 then
    3
  else if right = 4 then
    3
  else
    5

def divisorSubTable : FiniteTable where
  order := 6
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (Generated.Catalogue.S5_832.table.semigroup.pi (Fin 2)) where
  toFun := fun (element : Fin 6) (coordinate : Fin 2) =>
    if coordinate = 0 then
      if element = 0 then (0 : Fin 5)
      else if element = 1 then (0 : Fin 5)
      else if element = 2 then (0 : Fin 5)
      else if element = 3 then (2 : Fin 5)
      else if element = 4 then (2 : Fin 5)
      else (3 : Fin 5)
    else
      if element = 0 then (0 : Fin 5)
      else if element = 1 then (1 : Fin 5)
      else if element = 2 then (2 : Fin 5)
      else if element = 3 then (2 : Fin 5)
      else if element = 4 then (4 : Fin 5)
      else (3 : Fin 5)
  map_mul := by
    intro left right
    funext coordinate
    exact by decide +revert
  injective := by
    intro left right equal
    have first := congrFun equal (0 : Fin 2)
    have second := congrFun equal (1 : Fin 2)
    clear equal
    exact by decide +revert

/-- The exact quotient vector `[0,1,2,0,4,3]`, with split preimage
`[0,1,2,5,4]`. -/
def divisorQuotient :
    SplitSurjection divisorSubTable.semigroup
      Generated.Catalogue.S5_831.table.semigroup where
  toFun := fun element : Fin 6 =>
    if element = 0 then (0 : Fin 5)
    else if element = 1 then (1 : Fin 5)
    else if element = 2 then (2 : Fin 5)
    else if element = 3 then (0 : Fin 5)
    else if element = 4 then (4 : Fin 5)
    else (3 : Fin 5)
  map_mul := by
    intro left right
    exact by decide +revert
  preimage := fun value : Fin 5 =>
    if value = 0 then (0 : Fin 6)
    else if value = 1 then (1 : Fin 6)
    else if value = 2 then (2 : Fin 6)
    else if value = 3 then (5 : Fin 6)
    else (4 : Fin 6)
  right_inverse := by
    intro value
    exact by decide +revert

theorem targetModels :
    Models Generated.Catalogue.S5_832.table.semigroup
      SemigroupBasis.CoRoots.S5_831.basis :=
  SemigroupBasis.CoRoots.S5_831.models_of_finite_checks
    Generated.Catalogue.S5_832.table (by decide)

/-- `S5_831` is a quotient of the recorded subsemigroup of `S5_832²`, so
the root basis transfers by the direct-power divisor identity sandwich. -/
theorem representativeBasisFor :
    BasisFor Generated.Catalogue.S5_832.table.semigroup
      SemigroupBasis.CoRoots.S5_831.basis :=
  SemigroupBasis.CoRoots.S5_831.basis_complete.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels

theorem oppositeBasisFor :
    BasisFor Generated.Catalogue.S5_832.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_831.expectedOppositeBasis := by
  rw [← SemigroupBasis.CoRoots.S5_831.reversedBasis_eq_expected]
  exact representativeBasisFor.oppositeReversed

/-- Lifecycle-compatible name for the power-divisor representative endpoint. -/
theorem representative_basis :
    BasisFor Generated.Catalogue.S5_832.table.semigroup
      SemigroupBasis.CoRoots.S5_831.basis :=
  representativeBasisFor

/-- Lifecycle-compatible name for the reversed power-divisor endpoint. -/
theorem opposite_basis :
    BasisFor Generated.Catalogue.S5_832.table.semigroup.opposite
      SemigroupBasis.CoRoots.S5_831.expectedOppositeBasis :=
  oppositeBasisFor

end S5_832

end SemigroupBasis.Generated.S5_831Transfers
