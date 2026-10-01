import SemigroupBasis.EdmundsInflation
import SemigroupBasis.Generated.S4_90TransfersLayer2

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6ExactInflation.S6_6834

open SemigroupBasis

-- Witness registry: 9d6bc91f7f14844630559b793fc29887373b4eb309ee2111c8a1eb927b6b34f7
-- Target table: 2aad4cce1499c4b86f46ddd2aecb6df33733ef8aeb1d24c38cfbcedf5f1229b9
-- Source table: 068e758f64bd0e604b40ecdc812922ff38177649a44eeaef11416ab8ec30ad6e
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (0 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (3 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S5_668.table.semigroup table.semigroup where
  toFun := fun a : Fin 5 =>
    if a = 0 then (0 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (4 : Fin 6) else (5 : Fin 6)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.Catalogue.S5_668.table.semigroup table.semigroup where
  embedding := embedding
  retract := fun b : Fin 6 =>
    if b = 0 then (0 : Fin 5) else if b = 1 then (0 : Fin 5) else if b = 2 then (1 : Fin 5) else if b = 3 then (2 : Fin 5) else if b = 4 then (3 : Fin 5) else (4 : Fin 5)
  retract_embedding := by
    intro a
    exact by decide +revert
  product_represented := by
    intro a b
    exact by decide +revert

theorem proper : inflation.Proper := by
  refine Exists.intro (1 : Fin 6) ?_
  intro a
  exact by decide +revert

theorem representative_basis :
    BasisFor table.semigroup SemigroupBasis.EdmundsInflation.basis :=
  SemigroupBasis.Inflation.inheritEdmundsSuffixParityBasis inflation proper SemigroupBasis.Generated.S4_90Transfers.S5_668.representative_basis

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis SemigroupBasis.EdmundsInflation.basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6ExactInflation.S6_6834
