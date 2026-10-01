import SemigroupBasis.ParityInitialInflation
import SemigroupBasis.Generated.CatalogueOrder5Part04
import SemigroupBasis.Generated.CatalogueOrder5Part05
import SemigroupBasis.Generated.S4_95
import SemigroupBasis.Opposite

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.S5_452InflationTransfers

open SemigroupBasis

-- BEGIN S5_452
namespace S5_452

def embedding :
    Embedding SemigroupBasis.Generated.S4_95.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_452.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.S4_95.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_452.table.semigroup where
  embedding := embedding
  retract := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 4) else if b = 1 then (0 : Fin 4) else if b = 2 then (1 : Fin 4) else if b = 3 then (2 : Fin 4) else (3 : Fin 4)
  retract_embedding := by
    intro a
    exact by decide +revert
  product_represented := by
    intro a b
    exact by decide +revert

theorem proper : inflation.Proper := by
  refine ⟨(1 : Fin 5), ?_⟩
  intro a
  exact by decide +revert

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_452.table.semigroup
      SemigroupBasis.ParityInitialInflation.basis :=
  SemigroupBasis.Inflation.inheritParityInitialBasis
    inflation proper SemigroupBasis.Generated.S4_95.representative_basis

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_452.table.semigroup.opposite
      (reversedBasis SemigroupBasis.ParityInitialInflation.basis) :=
  representative_basis.oppositeReversed

end S5_452
-- END S5_452

-- BEGIN S5_474
namespace S5_474

def embedding :
    Embedding SemigroupBasis.Generated.S4_95.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_474.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.S4_95.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_474.table.semigroup where
  embedding := embedding
  retract := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (1 : Fin 4) else if b = 3 then (2 : Fin 4) else (3 : Fin 4)
  retract_embedding := by
    intro a
    exact by decide +revert
  product_represented := by
    intro a b
    exact by decide +revert

theorem proper : inflation.Proper := by
  refine ⟨(2 : Fin 5), ?_⟩
  intro a
  exact by decide +revert

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_474.table.semigroup
      SemigroupBasis.ParityInitialInflation.basis :=
  SemigroupBasis.Inflation.inheritParityInitialBasis
    inflation proper SemigroupBasis.Generated.S4_95.representative_basis

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_474.table.semigroup.opposite
      (reversedBasis SemigroupBasis.ParityInitialInflation.basis) :=
  representative_basis.oppositeReversed

end S5_474
-- END S5_474

-- BEGIN S5_561
namespace S5_561

def embedding :
    Embedding SemigroupBasis.Generated.S4_95.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_561.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (3 : Fin 5) else if a = 2 then (0 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.S4_95.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_561.table.semigroup where
  embedding := embedding
  retract := fun b : Fin 5 =>
    if b = 0 then (2 : Fin 4) else if b = 1 then (2 : Fin 4) else if b = 2 then (0 : Fin 4) else if b = 3 then (1 : Fin 4) else (3 : Fin 4)
  retract_embedding := by
    intro a
    exact by decide +revert
  product_represented := by
    intro a b
    exact by decide +revert

theorem proper : inflation.Proper := by
  refine ⟨(1 : Fin 5), ?_⟩
  intro a
  exact by decide +revert

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_561.table.semigroup
      SemigroupBasis.ParityInitialInflation.basis :=
  SemigroupBasis.Inflation.inheritParityInitialBasis
    inflation proper SemigroupBasis.Generated.S4_95.representative_basis

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_561.table.semigroup.opposite
      (reversedBasis SemigroupBasis.ParityInitialInflation.basis) :=
  representative_basis.oppositeReversed

end S5_561
-- END S5_561

end SemigroupBasis.Generated.S5_452InflationTransfers
