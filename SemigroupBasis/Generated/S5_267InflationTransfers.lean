import SemigroupBasis.S5_267Inflation
import SemigroupBasis.CoRoots.S4_52
import SemigroupBasis.Generated.CatalogueOrder5Part03
import SemigroupBasis.Opposite

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.S5_267InflationTransfers

open SemigroupBasis

theorem source_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S4_52.table.semigroup
      SemigroupBasis.S5_267Inflation.sourceBasis :=
  SemigroupBasis.CoRoots.S4_52.basis_complete

-- BEGIN S5_267
namespace S5_267

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_52.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_267.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.Catalogue.S4_52.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_267.table.semigroup where
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_267.table.semigroup
      SemigroupBasis.S5_267Inflation.basis :=
  SemigroupBasis.Inflation.inheritS5_267Basis
    inflation proper source_basis

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_267.table.semigroup.opposite
      (reversedBasis SemigroupBasis.S5_267Inflation.basis) :=
  representative_basis.oppositeReversed

end S5_267
-- END S5_267

-- BEGIN S5_280
namespace S5_280

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_52.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_280.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.Catalogue.S4_52.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_280.table.semigroup where
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_280.table.semigroup
      SemigroupBasis.S5_267Inflation.basis :=
  SemigroupBasis.Inflation.inheritS5_267Basis
    inflation proper source_basis

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_280.table.semigroup.opposite
      (reversedBasis SemigroupBasis.S5_267Inflation.basis) :=
  representative_basis.oppositeReversed

end S5_280
-- END S5_280

end SemigroupBasis.Generated.S5_267InflationTransfers
