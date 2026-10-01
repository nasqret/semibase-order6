import SemigroupBasis.NormalBandInflation
import SemigroupBasis.Generated.CatalogueOrder5Part06
import SemigroupBasis.Generated.CatalogueOrder5Part08
import SemigroupBasis.Generated.S4_110
import SemigroupBasis.Opposite

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.S5_700InflationTransfers

open SemigroupBasis

-- BEGIN S5_700
namespace S5_700

def embedding :
    Embedding SemigroupBasis.Generated.S4_110.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_700.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.S4_110.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_700.table.semigroup where
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_700.table.semigroup
      SemigroupBasis.NormalBandInflation.basis :=
  SemigroupBasis.Inflation.inheritNormalBandBasis
    inflation proper SemigroupBasis.Generated.S4_110.representative_basis

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_700.table.semigroup.opposite
      (reversedBasis SemigroupBasis.NormalBandInflation.basis) :=
  representative_basis.oppositeReversed

end S5_700
-- END S5_700

-- BEGIN S5_753
namespace S5_753

def embedding :
    Embedding SemigroupBasis.Generated.S4_110.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_753.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (3 : Fin 5) else if a = 2 then (0 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.S4_110.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_753.table.semigroup where
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_753.table.semigroup
      SemigroupBasis.NormalBandInflation.basis :=
  SemigroupBasis.Inflation.inheritNormalBandBasis
    inflation proper SemigroupBasis.Generated.S4_110.representative_basis

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_753.table.semigroup.opposite
      (reversedBasis SemigroupBasis.NormalBandInflation.basis) :=
  representative_basis.oppositeReversed

end S5_753
-- END S5_753

-- BEGIN S5_932
namespace S5_932

def embedding :
    Embedding SemigroupBasis.Generated.S4_110.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_932.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (3 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (4 : Fin 5) else (2 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.S4_110.table.semigroup.opposite
      SemigroupBasis.Generated.Catalogue.S5_932.table.semigroup where
  embedding := embedding
  retract := fun b : Fin 5 =>
    if b = 0 then (1 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (3 : Fin 4) else if b = 3 then (0 : Fin 4) else (2 : Fin 4)
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

theorem oriented_source_basis :
    BasisFor SemigroupBasis.Generated.S4_110.table.semigroup.opposite
      SemigroupBasis.Examples.normalBandBasis :=
  SemigroupBasis.NormalBandInflation.normalBandBasis_complete_of_reversed
    SemigroupBasis.Generated.S4_110.opposite_basis

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_932.table.semigroup
      SemigroupBasis.NormalBandInflation.basis :=
  SemigroupBasis.Inflation.inheritNormalBandBasis
    inflation proper oriented_source_basis

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_932.table.semigroup.opposite
      (reversedBasis SemigroupBasis.NormalBandInflation.basis) :=
  representative_basis.oppositeReversed

end S5_932
-- END S5_932

end SemigroupBasis.Generated.S5_700InflationTransfers
