import SemigroupBasis.PositiveModThreeInflation
import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.CommutativePositiveModThreeTransfersLayer1

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.S5_999InflationTransfers

open SemigroupBasis

-- BEGIN S5_999
namespace S5_999

def embedding :
    Embedding SemigroupBasis.Generated.S4_124.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_999.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.S4_124.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_999.table.semigroup where
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_999.table.semigroup
      SemigroupBasis.PositiveModThreeInflation.basis :=
  SemigroupBasis.Inflation.inheritCommutativePositiveModThreeBasis
    inflation proper SemigroupBasis.Generated.S4_124.representative_basis

end S5_999
-- END S5_999

-- BEGIN S5_1002
namespace S5_1002

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1002.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1002.table.semigroup where
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1002.table.semigroup
      SemigroupBasis.PositiveModThreeInflation.basis :=
  SemigroupBasis.Inflation.inheritCommutativePositiveModThreeBasis
    inflation proper SemigroupBasis.Generated.CommutativePositiveModThreeTransfers.S4_125.representative_basis

end S5_1002
-- END S5_1002

-- BEGIN S5_1005
namespace S5_1005

def embedding :
    Embedding SemigroupBasis.Generated.S4_124.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1005.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.S4_124.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1005.table.semigroup where
  embedding := embedding
  retract := fun b : Fin 5 =>
    if b = 0 then (1 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else if b = 3 then (2 : Fin 4) else (3 : Fin 4)
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1005.table.semigroup
      SemigroupBasis.PositiveModThreeInflation.basis :=
  SemigroupBasis.Inflation.inheritCommutativePositiveModThreeBasis
    inflation proper SemigroupBasis.Generated.S4_124.representative_basis

end S5_1005
-- END S5_1005

-- BEGIN S5_1006
namespace S5_1006

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1006.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1006.table.semigroup where
  embedding := embedding
  retract := fun b : Fin 5 =>
    if b = 0 then (1 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (0 : Fin 4) else if b = 3 then (2 : Fin 4) else (3 : Fin 4)
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1006.table.semigroup
      SemigroupBasis.PositiveModThreeInflation.basis :=
  SemigroupBasis.Inflation.inheritCommutativePositiveModThreeBasis
    inflation proper SemigroupBasis.Generated.CommutativePositiveModThreeTransfers.S4_125.representative_basis

end S5_1006
-- END S5_1006

-- BEGIN S5_1153
namespace S5_1153

def embedding :
    Embedding SemigroupBasis.Generated.S4_124.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1153.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.S4_124.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1153.table.semigroup where
  embedding := embedding
  retract := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else if b = 3 then (3 : Fin 4) else (3 : Fin 4)
  retract_embedding := by
    intro a
    exact by decide +revert
  product_represented := by
    intro a b
    exact by decide +revert

theorem proper : inflation.Proper := by
  refine ⟨(4 : Fin 5), ?_⟩
  intro a
  exact by decide +revert

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1153.table.semigroup
      SemigroupBasis.PositiveModThreeInflation.basis :=
  SemigroupBasis.Inflation.inheritCommutativePositiveModThreeBasis
    inflation proper SemigroupBasis.Generated.S4_124.representative_basis

end S5_1153
-- END S5_1153

-- BEGIN S5_1154
namespace S5_1154

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1154.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else (3 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.Catalogue.S4_125.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_1154.table.semigroup where
  embedding := embedding
  retract := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 4) else if b = 1 then (1 : Fin 4) else if b = 2 then (2 : Fin 4) else if b = 3 then (3 : Fin 4) else (3 : Fin 4)
  retract_embedding := by
    intro a
    exact by decide +revert
  product_represented := by
    intro a b
    exact by decide +revert

theorem proper : inflation.Proper := by
  refine ⟨(4 : Fin 5), ?_⟩
  intro a
  exact by decide +revert

theorem representative_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_1154.table.semigroup
      SemigroupBasis.PositiveModThreeInflation.basis :=
  SemigroupBasis.Inflation.inheritCommutativePositiveModThreeBasis
    inflation proper SemigroupBasis.Generated.CommutativePositiveModThreeTransfers.S4_125.representative_basis

end S5_1154
-- END S5_1154

end SemigroupBasis.Generated.S5_999InflationTransfers
