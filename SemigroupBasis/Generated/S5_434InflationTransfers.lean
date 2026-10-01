import SemigroupBasis.EdmundsInflation
import SemigroupBasis.Generated.Catalogue
import SemigroupBasis.Generated.S4_90TransfersLayer1

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.S5_434InflationTransfers

open SemigroupBasis

-- BEGIN S5_434
namespace S5_434

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_90.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_434.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.Catalogue.S4_90.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_434.table.semigroup where
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_434.table.semigroup
      SemigroupBasis.EdmundsInflation.basis :=
  SemigroupBasis.Inflation.inheritEdmundsSuffixParityBasis
    inflation proper SemigroupBasis.Generated.S4_90.representative_basis

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_434.table.semigroup.opposite
      (reversedBasis SemigroupBasis.EdmundsInflation.basis) :=
  representative_basis.oppositeReversed

end S5_434
-- END S5_434

-- BEGIN S5_450
namespace S5_450

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_450.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (2 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_450.table.semigroup where
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_450.table.semigroup
      SemigroupBasis.EdmundsInflation.basis :=
  SemigroupBasis.Inflation.inheritEdmundsSuffixParityBasis
    inflation proper SemigroupBasis.Generated.S4_90Transfers.S4_93.representative_basis

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_450.table.semigroup.opposite
      (reversedBasis SemigroupBasis.EdmundsInflation.basis) :=
  representative_basis.oppositeReversed

end S5_450
-- END S5_450

-- BEGIN S5_457
namespace S5_457

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_90.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_457.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.Catalogue.S4_90.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_457.table.semigroup where
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_457.table.semigroup
      SemigroupBasis.EdmundsInflation.basis :=
  SemigroupBasis.Inflation.inheritEdmundsSuffixParityBasis
    inflation proper SemigroupBasis.Generated.S4_90.representative_basis

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_457.table.semigroup.opposite
      (reversedBasis SemigroupBasis.EdmundsInflation.basis) :=
  representative_basis.oppositeReversed

end S5_457
-- END S5_457

-- BEGIN S5_472
namespace S5_472

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_472.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_472.table.semigroup where
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_472.table.semigroup
      SemigroupBasis.EdmundsInflation.basis :=
  SemigroupBasis.Inflation.inheritEdmundsSuffixParityBasis
    inflation proper SemigroupBasis.Generated.S4_90Transfers.S4_93.representative_basis

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_472.table.semigroup.opposite
      (reversedBasis SemigroupBasis.EdmundsInflation.basis) :=
  representative_basis.oppositeReversed

end S5_472
-- END S5_472

-- BEGIN S5_557
namespace S5_557

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_557.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (3 : Fin 5) else if a = 2 then (0 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_557.table.semigroup where
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_557.table.semigroup
      SemigroupBasis.EdmundsInflation.basis :=
  SemigroupBasis.Inflation.inheritEdmundsSuffixParityBasis
    inflation proper SemigroupBasis.Generated.S4_90Transfers.S4_93.representative_basis

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_557.table.semigroup.opposite
      (reversedBasis SemigroupBasis.EdmundsInflation.basis) :=
  representative_basis.oppositeReversed

end S5_557
-- END S5_557

-- BEGIN S5_598
namespace S5_598

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_598.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (3 : Fin 5) else if a = 2 then (4 : Fin 5) else (0 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.Catalogue.S4_93.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_598.table.semigroup where
  embedding := embedding
  retract := fun b : Fin 5 =>
    if b = 0 then (3 : Fin 4) else if b = 1 then (3 : Fin 4) else if b = 2 then (0 : Fin 4) else if b = 3 then (1 : Fin 4) else (2 : Fin 4)
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_598.table.semigroup
      SemigroupBasis.EdmundsInflation.basis :=
  SemigroupBasis.Inflation.inheritEdmundsSuffixParityBasis
    inflation proper SemigroupBasis.Generated.S4_90Transfers.S4_93.representative_basis

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_598.table.semigroup.opposite
      (reversedBasis SemigroupBasis.EdmundsInflation.basis) :=
  representative_basis.oppositeReversed

end S5_598
-- END S5_598

-- BEGIN S5_655
namespace S5_655

def embedding :
    Embedding SemigroupBasis.Generated.Catalogue.S4_90.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_655.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (2 : Fin 5) else if a = 1 then (3 : Fin 5) else if a = 2 then (0 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

def inflation :
    Inflation SemigroupBasis.Generated.Catalogue.S4_90.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_655.table.semigroup where
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
    BasisFor SemigroupBasis.Generated.Catalogue.S5_655.table.semigroup
      SemigroupBasis.EdmundsInflation.basis :=
  SemigroupBasis.Inflation.inheritEdmundsSuffixParityBasis
    inflation proper SemigroupBasis.Generated.S4_90.representative_basis

theorem opposite_basis :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_655.table.semigroup.opposite
      (reversedBasis SemigroupBasis.EdmundsInflation.basis) :=
  representative_basis.oppositeReversed

end S5_655
-- END S5_655

end SemigroupBasis.Generated.S5_434InflationTransfers
