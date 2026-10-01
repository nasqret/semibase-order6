import SemigroupBasis.S5_917Inflation
import SemigroupBasis.CoRoots.S4_123
import SemigroupBasis.Generated.CatalogueOrder5Part08
import SemigroupBasis.Opposite

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.S5_917InflationTransfers

open SemigroupBasis
open SemigroupBasis.Examples

theorem source_basis :
    BasisFor SemigroupBasis.CoRoots.S4_123.table.semigroup
      rectangularBandBasis :=
  SemigroupBasis.CoRoots.S4_123.representative_basis

namespace S5_917

/-- The recorded one-based image `[1,3,4,5]` embeds `S4_123`. -/
def embedding :
    Embedding SemigroupBasis.CoRoots.S4_123.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_917.table.semigroup where
  toFun := fun a : Fin 4 =>
    if a = 0 then (0 : Fin 5)
    else if a = 1 then (2 : Fin 5)
    else if a = 2 then (3 : Fin 5)
    else (4 : Fin 5)
  map_mul := by
    intro a b
    exact by decide +revert
  injective := by
    intro a b
    exact by decide +revert

/--
The recorded target representatives are `[1,1,3,4,5]`; the corresponding
source retraction is `[1,1,2,3,4]`.
-/
def inflation :
    Inflation SemigroupBasis.CoRoots.S4_123.table.semigroup
      SemigroupBasis.Generated.Catalogue.S5_917.table.semigroup where
  embedding := embedding
  retract := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 4)
    else if b = 1 then (0 : Fin 4)
    else if b = 2 then (1 : Fin 4)
    else if b = 3 then (2 : Fin 4)
    else (3 : Fin 4)
  retract_embedding := by
    intro a
    exact by decide +revert
  product_represented := by
    intro a b
    exact by decide +revert

def embeddingImageOneBased : List Nat :=
  List.ofFn fun a : Fin 4 => (embedding.toFun a).val + 1

theorem embeddingImageOneBased_certificate :
    embeddingImageOneBased = [1, 3, 4, 5] := by
  decide

def retractionRepresentativeImageOneBased : List Nat :=
  List.ofFn fun b : Fin 5 =>
    (embedding.toFun (inflation.retract b)).val + 1

theorem retractionRepresentativeImageOneBased_certificate :
    retractionRepresentativeImageOneBased = [1, 1, 3, 4, 5] := by
  decide

def retractToSourceOneBased : List Nat :=
  List.ofFn fun b : Fin 5 => (inflation.retract b).val + 1

theorem retractToSourceOneBased_certificate :
    retractToSourceOneBased = [1, 1, 2, 3, 4] := by
  decide

def outside : Fin 5 := 1

theorem outsideOneBased_certificate :
    outside.val + 1 = 2 := by
  decide

theorem proper : inflation.Proper := by
  refine ⟨outside, ?_⟩
  intro a
  exact by decide +revert

theorem representative_basis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_917.table.semigroup
      SemigroupBasis.S5_917Inflation.basis :=
  SemigroupBasis.Inflation.inheritS5_917Basis
    inflation proper source_basis

theorem opposite_basis :
    BasisFor
      SemigroupBasis.Generated.Catalogue.S5_917.table.semigroup.opposite
      (reversedBasis SemigroupBasis.S5_917Inflation.basis) :=
  representative_basis.oppositeReversed

end S5_917

end SemigroupBasis.Generated.S5_917InflationTransfers
