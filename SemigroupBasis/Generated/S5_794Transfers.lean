import SemigroupBasis.CoRoots.S5_794
import SemigroupBasis.Generated.CatalogueOrder5Part07
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace SemigroupBasis.Generated.S5_794Transfers

open SemigroupBasis

namespace S5_794

/-- The seven-element subsemigroup listed by the authoritative square
divisor certificate, in certificate order. -/
def divisorSubMul (a b : Fin 7) : Fin 7 :=
  if a = 0 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (0 : Fin 7) else (0 : Fin 7) else if a = 1 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (0 : Fin 7) else (1 : Fin 7) else if a = 2 then if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (1 : Fin 7) else if b = 5 then (2 : Fin 7) else (2 : Fin 7) else if a = 3 then if b = 0 then (3 : Fin 7) else if b = 1 then (3 : Fin 7) else if b = 2 then (3 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (3 : Fin 7) else if b = 5 then (3 : Fin 7) else (3 : Fin 7) else if a = 4 then if b = 0 then (3 : Fin 7) else if b = 1 then (3 : Fin 7) else if b = 2 then (3 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (3 : Fin 7) else if b = 5 then (3 : Fin 7) else (4 : Fin 7) else if a = 5 then if b = 0 then (3 : Fin 7) else if b = 1 then (4 : Fin 7) else if b = 2 then (5 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (5 : Fin 7) else (5 : Fin 7) else if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (5 : Fin 7) else (6 : Fin 7)

def divisorSubTable : FiniteTable where
  order := 7
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 7) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (3 : Fin 5) else if a = 4 then (3 : Fin 5) else if a = 5 then (3 : Fin 5) else (4 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (1 : Fin 5) else if a = 5 then (2 : Fin 5) else (4 : Fin 5)
  map_mul := by
    intro a b
    funext i
    exact by decide +revert
  injective := by
    intro a b equality
    have first := congrFun equality (0 : Fin 2)
    have second := congrFun equality (1 : Fin 2)
    clear equality
    exact by decide +revert

def divisorQuotient :
    SplitSurjection divisorSubTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup where
  toFun := fun a : Fin 7 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (0 : Fin 5) else if a = 4 then (1 : Fin 5) else if a = 5 then (3 : Fin 5) else (4 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (5 : Fin 7) else (6 : Fin 7)
  right_inverse := by
    intro b
    exact by decide +revert

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup SemigroupBasis.CoRoots.S5_794.basis :=
  SemigroupBasis.CoRoots.S5_794.models_of_finite_checks
    SemigroupBasis.Generated.Catalogue.S5_794.table (by decide)

/-- The exact divisor-of-square transfer. The only premise is the missing
published-root completeness theorem for `S5_802`. -/
theorem representativeBasisFor_of_root
    (rootBasis :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup SemigroupBasis.CoRoots.S5_794.basis) :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup SemigroupBasis.CoRoots.S5_794.basis :=
  rootBasis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels

theorem oppositeBasisFor_of_root
    (rootBasis :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup SemigroupBasis.CoRoots.S5_794.basis) :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_794.table.semigroup.opposite SemigroupBasis.CoRoots.S5_794.oppositeBasis :=
  (representativeBasisFor_of_root rootBasis).oppositeReversed

end S5_794

namespace S5_810

/-- The seven-element subsemigroup listed by the authoritative square
divisor certificate, in certificate order. -/
def divisorSubMul (a b : Fin 7) : Fin 7 :=
  if a = 0 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (0 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (0 : Fin 7) else (0 : Fin 7) else if a = 1 then if b = 0 then (0 : Fin 7) else if b = 1 then (0 : Fin 7) else if b = 2 then (0 : Fin 7) else if b = 3 then (1 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (0 : Fin 7) else (0 : Fin 7) else if a = 2 then if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (2 : Fin 7) else if b = 4 then (0 : Fin 7) else if b = 5 then (1 : Fin 7) else (2 : Fin 7) else if a = 3 then if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (3 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (5 : Fin 7) else (6 : Fin 7) else if a = 4 then if b = 0 then (4 : Fin 7) else if b = 1 then (4 : Fin 7) else if b = 2 then (4 : Fin 7) else if b = 3 then (4 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (4 : Fin 7) else (4 : Fin 7) else if a = 5 then if b = 0 then (4 : Fin 7) else if b = 1 then (4 : Fin 7) else if b = 2 then (4 : Fin 7) else if b = 3 then (5 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (4 : Fin 7) else (4 : Fin 7) else if b = 0 then (4 : Fin 7) else if b = 1 then (5 : Fin 7) else if b = 2 then (6 : Fin 7) else if b = 3 then (6 : Fin 7) else if b = 4 then (4 : Fin 7) else if b = 5 then (5 : Fin 7) else (6 : Fin 7)

def divisorSubTable : FiniteTable where
  order := 7
  mul := divisorSubMul
  assoc := by decide

def divisorSubEmbedding :
    Embedding divisorSubTable.semigroup
      (SemigroupBasis.Generated.Catalogue.S5_810.table.semigroup.pi (Fin 2)) where
  toFun := fun (a : Fin 7) (i : Fin 2) =>
    if i = 0 then if a = 0 then (0 : Fin 5) else if a = 1 then (0 : Fin 5) else if a = 2 then (0 : Fin 5) else if a = 3 then (2 : Fin 5) else if a = 4 then (3 : Fin 5) else if a = 5 then (3 : Fin 5) else (3 : Fin 5) else if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (4 : Fin 5) else if a = 4 then (0 : Fin 5) else if a = 5 then (1 : Fin 5) else (2 : Fin 5)
  map_mul := by
    intro a b
    funext i
    exact by decide +revert
  injective := by
    intro a b equality
    have first := congrFun equality (0 : Fin 2)
    have second := congrFun equality (1 : Fin 2)
    clear equality
    exact by decide +revert

def divisorQuotient :
    SplitSurjection divisorSubTable.semigroup
      SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup where
  toFun := fun a : Fin 7 =>
    if a = 0 then (0 : Fin 5) else if a = 1 then (1 : Fin 5) else if a = 2 then (2 : Fin 5) else if a = 3 then (4 : Fin 5) else if a = 4 then (0 : Fin 5) else if a = 5 then (1 : Fin 5) else (3 : Fin 5)
  map_mul := by decide
  preimage := fun b : Fin 5 =>
    if b = 0 then (0 : Fin 7) else if b = 1 then (1 : Fin 7) else if b = 2 then (2 : Fin 7) else if b = 3 then (6 : Fin 7) else (3 : Fin 7)
  right_inverse := by
    intro b
    exact by decide +revert

theorem targetModels :
    Models SemigroupBasis.Generated.Catalogue.S5_810.table.semigroup SemigroupBasis.CoRoots.S5_794.basis :=
  SemigroupBasis.CoRoots.S5_794.models_of_finite_checks
    SemigroupBasis.Generated.Catalogue.S5_810.table (by decide)

/-- The exact divisor-of-square transfer. The only premise is the missing
published-root completeness theorem for `S5_802`. -/
theorem representativeBasisFor_of_root
    (rootBasis :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup SemigroupBasis.CoRoots.S5_794.basis) :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_810.table.semigroup SemigroupBasis.CoRoots.S5_794.basis :=
  rootBasis.inheritAlongPowerDivisor
    divisorSubEmbedding divisorQuotient targetModels

theorem oppositeBasisFor_of_root
    (rootBasis :
      BasisFor SemigroupBasis.Generated.Catalogue.S5_802.table.semigroup SemigroupBasis.CoRoots.S5_794.basis) :
    BasisFor SemigroupBasis.Generated.Catalogue.S5_810.table.semigroup.opposite SemigroupBasis.CoRoots.S5_794.oppositeBasis :=
  (representativeBasisFor_of_root rootBasis).oppositeReversed

end S5_810

end SemigroupBasis.Generated.S5_794Transfers
