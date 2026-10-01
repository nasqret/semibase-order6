import SemigroupBasis.Generated.Order6FactorPairSharedFamilies
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6OverlookedExisting63FanoutV1.S6_13358

open SemigroupBasis

def routeRowSHA256 : String := "8353c381e6b902dc107c521993f88a59f5631b13e2f776497aad33ae31fa31a6"
def witnessRecordSHA256 : String := "fd2a35039f544995b74db4d43be96232c1156fb98ae42f5dc9fb4599de118be2"
def sourceTableSHA256 : String := "5a9a054cef4a5f6203fbaed2838d127c7a8046bbf6e43bd7203bee44e057a2ad"
def targetTableSHA256 : String := "5a2ef1e5ae2c8bf454aa474d768ae7579810da0995b168b516ebfb989223a1d8"

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,2,2],[1,2,3,1,2,3],[4,4,4,4,4,4],[1,1,1,4,5,5],[1,2,3,4,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (3 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (4 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- Exact one-based source-to-target coordinate maps: `[[1,1,1,1,1,3],[1,1,3,1,1,3],[1,1,1,1,3,3],[1,1,1,4,1,5],[1,2,3,1,5,6]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,1,1,1,1,3],[1,1,3,1,1,3],[1,1,1,1,3,3],[1,1,1,4,1,5],[1,2,3,1,5,6]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,1,1,1,1,3],[1,1,3,1,1,3],[1,1,1,1,3,3],[1,1,1,4,1,5],[1,2,3,1,5,6]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (2 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (2 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (2 : Fin 6) else (2 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (0 : Fin 6) else (4 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (4 : Fin 6) else (5 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom SemigroupBasis.Generated.Order6FactorPairSharedFamilies.S6_13357.table.semigroup table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding SemigroupBasis.Generated.Order6FactorPairSharedFamilies.S6_13357.table.semigroup
      (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

private def basisVariable (value : Nat) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3)

theorem targetModels : Models table.semigroup SemigroupBasis.Generated.Order6FactorPairSharedFamilies.S6_13357.basis :=
  FiniteCertificate.checkModels_sound
    table SemigroupBasis.Generated.Order6FactorPairSharedFamilies.S6_13357.basis basisVariable (by decide)

theorem representative_basis : BasisFor table.semigroup SemigroupBasis.Generated.Order6FactorPairSharedFamilies.S6_13357.basis :=
  BasisFor.inheritAlongPowerEmbedding
    SemigroupBasis.Generated.Order6FactorPairSharedFamilies.S6_13357.representative_basis sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis SemigroupBasis.Generated.Order6FactorPairSharedFamilies.S6_13357.basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6OverlookedExisting63FanoutV1.S6_13358
