import SemigroupBasis.Generated.Order6FactorPairSharedFamilies
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6OverlookedExisting63FanoutV1.S6_5531

open SemigroupBasis

def routeRowSHA256 : String := "6745bcb98e93359baf389a7ff3d82a77cad0e98a2962dcbbdbec1693de92c548"
def witnessRecordSHA256 : String := "74e65c75887957de109103ad6b7a731c93ea507e87117b0aadc75e8a8c9d1e0d"
def sourceTableSHA256 : String := "8717bd104172fb0cd5db48daeed9afc9f62e95bd3a3fab7b94ca24ff3691a592"
def targetTableSHA256 : String := "eeea151afe0b3d7dc4719d92faf682a52ced3696998b05a93161b63a6c4f3941"

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,2,1,1],[1,1,3,3,5,6],[1,1,3,3,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- Exact one-based source-to-target coordinate maps: `[[1,1,1,2,1,1],[1,2,1,4,1,1],[1,1,1,1,5,5],[1,1,3,1,5,5],[1,1,1,1,6,5]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,1,1,2,1,1],[1,2,1,4,1,1],[1,1,1,1,5,5],[1,1,3,1,5,5],[1,1,1,1,6,5]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,1,1,2,1,1],[1,2,1,4,1,1],[1,1,1,1,5,5],[1,1,3,1,5,5],[1,1,1,1,6,5]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (1 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (4 : Fin 6) else (4 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (5 : Fin 6) else (4 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom SemigroupBasis.Generated.Order6FactorPairSharedFamilies.S6_5525.table.semigroup table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding SemigroupBasis.Generated.Order6FactorPairSharedFamilies.S6_5525.table.semigroup
      (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

private def basisVariable (value : Nat) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3)

theorem targetModels : Models table.semigroup SemigroupBasis.Generated.Order6FactorPairSharedFamilies.S6_5525.basis :=
  FiniteCertificate.checkModels_sound
    table SemigroupBasis.Generated.Order6FactorPairSharedFamilies.S6_5525.basis basisVariable (by decide)

theorem representative_basis : BasisFor table.semigroup SemigroupBasis.Generated.Order6FactorPairSharedFamilies.S6_5525.basis :=
  BasisFor.inheritAlongPowerEmbedding
    SemigroupBasis.Generated.Order6FactorPairSharedFamilies.S6_5525.representative_basis sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis SemigroupBasis.Generated.Order6FactorPairSharedFamilies.S6_5525.basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6OverlookedExisting63FanoutV1.S6_5531
