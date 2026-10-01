import SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_5346
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6DirectPowerUnlockedV3.S6_5346_A53054f0117f9_Part01

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S6_5365
namespace S6_5365

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,6],[1,1,1,1,1,6],[1,1,1,1,2,6],[1,1,1,2,1,6],[1,1,2,2,3,6],[6,6,6,6,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (1 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (2 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "a8f175f3bd7f8d7c5a3727a0de4daafa6c20b60987bdd66f68b2fec6181d2a06"

/-- Exact one-based coordinate maps: `[[1,1,1,2,1,1],[1,1,1,1,2,1],[1,1,2,1,4,1],[1,2,3,4,5,1],[6,6,6,6,6,1]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,1,1,2,1,1],[1,1,1,1,2,1],[1,1,2,1,4,1],[1,2,3,4,5,1],[6,6,6,6,6,1]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,1,1,2,1,1],[1,1,1,1,2,1],[1,1,2,1,4,1],[1,2,3,4,5,1],[6,6,6,6,6,1]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (1 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (1 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 0 then (5 : Fin 6) else if a = 1 then (5 : Fin 6) else if a = 2 then (5 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (5 : Fin 6) else (0 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_5346.representativeSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_5346.representativeSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

private def basisVariable (value : Nat) : Fin 4 :=
  if value = 0 then (0 : Fin 4) else if value = 1 then (1 : Fin 4) else if value = 2 then (2 : Fin 4) else (3 : Fin 4)

theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_5346.representativeBasis) :=
  FiniteCertificate.checkModels_sound
    table (SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_5346.representativeBasis) basisVariable (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_5346.representativeBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_5346.representative_basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_5346.representativeBasis)) :=
  representative_basis.oppositeReversed

end S6_5365
-- END S6_5365

end SemigroupBasis.Generated.Order6DirectPowerUnlockedV3.S6_5346_A53054f0117f9_Part01
