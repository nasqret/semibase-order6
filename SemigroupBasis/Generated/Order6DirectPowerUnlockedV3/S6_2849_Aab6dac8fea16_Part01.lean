import SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2849
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.FiniteReflection
import SemigroupBasis.Opposite
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6DirectPowerUnlockedV3.S6_2849_Aab6dac8fea16_Part01

open SemigroupBasis
open SemigroupBasis.Examples

-- BEGIN S6_5398
namespace S6_5398

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,1,1,1,1],[1,1,2,2,1,1],[1,1,1,1,5,6],[1,1,1,1,6,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (5 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "694a32189928e7215c083116476794b2a359afb7af7ca302e921a4f514e63471"

/-- Exact one-based coordinate maps: `[[1,1,2,1,1,1],[1,1,1,1,2,1],[1,2,3,1,4,1],[1,1,1,1,1,5],[5,5,5,6,5,5]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,1,2,1,1,1],[1,1,1,1,2,1],[1,2,3,1,4,1],[1,1,1,1,1,5],[5,5,5,6,5,5]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,1,2,1,1,1],[1,1,1,1,2,1],[1,2,3,1,4,1],[1,1,1,1,1,5],[5,5,5,6,5,5]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (1 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (4 : Fin 6) else if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (4 : Fin 6) else (4 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2849.representativeSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2849.representativeSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

private def basisVariable (value : Nat) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3)

theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2849.representativeBasis) :=
  FiniteCertificate.checkModels_sound
    table (SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2849.representativeBasis) basisVariable (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2849.representativeBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2849.representative_basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2849.representativeBasis)) :=
  representative_basis.oppositeReversed

end S6_5398
-- END S6_5398

-- BEGIN S6_5484
namespace S6_5484

/-- Exact selected representative table, one-based: `[[1,1,1,1,5,6],[1,1,1,1,5,6],[1,1,1,1,5,6],[1,1,2,2,5,6],[5,5,5,5,5,6],[6,6,6,6,6,5]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (1 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (5 : Fin 6) else (4 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def tableSHA256 : String :=
  "121fb9025402e43e0b2878ef56b0e306ef835ee8f5b148e1e7e4fab048a0b9ca"

/-- Exact one-based coordinate maps: `[[1,1,2,1,1,1],[1,1,1,1,2,1],[1,2,3,1,4,1],[5,5,5,5,5,1],[5,5,5,6,5,1]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,1,2,1,1,1],[1,1,1,1,2,1],[1,2,3,1,4,1],[5,5,5,5,5,1],[5,5,5,6,5,1]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,1,2,1,1,1],[1,1,1,1,2,1],[1,2,3,1,4,1],[5,5,5,5,5,1],[5,5,5,6,5,1]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (1 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (1 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (4 : Fin 6) else if a = 4 then (4 : Fin 6) else (0 : Fin 6) else if a = 0 then (4 : Fin 6) else if a = 1 then (4 : Fin 6) else if a = 2 then (4 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (4 : Fin 6) else (0 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom (SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2849.representativeSemigroup) table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding (SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2849.representativeSemigroup) (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

private def basisVariable (value : Nat) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3)

theorem targetModels : Models table.semigroup (SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2849.representativeBasis) :=
  FiniteCertificate.checkModels_sound
    table (SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2849.representativeBasis) basisVariable (by decide)

theorem representative_basis : BasisFor table.semigroup (SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2849.representativeBasis) :=
  BasisFor.inheritAlongPowerEmbedding SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2849.representative_basis_complete sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite (reversedBasis (SemigroupBasis.Generated.Order6DirectPowerUnlockedV3Sources.S6_2849.representativeBasis)) :=
  representative_basis.oppositeReversed

end S6_5484
-- END S6_5484

end SemigroupBasis.Generated.Order6DirectPowerUnlockedV3.S6_2849_Aab6dac8fea16_Part01
