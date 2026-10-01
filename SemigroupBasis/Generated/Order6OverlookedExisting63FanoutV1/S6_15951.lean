import SemigroupBasis.Generated.Order6FactorPairS3_18S4_20Targets
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace SemigroupBasis.Generated.Order6OverlookedExisting63FanoutV1.S6_15951

open SemigroupBasis

def routeRowSHA256 : String := "3a902d63b4e1c84b49f292cee302ec9ad6cabf12cdff810fd81d9ec37f3a2034"
def witnessRecordSHA256 : String := "7ee6f3e4f926213bc1a518b54a44769e1ff95c2410469b7416eff7250f977247"
def sourceTableSHA256 : String := "f87d423c94d89840c5a3068b0e8749e231c89ff76f732e14fcf2ea0457699a8e"
def targetTableSHA256 : String := "e99418cd4a3aeda95d25573e59134daf5176b6d0d13fb733b956f02659043930"

/-- Exact selected representative table, one-based: `[[1,1,3,4,4,3],[1,2,3,4,4,6],[3,3,4,1,1,4],[4,4,1,3,3,1],[4,5,1,3,3,1],[3,3,4,1,1,4]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (2 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6) else if a = 3 then if b = 0 then (3 : Fin 6) else if b = 1 then (3 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if a = 4 then if b = 0 then (3 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (0 : Fin 6) else if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (3 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (3 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- Exact one-based source-to-target coordinate maps: `[[1,2,1,1,1,1],[1,1,4,3,3,3],[1,2,3,4,5,4],[1,2,4,3,3,6]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,2,1,1,1,1],[1,1,4,3,3,3],[1,2,3,4,5,4],[1,2,4,3,3,6]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,2,1,1,1,1],[1,1,4,3,3,3],[1,2,3,4,5,4],[1,2,4,3,3,6]] := by decide

def coordinateValue (i : Fin 4) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (2 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (2 : Fin 6) else if a = 4 then (2 : Fin 6) else (5 : Fin 6)

def coordinateHom (i : Fin 4) :
    Hom SemigroupBasis.Generated.Order6FactorPairS3_18S4_20Targets.S6_15941.table.semigroup table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding SemigroupBasis.Generated.Order6FactorPairS3_18S4_20Targets.S6_15941.table.semigroup
      (table.semigroup.pi (Fin 4)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

private def basisVariable (value : Nat) : Fin 4 :=
  if value = 0 then (0 : Fin 4) else if value = 1 then (1 : Fin 4) else if value = 2 then (2 : Fin 4) else (3 : Fin 4)

theorem targetModels : Models table.semigroup SemigroupBasis.Generated.Order6FactorPairS3_18S4_20Targets.S6_15941.basis :=
  FiniteCertificate.checkModels_sound
    table SemigroupBasis.Generated.Order6FactorPairS3_18S4_20Targets.S6_15941.basis basisVariable (by decide)

theorem representative_basis : BasisFor table.semigroup SemigroupBasis.Generated.Order6FactorPairS3_18S4_20Targets.S6_15941.basis :=
  BasisFor.inheritAlongPowerEmbedding
    SemigroupBasis.Generated.Order6FactorPairS3_18S4_20Targets.S6_15941.representative_basis sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis SemigroupBasis.Generated.Order6FactorPairS3_18S4_20Targets.S6_15941.basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6OverlookedExisting63FanoutV1.S6_15951
