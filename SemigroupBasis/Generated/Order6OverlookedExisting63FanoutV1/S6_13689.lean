import SemigroupBasis.Generated.Order6FactorPairS3_16SharedSevenLawTargets
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6OverlookedExisting63FanoutV1.S6_13689

open SemigroupBasis

def routeRowSHA256 : String := "bad5091d7b0ec29fee52af508d47d460eaad234ed43597c28273cc58bf26fe76"
def witnessRecordSHA256 : String := "65ad67e0047fa304d1412bdf78fdb01512174260c9d5cbe114351f9f24618969"
def sourceTableSHA256 : String := "a31a8ea69f03636afd940489a9cdbde822ca7e47ad9c9fa534fad4bf34d883db"
def targetTableSHA256 : String := "5ff82acc15d1efe2ca0b7db05f4620a05798d157571c44074dfe87eac12e7cc1"

/-- Exact selected representative table, one-based: `[[1,1,1,1,1,1],[1,1,1,2,2,2],[3,3,3,3,3,3],[1,1,3,4,4,6],[1,2,3,4,5,6],[1,1,3,4,6,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (0 : Fin 6) else (0 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (1 : Fin 6) else (1 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (2 : Fin 6) else (2 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (3 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (5 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- Exact one-based source-to-target coordinate maps: `[[1,1,1,1,4,1],[1,1,3,1,4,1],[1,1,1,4,4,4],[1,2,1,4,5,4],[1,1,1,6,5,4]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,1,1,1,4,1],[1,1,3,1,4,1],[1,1,1,4,4,4],[1,2,1,4,5,4],[1,1,1,6,5,4]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,1,1,1,4,1],[1,1,3,1,4,1],[1,1,1,4,4,4],[1,2,1,4,5,4],[1,1,1,6,5,4]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (2 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (3 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (3 : Fin 6) else (3 : Fin 6) else if i = 3 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (3 : Fin 6) else if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (5 : Fin 6) else if a = 4 then (4 : Fin 6) else (3 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom SemigroupBasis.Generated.Order6FactorPairS3_16SharedSevenLawTargets.S6_13668.table.semigroup table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding SemigroupBasis.Generated.Order6FactorPairS3_16SharedSevenLawTargets.S6_13668.table.semigroup
      (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

private def basisVariable (value : Nat) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3)

theorem targetModels : Models table.semigroup SemigroupBasis.Generated.Order6FactorPairS3_16SharedSevenLawTargets.S6_13668.basis :=
  FiniteCertificate.checkModels_sound
    table SemigroupBasis.Generated.Order6FactorPairS3_16SharedSevenLawTargets.S6_13668.basis basisVariable (by decide)

theorem representative_basis : BasisFor table.semigroup SemigroupBasis.Generated.Order6FactorPairS3_16SharedSevenLawTargets.S6_13668.basis :=
  BasisFor.inheritAlongPowerEmbedding
    SemigroupBasis.Generated.Order6FactorPairS3_16SharedSevenLawTargets.S6_13668.representative_basis sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis SemigroupBasis.Generated.Order6FactorPairS3_16SharedSevenLawTargets.S6_13668.basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6OverlookedExisting63FanoutV1.S6_13689
