import SemigroupBasis.Generated.Order6FactorPairS3_16SharedSevenLawTargets
import SemigroupBasis.FiniteCertificate
import SemigroupBasis.TransferPower

set_option maxRecDepth 100000

namespace SemigroupBasis.Generated.Order6OverlookedExisting63FanoutV1.S6_14263

open SemigroupBasis

def routeRowSHA256 : String := "1157fbffc5e8bca5f4b98e70a7f28d66670879905f9981bba644a12ceca51327"
def witnessRecordSHA256 : String := "c891bb4511223cf7fd6882d24509278244383428671de0251794bf6eab989ea7"
def sourceTableSHA256 : String := "986ae856119b8029471cfce7e22b010ff01f773836a98f73d85225deb8cc928d"
def targetTableSHA256 : String := "45ec02c9d9bc8ba0c760100a7a476ede771d0fdff1b35b5b2f17dfa0da7af71a"

/-- Exact selected representative table, one-based: `[[1,1,1,1,5,6],[1,1,1,2,5,6],[3,3,3,3,5,6],[1,2,3,4,5,6],[5,5,5,5,5,6],[6,6,6,6,5,6]]`. -/
def mul (a b : Fin 6) : Fin 6 :=
  if a = 0 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (0 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 1 then if b = 0 then (0 : Fin 6) else if b = 1 then (0 : Fin 6) else if b = 2 then (0 : Fin 6) else if b = 3 then (1 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 2 then if b = 0 then (2 : Fin 6) else if b = 1 then (2 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (2 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 3 then if b = 0 then (0 : Fin 6) else if b = 1 then (1 : Fin 6) else if b = 2 then (2 : Fin 6) else if b = 3 then (3 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if a = 4 then if b = 0 then (4 : Fin 6) else if b = 1 then (4 : Fin 6) else if b = 2 then (4 : Fin 6) else if b = 3 then (4 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6) else if b = 0 then (5 : Fin 6) else if b = 1 then (5 : Fin 6) else if b = 2 then (5 : Fin 6) else if b = 3 then (5 : Fin 6) else if b = 4 then (4 : Fin 6) else (5 : Fin 6)

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

/-- Exact one-based source-to-target coordinate maps: `[[1,1,1,4,1,1],[1,2,1,4,1,1],[4,4,4,4,1,1],[3,3,1,4,5,5],[6,6,6,1,6,5]]`. -/
def recordedHomomorphismsOneBased : List (List Nat) :=
  [[1,1,1,4,1,1],[1,2,1,4,1,1],[4,4,4,4,1,1],[3,3,1,4,5,5],[6,6,6,1,6,5]]

theorem recordedHomomorphismsOneBased_certificate :
    recordedHomomorphismsOneBased = [[1,1,1,4,1,1],[1,2,1,4,1,1],[4,4,4,4,1,1],[3,3,1,4,5,5],[6,6,6,1,6,5]] := by decide

def coordinateValue (i : Fin 5) (a : Fin 6) : Fin 6 :=
  if i = 0 then if a = 0 then (0 : Fin 6) else if a = 1 then (0 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 1 then if a = 0 then (0 : Fin 6) else if a = 1 then (1 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 2 then if a = 0 then (3 : Fin 6) else if a = 1 then (3 : Fin 6) else if a = 2 then (3 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (0 : Fin 6) else (0 : Fin 6) else if i = 3 then if a = 0 then (2 : Fin 6) else if a = 1 then (2 : Fin 6) else if a = 2 then (0 : Fin 6) else if a = 3 then (3 : Fin 6) else if a = 4 then (4 : Fin 6) else (4 : Fin 6) else if a = 0 then (5 : Fin 6) else if a = 1 then (5 : Fin 6) else if a = 2 then (5 : Fin 6) else if a = 3 then (0 : Fin 6) else if a = 4 then (5 : Fin 6) else (4 : Fin 6)

def coordinateHom (i : Fin 5) :
    Hom SemigroupBasis.Generated.Order6FactorPairS3_16SharedSevenLawTargets.S6_14262.table.semigroup table.semigroup where
  toFun := coordinateValue i
  map_mul := by
    intro a b
    apply Fin.ext
    revert i a b
    decide

def sourceEmbedding :
    Embedding SemigroupBasis.Generated.Order6FactorPairS3_16SharedSevenLawTargets.S6_14262.table.semigroup
      (table.semigroup.pi (Fin 5)) :=
  Embedding.ofSeparatingHoms coordinateHom (by
    intro a b equalCoordinates
    revert a b
    decide)

private def basisVariable (value : Nat) : Fin 3 :=
  if value = 0 then (0 : Fin 3) else if value = 1 then (1 : Fin 3) else (2 : Fin 3)

theorem targetModels : Models table.semigroup SemigroupBasis.Generated.Order6FactorPairS3_16SharedSevenLawTargets.S6_14262.basis :=
  FiniteCertificate.checkModels_sound
    table SemigroupBasis.Generated.Order6FactorPairS3_16SharedSevenLawTargets.S6_14262.basis basisVariable (by decide)

theorem representative_basis : BasisFor table.semigroup SemigroupBasis.Generated.Order6FactorPairS3_16SharedSevenLawTargets.S6_14262.basis :=
  BasisFor.inheritAlongPowerEmbedding
    SemigroupBasis.Generated.Order6FactorPairS3_16SharedSevenLawTargets.S6_14262.representative_basis sourceEmbedding targetModels

theorem opposite_basis :
    BasisFor table.semigroup.opposite
      (reversedBasis SemigroupBasis.Generated.Order6FactorPairS3_16SharedSevenLawTargets.S6_14262.basis) :=
  representative_basis.oppositeReversed

end SemigroupBasis.Generated.Order6OverlookedExisting63FanoutV1.S6_14263
