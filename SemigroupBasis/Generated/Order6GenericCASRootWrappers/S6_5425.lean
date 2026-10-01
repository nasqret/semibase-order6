import SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_2850
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6GenericCASRootWrappers.S6_5425

open SemigroupBasis

def routeManifestRowSHA256 : String := "896fc776612bace68b78ecf88ac285f3963833243324c54f18c31e4faeac2a26"
def witnessRecordSHA256 : String := "6b36a6f7aa6c3101009329ff381685b18eaba04b5d41d8e56831f92d5fba5f04"
def transferComponentSHA256 : String := "3da1f0f085698cad174dcbcb3c0d173e070fed597b09fd3e4c5da751f8e4c878"
def powerCertificateSHA256 : String := "0b926e72788e8f760c6c883675fde99a727bf073a78dd2e42a941e2753984a87"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 0 0 0 right else
    if left = 1 then row6 0 0 0 0 0 0 right else
      if left = 2 then row6 0 0 0 0 2 2 right else
        if left = 3 then row6 0 0 0 1 2 2 right else
          if left = 4 then row6 0 0 2 2 4 5 right else
            row6 0 0 2 2 5 4 right

def table : FiniteTable where
  order := 6
  mul := mul
  assoc := by decide

def oppositeTable : FiniteTable where
  order := 6
  mul := fun left right => mul right left
  assoc := by decide

theorem oppositeTable_semigroup :
    oppositeTable.semigroup = table.semigroup.opposite :=
  rfl

def targetTableSHA256 : String :=
  "51bb4fa731324f0b14d45d3ec57bf04c4f654a5b360dc89100a2732340d86c9c"

private def stateVectorChunk0 (index : Nat)
    (coordinate : Fin 11) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)

private def stateVectorChunk1 (index : Nat)
    (coordinate : Fin 11) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)

private def stateVectorChunk2 (index : Nat)
    (coordinate : Fin 11) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)

private def stateVectorChunk3 (index : Nat)
    (coordinate : Fin 11) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)

private def stateVectorChunk4 (index : Nat)
    (coordinate : Fin 11) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)

private def stateVectorChunk5 (index : Nat)
    (coordinate : Fin 11) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)

private def stateVectorChunk6 (index : Nat)
    (coordinate : Fin 11) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)

private def stateVectorChunk7 (index : Nat)
    (coordinate : Fin 11) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)

private def stateVectorChunk8 (index : Nat)
    (coordinate : Fin 11) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (5 : Fin 6)

def stateVector (state : Fin 259)
    (coordinate : Fin 11) : Fin 6 :=
  if state.val < 32 then stateVectorChunk0 state.val coordinate else
    if state.val < 64 then stateVectorChunk1 (state.val - 32) coordinate else
      if state.val < 96 then stateVectorChunk2 (state.val - 64) coordinate else
        if state.val < 128 then stateVectorChunk3 (state.val - 96) coordinate else
          if state.val < 160 then stateVectorChunk4 (state.val - 128) coordinate else
            if state.val < 192 then stateVectorChunk5 (state.val - 160) coordinate else
              if state.val < 224 then stateVectorChunk6 (state.val - 192) coordinate else
                if state.val < 256 then stateVectorChunk7 (state.val - 224) coordinate else
                  stateVectorChunk8 (state.val - 256) coordinate

def generatorVector (generator : Fin 4)
    (coordinate : Fin 11) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | _ => (4 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | _ => (4 : Fin 6)

private def transitionChunk0 (index : Nat)
    (generator : Fin 4) : Fin 259 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (4 : Fin 259)
      | 1 => (5 : Fin 259)
      | 2 => (6 : Fin 259)
      | _ => (7 : Fin 259)
  | 1 =>
      match generator.val with
      | 0 => (5 : Fin 259)
      | 1 => (8 : Fin 259)
      | 2 => (9 : Fin 259)
      | _ => (10 : Fin 259)
  | 2 =>
      match generator.val with
      | 0 => (6 : Fin 259)
      | 1 => (9 : Fin 259)
      | 2 => (11 : Fin 259)
      | _ => (12 : Fin 259)
  | 3 =>
      match generator.val with
      | 0 => (7 : Fin 259)
      | 1 => (10 : Fin 259)
      | 2 => (12 : Fin 259)
      | _ => (13 : Fin 259)
  | 4 =>
      match generator.val with
      | 0 => (14 : Fin 259)
      | 1 => (15 : Fin 259)
      | 2 => (16 : Fin 259)
      | _ => (17 : Fin 259)
  | 5 =>
      match generator.val with
      | 0 => (15 : Fin 259)
      | 1 => (18 : Fin 259)
      | 2 => (19 : Fin 259)
      | _ => (20 : Fin 259)
  | 6 =>
      match generator.val with
      | 0 => (16 : Fin 259)
      | 1 => (19 : Fin 259)
      | 2 => (21 : Fin 259)
      | _ => (22 : Fin 259)
  | 7 =>
      match generator.val with
      | 0 => (17 : Fin 259)
      | 1 => (20 : Fin 259)
      | 2 => (22 : Fin 259)
      | _ => (23 : Fin 259)
  | 8 =>
      match generator.val with
      | 0 => (18 : Fin 259)
      | 1 => (24 : Fin 259)
      | 2 => (25 : Fin 259)
      | _ => (26 : Fin 259)
  | 9 =>
      match generator.val with
      | 0 => (19 : Fin 259)
      | 1 => (25 : Fin 259)
      | 2 => (27 : Fin 259)
      | _ => (28 : Fin 259)
  | 10 =>
      match generator.val with
      | 0 => (20 : Fin 259)
      | 1 => (26 : Fin 259)
      | 2 => (28 : Fin 259)
      | _ => (29 : Fin 259)
  | 11 =>
      match generator.val with
      | 0 => (21 : Fin 259)
      | 1 => (27 : Fin 259)
      | 2 => (30 : Fin 259)
      | _ => (31 : Fin 259)
  | 12 =>
      match generator.val with
      | 0 => (22 : Fin 259)
      | 1 => (28 : Fin 259)
      | 2 => (31 : Fin 259)
      | _ => (32 : Fin 259)
  | 13 =>
      match generator.val with
      | 0 => (23 : Fin 259)
      | 1 => (29 : Fin 259)
      | 2 => (32 : Fin 259)
      | _ => (33 : Fin 259)
  | 14 =>
      match generator.val with
      | 0 => (34 : Fin 259)
      | 1 => (35 : Fin 259)
      | 2 => (36 : Fin 259)
      | _ => (37 : Fin 259)
  | 15 =>
      match generator.val with
      | 0 => (35 : Fin 259)
      | 1 => (38 : Fin 259)
      | 2 => (39 : Fin 259)
      | _ => (40 : Fin 259)
  | 16 =>
      match generator.val with
      | 0 => (36 : Fin 259)
      | 1 => (39 : Fin 259)
      | 2 => (41 : Fin 259)
      | _ => (42 : Fin 259)
  | 17 =>
      match generator.val with
      | 0 => (37 : Fin 259)
      | 1 => (40 : Fin 259)
      | 2 => (42 : Fin 259)
      | _ => (43 : Fin 259)
  | 18 =>
      match generator.val with
      | 0 => (38 : Fin 259)
      | 1 => (44 : Fin 259)
      | 2 => (45 : Fin 259)
      | _ => (46 : Fin 259)
  | 19 =>
      match generator.val with
      | 0 => (39 : Fin 259)
      | 1 => (45 : Fin 259)
      | 2 => (47 : Fin 259)
      | _ => (48 : Fin 259)
  | 20 =>
      match generator.val with
      | 0 => (40 : Fin 259)
      | 1 => (46 : Fin 259)
      | 2 => (48 : Fin 259)
      | _ => (49 : Fin 259)
  | 21 =>
      match generator.val with
      | 0 => (41 : Fin 259)
      | 1 => (47 : Fin 259)
      | 2 => (50 : Fin 259)
      | _ => (51 : Fin 259)
  | 22 =>
      match generator.val with
      | 0 => (42 : Fin 259)
      | 1 => (48 : Fin 259)
      | 2 => (51 : Fin 259)
      | _ => (52 : Fin 259)
  | 23 =>
      match generator.val with
      | 0 => (43 : Fin 259)
      | 1 => (49 : Fin 259)
      | 2 => (52 : Fin 259)
      | _ => (53 : Fin 259)
  | 24 =>
      match generator.val with
      | 0 => (44 : Fin 259)
      | 1 => (54 : Fin 259)
      | 2 => (55 : Fin 259)
      | _ => (56 : Fin 259)
  | 25 =>
      match generator.val with
      | 0 => (45 : Fin 259)
      | 1 => (55 : Fin 259)
      | 2 => (57 : Fin 259)
      | _ => (58 : Fin 259)
  | 26 =>
      match generator.val with
      | 0 => (46 : Fin 259)
      | 1 => (56 : Fin 259)
      | 2 => (58 : Fin 259)
      | _ => (59 : Fin 259)
  | 27 =>
      match generator.val with
      | 0 => (47 : Fin 259)
      | 1 => (57 : Fin 259)
      | 2 => (60 : Fin 259)
      | _ => (61 : Fin 259)
  | 28 =>
      match generator.val with
      | 0 => (48 : Fin 259)
      | 1 => (58 : Fin 259)
      | 2 => (61 : Fin 259)
      | _ => (62 : Fin 259)
  | 29 =>
      match generator.val with
      | 0 => (49 : Fin 259)
      | 1 => (59 : Fin 259)
      | 2 => (62 : Fin 259)
      | _ => (63 : Fin 259)
  | 30 =>
      match generator.val with
      | 0 => (50 : Fin 259)
      | 1 => (60 : Fin 259)
      | 2 => (64 : Fin 259)
      | _ => (65 : Fin 259)
  | _ =>
      match generator.val with
      | 0 => (51 : Fin 259)
      | 1 => (61 : Fin 259)
      | 2 => (65 : Fin 259)
      | _ => (66 : Fin 259)

private def transitionChunk1 (index : Nat)
    (generator : Fin 4) : Fin 259 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (52 : Fin 259)
      | 1 => (62 : Fin 259)
      | 2 => (66 : Fin 259)
      | _ => (67 : Fin 259)
  | 1 =>
      match generator.val with
      | 0 => (53 : Fin 259)
      | 1 => (63 : Fin 259)
      | 2 => (67 : Fin 259)
      | _ => (68 : Fin 259)
  | 2 =>
      match generator.val with
      | 0 => (14 : Fin 259)
      | 1 => (15 : Fin 259)
      | 2 => (16 : Fin 259)
      | _ => (17 : Fin 259)
  | 3 =>
      match generator.val with
      | 0 => (15 : Fin 259)
      | 1 => (69 : Fin 259)
      | 2 => (70 : Fin 259)
      | _ => (71 : Fin 259)
  | 4 =>
      match generator.val with
      | 0 => (16 : Fin 259)
      | 1 => (70 : Fin 259)
      | 2 => (72 : Fin 259)
      | _ => (73 : Fin 259)
  | 5 =>
      match generator.val with
      | 0 => (17 : Fin 259)
      | 1 => (71 : Fin 259)
      | 2 => (73 : Fin 259)
      | _ => (74 : Fin 259)
  | 6 =>
      match generator.val with
      | 0 => (69 : Fin 259)
      | 1 => (75 : Fin 259)
      | 2 => (76 : Fin 259)
      | _ => (77 : Fin 259)
  | 7 =>
      match generator.val with
      | 0 => (70 : Fin 259)
      | 1 => (76 : Fin 259)
      | 2 => (78 : Fin 259)
      | _ => (79 : Fin 259)
  | 8 =>
      match generator.val with
      | 0 => (71 : Fin 259)
      | 1 => (77 : Fin 259)
      | 2 => (79 : Fin 259)
      | _ => (80 : Fin 259)
  | 9 =>
      match generator.val with
      | 0 => (72 : Fin 259)
      | 1 => (78 : Fin 259)
      | 2 => (81 : Fin 259)
      | _ => (82 : Fin 259)
  | 10 =>
      match generator.val with
      | 0 => (73 : Fin 259)
      | 1 => (79 : Fin 259)
      | 2 => (82 : Fin 259)
      | _ => (83 : Fin 259)
  | 11 =>
      match generator.val with
      | 0 => (74 : Fin 259)
      | 1 => (80 : Fin 259)
      | 2 => (83 : Fin 259)
      | _ => (84 : Fin 259)
  | 12 =>
      match generator.val with
      | 0 => (75 : Fin 259)
      | 1 => (18 : Fin 259)
      | 2 => (85 : Fin 259)
      | _ => (86 : Fin 259)
  | 13 =>
      match generator.val with
      | 0 => (76 : Fin 259)
      | 1 => (85 : Fin 259)
      | 2 => (87 : Fin 259)
      | _ => (88 : Fin 259)
  | 14 =>
      match generator.val with
      | 0 => (77 : Fin 259)
      | 1 => (86 : Fin 259)
      | 2 => (88 : Fin 259)
      | _ => (89 : Fin 259)
  | 15 =>
      match generator.val with
      | 0 => (78 : Fin 259)
      | 1 => (87 : Fin 259)
      | 2 => (90 : Fin 259)
      | _ => (91 : Fin 259)
  | 16 =>
      match generator.val with
      | 0 => (79 : Fin 259)
      | 1 => (88 : Fin 259)
      | 2 => (91 : Fin 259)
      | _ => (92 : Fin 259)
  | 17 =>
      match generator.val with
      | 0 => (80 : Fin 259)
      | 1 => (89 : Fin 259)
      | 2 => (92 : Fin 259)
      | _ => (93 : Fin 259)
  | 18 =>
      match generator.val with
      | 0 => (81 : Fin 259)
      | 1 => (90 : Fin 259)
      | 2 => (21 : Fin 259)
      | _ => (94 : Fin 259)
  | 19 =>
      match generator.val with
      | 0 => (82 : Fin 259)
      | 1 => (91 : Fin 259)
      | 2 => (94 : Fin 259)
      | _ => (95 : Fin 259)
  | 20 =>
      match generator.val with
      | 0 => (83 : Fin 259)
      | 1 => (92 : Fin 259)
      | 2 => (95 : Fin 259)
      | _ => (96 : Fin 259)
  | 21 =>
      match generator.val with
      | 0 => (84 : Fin 259)
      | 1 => (93 : Fin 259)
      | 2 => (96 : Fin 259)
      | _ => (23 : Fin 259)
  | 22 =>
      match generator.val with
      | 0 => (18 : Fin 259)
      | 1 => (24 : Fin 259)
      | 2 => (25 : Fin 259)
      | _ => (26 : Fin 259)
  | 23 =>
      match generator.val with
      | 0 => (85 : Fin 259)
      | 1 => (25 : Fin 259)
      | 2 => (97 : Fin 259)
      | _ => (98 : Fin 259)
  | 24 =>
      match generator.val with
      | 0 => (86 : Fin 259)
      | 1 => (26 : Fin 259)
      | 2 => (98 : Fin 259)
      | _ => (99 : Fin 259)
  | 25 =>
      match generator.val with
      | 0 => (87 : Fin 259)
      | 1 => (97 : Fin 259)
      | 2 => (100 : Fin 259)
      | _ => (101 : Fin 259)
  | 26 =>
      match generator.val with
      | 0 => (88 : Fin 259)
      | 1 => (98 : Fin 259)
      | 2 => (101 : Fin 259)
      | _ => (102 : Fin 259)
  | 27 =>
      match generator.val with
      | 0 => (89 : Fin 259)
      | 1 => (99 : Fin 259)
      | 2 => (102 : Fin 259)
      | _ => (103 : Fin 259)
  | 28 =>
      match generator.val with
      | 0 => (90 : Fin 259)
      | 1 => (100 : Fin 259)
      | 2 => (27 : Fin 259)
      | _ => (104 : Fin 259)
  | 29 =>
      match generator.val with
      | 0 => (91 : Fin 259)
      | 1 => (101 : Fin 259)
      | 2 => (104 : Fin 259)
      | _ => (105 : Fin 259)
  | 30 =>
      match generator.val with
      | 0 => (92 : Fin 259)
      | 1 => (102 : Fin 259)
      | 2 => (105 : Fin 259)
      | _ => (106 : Fin 259)
  | _ =>
      match generator.val with
      | 0 => (93 : Fin 259)
      | 1 => (103 : Fin 259)
      | 2 => (106 : Fin 259)
      | _ => (29 : Fin 259)

private def transitionChunk2 (index : Nat)
    (generator : Fin 4) : Fin 259 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (21 : Fin 259)
      | 1 => (27 : Fin 259)
      | 2 => (30 : Fin 259)
      | _ => (31 : Fin 259)
  | 1 =>
      match generator.val with
      | 0 => (94 : Fin 259)
      | 1 => (104 : Fin 259)
      | 2 => (31 : Fin 259)
      | _ => (107 : Fin 259)
  | 2 =>
      match generator.val with
      | 0 => (95 : Fin 259)
      | 1 => (105 : Fin 259)
      | 2 => (107 : Fin 259)
      | _ => (108 : Fin 259)
  | 3 =>
      match generator.val with
      | 0 => (96 : Fin 259)
      | 1 => (106 : Fin 259)
      | 2 => (108 : Fin 259)
      | _ => (32 : Fin 259)
  | 4 =>
      match generator.val with
      | 0 => (23 : Fin 259)
      | 1 => (29 : Fin 259)
      | 2 => (32 : Fin 259)
      | _ => (33 : Fin 259)
  | 5 =>
      match generator.val with
      | 0 => (38 : Fin 259)
      | 1 => (109 : Fin 259)
      | 2 => (110 : Fin 259)
      | _ => (111 : Fin 259)
  | 6 =>
      match generator.val with
      | 0 => (39 : Fin 259)
      | 1 => (110 : Fin 259)
      | 2 => (112 : Fin 259)
      | _ => (113 : Fin 259)
  | 7 =>
      match generator.val with
      | 0 => (40 : Fin 259)
      | 1 => (111 : Fin 259)
      | 2 => (113 : Fin 259)
      | _ => (114 : Fin 259)
  | 8 =>
      match generator.val with
      | 0 => (41 : Fin 259)
      | 1 => (112 : Fin 259)
      | 2 => (115 : Fin 259)
      | _ => (116 : Fin 259)
  | 9 =>
      match generator.val with
      | 0 => (42 : Fin 259)
      | 1 => (113 : Fin 259)
      | 2 => (116 : Fin 259)
      | _ => (117 : Fin 259)
  | 10 =>
      match generator.val with
      | 0 => (43 : Fin 259)
      | 1 => (114 : Fin 259)
      | 2 => (117 : Fin 259)
      | _ => (118 : Fin 259)
  | 11 =>
      match generator.val with
      | 0 => (109 : Fin 259)
      | 1 => (38 : Fin 259)
      | 2 => (119 : Fin 259)
      | _ => (120 : Fin 259)
  | 12 =>
      match generator.val with
      | 0 => (110 : Fin 259)
      | 1 => (119 : Fin 259)
      | 2 => (121 : Fin 259)
      | _ => (122 : Fin 259)
  | 13 =>
      match generator.val with
      | 0 => (111 : Fin 259)
      | 1 => (120 : Fin 259)
      | 2 => (122 : Fin 259)
      | _ => (123 : Fin 259)
  | 14 =>
      match generator.val with
      | 0 => (112 : Fin 259)
      | 1 => (121 : Fin 259)
      | 2 => (124 : Fin 259)
      | _ => (125 : Fin 259)
  | 15 =>
      match generator.val with
      | 0 => (113 : Fin 259)
      | 1 => (122 : Fin 259)
      | 2 => (125 : Fin 259)
      | _ => (126 : Fin 259)
  | 16 =>
      match generator.val with
      | 0 => (114 : Fin 259)
      | 1 => (123 : Fin 259)
      | 2 => (126 : Fin 259)
      | _ => (127 : Fin 259)
  | 17 =>
      match generator.val with
      | 0 => (115 : Fin 259)
      | 1 => (124 : Fin 259)
      | 2 => (41 : Fin 259)
      | _ => (128 : Fin 259)
  | 18 =>
      match generator.val with
      | 0 => (116 : Fin 259)
      | 1 => (125 : Fin 259)
      | 2 => (128 : Fin 259)
      | _ => (129 : Fin 259)
  | 19 =>
      match generator.val with
      | 0 => (117 : Fin 259)
      | 1 => (126 : Fin 259)
      | 2 => (129 : Fin 259)
      | _ => (130 : Fin 259)
  | 20 =>
      match generator.val with
      | 0 => (118 : Fin 259)
      | 1 => (127 : Fin 259)
      | 2 => (130 : Fin 259)
      | _ => (43 : Fin 259)
  | 21 =>
      match generator.val with
      | 0 => (119 : Fin 259)
      | 1 => (45 : Fin 259)
      | 2 => (131 : Fin 259)
      | _ => (132 : Fin 259)
  | 22 =>
      match generator.val with
      | 0 => (120 : Fin 259)
      | 1 => (46 : Fin 259)
      | 2 => (132 : Fin 259)
      | _ => (133 : Fin 259)
  | 23 =>
      match generator.val with
      | 0 => (121 : Fin 259)
      | 1 => (131 : Fin 259)
      | 2 => (134 : Fin 259)
      | _ => (135 : Fin 259)
  | 24 =>
      match generator.val with
      | 0 => (122 : Fin 259)
      | 1 => (132 : Fin 259)
      | 2 => (135 : Fin 259)
      | _ => (136 : Fin 259)
  | 25 =>
      match generator.val with
      | 0 => (123 : Fin 259)
      | 1 => (133 : Fin 259)
      | 2 => (136 : Fin 259)
      | _ => (137 : Fin 259)
  | 26 =>
      match generator.val with
      | 0 => (124 : Fin 259)
      | 1 => (134 : Fin 259)
      | 2 => (47 : Fin 259)
      | _ => (138 : Fin 259)
  | 27 =>
      match generator.val with
      | 0 => (125 : Fin 259)
      | 1 => (135 : Fin 259)
      | 2 => (138 : Fin 259)
      | _ => (139 : Fin 259)
  | 28 =>
      match generator.val with
      | 0 => (126 : Fin 259)
      | 1 => (136 : Fin 259)
      | 2 => (139 : Fin 259)
      | _ => (140 : Fin 259)
  | 29 =>
      match generator.val with
      | 0 => (127 : Fin 259)
      | 1 => (137 : Fin 259)
      | 2 => (140 : Fin 259)
      | _ => (49 : Fin 259)
  | 30 =>
      match generator.val with
      | 0 => (128 : Fin 259)
      | 1 => (138 : Fin 259)
      | 2 => (51 : Fin 259)
      | _ => (141 : Fin 259)
  | _ =>
      match generator.val with
      | 0 => (129 : Fin 259)
      | 1 => (139 : Fin 259)
      | 2 => (141 : Fin 259)
      | _ => (142 : Fin 259)

private def transitionChunk3 (index : Nat)
    (generator : Fin 4) : Fin 259 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (130 : Fin 259)
      | 1 => (140 : Fin 259)
      | 2 => (142 : Fin 259)
      | _ => (52 : Fin 259)
  | 1 =>
      match generator.val with
      | 0 => (131 : Fin 259)
      | 1 => (57 : Fin 259)
      | 2 => (143 : Fin 259)
      | _ => (144 : Fin 259)
  | 2 =>
      match generator.val with
      | 0 => (132 : Fin 259)
      | 1 => (58 : Fin 259)
      | 2 => (144 : Fin 259)
      | _ => (145 : Fin 259)
  | 3 =>
      match generator.val with
      | 0 => (133 : Fin 259)
      | 1 => (59 : Fin 259)
      | 2 => (145 : Fin 259)
      | _ => (146 : Fin 259)
  | 4 =>
      match generator.val with
      | 0 => (134 : Fin 259)
      | 1 => (143 : Fin 259)
      | 2 => (57 : Fin 259)
      | _ => (147 : Fin 259)
  | 5 =>
      match generator.val with
      | 0 => (135 : Fin 259)
      | 1 => (144 : Fin 259)
      | 2 => (147 : Fin 259)
      | _ => (148 : Fin 259)
  | 6 =>
      match generator.val with
      | 0 => (136 : Fin 259)
      | 1 => (145 : Fin 259)
      | 2 => (148 : Fin 259)
      | _ => (149 : Fin 259)
  | 7 =>
      match generator.val with
      | 0 => (137 : Fin 259)
      | 1 => (146 : Fin 259)
      | 2 => (149 : Fin 259)
      | _ => (59 : Fin 259)
  | 8 =>
      match generator.val with
      | 0 => (138 : Fin 259)
      | 1 => (147 : Fin 259)
      | 2 => (61 : Fin 259)
      | _ => (150 : Fin 259)
  | 9 =>
      match generator.val with
      | 0 => (139 : Fin 259)
      | 1 => (148 : Fin 259)
      | 2 => (150 : Fin 259)
      | _ => (151 : Fin 259)
  | 10 =>
      match generator.val with
      | 0 => (140 : Fin 259)
      | 1 => (149 : Fin 259)
      | 2 => (151 : Fin 259)
      | _ => (62 : Fin 259)
  | 11 =>
      match generator.val with
      | 0 => (141 : Fin 259)
      | 1 => (150 : Fin 259)
      | 2 => (66 : Fin 259)
      | _ => (152 : Fin 259)
  | 12 =>
      match generator.val with
      | 0 => (142 : Fin 259)
      | 1 => (151 : Fin 259)
      | 2 => (152 : Fin 259)
      | _ => (66 : Fin 259)
  | 13 =>
      match generator.val with
      | 0 => (75 : Fin 259)
      | 1 => (69 : Fin 259)
      | 2 => (153 : Fin 259)
      | _ => (154 : Fin 259)
  | 14 =>
      match generator.val with
      | 0 => (76 : Fin 259)
      | 1 => (153 : Fin 259)
      | 2 => (155 : Fin 259)
      | _ => (156 : Fin 259)
  | 15 =>
      match generator.val with
      | 0 => (77 : Fin 259)
      | 1 => (154 : Fin 259)
      | 2 => (156 : Fin 259)
      | _ => (157 : Fin 259)
  | 16 =>
      match generator.val with
      | 0 => (78 : Fin 259)
      | 1 => (155 : Fin 259)
      | 2 => (158 : Fin 259)
      | _ => (159 : Fin 259)
  | 17 =>
      match generator.val with
      | 0 => (79 : Fin 259)
      | 1 => (156 : Fin 259)
      | 2 => (159 : Fin 259)
      | _ => (160 : Fin 259)
  | 18 =>
      match generator.val with
      | 0 => (80 : Fin 259)
      | 1 => (157 : Fin 259)
      | 2 => (160 : Fin 259)
      | _ => (161 : Fin 259)
  | 19 =>
      match generator.val with
      | 0 => (81 : Fin 259)
      | 1 => (158 : Fin 259)
      | 2 => (72 : Fin 259)
      | _ => (162 : Fin 259)
  | 20 =>
      match generator.val with
      | 0 => (82 : Fin 259)
      | 1 => (159 : Fin 259)
      | 2 => (162 : Fin 259)
      | _ => (163 : Fin 259)
  | 21 =>
      match generator.val with
      | 0 => (83 : Fin 259)
      | 1 => (160 : Fin 259)
      | 2 => (163 : Fin 259)
      | _ => (164 : Fin 259)
  | 22 =>
      match generator.val with
      | 0 => (84 : Fin 259)
      | 1 => (161 : Fin 259)
      | 2 => (164 : Fin 259)
      | _ => (74 : Fin 259)
  | 23 =>
      match generator.val with
      | 0 => (153 : Fin 259)
      | 1 => (76 : Fin 259)
      | 2 => (165 : Fin 259)
      | _ => (166 : Fin 259)
  | 24 =>
      match generator.val with
      | 0 => (154 : Fin 259)
      | 1 => (77 : Fin 259)
      | 2 => (166 : Fin 259)
      | _ => (167 : Fin 259)
  | 25 =>
      match generator.val with
      | 0 => (155 : Fin 259)
      | 1 => (165 : Fin 259)
      | 2 => (168 : Fin 259)
      | _ => (169 : Fin 259)
  | 26 =>
      match generator.val with
      | 0 => (156 : Fin 259)
      | 1 => (166 : Fin 259)
      | 2 => (169 : Fin 259)
      | _ => (170 : Fin 259)
  | 27 =>
      match generator.val with
      | 0 => (157 : Fin 259)
      | 1 => (167 : Fin 259)
      | 2 => (170 : Fin 259)
      | _ => (171 : Fin 259)
  | 28 =>
      match generator.val with
      | 0 => (158 : Fin 259)
      | 1 => (168 : Fin 259)
      | 2 => (78 : Fin 259)
      | _ => (172 : Fin 259)
  | 29 =>
      match generator.val with
      | 0 => (159 : Fin 259)
      | 1 => (169 : Fin 259)
      | 2 => (172 : Fin 259)
      | _ => (173 : Fin 259)
  | 30 =>
      match generator.val with
      | 0 => (160 : Fin 259)
      | 1 => (170 : Fin 259)
      | 2 => (173 : Fin 259)
      | _ => (174 : Fin 259)
  | _ =>
      match generator.val with
      | 0 => (161 : Fin 259)
      | 1 => (171 : Fin 259)
      | 2 => (174 : Fin 259)
      | _ => (80 : Fin 259)

private def transitionChunk4 (index : Nat)
    (generator : Fin 4) : Fin 259 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (162 : Fin 259)
      | 1 => (172 : Fin 259)
      | 2 => (82 : Fin 259)
      | _ => (175 : Fin 259)
  | 1 =>
      match generator.val with
      | 0 => (163 : Fin 259)
      | 1 => (173 : Fin 259)
      | 2 => (175 : Fin 259)
      | _ => (176 : Fin 259)
  | 2 =>
      match generator.val with
      | 0 => (164 : Fin 259)
      | 1 => (174 : Fin 259)
      | 2 => (176 : Fin 259)
      | _ => (83 : Fin 259)
  | 3 =>
      match generator.val with
      | 0 => (165 : Fin 259)
      | 1 => (87 : Fin 259)
      | 2 => (177 : Fin 259)
      | _ => (178 : Fin 259)
  | 4 =>
      match generator.val with
      | 0 => (166 : Fin 259)
      | 1 => (88 : Fin 259)
      | 2 => (178 : Fin 259)
      | _ => (179 : Fin 259)
  | 5 =>
      match generator.val with
      | 0 => (167 : Fin 259)
      | 1 => (89 : Fin 259)
      | 2 => (179 : Fin 259)
      | _ => (180 : Fin 259)
  | 6 =>
      match generator.val with
      | 0 => (168 : Fin 259)
      | 1 => (177 : Fin 259)
      | 2 => (87 : Fin 259)
      | _ => (181 : Fin 259)
  | 7 =>
      match generator.val with
      | 0 => (169 : Fin 259)
      | 1 => (178 : Fin 259)
      | 2 => (181 : Fin 259)
      | _ => (182 : Fin 259)
  | 8 =>
      match generator.val with
      | 0 => (170 : Fin 259)
      | 1 => (179 : Fin 259)
      | 2 => (182 : Fin 259)
      | _ => (183 : Fin 259)
  | 9 =>
      match generator.val with
      | 0 => (171 : Fin 259)
      | 1 => (180 : Fin 259)
      | 2 => (183 : Fin 259)
      | _ => (89 : Fin 259)
  | 10 =>
      match generator.val with
      | 0 => (172 : Fin 259)
      | 1 => (181 : Fin 259)
      | 2 => (91 : Fin 259)
      | _ => (184 : Fin 259)
  | 11 =>
      match generator.val with
      | 0 => (173 : Fin 259)
      | 1 => (182 : Fin 259)
      | 2 => (184 : Fin 259)
      | _ => (185 : Fin 259)
  | 12 =>
      match generator.val with
      | 0 => (174 : Fin 259)
      | 1 => (183 : Fin 259)
      | 2 => (185 : Fin 259)
      | _ => (92 : Fin 259)
  | 13 =>
      match generator.val with
      | 0 => (175 : Fin 259)
      | 1 => (184 : Fin 259)
      | 2 => (95 : Fin 259)
      | _ => (186 : Fin 259)
  | 14 =>
      match generator.val with
      | 0 => (176 : Fin 259)
      | 1 => (185 : Fin 259)
      | 2 => (186 : Fin 259)
      | _ => (95 : Fin 259)
  | 15 =>
      match generator.val with
      | 0 => (177 : Fin 259)
      | 1 => (100 : Fin 259)
      | 2 => (97 : Fin 259)
      | _ => (187 : Fin 259)
  | 16 =>
      match generator.val with
      | 0 => (178 : Fin 259)
      | 1 => (101 : Fin 259)
      | 2 => (187 : Fin 259)
      | _ => (188 : Fin 259)
  | 17 =>
      match generator.val with
      | 0 => (179 : Fin 259)
      | 1 => (102 : Fin 259)
      | 2 => (188 : Fin 259)
      | _ => (189 : Fin 259)
  | 18 =>
      match generator.val with
      | 0 => (180 : Fin 259)
      | 1 => (103 : Fin 259)
      | 2 => (189 : Fin 259)
      | _ => (99 : Fin 259)
  | 19 =>
      match generator.val with
      | 0 => (181 : Fin 259)
      | 1 => (187 : Fin 259)
      | 2 => (101 : Fin 259)
      | _ => (190 : Fin 259)
  | 20 =>
      match generator.val with
      | 0 => (182 : Fin 259)
      | 1 => (188 : Fin 259)
      | 2 => (190 : Fin 259)
      | _ => (191 : Fin 259)
  | 21 =>
      match generator.val with
      | 0 => (183 : Fin 259)
      | 1 => (189 : Fin 259)
      | 2 => (191 : Fin 259)
      | _ => (102 : Fin 259)
  | 22 =>
      match generator.val with
      | 0 => (184 : Fin 259)
      | 1 => (190 : Fin 259)
      | 2 => (105 : Fin 259)
      | _ => (192 : Fin 259)
  | 23 =>
      match generator.val with
      | 0 => (185 : Fin 259)
      | 1 => (191 : Fin 259)
      | 2 => (192 : Fin 259)
      | _ => (105 : Fin 259)
  | 24 =>
      match generator.val with
      | 0 => (186 : Fin 259)
      | 1 => (192 : Fin 259)
      | 2 => (108 : Fin 259)
      | _ => (107 : Fin 259)
  | 25 =>
      match generator.val with
      | 0 => (119 : Fin 259)
      | 1 => (110 : Fin 259)
      | 2 => (193 : Fin 259)
      | _ => (194 : Fin 259)
  | 26 =>
      match generator.val with
      | 0 => (120 : Fin 259)
      | 1 => (111 : Fin 259)
      | 2 => (194 : Fin 259)
      | _ => (195 : Fin 259)
  | 27 =>
      match generator.val with
      | 0 => (121 : Fin 259)
      | 1 => (193 : Fin 259)
      | 2 => (196 : Fin 259)
      | _ => (197 : Fin 259)
  | 28 =>
      match generator.val with
      | 0 => (122 : Fin 259)
      | 1 => (194 : Fin 259)
      | 2 => (197 : Fin 259)
      | _ => (198 : Fin 259)
  | 29 =>
      match generator.val with
      | 0 => (123 : Fin 259)
      | 1 => (195 : Fin 259)
      | 2 => (198 : Fin 259)
      | _ => (199 : Fin 259)
  | 30 =>
      match generator.val with
      | 0 => (124 : Fin 259)
      | 1 => (196 : Fin 259)
      | 2 => (112 : Fin 259)
      | _ => (200 : Fin 259)
  | _ =>
      match generator.val with
      | 0 => (125 : Fin 259)
      | 1 => (197 : Fin 259)
      | 2 => (200 : Fin 259)
      | _ => (201 : Fin 259)

private def transitionChunk5 (index : Nat)
    (generator : Fin 4) : Fin 259 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (126 : Fin 259)
      | 1 => (198 : Fin 259)
      | 2 => (201 : Fin 259)
      | _ => (202 : Fin 259)
  | 1 =>
      match generator.val with
      | 0 => (127 : Fin 259)
      | 1 => (199 : Fin 259)
      | 2 => (202 : Fin 259)
      | _ => (114 : Fin 259)
  | 2 =>
      match generator.val with
      | 0 => (128 : Fin 259)
      | 1 => (200 : Fin 259)
      | 2 => (116 : Fin 259)
      | _ => (203 : Fin 259)
  | 3 =>
      match generator.val with
      | 0 => (129 : Fin 259)
      | 1 => (201 : Fin 259)
      | 2 => (203 : Fin 259)
      | _ => (204 : Fin 259)
  | 4 =>
      match generator.val with
      | 0 => (130 : Fin 259)
      | 1 => (202 : Fin 259)
      | 2 => (204 : Fin 259)
      | _ => (117 : Fin 259)
  | 5 =>
      match generator.val with
      | 0 => (193 : Fin 259)
      | 1 => (121 : Fin 259)
      | 2 => (205 : Fin 259)
      | _ => (206 : Fin 259)
  | 6 =>
      match generator.val with
      | 0 => (194 : Fin 259)
      | 1 => (122 : Fin 259)
      | 2 => (206 : Fin 259)
      | _ => (207 : Fin 259)
  | 7 =>
      match generator.val with
      | 0 => (195 : Fin 259)
      | 1 => (123 : Fin 259)
      | 2 => (207 : Fin 259)
      | _ => (208 : Fin 259)
  | 8 =>
      match generator.val with
      | 0 => (196 : Fin 259)
      | 1 => (205 : Fin 259)
      | 2 => (121 : Fin 259)
      | _ => (209 : Fin 259)
  | 9 =>
      match generator.val with
      | 0 => (197 : Fin 259)
      | 1 => (206 : Fin 259)
      | 2 => (209 : Fin 259)
      | _ => (210 : Fin 259)
  | 10 =>
      match generator.val with
      | 0 => (198 : Fin 259)
      | 1 => (207 : Fin 259)
      | 2 => (210 : Fin 259)
      | _ => (211 : Fin 259)
  | 11 =>
      match generator.val with
      | 0 => (199 : Fin 259)
      | 1 => (208 : Fin 259)
      | 2 => (211 : Fin 259)
      | _ => (123 : Fin 259)
  | 12 =>
      match generator.val with
      | 0 => (200 : Fin 259)
      | 1 => (209 : Fin 259)
      | 2 => (125 : Fin 259)
      | _ => (212 : Fin 259)
  | 13 =>
      match generator.val with
      | 0 => (201 : Fin 259)
      | 1 => (210 : Fin 259)
      | 2 => (212 : Fin 259)
      | _ => (213 : Fin 259)
  | 14 =>
      match generator.val with
      | 0 => (202 : Fin 259)
      | 1 => (211 : Fin 259)
      | 2 => (213 : Fin 259)
      | _ => (126 : Fin 259)
  | 15 =>
      match generator.val with
      | 0 => (203 : Fin 259)
      | 1 => (212 : Fin 259)
      | 2 => (129 : Fin 259)
      | _ => (214 : Fin 259)
  | 16 =>
      match generator.val with
      | 0 => (204 : Fin 259)
      | 1 => (213 : Fin 259)
      | 2 => (214 : Fin 259)
      | _ => (129 : Fin 259)
  | 17 =>
      match generator.val with
      | 0 => (205 : Fin 259)
      | 1 => (134 : Fin 259)
      | 2 => (131 : Fin 259)
      | _ => (215 : Fin 259)
  | 18 =>
      match generator.val with
      | 0 => (206 : Fin 259)
      | 1 => (135 : Fin 259)
      | 2 => (215 : Fin 259)
      | _ => (216 : Fin 259)
  | 19 =>
      match generator.val with
      | 0 => (207 : Fin 259)
      | 1 => (136 : Fin 259)
      | 2 => (216 : Fin 259)
      | _ => (217 : Fin 259)
  | 20 =>
      match generator.val with
      | 0 => (208 : Fin 259)
      | 1 => (137 : Fin 259)
      | 2 => (217 : Fin 259)
      | _ => (133 : Fin 259)
  | 21 =>
      match generator.val with
      | 0 => (209 : Fin 259)
      | 1 => (215 : Fin 259)
      | 2 => (135 : Fin 259)
      | _ => (218 : Fin 259)
  | 22 =>
      match generator.val with
      | 0 => (210 : Fin 259)
      | 1 => (216 : Fin 259)
      | 2 => (218 : Fin 259)
      | _ => (219 : Fin 259)
  | 23 =>
      match generator.val with
      | 0 => (211 : Fin 259)
      | 1 => (217 : Fin 259)
      | 2 => (219 : Fin 259)
      | _ => (136 : Fin 259)
  | 24 =>
      match generator.val with
      | 0 => (212 : Fin 259)
      | 1 => (218 : Fin 259)
      | 2 => (139 : Fin 259)
      | _ => (220 : Fin 259)
  | 25 =>
      match generator.val with
      | 0 => (213 : Fin 259)
      | 1 => (219 : Fin 259)
      | 2 => (220 : Fin 259)
      | _ => (139 : Fin 259)
  | 26 =>
      match generator.val with
      | 0 => (214 : Fin 259)
      | 1 => (220 : Fin 259)
      | 2 => (142 : Fin 259)
      | _ => (141 : Fin 259)
  | 27 =>
      match generator.val with
      | 0 => (215 : Fin 259)
      | 1 => (147 : Fin 259)
      | 2 => (144 : Fin 259)
      | _ => (221 : Fin 259)
  | 28 =>
      match generator.val with
      | 0 => (216 : Fin 259)
      | 1 => (148 : Fin 259)
      | 2 => (221 : Fin 259)
      | _ => (222 : Fin 259)
  | 29 =>
      match generator.val with
      | 0 => (217 : Fin 259)
      | 1 => (149 : Fin 259)
      | 2 => (222 : Fin 259)
      | _ => (145 : Fin 259)
  | 30 =>
      match generator.val with
      | 0 => (218 : Fin 259)
      | 1 => (221 : Fin 259)
      | 2 => (148 : Fin 259)
      | _ => (223 : Fin 259)
  | _ =>
      match generator.val with
      | 0 => (219 : Fin 259)
      | 1 => (222 : Fin 259)
      | 2 => (223 : Fin 259)
      | _ => (148 : Fin 259)

private def transitionChunk6 (index : Nat)
    (generator : Fin 4) : Fin 259 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (220 : Fin 259)
      | 1 => (223 : Fin 259)
      | 2 => (151 : Fin 259)
      | _ => (150 : Fin 259)
  | 1 =>
      match generator.val with
      | 0 => (165 : Fin 259)
      | 1 => (155 : Fin 259)
      | 2 => (224 : Fin 259)
      | _ => (225 : Fin 259)
  | 2 =>
      match generator.val with
      | 0 => (166 : Fin 259)
      | 1 => (156 : Fin 259)
      | 2 => (225 : Fin 259)
      | _ => (226 : Fin 259)
  | 3 =>
      match generator.val with
      | 0 => (167 : Fin 259)
      | 1 => (157 : Fin 259)
      | 2 => (226 : Fin 259)
      | _ => (227 : Fin 259)
  | 4 =>
      match generator.val with
      | 0 => (168 : Fin 259)
      | 1 => (224 : Fin 259)
      | 2 => (155 : Fin 259)
      | _ => (228 : Fin 259)
  | 5 =>
      match generator.val with
      | 0 => (169 : Fin 259)
      | 1 => (225 : Fin 259)
      | 2 => (228 : Fin 259)
      | _ => (229 : Fin 259)
  | 6 =>
      match generator.val with
      | 0 => (170 : Fin 259)
      | 1 => (226 : Fin 259)
      | 2 => (229 : Fin 259)
      | _ => (230 : Fin 259)
  | 7 =>
      match generator.val with
      | 0 => (171 : Fin 259)
      | 1 => (227 : Fin 259)
      | 2 => (230 : Fin 259)
      | _ => (157 : Fin 259)
  | 8 =>
      match generator.val with
      | 0 => (172 : Fin 259)
      | 1 => (228 : Fin 259)
      | 2 => (159 : Fin 259)
      | _ => (231 : Fin 259)
  | 9 =>
      match generator.val with
      | 0 => (173 : Fin 259)
      | 1 => (229 : Fin 259)
      | 2 => (231 : Fin 259)
      | _ => (232 : Fin 259)
  | 10 =>
      match generator.val with
      | 0 => (174 : Fin 259)
      | 1 => (230 : Fin 259)
      | 2 => (232 : Fin 259)
      | _ => (160 : Fin 259)
  | 11 =>
      match generator.val with
      | 0 => (175 : Fin 259)
      | 1 => (231 : Fin 259)
      | 2 => (163 : Fin 259)
      | _ => (233 : Fin 259)
  | 12 =>
      match generator.val with
      | 0 => (176 : Fin 259)
      | 1 => (232 : Fin 259)
      | 2 => (233 : Fin 259)
      | _ => (163 : Fin 259)
  | 13 =>
      match generator.val with
      | 0 => (224 : Fin 259)
      | 1 => (168 : Fin 259)
      | 2 => (165 : Fin 259)
      | _ => (234 : Fin 259)
  | 14 =>
      match generator.val with
      | 0 => (225 : Fin 259)
      | 1 => (169 : Fin 259)
      | 2 => (234 : Fin 259)
      | _ => (235 : Fin 259)
  | 15 =>
      match generator.val with
      | 0 => (226 : Fin 259)
      | 1 => (170 : Fin 259)
      | 2 => (235 : Fin 259)
      | _ => (236 : Fin 259)
  | 16 =>
      match generator.val with
      | 0 => (227 : Fin 259)
      | 1 => (171 : Fin 259)
      | 2 => (236 : Fin 259)
      | _ => (167 : Fin 259)
  | 17 =>
      match generator.val with
      | 0 => (228 : Fin 259)
      | 1 => (234 : Fin 259)
      | 2 => (169 : Fin 259)
      | _ => (237 : Fin 259)
  | 18 =>
      match generator.val with
      | 0 => (229 : Fin 259)
      | 1 => (235 : Fin 259)
      | 2 => (237 : Fin 259)
      | _ => (238 : Fin 259)
  | 19 =>
      match generator.val with
      | 0 => (230 : Fin 259)
      | 1 => (236 : Fin 259)
      | 2 => (238 : Fin 259)
      | _ => (170 : Fin 259)
  | 20 =>
      match generator.val with
      | 0 => (231 : Fin 259)
      | 1 => (237 : Fin 259)
      | 2 => (173 : Fin 259)
      | _ => (239 : Fin 259)
  | 21 =>
      match generator.val with
      | 0 => (232 : Fin 259)
      | 1 => (238 : Fin 259)
      | 2 => (239 : Fin 259)
      | _ => (173 : Fin 259)
  | 22 =>
      match generator.val with
      | 0 => (233 : Fin 259)
      | 1 => (239 : Fin 259)
      | 2 => (176 : Fin 259)
      | _ => (175 : Fin 259)
  | 23 =>
      match generator.val with
      | 0 => (234 : Fin 259)
      | 1 => (181 : Fin 259)
      | 2 => (178 : Fin 259)
      | _ => (240 : Fin 259)
  | 24 =>
      match generator.val with
      | 0 => (235 : Fin 259)
      | 1 => (182 : Fin 259)
      | 2 => (240 : Fin 259)
      | _ => (241 : Fin 259)
  | 25 =>
      match generator.val with
      | 0 => (236 : Fin 259)
      | 1 => (183 : Fin 259)
      | 2 => (241 : Fin 259)
      | _ => (179 : Fin 259)
  | 26 =>
      match generator.val with
      | 0 => (237 : Fin 259)
      | 1 => (240 : Fin 259)
      | 2 => (182 : Fin 259)
      | _ => (242 : Fin 259)
  | 27 =>
      match generator.val with
      | 0 => (238 : Fin 259)
      | 1 => (241 : Fin 259)
      | 2 => (242 : Fin 259)
      | _ => (182 : Fin 259)
  | 28 =>
      match generator.val with
      | 0 => (239 : Fin 259)
      | 1 => (242 : Fin 259)
      | 2 => (185 : Fin 259)
      | _ => (184 : Fin 259)
  | 29 =>
      match generator.val with
      | 0 => (240 : Fin 259)
      | 1 => (190 : Fin 259)
      | 2 => (188 : Fin 259)
      | _ => (243 : Fin 259)
  | 30 =>
      match generator.val with
      | 0 => (241 : Fin 259)
      | 1 => (191 : Fin 259)
      | 2 => (243 : Fin 259)
      | _ => (188 : Fin 259)
  | _ =>
      match generator.val with
      | 0 => (242 : Fin 259)
      | 1 => (243 : Fin 259)
      | 2 => (191 : Fin 259)
      | _ => (190 : Fin 259)

private def transitionChunk7 (index : Nat)
    (generator : Fin 4) : Fin 259 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (205 : Fin 259)
      | 1 => (196 : Fin 259)
      | 2 => (193 : Fin 259)
      | _ => (244 : Fin 259)
  | 1 =>
      match generator.val with
      | 0 => (206 : Fin 259)
      | 1 => (197 : Fin 259)
      | 2 => (244 : Fin 259)
      | _ => (245 : Fin 259)
  | 2 =>
      match generator.val with
      | 0 => (207 : Fin 259)
      | 1 => (198 : Fin 259)
      | 2 => (245 : Fin 259)
      | _ => (246 : Fin 259)
  | 3 =>
      match generator.val with
      | 0 => (208 : Fin 259)
      | 1 => (199 : Fin 259)
      | 2 => (246 : Fin 259)
      | _ => (195 : Fin 259)
  | 4 =>
      match generator.val with
      | 0 => (209 : Fin 259)
      | 1 => (244 : Fin 259)
      | 2 => (197 : Fin 259)
      | _ => (247 : Fin 259)
  | 5 =>
      match generator.val with
      | 0 => (210 : Fin 259)
      | 1 => (245 : Fin 259)
      | 2 => (247 : Fin 259)
      | _ => (248 : Fin 259)
  | 6 =>
      match generator.val with
      | 0 => (211 : Fin 259)
      | 1 => (246 : Fin 259)
      | 2 => (248 : Fin 259)
      | _ => (198 : Fin 259)
  | 7 =>
      match generator.val with
      | 0 => (212 : Fin 259)
      | 1 => (247 : Fin 259)
      | 2 => (201 : Fin 259)
      | _ => (249 : Fin 259)
  | 8 =>
      match generator.val with
      | 0 => (213 : Fin 259)
      | 1 => (248 : Fin 259)
      | 2 => (249 : Fin 259)
      | _ => (201 : Fin 259)
  | 9 =>
      match generator.val with
      | 0 => (214 : Fin 259)
      | 1 => (249 : Fin 259)
      | 2 => (204 : Fin 259)
      | _ => (203 : Fin 259)
  | 10 =>
      match generator.val with
      | 0 => (244 : Fin 259)
      | 1 => (209 : Fin 259)
      | 2 => (206 : Fin 259)
      | _ => (250 : Fin 259)
  | 11 =>
      match generator.val with
      | 0 => (245 : Fin 259)
      | 1 => (210 : Fin 259)
      | 2 => (250 : Fin 259)
      | _ => (251 : Fin 259)
  | 12 =>
      match generator.val with
      | 0 => (246 : Fin 259)
      | 1 => (211 : Fin 259)
      | 2 => (251 : Fin 259)
      | _ => (207 : Fin 259)
  | 13 =>
      match generator.val with
      | 0 => (247 : Fin 259)
      | 1 => (250 : Fin 259)
      | 2 => (210 : Fin 259)
      | _ => (252 : Fin 259)
  | 14 =>
      match generator.val with
      | 0 => (248 : Fin 259)
      | 1 => (251 : Fin 259)
      | 2 => (252 : Fin 259)
      | _ => (210 : Fin 259)
  | 15 =>
      match generator.val with
      | 0 => (249 : Fin 259)
      | 1 => (252 : Fin 259)
      | 2 => (213 : Fin 259)
      | _ => (212 : Fin 259)
  | 16 =>
      match generator.val with
      | 0 => (250 : Fin 259)
      | 1 => (218 : Fin 259)
      | 2 => (216 : Fin 259)
      | _ => (253 : Fin 259)
  | 17 =>
      match generator.val with
      | 0 => (251 : Fin 259)
      | 1 => (219 : Fin 259)
      | 2 => (253 : Fin 259)
      | _ => (216 : Fin 259)
  | 18 =>
      match generator.val with
      | 0 => (252 : Fin 259)
      | 1 => (253 : Fin 259)
      | 2 => (219 : Fin 259)
      | _ => (218 : Fin 259)
  | 19 =>
      match generator.val with
      | 0 => (253 : Fin 259)
      | 1 => (223 : Fin 259)
      | 2 => (222 : Fin 259)
      | _ => (221 : Fin 259)
  | 20 =>
      match generator.val with
      | 0 => (234 : Fin 259)
      | 1 => (228 : Fin 259)
      | 2 => (225 : Fin 259)
      | _ => (254 : Fin 259)
  | 21 =>
      match generator.val with
      | 0 => (235 : Fin 259)
      | 1 => (229 : Fin 259)
      | 2 => (254 : Fin 259)
      | _ => (255 : Fin 259)
  | 22 =>
      match generator.val with
      | 0 => (236 : Fin 259)
      | 1 => (230 : Fin 259)
      | 2 => (255 : Fin 259)
      | _ => (226 : Fin 259)
  | 23 =>
      match generator.val with
      | 0 => (237 : Fin 259)
      | 1 => (254 : Fin 259)
      | 2 => (229 : Fin 259)
      | _ => (256 : Fin 259)
  | 24 =>
      match generator.val with
      | 0 => (238 : Fin 259)
      | 1 => (255 : Fin 259)
      | 2 => (256 : Fin 259)
      | _ => (229 : Fin 259)
  | 25 =>
      match generator.val with
      | 0 => (239 : Fin 259)
      | 1 => (256 : Fin 259)
      | 2 => (232 : Fin 259)
      | _ => (231 : Fin 259)
  | 26 =>
      match generator.val with
      | 0 => (254 : Fin 259)
      | 1 => (237 : Fin 259)
      | 2 => (235 : Fin 259)
      | _ => (257 : Fin 259)
  | 27 =>
      match generator.val with
      | 0 => (255 : Fin 259)
      | 1 => (238 : Fin 259)
      | 2 => (257 : Fin 259)
      | _ => (235 : Fin 259)
  | 28 =>
      match generator.val with
      | 0 => (256 : Fin 259)
      | 1 => (257 : Fin 259)
      | 2 => (238 : Fin 259)
      | _ => (237 : Fin 259)
  | 29 =>
      match generator.val with
      | 0 => (257 : Fin 259)
      | 1 => (242 : Fin 259)
      | 2 => (241 : Fin 259)
      | _ => (240 : Fin 259)
  | 30 =>
      match generator.val with
      | 0 => (250 : Fin 259)
      | 1 => (247 : Fin 259)
      | 2 => (245 : Fin 259)
      | _ => (258 : Fin 259)
  | _ =>
      match generator.val with
      | 0 => (251 : Fin 259)
      | 1 => (248 : Fin 259)
      | 2 => (258 : Fin 259)
      | _ => (245 : Fin 259)

private def transitionChunk8 (index : Nat)
    (generator : Fin 4) : Fin 259 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (252 : Fin 259)
      | 1 => (258 : Fin 259)
      | 2 => (248 : Fin 259)
      | _ => (247 : Fin 259)
  | 1 =>
      match generator.val with
      | 0 => (258 : Fin 259)
      | 1 => (252 : Fin 259)
      | 2 => (251 : Fin 259)
      | _ => (250 : Fin 259)
  | _ =>
      match generator.val with
      | 0 => (257 : Fin 259)
      | 1 => (256 : Fin 259)
      | 2 => (255 : Fin 259)
      | _ => (254 : Fin 259)

def transition (state : Fin 259)
    (generator : Fin 4) : Fin 259 :=
  if state.val < 32 then transitionChunk0 state.val generator else
    if state.val < 64 then transitionChunk1 (state.val - 32) generator else
      if state.val < 96 then transitionChunk2 (state.val - 64) generator else
        if state.val < 128 then transitionChunk3 (state.val - 96) generator else
          if state.val < 160 then transitionChunk4 (state.val - 128) generator else
            if state.val < 192 then transitionChunk5 (state.val - 160) generator else
              if state.val < 224 then transitionChunk6 (state.val - 192) generator else
                if state.val < 256 then transitionChunk7 (state.val - 224) generator else
                  transitionChunk8 (state.val - 256) generator

private def representativeHeadChunk0 (index : Nat) : Fin 4 :=
  match index with
  | 0 => (0 : Fin 4)
  | 1 => (1 : Fin 4)
  | 2 => (2 : Fin 4)
  | 3 => (3 : Fin 4)
  | 4 => (0 : Fin 4)
  | 5 => (0 : Fin 4)
  | 6 => (0 : Fin 4)
  | 7 => (0 : Fin 4)
  | 8 => (1 : Fin 4)
  | 9 => (1 : Fin 4)
  | 10 => (1 : Fin 4)
  | 11 => (2 : Fin 4)
  | 12 => (2 : Fin 4)
  | 13 => (3 : Fin 4)
  | 14 => (0 : Fin 4)
  | 15 => (0 : Fin 4)
  | 16 => (0 : Fin 4)
  | 17 => (0 : Fin 4)
  | 18 => (0 : Fin 4)
  | 19 => (0 : Fin 4)
  | 20 => (0 : Fin 4)
  | 21 => (0 : Fin 4)
  | 22 => (0 : Fin 4)
  | 23 => (0 : Fin 4)
  | 24 => (1 : Fin 4)
  | 25 => (1 : Fin 4)
  | 26 => (1 : Fin 4)
  | 27 => (1 : Fin 4)
  | 28 => (1 : Fin 4)
  | 29 => (1 : Fin 4)
  | 30 => (2 : Fin 4)
  | _ => (2 : Fin 4)

private def representativeHeadChunk1 (index : Nat) : Fin 4 :=
  match index with
  | 0 => (2 : Fin 4)
  | 1 => (3 : Fin 4)
  | 2 => (0 : Fin 4)
  | 3 => (0 : Fin 4)
  | 4 => (0 : Fin 4)
  | 5 => (0 : Fin 4)
  | 6 => (0 : Fin 4)
  | 7 => (0 : Fin 4)
  | 8 => (0 : Fin 4)
  | 9 => (0 : Fin 4)
  | 10 => (0 : Fin 4)
  | 11 => (0 : Fin 4)
  | 12 => (0 : Fin 4)
  | 13 => (0 : Fin 4)
  | 14 => (0 : Fin 4)
  | 15 => (0 : Fin 4)
  | 16 => (0 : Fin 4)
  | 17 => (0 : Fin 4)
  | 18 => (0 : Fin 4)
  | 19 => (0 : Fin 4)
  | 20 => (0 : Fin 4)
  | 21 => (0 : Fin 4)
  | 22 => (1 : Fin 4)
  | 23 => (1 : Fin 4)
  | 24 => (1 : Fin 4)
  | 25 => (1 : Fin 4)
  | 26 => (1 : Fin 4)
  | 27 => (1 : Fin 4)
  | 28 => (1 : Fin 4)
  | 29 => (1 : Fin 4)
  | 30 => (1 : Fin 4)
  | _ => (1 : Fin 4)

private def representativeHeadChunk2 (index : Nat) : Fin 4 :=
  match index with
  | 0 => (2 : Fin 4)
  | 1 => (2 : Fin 4)
  | 2 => (2 : Fin 4)
  | 3 => (2 : Fin 4)
  | 4 => (3 : Fin 4)
  | 5 => (0 : Fin 4)
  | 6 => (0 : Fin 4)
  | 7 => (0 : Fin 4)
  | 8 => (0 : Fin 4)
  | 9 => (0 : Fin 4)
  | 10 => (0 : Fin 4)
  | 11 => (0 : Fin 4)
  | 12 => (0 : Fin 4)
  | 13 => (0 : Fin 4)
  | 14 => (0 : Fin 4)
  | 15 => (0 : Fin 4)
  | 16 => (0 : Fin 4)
  | 17 => (0 : Fin 4)
  | 18 => (0 : Fin 4)
  | 19 => (0 : Fin 4)
  | 20 => (0 : Fin 4)
  | 21 => (0 : Fin 4)
  | 22 => (0 : Fin 4)
  | 23 => (0 : Fin 4)
  | 24 => (0 : Fin 4)
  | 25 => (0 : Fin 4)
  | 26 => (0 : Fin 4)
  | 27 => (0 : Fin 4)
  | 28 => (0 : Fin 4)
  | 29 => (0 : Fin 4)
  | 30 => (0 : Fin 4)
  | _ => (0 : Fin 4)

private def representativeHeadChunk3 (index : Nat) : Fin 4 :=
  match index with
  | 0 => (0 : Fin 4)
  | 1 => (1 : Fin 4)
  | 2 => (1 : Fin 4)
  | 3 => (1 : Fin 4)
  | 4 => (1 : Fin 4)
  | 5 => (1 : Fin 4)
  | 6 => (1 : Fin 4)
  | 7 => (1 : Fin 4)
  | 8 => (1 : Fin 4)
  | 9 => (1 : Fin 4)
  | 10 => (1 : Fin 4)
  | 11 => (2 : Fin 4)
  | 12 => (2 : Fin 4)
  | 13 => (0 : Fin 4)
  | 14 => (0 : Fin 4)
  | 15 => (0 : Fin 4)
  | 16 => (0 : Fin 4)
  | 17 => (0 : Fin 4)
  | 18 => (0 : Fin 4)
  | 19 => (0 : Fin 4)
  | 20 => (0 : Fin 4)
  | 21 => (0 : Fin 4)
  | 22 => (0 : Fin 4)
  | 23 => (0 : Fin 4)
  | 24 => (0 : Fin 4)
  | 25 => (0 : Fin 4)
  | 26 => (0 : Fin 4)
  | 27 => (0 : Fin 4)
  | 28 => (0 : Fin 4)
  | 29 => (0 : Fin 4)
  | 30 => (0 : Fin 4)
  | _ => (0 : Fin 4)

private def representativeHeadChunk4 (index : Nat) : Fin 4 :=
  match index with
  | 0 => (0 : Fin 4)
  | 1 => (0 : Fin 4)
  | 2 => (0 : Fin 4)
  | 3 => (0 : Fin 4)
  | 4 => (0 : Fin 4)
  | 5 => (0 : Fin 4)
  | 6 => (0 : Fin 4)
  | 7 => (0 : Fin 4)
  | 8 => (0 : Fin 4)
  | 9 => (0 : Fin 4)
  | 10 => (0 : Fin 4)
  | 11 => (0 : Fin 4)
  | 12 => (0 : Fin 4)
  | 13 => (0 : Fin 4)
  | 14 => (0 : Fin 4)
  | 15 => (1 : Fin 4)
  | 16 => (1 : Fin 4)
  | 17 => (1 : Fin 4)
  | 18 => (1 : Fin 4)
  | 19 => (1 : Fin 4)
  | 20 => (1 : Fin 4)
  | 21 => (1 : Fin 4)
  | 22 => (1 : Fin 4)
  | 23 => (1 : Fin 4)
  | 24 => (2 : Fin 4)
  | 25 => (0 : Fin 4)
  | 26 => (0 : Fin 4)
  | 27 => (0 : Fin 4)
  | 28 => (0 : Fin 4)
  | 29 => (0 : Fin 4)
  | 30 => (0 : Fin 4)
  | _ => (0 : Fin 4)

private def representativeHeadChunk5 (index : Nat) : Fin 4 :=
  match index with
  | 0 => (0 : Fin 4)
  | 1 => (0 : Fin 4)
  | 2 => (0 : Fin 4)
  | 3 => (0 : Fin 4)
  | 4 => (0 : Fin 4)
  | 5 => (0 : Fin 4)
  | 6 => (0 : Fin 4)
  | 7 => (0 : Fin 4)
  | 8 => (0 : Fin 4)
  | 9 => (0 : Fin 4)
  | 10 => (0 : Fin 4)
  | 11 => (0 : Fin 4)
  | 12 => (0 : Fin 4)
  | 13 => (0 : Fin 4)
  | 14 => (0 : Fin 4)
  | 15 => (0 : Fin 4)
  | 16 => (0 : Fin 4)
  | 17 => (0 : Fin 4)
  | 18 => (0 : Fin 4)
  | 19 => (0 : Fin 4)
  | 20 => (0 : Fin 4)
  | 21 => (0 : Fin 4)
  | 22 => (0 : Fin 4)
  | 23 => (0 : Fin 4)
  | 24 => (0 : Fin 4)
  | 25 => (0 : Fin 4)
  | 26 => (0 : Fin 4)
  | 27 => (1 : Fin 4)
  | 28 => (1 : Fin 4)
  | 29 => (1 : Fin 4)
  | 30 => (1 : Fin 4)
  | _ => (1 : Fin 4)

private def representativeHeadChunk6 (index : Nat) : Fin 4 :=
  match index with
  | 0 => (1 : Fin 4)
  | 1 => (0 : Fin 4)
  | 2 => (0 : Fin 4)
  | 3 => (0 : Fin 4)
  | 4 => (0 : Fin 4)
  | 5 => (0 : Fin 4)
  | 6 => (0 : Fin 4)
  | 7 => (0 : Fin 4)
  | 8 => (0 : Fin 4)
  | 9 => (0 : Fin 4)
  | 10 => (0 : Fin 4)
  | 11 => (0 : Fin 4)
  | 12 => (0 : Fin 4)
  | 13 => (0 : Fin 4)
  | 14 => (0 : Fin 4)
  | 15 => (0 : Fin 4)
  | 16 => (0 : Fin 4)
  | 17 => (0 : Fin 4)
  | 18 => (0 : Fin 4)
  | 19 => (0 : Fin 4)
  | 20 => (0 : Fin 4)
  | 21 => (0 : Fin 4)
  | 22 => (0 : Fin 4)
  | 23 => (0 : Fin 4)
  | 24 => (0 : Fin 4)
  | 25 => (0 : Fin 4)
  | 26 => (0 : Fin 4)
  | 27 => (0 : Fin 4)
  | 28 => (0 : Fin 4)
  | 29 => (1 : Fin 4)
  | 30 => (1 : Fin 4)
  | _ => (1 : Fin 4)

private def representativeHeadChunk7 (index : Nat) : Fin 4 :=
  match index with
  | 0 => (0 : Fin 4)
  | 1 => (0 : Fin 4)
  | 2 => (0 : Fin 4)
  | 3 => (0 : Fin 4)
  | 4 => (0 : Fin 4)
  | 5 => (0 : Fin 4)
  | 6 => (0 : Fin 4)
  | 7 => (0 : Fin 4)
  | 8 => (0 : Fin 4)
  | 9 => (0 : Fin 4)
  | 10 => (0 : Fin 4)
  | 11 => (0 : Fin 4)
  | 12 => (0 : Fin 4)
  | 13 => (0 : Fin 4)
  | 14 => (0 : Fin 4)
  | 15 => (0 : Fin 4)
  | 16 => (0 : Fin 4)
  | 17 => (0 : Fin 4)
  | 18 => (0 : Fin 4)
  | 19 => (1 : Fin 4)
  | 20 => (0 : Fin 4)
  | 21 => (0 : Fin 4)
  | 22 => (0 : Fin 4)
  | 23 => (0 : Fin 4)
  | 24 => (0 : Fin 4)
  | 25 => (0 : Fin 4)
  | 26 => (0 : Fin 4)
  | 27 => (0 : Fin 4)
  | 28 => (0 : Fin 4)
  | 29 => (0 : Fin 4)
  | 30 => (0 : Fin 4)
  | _ => (0 : Fin 4)

private def representativeHeadChunk8 (index : Nat) : Fin 4 :=
  match index with
  | 0 => (0 : Fin 4)
  | 1 => (0 : Fin 4)
  | _ => (0 : Fin 4)

def representativeHead (state : Fin 259) : Fin 4 :=
  if state.val < 32 then representativeHeadChunk0 state.val else
    if state.val < 64 then representativeHeadChunk1 (state.val - 32) else
      if state.val < 96 then representativeHeadChunk2 (state.val - 64) else
        if state.val < 128 then representativeHeadChunk3 (state.val - 96) else
          if state.val < 160 then representativeHeadChunk4 (state.val - 128) else
            if state.val < 192 then representativeHeadChunk5 (state.val - 160) else
              if state.val < 224 then representativeHeadChunk6 (state.val - 192) else
                if state.val < 256 then representativeHeadChunk7 (state.val - 224) else
                  representativeHeadChunk8 (state.val - 256)

private def representativeTailChunk0 (index : Nat) :
    List (Fin 4) :=
  match index with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => []
  | 4 => [0]
  | 5 => [1]
  | 6 => [2]
  | 7 => [3]
  | 8 => [1]
  | 9 => [2]
  | 10 => [3]
  | 11 => [2]
  | 12 => [3]
  | 13 => [3]
  | 14 => [0, 0]
  | 15 => [0, 1]
  | 16 => [0, 2]
  | 17 => [0, 3]
  | 18 => [1, 1]
  | 19 => [1, 2]
  | 20 => [1, 3]
  | 21 => [2, 2]
  | 22 => [2, 3]
  | 23 => [3, 3]
  | 24 => [1, 1]
  | 25 => [1, 2]
  | 26 => [1, 3]
  | 27 => [2, 2]
  | 28 => [2, 3]
  | 29 => [3, 3]
  | 30 => [2, 2]
  | _ => [2, 3]

private def representativeTailChunk1 (index : Nat) :
    List (Fin 4) :=
  match index with
  | 0 => [3, 3]
  | 1 => [3, 3]
  | 2 => [0, 0, 0]
  | 3 => [0, 0, 1]
  | 4 => [0, 0, 2]
  | 5 => [0, 0, 3]
  | 6 => [0, 1, 1]
  | 7 => [0, 1, 2]
  | 8 => [0, 1, 3]
  | 9 => [0, 2, 2]
  | 10 => [0, 2, 3]
  | 11 => [0, 3, 3]
  | 12 => [1, 1, 1]
  | 13 => [1, 1, 2]
  | 14 => [1, 1, 3]
  | 15 => [1, 2, 2]
  | 16 => [1, 2, 3]
  | 17 => [1, 3, 3]
  | 18 => [2, 2, 2]
  | 19 => [2, 2, 3]
  | 20 => [2, 3, 3]
  | 21 => [3, 3, 3]
  | 22 => [1, 1, 1]
  | 23 => [1, 1, 2]
  | 24 => [1, 1, 3]
  | 25 => [1, 2, 2]
  | 26 => [1, 2, 3]
  | 27 => [1, 3, 3]
  | 28 => [2, 2, 2]
  | 29 => [2, 2, 3]
  | 30 => [2, 3, 3]
  | _ => [3, 3, 3]

private def representativeTailChunk2 (index : Nat) :
    List (Fin 4) :=
  match index with
  | 0 => [2, 2, 2]
  | 1 => [2, 2, 3]
  | 2 => [2, 3, 3]
  | 3 => [3, 3, 3]
  | 4 => [3, 3, 3]
  | 5 => [0, 0, 1, 1]
  | 6 => [0, 0, 1, 2]
  | 7 => [0, 0, 1, 3]
  | 8 => [0, 0, 2, 2]
  | 9 => [0, 0, 2, 3]
  | 10 => [0, 0, 3, 3]
  | 11 => [0, 1, 1, 1]
  | 12 => [0, 1, 1, 2]
  | 13 => [0, 1, 1, 3]
  | 14 => [0, 1, 2, 2]
  | 15 => [0, 1, 2, 3]
  | 16 => [0, 1, 3, 3]
  | 17 => [0, 2, 2, 2]
  | 18 => [0, 2, 2, 3]
  | 19 => [0, 2, 3, 3]
  | 20 => [0, 3, 3, 3]
  | 21 => [1, 1, 1, 2]
  | 22 => [1, 1, 1, 3]
  | 23 => [1, 1, 2, 2]
  | 24 => [1, 1, 2, 3]
  | 25 => [1, 1, 3, 3]
  | 26 => [1, 2, 2, 2]
  | 27 => [1, 2, 2, 3]
  | 28 => [1, 2, 3, 3]
  | 29 => [1, 3, 3, 3]
  | 30 => [2, 2, 2, 3]
  | _ => [2, 2, 3, 3]

private def representativeTailChunk3 (index : Nat) :
    List (Fin 4) :=
  match index with
  | 0 => [2, 3, 3, 3]
  | 1 => [1, 1, 2, 2]
  | 2 => [1, 1, 2, 3]
  | 3 => [1, 1, 3, 3]
  | 4 => [1, 2, 2, 2]
  | 5 => [1, 2, 2, 3]
  | 6 => [1, 2, 3, 3]
  | 7 => [1, 3, 3, 3]
  | 8 => [2, 2, 2, 3]
  | 9 => [2, 2, 3, 3]
  | 10 => [2, 3, 3, 3]
  | 11 => [2, 2, 3, 3]
  | 12 => [2, 3, 3, 3]
  | 13 => [0, 0, 1, 1, 1]
  | 14 => [0, 0, 1, 1, 2]
  | 15 => [0, 0, 1, 1, 3]
  | 16 => [0, 0, 1, 2, 2]
  | 17 => [0, 0, 1, 2, 3]
  | 18 => [0, 0, 1, 3, 3]
  | 19 => [0, 0, 2, 2, 2]
  | 20 => [0, 0, 2, 2, 3]
  | 21 => [0, 0, 2, 3, 3]
  | 22 => [0, 0, 3, 3, 3]
  | 23 => [0, 1, 1, 1, 2]
  | 24 => [0, 1, 1, 1, 3]
  | 25 => [0, 1, 1, 2, 2]
  | 26 => [0, 1, 1, 2, 3]
  | 27 => [0, 1, 1, 3, 3]
  | 28 => [0, 1, 2, 2, 2]
  | 29 => [0, 1, 2, 2, 3]
  | 30 => [0, 1, 2, 3, 3]
  | _ => [0, 1, 3, 3, 3]

private def representativeTailChunk4 (index : Nat) :
    List (Fin 4) :=
  match index with
  | 0 => [0, 2, 2, 2, 3]
  | 1 => [0, 2, 2, 3, 3]
  | 2 => [0, 2, 3, 3, 3]
  | 3 => [1, 1, 1, 2, 2]
  | 4 => [1, 1, 1, 2, 3]
  | 5 => [1, 1, 1, 3, 3]
  | 6 => [1, 1, 2, 2, 2]
  | 7 => [1, 1, 2, 2, 3]
  | 8 => [1, 1, 2, 3, 3]
  | 9 => [1, 1, 3, 3, 3]
  | 10 => [1, 2, 2, 2, 3]
  | 11 => [1, 2, 2, 3, 3]
  | 12 => [1, 2, 3, 3, 3]
  | 13 => [2, 2, 2, 3, 3]
  | 14 => [2, 2, 3, 3, 3]
  | 15 => [1, 1, 2, 2, 2]
  | 16 => [1, 1, 2, 2, 3]
  | 17 => [1, 1, 2, 3, 3]
  | 18 => [1, 1, 3, 3, 3]
  | 19 => [1, 2, 2, 2, 3]
  | 20 => [1, 2, 2, 3, 3]
  | 21 => [1, 2, 3, 3, 3]
  | 22 => [2, 2, 2, 3, 3]
  | 23 => [2, 2, 3, 3, 3]
  | 24 => [2, 2, 3, 3, 3]
  | 25 => [0, 0, 1, 1, 1, 2]
  | 26 => [0, 0, 1, 1, 1, 3]
  | 27 => [0, 0, 1, 1, 2, 2]
  | 28 => [0, 0, 1, 1, 2, 3]
  | 29 => [0, 0, 1, 1, 3, 3]
  | 30 => [0, 0, 1, 2, 2, 2]
  | _ => [0, 0, 1, 2, 2, 3]

private def representativeTailChunk5 (index : Nat) :
    List (Fin 4) :=
  match index with
  | 0 => [0, 0, 1, 2, 3, 3]
  | 1 => [0, 0, 1, 3, 3, 3]
  | 2 => [0, 0, 2, 2, 2, 3]
  | 3 => [0, 0, 2, 2, 3, 3]
  | 4 => [0, 0, 2, 3, 3, 3]
  | 5 => [0, 1, 1, 1, 2, 2]
  | 6 => [0, 1, 1, 1, 2, 3]
  | 7 => [0, 1, 1, 1, 3, 3]
  | 8 => [0, 1, 1, 2, 2, 2]
  | 9 => [0, 1, 1, 2, 2, 3]
  | 10 => [0, 1, 1, 2, 3, 3]
  | 11 => [0, 1, 1, 3, 3, 3]
  | 12 => [0, 1, 2, 2, 2, 3]
  | 13 => [0, 1, 2, 2, 3, 3]
  | 14 => [0, 1, 2, 3, 3, 3]
  | 15 => [0, 2, 2, 2, 3, 3]
  | 16 => [0, 2, 2, 3, 3, 3]
  | 17 => [1, 1, 1, 2, 2, 2]
  | 18 => [1, 1, 1, 2, 2, 3]
  | 19 => [1, 1, 1, 2, 3, 3]
  | 20 => [1, 1, 1, 3, 3, 3]
  | 21 => [1, 1, 2, 2, 2, 3]
  | 22 => [1, 1, 2, 2, 3, 3]
  | 23 => [1, 1, 2, 3, 3, 3]
  | 24 => [1, 2, 2, 2, 3, 3]
  | 25 => [1, 2, 2, 3, 3, 3]
  | 26 => [2, 2, 2, 3, 3, 3]
  | 27 => [1, 1, 2, 2, 2, 3]
  | 28 => [1, 1, 2, 2, 3, 3]
  | 29 => [1, 1, 2, 3, 3, 3]
  | 30 => [1, 2, 2, 2, 3, 3]
  | _ => [1, 2, 2, 3, 3, 3]

private def representativeTailChunk6 (index : Nat) :
    List (Fin 4) :=
  match index with
  | 0 => [2, 2, 2, 3, 3, 3]
  | 1 => [0, 0, 1, 1, 1, 2, 2]
  | 2 => [0, 0, 1, 1, 1, 2, 3]
  | 3 => [0, 0, 1, 1, 1, 3, 3]
  | 4 => [0, 0, 1, 1, 2, 2, 2]
  | 5 => [0, 0, 1, 1, 2, 2, 3]
  | 6 => [0, 0, 1, 1, 2, 3, 3]
  | 7 => [0, 0, 1, 1, 3, 3, 3]
  | 8 => [0, 0, 1, 2, 2, 2, 3]
  | 9 => [0, 0, 1, 2, 2, 3, 3]
  | 10 => [0, 0, 1, 2, 3, 3, 3]
  | 11 => [0, 0, 2, 2, 2, 3, 3]
  | 12 => [0, 0, 2, 2, 3, 3, 3]
  | 13 => [0, 1, 1, 1, 2, 2, 2]
  | 14 => [0, 1, 1, 1, 2, 2, 3]
  | 15 => [0, 1, 1, 1, 2, 3, 3]
  | 16 => [0, 1, 1, 1, 3, 3, 3]
  | 17 => [0, 1, 1, 2, 2, 2, 3]
  | 18 => [0, 1, 1, 2, 2, 3, 3]
  | 19 => [0, 1, 1, 2, 3, 3, 3]
  | 20 => [0, 1, 2, 2, 2, 3, 3]
  | 21 => [0, 1, 2, 2, 3, 3, 3]
  | 22 => [0, 2, 2, 2, 3, 3, 3]
  | 23 => [1, 1, 1, 2, 2, 2, 3]
  | 24 => [1, 1, 1, 2, 2, 3, 3]
  | 25 => [1, 1, 1, 2, 3, 3, 3]
  | 26 => [1, 1, 2, 2, 2, 3, 3]
  | 27 => [1, 1, 2, 2, 3, 3, 3]
  | 28 => [1, 2, 2, 2, 3, 3, 3]
  | 29 => [1, 1, 2, 2, 2, 3, 3]
  | 30 => [1, 1, 2, 2, 3, 3, 3]
  | _ => [1, 2, 2, 2, 3, 3, 3]

private def representativeTailChunk7 (index : Nat) :
    List (Fin 4) :=
  match index with
  | 0 => [0, 0, 1, 1, 1, 2, 2, 2]
  | 1 => [0, 0, 1, 1, 1, 2, 2, 3]
  | 2 => [0, 0, 1, 1, 1, 2, 3, 3]
  | 3 => [0, 0, 1, 1, 1, 3, 3, 3]
  | 4 => [0, 0, 1, 1, 2, 2, 2, 3]
  | 5 => [0, 0, 1, 1, 2, 2, 3, 3]
  | 6 => [0, 0, 1, 1, 2, 3, 3, 3]
  | 7 => [0, 0, 1, 2, 2, 2, 3, 3]
  | 8 => [0, 0, 1, 2, 2, 3, 3, 3]
  | 9 => [0, 0, 2, 2, 2, 3, 3, 3]
  | 10 => [0, 1, 1, 1, 2, 2, 2, 3]
  | 11 => [0, 1, 1, 1, 2, 2, 3, 3]
  | 12 => [0, 1, 1, 1, 2, 3, 3, 3]
  | 13 => [0, 1, 1, 2, 2, 2, 3, 3]
  | 14 => [0, 1, 1, 2, 2, 3, 3, 3]
  | 15 => [0, 1, 2, 2, 2, 3, 3, 3]
  | 16 => [1, 1, 1, 2, 2, 2, 3, 3]
  | 17 => [1, 1, 1, 2, 2, 3, 3, 3]
  | 18 => [1, 1, 2, 2, 2, 3, 3, 3]
  | 19 => [1, 1, 2, 2, 2, 3, 3, 3]
  | 20 => [0, 0, 1, 1, 1, 2, 2, 2, 3]
  | 21 => [0, 0, 1, 1, 1, 2, 2, 3, 3]
  | 22 => [0, 0, 1, 1, 1, 2, 3, 3, 3]
  | 23 => [0, 0, 1, 1, 2, 2, 2, 3, 3]
  | 24 => [0, 0, 1, 1, 2, 2, 3, 3, 3]
  | 25 => [0, 0, 1, 2, 2, 2, 3, 3, 3]
  | 26 => [0, 1, 1, 1, 2, 2, 2, 3, 3]
  | 27 => [0, 1, 1, 1, 2, 2, 3, 3, 3]
  | 28 => [0, 1, 1, 2, 2, 2, 3, 3, 3]
  | 29 => [1, 1, 1, 2, 2, 2, 3, 3, 3]
  | 30 => [0, 0, 1, 1, 1, 2, 2, 2, 3, 3]
  | _ => [0, 0, 1, 1, 1, 2, 2, 3, 3, 3]

private def representativeTailChunk8 (index : Nat) :
    List (Fin 4) :=
  match index with
  | 0 => [0, 0, 1, 1, 2, 2, 2, 3, 3, 3]
  | 1 => [0, 1, 1, 1, 2, 2, 2, 3, 3, 3]
  | _ => [0, 0, 1, 1, 1, 2, 2, 2, 3, 3, 3]

def representativeTail (state : Fin 259) :
    List (Fin 4) :=
  if state.val < 32 then representativeTailChunk0 state.val else
    if state.val < 64 then representativeTailChunk1 (state.val - 32) else
      if state.val < 96 then representativeTailChunk2 (state.val - 64) else
        if state.val < 128 then representativeTailChunk3 (state.val - 96) else
          if state.val < 160 then representativeTailChunk4 (state.val - 128) else
            if state.val < 192 then representativeTailChunk5 (state.val - 160) else
              if state.val < 224 then representativeTailChunk6 (state.val - 192) else
                if state.val < 256 then representativeTailChunk7 (state.val - 224) else
                  representativeTailChunk8 (state.val - 256)

private def sourceLabelChunk0 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (5 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (3 : Fin 6)
  | 3 => (2 : Fin 6)
  | 4 => (5 : Fin 6)
  | 5 => (0 : Fin 6)
  | 6 => (3 : Fin 6)
  | 7 => (2 : Fin 6)
  | 8 => (1 : Fin 6)
  | 9 => (3 : Fin 6)
  | 10 => (0 : Fin 6)
  | 11 => (0 : Fin 6)
  | 12 => (3 : Fin 6)
  | 13 => (0 : Fin 6)
  | 14 => (5 : Fin 6)
  | 15 => (0 : Fin 6)
  | 16 => (3 : Fin 6)
  | 17 => (2 : Fin 6)
  | 18 => (0 : Fin 6)
  | 19 => (3 : Fin 6)
  | 20 => (0 : Fin 6)
  | 21 => (0 : Fin 6)
  | 22 => (3 : Fin 6)
  | 23 => (0 : Fin 6)
  | 24 => (0 : Fin 6)
  | 25 => (3 : Fin 6)
  | 26 => (0 : Fin 6)
  | 27 => (0 : Fin 6)
  | 28 => (3 : Fin 6)
  | 29 => (0 : Fin 6)
  | 30 => (3 : Fin 6)
  | _ => (0 : Fin 6)

private def sourceLabelChunk1 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (3 : Fin 6)
  | 1 => (0 : Fin 6)
  | 2 => (5 : Fin 6)
  | 3 => (0 : Fin 6)
  | 4 => (3 : Fin 6)
  | 5 => (2 : Fin 6)
  | 6 => (0 : Fin 6)
  | 7 => (3 : Fin 6)
  | 8 => (0 : Fin 6)
  | 9 => (0 : Fin 6)
  | 10 => (3 : Fin 6)
  | 11 => (0 : Fin 6)
  | 12 => (0 : Fin 6)
  | 13 => (3 : Fin 6)
  | 14 => (0 : Fin 6)
  | 15 => (0 : Fin 6)
  | 16 => (3 : Fin 6)
  | 17 => (0 : Fin 6)
  | 18 => (3 : Fin 6)
  | 19 => (0 : Fin 6)
  | 20 => (3 : Fin 6)
  | 21 => (0 : Fin 6)
  | 22 => (0 : Fin 6)
  | 23 => (3 : Fin 6)
  | 24 => (0 : Fin 6)
  | 25 => (0 : Fin 6)
  | 26 => (3 : Fin 6)
  | 27 => (0 : Fin 6)
  | 28 => (3 : Fin 6)
  | 29 => (0 : Fin 6)
  | 30 => (3 : Fin 6)
  | _ => (0 : Fin 6)

private def sourceLabelChunk2 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (0 : Fin 6)
  | 1 => (3 : Fin 6)
  | 2 => (0 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (0 : Fin 6)
  | 5 => (0 : Fin 6)
  | 6 => (3 : Fin 6)
  | 7 => (0 : Fin 6)
  | 8 => (0 : Fin 6)
  | 9 => (3 : Fin 6)
  | 10 => (0 : Fin 6)
  | 11 => (0 : Fin 6)
  | 12 => (3 : Fin 6)
  | 13 => (0 : Fin 6)
  | 14 => (0 : Fin 6)
  | 15 => (3 : Fin 6)
  | 16 => (0 : Fin 6)
  | 17 => (3 : Fin 6)
  | 18 => (0 : Fin 6)
  | 19 => (3 : Fin 6)
  | 20 => (0 : Fin 6)
  | 21 => (3 : Fin 6)
  | 22 => (0 : Fin 6)
  | 23 => (0 : Fin 6)
  | 24 => (3 : Fin 6)
  | 25 => (0 : Fin 6)
  | 26 => (3 : Fin 6)
  | 27 => (0 : Fin 6)
  | 28 => (3 : Fin 6)
  | 29 => (0 : Fin 6)
  | 30 => (3 : Fin 6)
  | _ => (0 : Fin 6)

private def sourceLabelChunk3 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (3 : Fin 6)
  | 1 => (0 : Fin 6)
  | 2 => (3 : Fin 6)
  | 3 => (0 : Fin 6)
  | 4 => (3 : Fin 6)
  | 5 => (0 : Fin 6)
  | 6 => (3 : Fin 6)
  | 7 => (0 : Fin 6)
  | 8 => (3 : Fin 6)
  | 9 => (0 : Fin 6)
  | 10 => (3 : Fin 6)
  | 11 => (3 : Fin 6)
  | 12 => (0 : Fin 6)
  | 13 => (0 : Fin 6)
  | 14 => (3 : Fin 6)
  | 15 => (0 : Fin 6)
  | 16 => (0 : Fin 6)
  | 17 => (3 : Fin 6)
  | 18 => (0 : Fin 6)
  | 19 => (3 : Fin 6)
  | 20 => (0 : Fin 6)
  | 21 => (3 : Fin 6)
  | 22 => (0 : Fin 6)
  | 23 => (3 : Fin 6)
  | 24 => (0 : Fin 6)
  | 25 => (0 : Fin 6)
  | 26 => (3 : Fin 6)
  | 27 => (0 : Fin 6)
  | 28 => (3 : Fin 6)
  | 29 => (0 : Fin 6)
  | 30 => (3 : Fin 6)
  | _ => (0 : Fin 6)

private def sourceLabelChunk4 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (3 : Fin 6)
  | 1 => (0 : Fin 6)
  | 2 => (3 : Fin 6)
  | 3 => (0 : Fin 6)
  | 4 => (3 : Fin 6)
  | 5 => (0 : Fin 6)
  | 6 => (3 : Fin 6)
  | 7 => (0 : Fin 6)
  | 8 => (3 : Fin 6)
  | 9 => (0 : Fin 6)
  | 10 => (3 : Fin 6)
  | 11 => (0 : Fin 6)
  | 12 => (3 : Fin 6)
  | 13 => (3 : Fin 6)
  | 14 => (0 : Fin 6)
  | 15 => (3 : Fin 6)
  | 16 => (0 : Fin 6)
  | 17 => (3 : Fin 6)
  | 18 => (0 : Fin 6)
  | 19 => (3 : Fin 6)
  | 20 => (0 : Fin 6)
  | 21 => (3 : Fin 6)
  | 22 => (3 : Fin 6)
  | 23 => (0 : Fin 6)
  | 24 => (3 : Fin 6)
  | 25 => (3 : Fin 6)
  | 26 => (0 : Fin 6)
  | 27 => (0 : Fin 6)
  | 28 => (3 : Fin 6)
  | 29 => (0 : Fin 6)
  | 30 => (3 : Fin 6)
  | _ => (0 : Fin 6)

private def sourceLabelChunk5 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (3 : Fin 6)
  | 1 => (0 : Fin 6)
  | 2 => (3 : Fin 6)
  | 3 => (0 : Fin 6)
  | 4 => (3 : Fin 6)
  | 5 => (0 : Fin 6)
  | 6 => (3 : Fin 6)
  | 7 => (0 : Fin 6)
  | 8 => (3 : Fin 6)
  | 9 => (0 : Fin 6)
  | 10 => (3 : Fin 6)
  | 11 => (0 : Fin 6)
  | 12 => (3 : Fin 6)
  | 13 => (0 : Fin 6)
  | 14 => (3 : Fin 6)
  | 15 => (3 : Fin 6)
  | 16 => (0 : Fin 6)
  | 17 => (3 : Fin 6)
  | 18 => (0 : Fin 6)
  | 19 => (3 : Fin 6)
  | 20 => (0 : Fin 6)
  | 21 => (3 : Fin 6)
  | 22 => (0 : Fin 6)
  | 23 => (3 : Fin 6)
  | 24 => (3 : Fin 6)
  | 25 => (0 : Fin 6)
  | 26 => (3 : Fin 6)
  | 27 => (3 : Fin 6)
  | 28 => (0 : Fin 6)
  | 29 => (3 : Fin 6)
  | 30 => (3 : Fin 6)
  | _ => (0 : Fin 6)

private def sourceLabelChunk6 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (3 : Fin 6)
  | 1 => (0 : Fin 6)
  | 2 => (3 : Fin 6)
  | 3 => (0 : Fin 6)
  | 4 => (3 : Fin 6)
  | 5 => (0 : Fin 6)
  | 6 => (3 : Fin 6)
  | 7 => (0 : Fin 6)
  | 8 => (3 : Fin 6)
  | 9 => (0 : Fin 6)
  | 10 => (3 : Fin 6)
  | 11 => (3 : Fin 6)
  | 12 => (0 : Fin 6)
  | 13 => (3 : Fin 6)
  | 14 => (0 : Fin 6)
  | 15 => (3 : Fin 6)
  | 16 => (0 : Fin 6)
  | 17 => (3 : Fin 6)
  | 18 => (0 : Fin 6)
  | 19 => (3 : Fin 6)
  | 20 => (3 : Fin 6)
  | 21 => (0 : Fin 6)
  | 22 => (3 : Fin 6)
  | 23 => (3 : Fin 6)
  | 24 => (0 : Fin 6)
  | 25 => (3 : Fin 6)
  | 26 => (3 : Fin 6)
  | 27 => (0 : Fin 6)
  | 28 => (3 : Fin 6)
  | 29 => (3 : Fin 6)
  | 30 => (0 : Fin 6)
  | _ => (3 : Fin 6)

private def sourceLabelChunk7 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (3 : Fin 6)
  | 1 => (0 : Fin 6)
  | 2 => (3 : Fin 6)
  | 3 => (0 : Fin 6)
  | 4 => (3 : Fin 6)
  | 5 => (0 : Fin 6)
  | 6 => (3 : Fin 6)
  | 7 => (3 : Fin 6)
  | 8 => (0 : Fin 6)
  | 9 => (3 : Fin 6)
  | 10 => (3 : Fin 6)
  | 11 => (0 : Fin 6)
  | 12 => (3 : Fin 6)
  | 13 => (3 : Fin 6)
  | 14 => (0 : Fin 6)
  | 15 => (3 : Fin 6)
  | 16 => (3 : Fin 6)
  | 17 => (0 : Fin 6)
  | 18 => (3 : Fin 6)
  | 19 => (3 : Fin 6)
  | 20 => (3 : Fin 6)
  | 21 => (0 : Fin 6)
  | 22 => (3 : Fin 6)
  | 23 => (3 : Fin 6)
  | 24 => (0 : Fin 6)
  | 25 => (3 : Fin 6)
  | 26 => (3 : Fin 6)
  | 27 => (0 : Fin 6)
  | 28 => (3 : Fin 6)
  | 29 => (3 : Fin 6)
  | 30 => (3 : Fin 6)
  | _ => (0 : Fin 6)

private def sourceLabelChunk8 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (3 : Fin 6)
  | 1 => (3 : Fin 6)
  | _ => (3 : Fin 6)

def sourceLabel (state : Fin 259) : Fin 6 :=
  if state.val < 32 then sourceLabelChunk0 state.val else
    if state.val < 64 then sourceLabelChunk1 (state.val - 32) else
      if state.val < 96 then sourceLabelChunk2 (state.val - 64) else
        if state.val < 128 then sourceLabelChunk3 (state.val - 96) else
          if state.val < 160 then sourceLabelChunk4 (state.val - 128) else
            if state.val < 192 then sourceLabelChunk5 (state.val - 160) else
              if state.val < 224 then sourceLabelChunk6 (state.val - 192) else
                if state.val < 256 then sourceLabelChunk7 (state.val - 224) else
                  sourceLabelChunk8 (state.val - 256)

def generatorSourceLabel (generator : Fin 4) : Fin 6 :=
  match generator.val with
  | 0 => (5 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (3 : Fin 6)
  | _ => (2 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 259 :=
  match value.val with
  | 0 => (5 : Fin 259)
  | 1 => (8 : Fin 259)
  | 2 => (3 : Fin 259)
  | 3 => (2 : Fin 259)
  | 4 => (1 : Fin 259)
  | _ => (0 : Fin 259)

private def stateVectorCode
    (vector : Fin 11 -> Fin 6) : Nat :=
  (vector (0 : Fin 11)).val + 6 * ((vector (1 : Fin 11)).val + 6 * ((vector (2 : Fin 11)).val + 6 * ((vector (3 : Fin 11)).val + 6 * ((vector (4 : Fin 11)).val + 6 * ((vector (5 : Fin 11)).val + 6 * ((vector (6 : Fin 11)).val + 6 * ((vector (7 : Fin 11)).val + 6 * ((vector (8 : Fin 11)).val + 6 * ((vector (9 : Fin 11)).val + 6 * ((vector (10 : Fin 11)).val))))))))))

private def decodeStateCode (code : Nat) : Fin 259 :=
  if code < 302306256 then
    if code < 292098096 then
      if code < 290566296 then
        if code < 290232442 then
          if code < 290050854 then
            if code < 290044800 then
              if code < 290018880 then
                if code < 290014560 then
                  if code = 290013696 then (210 : Fin 259) else (0 : Fin 259)
                else if code = 290014560 then (121 : Fin 259) else
                  (0 : Fin 259)
              else if code = 290018880 then (148 : Fin 259) else
                if code = 290019744 then (57 : Fin 259) else (0 : Fin 259)
            else if code = 290044800 then (129 : Fin 259) else
              if code < 290049984 then
                if code = 290045664 then (41 : Fin 259) else (0 : Fin 259)
              else if code = 290049984 then (66 : Fin 259) else
                if code = 290050848 then (64 : Fin 259) else (0 : Fin 259)
          else if code = 290050854 then (11 : Fin 259) else
            if code < 290206536 then
              if code < 290201328 then
                if code = 290200320 then (123 : Fin 259) else (0 : Fin 259)
              else if code = 290201328 then (38 : Fin 259) else
                if code = 290205504 then (59 : Fin 259) else (0 : Fin 259)
            else if code = 290206536 then (54 : Fin 259) else
              if code < 290231424 then
                if code = 290206537 then (8 : Fin 259) else (0 : Fin 259)
              else if code = 290231424 then (43 : Fin 259) else
                if code = 290232436 then (34 : Fin 259) else (0 : Fin 259)
        else if code = 290232442 then (4 : Fin 259) else
          if code < 290332944 then
            if code < 290294064 then
              if code < 290236644 then
                if code = 290236608 then (68 : Fin 259) else (0 : Fin 259)
              else if code = 290236644 then (13 : Fin 259) else
                if code = 290293632 then (238 : Fin 259) else (0 : Fin 259)
            else if code = 290294064 then (169 : Fin 259) else
              if code < 290299248 then
                if code = 290298816 then (191 : Fin 259) else (0 : Fin 259)
              else if code = 290299248 then (101 : Fin 259) else
                if code = 290332512 then (176 : Fin 259) else (0 : Fin 259)
          else if code = 290332944 then (82 : Fin 259) else
            if code < 290527416 then
              if code < 290338128 then
                if code = 290337696 then (108 : Fin 259) else (0 : Fin 259)
              else if code = 290338128 then (31 : Fin 259) else
                if code = 290526912 then (171 : Fin 259) else (0 : Fin 259)
            else if code = 290527416 then (77 : Fin 259) else
              if code < 290532600 then
                if code = 290532096 then (103 : Fin 259) else (0 : Fin 259)
              else if code = 290532600 then (26 : Fin 259) else
                if code = 290565792 then (84 : Fin 259) else (0 : Fin 259)
      else if code = 290566296 then (17 : Fin 259) else
        if code < 291826440 then
          if code < 291733056 then
            if code < 291694176 then
              if code < 290571516 then
                if code = 290570976 then (33 : Fin 259) else (0 : Fin 259)
              else if code = 290571516 then (3 : Fin 259) else
                if code = 291693312 then (237 : Fin 259) else (0 : Fin 259)
            else if code = 291694176 then (168 : Fin 259) else
              if code < 291700656 then
                if code = 291699792 then (190 : Fin 259) else (0 : Fin 259)
              else if code = 291700656 then (100 : Fin 259) else
                if code = 291732192 then (175 : Fin 259) else (0 : Fin 259)
          else if code = 291733056 then (81 : Fin 259) else
            if code < 291787560 then
              if code < 291739536 then
                if code = 291738672 then (107 : Fin 259) else (0 : Fin 259)
              else if code = 291739536 then (30 : Fin 259) else
                if code = 291786624 then (170 : Fin 259) else (0 : Fin 259)
            else if code = 291787560 then (76 : Fin 259) else
              if code < 291794052 then
                if code = 291793104 then (102 : Fin 259) else (0 : Fin 259)
              else if code = 291794052 then (25 : Fin 259) else
                if code = 291825504 then (83 : Fin 259) else (0 : Fin 259)
        else if code = 291826440 then (16 : Fin 259) else
          if code < 292004784 then
            if code < 291973680 then
              if code < 291832938 then
                if code = 291831984 then (32 : Fin 259) else (0 : Fin 259)
              else if code = 291832938 then (2 : Fin 259) else
                if code = 291973248 then (252 : Fin 259) else (0 : Fin 259)
            else if code = 291973680 then (209 : Fin 259) else
              if code < 291980160 then
                if code = 291979728 then (223 : Fin 259) else (0 : Fin 259)
              else if code = 291980160 then (147 : Fin 259) else
                if code = 292004352 then (214 : Fin 259) else (0 : Fin 259)
          else if code = 292004784 then (128 : Fin 259) else
            if code < 292066992 then
              if code < 292011264 then
                if code = 292010832 then (152 : Fin 259) else (0 : Fin 259)
              else if code = 292011264 then (65 : Fin 259) else
                if code = 292066560 then (211 : Fin 259) else (0 : Fin 259)
            else if code = 292066992 then (122 : Fin 259) else
              if code < 292073472 then
                if code = 292073040 then (149 : Fin 259) else (0 : Fin 259)
              else if code = 292073472 then (58 : Fin 259) else
                if code = 292097664 then (130 : Fin 259) else (0 : Fin 259)
    else if code = 292098096 then (42 : Fin 259) else
      if code < 300485376 then
        if code < 300205440 then
          if code < 300112128 then
            if code < 300096576 then
              if code < 300091392 then
                if code < 292104576 then
                  if code = 292104144 then (67 : Fin 259) else (0 : Fin 259)
                else if code = 292104576 then (12 : Fin 259) else
                  (0 : Fin 259)
              else if code = 300091392 then (257 : Fin 259) else
                if code = 300091824 then (234 : Fin 259) else (0 : Fin 259)
            else if code = 300096576 then (243 : Fin 259) else
              if code < 300106944 then
                if code = 300097008 then (187 : Fin 259) else (0 : Fin 259)
              else if code = 300106944 then (239 : Fin 259) else
                if code = 300107376 then (172 : Fin 259) else (0 : Fin 259)
          else if code = 300112128 then (192 : Fin 259) else
            if code < 300189888 then
              if code < 300184704 then
                if code = 300112560 then (104 : Fin 259) else (0 : Fin 259)
              else if code = 300184704 then (236 : Fin 259) else
                if code = 300185136 then (166 : Fin 259) else (0 : Fin 259)
            else if code = 300189888 then (189 : Fin 259) else
              if code < 300200256 then
                if code = 300190320 then (98 : Fin 259) else (0 : Fin 259)
              else if code = 300200256 then (174 : Fin 259) else
                if code = 300200688 then (79 : Fin 259) else (0 : Fin 259)
        else if code = 300205440 then (106 : Fin 259) else
          if code < 300392064 then
            if code < 300376512 then
              if code < 300371328 then
                if code = 300205872 then (28 : Fin 259) else (0 : Fin 259)
              else if code = 300371328 then (250 : Fin 259) else
                if code = 300372408 then (205 : Fin 259) else (0 : Fin 259)
            else if code = 300376512 then (221 : Fin 259) else
              if code < 300386880 then
                if code = 300377592 then (143 : Fin 259) else (0 : Fin 259)
              else if code = 300386880 then (212 : Fin 259) else
                if code = 300387960 then (124 : Fin 259) else (0 : Fin 259)
          else if code = 300392064 then (150 : Fin 259) else
            if code < 300469824 then
              if code < 300464640 then
                if code = 300393144 then (60 : Fin 259) else (0 : Fin 259)
              else if code = 300464640 then (207 : Fin 259) else
                if code = 300465792 then (119 : Fin 259) else (0 : Fin 259)
            else if code = 300469824 then (145 : Fin 259) else
              if code < 300480192 then
                if code = 300470988 then (55 : Fin 259) else (0 : Fin 259)
              else if code = 300480192 then (126 : Fin 259) else
                if code = 300481344 then (39 : Fin 259) else (0 : Fin 259)
      else if code = 300485376 then (62 : Fin 259) else
        if code < 301979664 then
          if code < 301793040 then
            if code < 301777488 then
              if code < 301771008 then
                if code = 300486540 then (9 : Fin 259) else (0 : Fin 259)
              else if code = 301771008 then (251 : Fin 259) else
                if code = 301771440 then (206 : Fin 259) else (0 : Fin 259)
            else if code = 301777488 then (222 : Fin 259) else
              if code < 301786560 then
                if code = 301777920 then (144 : Fin 259) else (0 : Fin 259)
              else if code = 301786560 then (213 : Fin 259) else
                if code = 301786992 then (125 : Fin 259) else (0 : Fin 259)
          else if code = 301793040 then (151 : Fin 259) else
            if code < 301964112 then
              if code < 301957632 then
                if code = 301793472 then (61 : Fin 259) else (0 : Fin 259)
              else if code = 301957632 then (208 : Fin 259) else
                if code = 301958136 then (120 : Fin 259) else (0 : Fin 259)
            else if code = 301964112 then (146 : Fin 259) else
              if code < 301973184 then
                if code = 301964616 then (56 : Fin 259) else (0 : Fin 259)
              else if code = 301973184 then (127 : Fin 259) else
                if code = 301973688 then (40 : Fin 259) else (0 : Fin 259)
        else if code = 301979664 then (63 : Fin 259) else
          if code < 302072976 then
            if code < 302057424 then
              if code < 302050944 then
                if code = 301980168 then (10 : Fin 259) else (0 : Fin 259)
              else if code = 302050944 then (235 : Fin 259) else
                if code = 302052024 then (165 : Fin 259) else (0 : Fin 259)
            else if code = 302057424 then (188 : Fin 259) else
              if code < 302066496 then
                if code = 302058504 then (97 : Fin 259) else (0 : Fin 259)
              else if code = 302066496 then (173 : Fin 259) else
                if code = 302067576 then (78 : Fin 259) else (0 : Fin 259)
          else if code = 302072976 then (105 : Fin 259) else
            if code < 302290704 then
              if code < 302284224 then
                if code = 302074056 then (27 : Fin 259) else (0 : Fin 259)
              else if code = 302284224 then (167 : Fin 259) else
                if code = 302285484 then (75 : Fin 259) else (0 : Fin 259)
            else if code = 302290704 then (99 : Fin 259) else
              if code < 302299776 then
                if code = 302291994 then (24 : Fin 259) else (0 : Fin 259)
              else if code = 302299776 then (80 : Fin 259) else
                if code = 302301038 then (15 : Fin 259) else (0 : Fin 259)
  else if code = 302306256 then (29 : Fin 259) else
    if code < 352668587 then
      if code < 350887758 then
        if code < 350615088 then
          if code < 350521776 then
            if code < 350482896 then
              if code < 350480304 then
                if code < 350479872 then
                  if code = 302307549 then (1 : Fin 259) else (0 : Fin 259)
                else if code = 350479872 then (256 : Fin 259) else
                  (0 : Fin 259)
              else if code = 350480304 then (228 : Fin 259) else
                if code = 350482464 then (242 : Fin 259) else (0 : Fin 259)
            else if code = 350482896 then (181 : Fin 259) else
              if code < 350519184 then
                if code = 350518752 then (233 : Fin 259) else (0 : Fin 259)
              else if code = 350519184 then (162 : Fin 259) else
                if code = 350521344 then (186 : Fin 259) else (0 : Fin 259)
          else if code = 350521776 then (94 : Fin 259) else
            if code < 350576208 then
              if code < 350573616 then
                if code = 350573184 then (230 : Fin 259) else (0 : Fin 259)
              else if code = 350573616 then (156 : Fin 259) else
                if code = 350575776 then (183 : Fin 259) else (0 : Fin 259)
            else if code = 350576208 then (88 : Fin 259) else
              if code < 350612496 then
                if code = 350612064 then (164 : Fin 259) else (0 : Fin 259)
              else if code = 350612496 then (73 : Fin 259) else
                if code = 350614656 then (96 : Fin 259) else (0 : Fin 259)
        else if code = 350615088 then (22 : Fin 259) else
          if code < 350794368 then
            if code < 350763264 then
              if code < 350760672 then
                if code = 350759808 then (247 : Fin 259) else (0 : Fin 259)
              else if code = 350760672 then (196 : Fin 259) else
                if code = 350762400 then (218 : Fin 259) else (0 : Fin 259)
            else if code = 350763264 then (134 : Fin 259) else
              if code < 350791776 then
                if code = 350790912 then (203 : Fin 259) else (0 : Fin 259)
              else if code = 350791776 then (115 : Fin 259) else
                if code = 350793504 then (141 : Fin 259) else (0 : Fin 259)
          else if code = 350794368 then (50 : Fin 259) else
            if code < 350856648 then
              if code < 350854056 then
                if code = 350853120 then (198 : Fin 259) else (0 : Fin 259)
              else if code = 350854056 then (110 : Fin 259) else
                if code = 350855712 then (136 : Fin 259) else (0 : Fin 259)
            else if code = 350856648 then (45 : Fin 259) else
              if code < 350885160 then
                if code = 350884224 then (117 : Fin 259) else (0 : Fin 259)
              else if code = 350885160 then (36 : Fin 259) else
                if code = 350886816 then (52 : Fin 259) else (0 : Fin 259)
      else if code = 350887758 then (6 : Fin 259) else
        if code < 352426968 then
          if code < 352193616 then
            if code < 352162512 then
              if code < 352159920 then
                if code = 352159488 then (248 : Fin 259) else (0 : Fin 259)
              else if code = 352159920 then (197 : Fin 259) else
                if code = 352162080 then (219 : Fin 259) else (0 : Fin 259)
            else if code = 352162512 then (135 : Fin 259) else
              if code < 352191024 then
                if code = 352190592 then (204 : Fin 259) else (0 : Fin 259)
              else if code = 352191024 then (116 : Fin 259) else
                if code = 352193184 then (142 : Fin 259) else (0 : Fin 259)
          else if code = 352193616 then (51 : Fin 259) else
            if code < 352395864 then
              if code < 352393272 then
                if code = 352392768 then (199 : Fin 259) else (0 : Fin 259)
              else if code = 352393272 then (111 : Fin 259) else
                if code = 352395360 then (137 : Fin 259) else (0 : Fin 259)
            else if code = 352395864 then (46 : Fin 259) else
              if code < 352424376 then
                if code = 352423872 then (118 : Fin 259) else (0 : Fin 259)
              else if code = 352424376 then (37 : Fin 259) else
                if code = 352426464 then (53 : Fin 259) else (0 : Fin 259)
        else if code = 352426968 then (7 : Fin 259) else
          if code < 352481760 then
            if code < 352442880 then
              if code < 352440288 then
                if code = 352439424 then (229 : Fin 259) else (0 : Fin 259)
              else if code = 352440288 then (155 : Fin 259) else
                if code = 352442016 then (182 : Fin 259) else (0 : Fin 259)
            else if code = 352442880 then (87 : Fin 259) else
              if code < 352479168 then
                if code = 352478304 then (163 : Fin 259) else (0 : Fin 259)
              else if code = 352479168 then (72 : Fin 259) else
                if code = 352480896 then (95 : Fin 259) else (0 : Fin 259)
          else if code = 352481760 then (21 : Fin 259) else
            if code < 352629696 then
              if code < 352627092 then
                if code = 352626048 then (157 : Fin 259) else (0 : Fin 259)
              else if code = 352627092 then (69 : Fin 259) else
                if code = 352628640 then (89 : Fin 259) else (0 : Fin 259)
            else if code = 352629696 then (18 : Fin 259) else
              if code < 352665977 then
                if code = 352664928 then (74 : Fin 259) else (0 : Fin 259)
              else if code = 352665977 then (14 : Fin 259) else
                if code = 352667520 then (23 : Fin 259) else (0 : Fin 259)
    else if code = 352668587 then (0 : Fin 259) else
      if code < 362237184 then
        if code < 360837504 then
          if code < 360790848 then
            if code < 360573120 then
              if code < 360560160 then
                if code < 360558648 then
                  if code = 360557568 then (245 : Fin 259) else (0 : Fin 259)
                else if code = 360558648 then (193 : Fin 259) else
                  (0 : Fin 259)
              else if code = 360560160 then (216 : Fin 259) else
                if code = 360561240 then (131 : Fin 259) else (0 : Fin 259)
            else if code = 360573120 then (201 : Fin 259) else
              if code < 360575712 then
                if code = 360574200 then (112 : Fin 259) else (0 : Fin 259)
              else if code = 360575712 then (139 : Fin 259) else
                if code = 360576792 then (47 : Fin 259) else (0 : Fin 259)
          else if code = 360790848 then (195 : Fin 259) else
            if code < 360806400 then
              if code < 360793440 then
                if code = 360792072 then (109 : Fin 259) else (0 : Fin 259)
              else if code = 360793440 then (133 : Fin 259) else
                if code = 360794676 then (44 : Fin 259) else (0 : Fin 259)
            else if code = 360806400 then (114 : Fin 259) else
              if code < 360808992 then
                if code = 360807626 then (35 : Fin 259) else (0 : Fin 259)
              else if code = 360808992 then (49 : Fin 259) else
                if code = 360810230 then (5 : Fin 259) else (0 : Fin 259)
        else if code = 360837504 then (255 : Fin 259) else
          if code < 361024128 then
            if code < 360853056 then
              if code < 360840096 then
                if code = 360837936 then (225 : Fin 259) else (0 : Fin 259)
              else if code = 360840096 then (241 : Fin 259) else
                if code = 360840528 then (178 : Fin 259) else (0 : Fin 259)
            else if code = 360853056 then (232 : Fin 259) else
              if code < 360855648 then
                if code = 360853488 then (159 : Fin 259) else (0 : Fin 259)
              else if code = 360855648 then (185 : Fin 259) else
                if code = 360856080 then (91 : Fin 259) else (0 : Fin 259)
          else if code = 361024128 then (227 : Fin 259) else
            if code < 361039680 then
              if code < 361026720 then
                if code = 361024632 then (154 : Fin 259) else (0 : Fin 259)
              else if code = 361026720 then (180 : Fin 259) else
                if code = 361027224 then (86 : Fin 259) else (0 : Fin 259)
            else if code = 361039680 then (161 : Fin 259) else
              if code < 361042272 then
                if code = 361040184 then (71 : Fin 259) else (0 : Fin 259)
              else if code = 361042272 then (93 : Fin 259) else
                if code = 361042776 then (20 : Fin 259) else (0 : Fin 259)
      else if code = 362237184 then (254 : Fin 259) else
        if code < 362517120 then
          if code < 362330496 then
            if code < 362252736 then
              if code < 362239776 then
                if code = 362238264 then (224 : Fin 259) else (0 : Fin 259)
              else if code = 362239776 then (240 : Fin 259) else
                if code = 362240856 then (177 : Fin 259) else (0 : Fin 259)
            else if code = 362252736 then (231 : Fin 259) else
              if code < 362255328 then
                if code = 362253816 then (158 : Fin 259) else (0 : Fin 259)
              else if code = 362255328 then (184 : Fin 259) else
                if code = 362256408 then (90 : Fin 259) else (0 : Fin 259)
          else if code = 362330496 then (226 : Fin 259) else
            if code < 362346048 then
              if code < 362333088 then
                if code = 362331648 then (153 : Fin 259) else (0 : Fin 259)
              else if code = 362333088 then (179 : Fin 259) else
                if code = 362334240 then (85 : Fin 259) else (0 : Fin 259)
            else if code = 362346048 then (160 : Fin 259) else
              if code < 362348640 then
                if code = 362347200 then (70 : Fin 259) else (0 : Fin 259)
              else if code = 362348640 then (92 : Fin 259) else
                if code = 362349792 then (19 : Fin 259) else (0 : Fin 259)
        else if code = 362517120 then (258 : Fin 259) else
          if code < 362610432 then
            if code < 362532672 then
              if code < 362519712 then
                if code = 362517552 then (244 : Fin 259) else (0 : Fin 259)
              else if code = 362519712 then (253 : Fin 259) else
                if code = 362520144 then (215 : Fin 259) else (0 : Fin 259)
            else if code = 362532672 then (249 : Fin 259) else
              if code < 362535264 then
                if code = 362533104 then (200 : Fin 259) else (0 : Fin 259)
              else if code = 362535264 then (220 : Fin 259) else
                if code = 362535696 then (138 : Fin 259) else (0 : Fin 259)
          else if code = 362610432 then (246 : Fin 259) else
            if code < 362625984 then
              if code < 362613024 then
                if code = 362610864 then (194 : Fin 259) else (0 : Fin 259)
              else if code = 362613024 then (217 : Fin 259) else
                if code = 362613456 then (132 : Fin 259) else (0 : Fin 259)
            else if code = 362625984 then (202 : Fin 259) else
              if code < 362628576 then
                if code = 362626416 then (113 : Fin 259) else (0 : Fin 259)
              else if code = 362628576 then (140 : Fin 259) else
                if code = 362629008 then (48 : Fin 259) else (0 : Fin 259)

private def decodeState
    (vector : Fin 11 -> Fin 6) : Fin 259 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 259) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 259)
      (generator : Fin 4)
      (coordinate : Fin 11),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem representativeMap :
    forall (state : Fin 259)
      (coordinate : Fin 11),
      stateVector state coordinate =
        (representativeTail state).foldl
          (fun value generator =>
            oppositeTable.semigroup.mul value
              (generatorVector generator coordinate))
          (generatorVector (representativeHead state) coordinate) := by
  intro state coordinate
  apply Fin.ext
  exact by decide +revert

/-- Reduced term-function states embedded in a finite power of the target. -/
def powerCertificate : RightGeneratedPowerCertificate
    (U := Fin 259)
    (G := Fin 4)
    (I := Fin 11) oppositeTable.semigroup where
  stateVector := stateVector
  generatorVector := generatorVector
  transition := transition
  representativeHead := representativeHead
  representativeTail := representativeTail
  injective := by
    intro left right equalVectors
    exact
      (decodeState_stateVector left).symm.trans <|
        (congrArg decodeState equalVectors).trans <|
          decodeState_stateVector right
  transition_map := transitionMap
  representative_map := representativeMap

set_option maxHeartbeats 2000000 in
private theorem sourceLabelTransition :
    forall (state : Fin 259)
      (generator : Fin 4),
      sourceLabel (transition state generator) =
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul (sourceLabel state)
          (generatorSourceLabel generator) := by
  intro state generator
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem sourceLabelRepresentative :
    forall state : Fin 259,
      sourceLabel state =
        (representativeTail state).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (generatorSourceLabel (representativeHead state)) := by
  intro state
  apply Fin.ext
  exact by decide +revert

private theorem sourceLabelRightMultiplyWord
    (state : Fin 259)
    (word : List (Fin 4)) :
    sourceLabel (powerCertificate.rightMultiplyWord state word) =
      word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul value
            (generatorSourceLabel generator))
        (sourceLabel state) := by
  induction word generalizing state with
  | nil => rfl
  | cons generator word inductionHypothesis =>
      change
        sourceLabel
            (powerCertificate.rightMultiplyWord
              (transition state generator) word) =
          word.foldl
            (fun value nextGenerator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul value
                (generatorSourceLabel nextGenerator))
            (SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul (sourceLabel state)
              (generatorSourceLabel generator))
      rw [inductionHypothesis]
      rw [sourceLabelTransition]

private theorem sourceFoldlGeneratorAssoc
    (left right : Fin 6)
    (word : List (Fin 4)) :
    word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul value
            (generatorSourceLabel generator))
        (SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul left right) =
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul left
        (word.foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          right) := by
  induction word generalizing right with
  | nil => rfl
  | cons generator word inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.assoc]
      exact inductionHypothesis
        (SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul right (generatorSourceLabel generator))

private theorem sourceLabelMapMul :
    forall (left right : Fin 259),
      sourceLabel (powerCertificate.semigroup.mul left right) =
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul (sourceLabel left) (sourceLabel right) := by
  intro left right
  calc
    sourceLabel (powerCertificate.semigroup.mul left right) =
        sourceLabel
          (powerCertificate.rightMultiplyWord
            (transition left (representativeHead right))
            (representativeTail right)) := rfl
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (sourceLabel (transition left (representativeHead right))) :=
      sourceLabelRightMultiplyWord _ _
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul (sourceLabel left)
            (generatorSourceLabel (representativeHead right))) :=
      congrArg
        (fun initial =>
          (representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul value
                (generatorSourceLabel generator))
            initial)
        (sourceLabelTransition left (representativeHead right))
    _ = SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul (sourceLabel left)
          ((representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul value
                (generatorSourceLabel generator))
            (generatorSourceLabel (representativeHead right))) :=
      sourceFoldlGeneratorAssoc _ _ _
    _ = SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul (sourceLabel left) (sourceLabel right) :=
      congrArg (SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup.mul (sourceLabel left))
        (sourceLabelRepresentative right).symm

set_option maxHeartbeats 1000000 in
private theorem sourceLabelRightInverse :
    forall value : Fin 6, sourceLabel (sourcePreimage value) = value := by
  intro value
  apply Fin.ext
  exact by decide +revert

/-- The generated term-function semigroup maps onto the selected root. -/
def quotient : SplitSurjection powerCertificate.semigroup
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup where
  toFun := sourceLabel
  map_mul := sourceLabelMapMul
  preimage := sourcePreimage
  right_inverse := sourceLabelRightInverse

private def targetLaw0ToFinite : Nat -> Fin 2
  | 0 => (0 : Fin 2)
  | 1 => (1 : Fin 2)
  | _ => (0 : Fin 2)

private def targetLaw0FromFinite (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw0Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.law0.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.law0
    targetLaw0ToFinite targetLaw0FromFinite (by decide) (by decide)

private def targetLaw1ToFinite : Nat -> Fin 1
  | 0 => (0 : Fin 1)
  | _ => (0 : Fin 1)

private def targetLaw1FromFinite (index : Fin 1) : Nat :=
  match index.val with
  | 0 => 0
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw1Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.law1.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.law1
    targetLaw1ToFinite targetLaw1FromFinite (by decide) (by decide)

private def targetLaw2ToFinite : Nat -> Fin 2
  | 0 => (0 : Fin 2)
  | 1 => (1 : Fin 2)
  | _ => (0 : Fin 2)

private def targetLaw2FromFinite (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw2Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.law2.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.law2
    targetLaw2ToFinite targetLaw2FromFinite (by decide) (by decide)

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.basis := by
  unfold SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_cons targetLaw2Valid <|
          FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

/-- Exact identity-theory transfer authenticated by the finite certificate. -/
theorem sameIdentityTheory :
    SameIdentityTheoryOver SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.oppositeTable.semigroup
      oppositeTable.semigroup Nat := by
  intro identity
  constructor
  · intro sourceValid valuation
    exact Derives.sound targetModels
      (SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_2850.basisFor.2 identity sourceValid) valuation
  · intro targetValid
    have powerValid :=
      identity.satisfiedByPi oppositeTable.semigroup
        (Fin 11) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_5425`. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.basis := by
  have transferred :
      BasisFor oppositeTable.semigroup SemigroupBasis.Generated.Order6GenericCASRootData.S6_2850.basis :=
    (basisFor_iff_of_sameIdentityTheoryOver sameIdentityTheory).mp
      SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_2850.basisFor
  simpa only [oppositeTable_semigroup] using transferred

end SemigroupBasis.Generated.Order6GenericCASRootWrappers.S6_5425
