import SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_1250
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6GenericCASRootWrappers.S6_5790

open SemigroupBasis

def routeManifestRowSHA256 : String := "02ebd8ded9f3b804c2995e435a8c5e7ae25fe57f675ede9e4ee4122ea083b1bc"
def witnessRecordSHA256 : String := "54b3e22a0a8919fca82f9e769792b9a7d72907663c821b9f24ce855bd9cf809e"
def transferComponentSHA256 : String := "716800162167cebe119bae3491f70a54c914a78c6a3c26eb67371da47edbce34"
def powerCertificateSHA256 : String := "447bbe6c1bb302325d351bb74c4f45292495ab754311e97f8b93524ef9604e2a"

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
      if left = 2 then row6 0 0 0 0 0 1 right else
        if left = 3 then row6 0 0 0 3 4 3 right else
          if left = 4 then row6 0 0 0 4 3 4 right else
            row6 0 0 1 3 4 3 right

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
  "efa4b5dcfeee4b45bf2312ed1f0419af755895747cf3c4152062d68b804d148b"

private def stateVectorChunk0 (index : Nat)
    (coordinate : Fin 12) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)

private def stateVectorChunk1 (index : Nat)
    (coordinate : Fin 12) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)

private def stateVectorChunk2 (index : Nat)
    (coordinate : Fin 12) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)

def stateVector (state : Fin 90)
    (coordinate : Fin 12) : Fin 6 :=
  if state.val < 32 then stateVectorChunk0 state.val coordinate else
    if state.val < 64 then stateVectorChunk1 (state.val - 32) coordinate else
      stateVectorChunk2 (state.val - 64) coordinate

def generatorVector (generator : Fin 4)
    (coordinate : Fin 12) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (4 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (4 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (4 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (4 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (4 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | _ => (3 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (2 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | 5 => (3 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (4 : Fin 6)
      | 8 => (4 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | _ => (3 : Fin 6)

private def transitionChunk0 (index : Nat)
    (generator : Fin 4) : Fin 90 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (4 : Fin 90)
      | 1 => (5 : Fin 90)
      | 2 => (6 : Fin 90)
      | _ => (7 : Fin 90)
  | 1 =>
      match generator.val with
      | 0 => (5 : Fin 90)
      | 1 => (8 : Fin 90)
      | 2 => (9 : Fin 90)
      | _ => (10 : Fin 90)
  | 2 =>
      match generator.val with
      | 0 => (6 : Fin 90)
      | 1 => (9 : Fin 90)
      | 2 => (11 : Fin 90)
      | _ => (12 : Fin 90)
  | 3 =>
      match generator.val with
      | 0 => (7 : Fin 90)
      | 1 => (10 : Fin 90)
      | 2 => (12 : Fin 90)
      | _ => (13 : Fin 90)
  | 4 =>
      match generator.val with
      | 0 => (14 : Fin 90)
      | 1 => (15 : Fin 90)
      | 2 => (16 : Fin 90)
      | _ => (17 : Fin 90)
  | 5 =>
      match generator.val with
      | 0 => (15 : Fin 90)
      | 1 => (18 : Fin 90)
      | 2 => (19 : Fin 90)
      | _ => (20 : Fin 90)
  | 6 =>
      match generator.val with
      | 0 => (16 : Fin 90)
      | 1 => (19 : Fin 90)
      | 2 => (21 : Fin 90)
      | _ => (22 : Fin 90)
  | 7 =>
      match generator.val with
      | 0 => (17 : Fin 90)
      | 1 => (20 : Fin 90)
      | 2 => (22 : Fin 90)
      | _ => (23 : Fin 90)
  | 8 =>
      match generator.val with
      | 0 => (18 : Fin 90)
      | 1 => (24 : Fin 90)
      | 2 => (25 : Fin 90)
      | _ => (26 : Fin 90)
  | 9 =>
      match generator.val with
      | 0 => (19 : Fin 90)
      | 1 => (25 : Fin 90)
      | 2 => (27 : Fin 90)
      | _ => (28 : Fin 90)
  | 10 =>
      match generator.val with
      | 0 => (20 : Fin 90)
      | 1 => (26 : Fin 90)
      | 2 => (28 : Fin 90)
      | _ => (29 : Fin 90)
  | 11 =>
      match generator.val with
      | 0 => (21 : Fin 90)
      | 1 => (27 : Fin 90)
      | 2 => (30 : Fin 90)
      | _ => (31 : Fin 90)
  | 12 =>
      match generator.val with
      | 0 => (22 : Fin 90)
      | 1 => (28 : Fin 90)
      | 2 => (31 : Fin 90)
      | _ => (32 : Fin 90)
  | 13 =>
      match generator.val with
      | 0 => (23 : Fin 90)
      | 1 => (29 : Fin 90)
      | 2 => (32 : Fin 90)
      | _ => (33 : Fin 90)
  | 14 =>
      match generator.val with
      | 0 => (4 : Fin 90)
      | 1 => (34 : Fin 90)
      | 2 => (35 : Fin 90)
      | _ => (36 : Fin 90)
  | 15 =>
      match generator.val with
      | 0 => (34 : Fin 90)
      | 1 => (37 : Fin 90)
      | 2 => (38 : Fin 90)
      | _ => (39 : Fin 90)
  | 16 =>
      match generator.val with
      | 0 => (35 : Fin 90)
      | 1 => (38 : Fin 90)
      | 2 => (40 : Fin 90)
      | _ => (41 : Fin 90)
  | 17 =>
      match generator.val with
      | 0 => (36 : Fin 90)
      | 1 => (39 : Fin 90)
      | 2 => (41 : Fin 90)
      | _ => (42 : Fin 90)
  | 18 =>
      match generator.val with
      | 0 => (37 : Fin 90)
      | 1 => (34 : Fin 90)
      | 2 => (43 : Fin 90)
      | _ => (44 : Fin 90)
  | 19 =>
      match generator.val with
      | 0 => (38 : Fin 90)
      | 1 => (43 : Fin 90)
      | 2 => (45 : Fin 90)
      | _ => (46 : Fin 90)
  | 20 =>
      match generator.val with
      | 0 => (39 : Fin 90)
      | 1 => (44 : Fin 90)
      | 2 => (46 : Fin 90)
      | _ => (47 : Fin 90)
  | 21 =>
      match generator.val with
      | 0 => (40 : Fin 90)
      | 1 => (45 : Fin 90)
      | 2 => (35 : Fin 90)
      | _ => (48 : Fin 90)
  | 22 =>
      match generator.val with
      | 0 => (41 : Fin 90)
      | 1 => (46 : Fin 90)
      | 2 => (48 : Fin 90)
      | _ => (49 : Fin 90)
  | 23 =>
      match generator.val with
      | 0 => (42 : Fin 90)
      | 1 => (47 : Fin 90)
      | 2 => (49 : Fin 90)
      | _ => (36 : Fin 90)
  | 24 =>
      match generator.val with
      | 0 => (34 : Fin 90)
      | 1 => (8 : Fin 90)
      | 2 => (50 : Fin 90)
      | _ => (51 : Fin 90)
  | 25 =>
      match generator.val with
      | 0 => (43 : Fin 90)
      | 1 => (50 : Fin 90)
      | 2 => (52 : Fin 90)
      | _ => (53 : Fin 90)
  | 26 =>
      match generator.val with
      | 0 => (44 : Fin 90)
      | 1 => (51 : Fin 90)
      | 2 => (53 : Fin 90)
      | _ => (54 : Fin 90)
  | 27 =>
      match generator.val with
      | 0 => (45 : Fin 90)
      | 1 => (52 : Fin 90)
      | 2 => (50 : Fin 90)
      | _ => (55 : Fin 90)
  | 28 =>
      match generator.val with
      | 0 => (46 : Fin 90)
      | 1 => (53 : Fin 90)
      | 2 => (55 : Fin 90)
      | _ => (56 : Fin 90)
  | 29 =>
      match generator.val with
      | 0 => (47 : Fin 90)
      | 1 => (54 : Fin 90)
      | 2 => (56 : Fin 90)
      | _ => (51 : Fin 90)
  | 30 =>
      match generator.val with
      | 0 => (35 : Fin 90)
      | 1 => (50 : Fin 90)
      | 2 => (11 : Fin 90)
      | _ => (57 : Fin 90)
  | _ =>
      match generator.val with
      | 0 => (48 : Fin 90)
      | 1 => (55 : Fin 90)
      | 2 => (57 : Fin 90)
      | _ => (58 : Fin 90)

private def transitionChunk1 (index : Nat)
    (generator : Fin 4) : Fin 90 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (49 : Fin 90)
      | 1 => (56 : Fin 90)
      | 2 => (58 : Fin 90)
      | _ => (57 : Fin 90)
  | 1 =>
      match generator.val with
      | 0 => (36 : Fin 90)
      | 1 => (51 : Fin 90)
      | 2 => (57 : Fin 90)
      | _ => (13 : Fin 90)
  | 2 =>
      match generator.val with
      | 0 => (15 : Fin 90)
      | 1 => (18 : Fin 90)
      | 2 => (19 : Fin 90)
      | _ => (20 : Fin 90)
  | 3 =>
      match generator.val with
      | 0 => (16 : Fin 90)
      | 1 => (19 : Fin 90)
      | 2 => (21 : Fin 90)
      | _ => (22 : Fin 90)
  | 4 =>
      match generator.val with
      | 0 => (17 : Fin 90)
      | 1 => (20 : Fin 90)
      | 2 => (22 : Fin 90)
      | _ => (23 : Fin 90)
  | 5 =>
      match generator.val with
      | 0 => (18 : Fin 90)
      | 1 => (15 : Fin 90)
      | 2 => (59 : Fin 90)
      | _ => (60 : Fin 90)
  | 6 =>
      match generator.val with
      | 0 => (19 : Fin 90)
      | 1 => (59 : Fin 90)
      | 2 => (61 : Fin 90)
      | _ => (62 : Fin 90)
  | 7 =>
      match generator.val with
      | 0 => (20 : Fin 90)
      | 1 => (60 : Fin 90)
      | 2 => (62 : Fin 90)
      | _ => (63 : Fin 90)
  | 8 =>
      match generator.val with
      | 0 => (21 : Fin 90)
      | 1 => (61 : Fin 90)
      | 2 => (16 : Fin 90)
      | _ => (64 : Fin 90)
  | 9 =>
      match generator.val with
      | 0 => (22 : Fin 90)
      | 1 => (62 : Fin 90)
      | 2 => (64 : Fin 90)
      | _ => (65 : Fin 90)
  | 10 =>
      match generator.val with
      | 0 => (23 : Fin 90)
      | 1 => (63 : Fin 90)
      | 2 => (65 : Fin 90)
      | _ => (17 : Fin 90)
  | 11 =>
      match generator.val with
      | 0 => (59 : Fin 90)
      | 1 => (19 : Fin 90)
      | 2 => (66 : Fin 90)
      | _ => (67 : Fin 90)
  | 12 =>
      match generator.val with
      | 0 => (60 : Fin 90)
      | 1 => (20 : Fin 90)
      | 2 => (67 : Fin 90)
      | _ => (68 : Fin 90)
  | 13 =>
      match generator.val with
      | 0 => (61 : Fin 90)
      | 1 => (66 : Fin 90)
      | 2 => (19 : Fin 90)
      | _ => (69 : Fin 90)
  | 14 =>
      match generator.val with
      | 0 => (62 : Fin 90)
      | 1 => (67 : Fin 90)
      | 2 => (69 : Fin 90)
      | _ => (70 : Fin 90)
  | 15 =>
      match generator.val with
      | 0 => (63 : Fin 90)
      | 1 => (68 : Fin 90)
      | 2 => (70 : Fin 90)
      | _ => (20 : Fin 90)
  | 16 =>
      match generator.val with
      | 0 => (64 : Fin 90)
      | 1 => (69 : Fin 90)
      | 2 => (22 : Fin 90)
      | _ => (71 : Fin 90)
  | 17 =>
      match generator.val with
      | 0 => (65 : Fin 90)
      | 1 => (70 : Fin 90)
      | 2 => (71 : Fin 90)
      | _ => (22 : Fin 90)
  | 18 =>
      match generator.val with
      | 0 => (19 : Fin 90)
      | 1 => (25 : Fin 90)
      | 2 => (27 : Fin 90)
      | _ => (28 : Fin 90)
  | 19 =>
      match generator.val with
      | 0 => (20 : Fin 90)
      | 1 => (26 : Fin 90)
      | 2 => (28 : Fin 90)
      | _ => (29 : Fin 90)
  | 20 =>
      match generator.val with
      | 0 => (66 : Fin 90)
      | 1 => (27 : Fin 90)
      | 2 => (25 : Fin 90)
      | _ => (72 : Fin 90)
  | 21 =>
      match generator.val with
      | 0 => (67 : Fin 90)
      | 1 => (28 : Fin 90)
      | 2 => (72 : Fin 90)
      | _ => (73 : Fin 90)
  | 22 =>
      match generator.val with
      | 0 => (68 : Fin 90)
      | 1 => (29 : Fin 90)
      | 2 => (73 : Fin 90)
      | _ => (26 : Fin 90)
  | 23 =>
      match generator.val with
      | 0 => (69 : Fin 90)
      | 1 => (72 : Fin 90)
      | 2 => (28 : Fin 90)
      | _ => (74 : Fin 90)
  | 24 =>
      match generator.val with
      | 0 => (70 : Fin 90)
      | 1 => (73 : Fin 90)
      | 2 => (74 : Fin 90)
      | _ => (28 : Fin 90)
  | 25 =>
      match generator.val with
      | 0 => (22 : Fin 90)
      | 1 => (28 : Fin 90)
      | 2 => (31 : Fin 90)
      | _ => (32 : Fin 90)
  | 26 =>
      match generator.val with
      | 0 => (71 : Fin 90)
      | 1 => (74 : Fin 90)
      | 2 => (32 : Fin 90)
      | _ => (31 : Fin 90)
  | 27 =>
      match generator.val with
      | 0 => (43 : Fin 90)
      | 1 => (38 : Fin 90)
      | 2 => (75 : Fin 90)
      | _ => (76 : Fin 90)
  | 28 =>
      match generator.val with
      | 0 => (44 : Fin 90)
      | 1 => (39 : Fin 90)
      | 2 => (76 : Fin 90)
      | _ => (77 : Fin 90)
  | 29 =>
      match generator.val with
      | 0 => (45 : Fin 90)
      | 1 => (75 : Fin 90)
      | 2 => (38 : Fin 90)
      | _ => (78 : Fin 90)
  | 30 =>
      match generator.val with
      | 0 => (46 : Fin 90)
      | 1 => (76 : Fin 90)
      | 2 => (78 : Fin 90)
      | _ => (79 : Fin 90)
  | _ =>
      match generator.val with
      | 0 => (47 : Fin 90)
      | 1 => (77 : Fin 90)
      | 2 => (79 : Fin 90)
      | _ => (39 : Fin 90)

private def transitionChunk2 (index : Nat)
    (generator : Fin 4) : Fin 90 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (48 : Fin 90)
      | 1 => (78 : Fin 90)
      | 2 => (41 : Fin 90)
      | _ => (80 : Fin 90)
  | 1 =>
      match generator.val with
      | 0 => (49 : Fin 90)
      | 1 => (79 : Fin 90)
      | 2 => (80 : Fin 90)
      | _ => (41 : Fin 90)
  | 2 =>
      match generator.val with
      | 0 => (75 : Fin 90)
      | 1 => (45 : Fin 90)
      | 2 => (43 : Fin 90)
      | _ => (81 : Fin 90)
  | 3 =>
      match generator.val with
      | 0 => (76 : Fin 90)
      | 1 => (46 : Fin 90)
      | 2 => (81 : Fin 90)
      | _ => (82 : Fin 90)
  | 4 =>
      match generator.val with
      | 0 => (77 : Fin 90)
      | 1 => (47 : Fin 90)
      | 2 => (82 : Fin 90)
      | _ => (44 : Fin 90)
  | 5 =>
      match generator.val with
      | 0 => (78 : Fin 90)
      | 1 => (81 : Fin 90)
      | 2 => (46 : Fin 90)
      | _ => (83 : Fin 90)
  | 6 =>
      match generator.val with
      | 0 => (79 : Fin 90)
      | 1 => (82 : Fin 90)
      | 2 => (83 : Fin 90)
      | _ => (46 : Fin 90)
  | 7 =>
      match generator.val with
      | 0 => (80 : Fin 90)
      | 1 => (83 : Fin 90)
      | 2 => (49 : Fin 90)
      | _ => (48 : Fin 90)
  | 8 =>
      match generator.val with
      | 0 => (81 : Fin 90)
      | 1 => (55 : Fin 90)
      | 2 => (53 : Fin 90)
      | _ => (84 : Fin 90)
  | 9 =>
      match generator.val with
      | 0 => (82 : Fin 90)
      | 1 => (56 : Fin 90)
      | 2 => (84 : Fin 90)
      | _ => (53 : Fin 90)
  | 10 =>
      match generator.val with
      | 0 => (83 : Fin 90)
      | 1 => (84 : Fin 90)
      | 2 => (56 : Fin 90)
      | _ => (55 : Fin 90)
  | 11 =>
      match generator.val with
      | 0 => (66 : Fin 90)
      | 1 => (61 : Fin 90)
      | 2 => (59 : Fin 90)
      | _ => (85 : Fin 90)
  | 12 =>
      match generator.val with
      | 0 => (67 : Fin 90)
      | 1 => (62 : Fin 90)
      | 2 => (85 : Fin 90)
      | _ => (86 : Fin 90)
  | 13 =>
      match generator.val with
      | 0 => (68 : Fin 90)
      | 1 => (63 : Fin 90)
      | 2 => (86 : Fin 90)
      | _ => (60 : Fin 90)
  | 14 =>
      match generator.val with
      | 0 => (69 : Fin 90)
      | 1 => (85 : Fin 90)
      | 2 => (62 : Fin 90)
      | _ => (87 : Fin 90)
  | 15 =>
      match generator.val with
      | 0 => (70 : Fin 90)
      | 1 => (86 : Fin 90)
      | 2 => (87 : Fin 90)
      | _ => (62 : Fin 90)
  | 16 =>
      match generator.val with
      | 0 => (71 : Fin 90)
      | 1 => (87 : Fin 90)
      | 2 => (65 : Fin 90)
      | _ => (64 : Fin 90)
  | 17 =>
      match generator.val with
      | 0 => (85 : Fin 90)
      | 1 => (69 : Fin 90)
      | 2 => (67 : Fin 90)
      | _ => (88 : Fin 90)
  | 18 =>
      match generator.val with
      | 0 => (86 : Fin 90)
      | 1 => (70 : Fin 90)
      | 2 => (88 : Fin 90)
      | _ => (67 : Fin 90)
  | 19 =>
      match generator.val with
      | 0 => (87 : Fin 90)
      | 1 => (88 : Fin 90)
      | 2 => (70 : Fin 90)
      | _ => (69 : Fin 90)
  | 20 =>
      match generator.val with
      | 0 => (88 : Fin 90)
      | 1 => (74 : Fin 90)
      | 2 => (73 : Fin 90)
      | _ => (72 : Fin 90)
  | 21 =>
      match generator.val with
      | 0 => (81 : Fin 90)
      | 1 => (78 : Fin 90)
      | 2 => (76 : Fin 90)
      | _ => (89 : Fin 90)
  | 22 =>
      match generator.val with
      | 0 => (82 : Fin 90)
      | 1 => (79 : Fin 90)
      | 2 => (89 : Fin 90)
      | _ => (76 : Fin 90)
  | 23 =>
      match generator.val with
      | 0 => (83 : Fin 90)
      | 1 => (89 : Fin 90)
      | 2 => (79 : Fin 90)
      | _ => (78 : Fin 90)
  | 24 =>
      match generator.val with
      | 0 => (89 : Fin 90)
      | 1 => (83 : Fin 90)
      | 2 => (82 : Fin 90)
      | _ => (81 : Fin 90)
  | _ =>
      match generator.val with
      | 0 => (88 : Fin 90)
      | 1 => (87 : Fin 90)
      | 2 => (86 : Fin 90)
      | _ => (85 : Fin 90)

def transition (state : Fin 90)
    (generator : Fin 4) : Fin 90 :=
  if state.val < 32 then transitionChunk0 state.val generator else
    if state.val < 64 then transitionChunk1 (state.val - 32) generator else
      transitionChunk2 (state.val - 64) generator

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
  | 18 => (1 : Fin 4)
  | 19 => (1 : Fin 4)
  | 20 => (1 : Fin 4)
  | 21 => (1 : Fin 4)
  | 22 => (1 : Fin 4)
  | 23 => (1 : Fin 4)
  | 24 => (1 : Fin 4)
  | 25 => (2 : Fin 4)
  | 26 => (2 : Fin 4)
  | 27 => (0 : Fin 4)
  | 28 => (0 : Fin 4)
  | 29 => (0 : Fin 4)
  | 30 => (0 : Fin 4)
  | _ => (0 : Fin 4)

private def representativeHeadChunk2 (index : Nat) : Fin 4 :=
  match index with
  | 0 => (0 : Fin 4)
  | 1 => (0 : Fin 4)
  | 2 => (0 : Fin 4)
  | 3 => (0 : Fin 4)
  | 4 => (0 : Fin 4)
  | 5 => (0 : Fin 4)
  | 6 => (0 : Fin 4)
  | 7 => (0 : Fin 4)
  | 8 => (1 : Fin 4)
  | 9 => (1 : Fin 4)
  | 10 => (1 : Fin 4)
  | 11 => (0 : Fin 4)
  | 12 => (0 : Fin 4)
  | 13 => (0 : Fin 4)
  | 14 => (0 : Fin 4)
  | 15 => (0 : Fin 4)
  | 16 => (0 : Fin 4)
  | 17 => (0 : Fin 4)
  | 18 => (0 : Fin 4)
  | 19 => (0 : Fin 4)
  | 20 => (1 : Fin 4)
  | 21 => (0 : Fin 4)
  | 22 => (0 : Fin 4)
  | 23 => (0 : Fin 4)
  | 24 => (0 : Fin 4)
  | _ => (0 : Fin 4)

def representativeHead (state : Fin 90) : Fin 4 :=
  if state.val < 32 then representativeHeadChunk0 state.val else
    if state.val < 64 then representativeHeadChunk1 (state.val - 32) else
      representativeHeadChunk2 (state.val - 64)

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
  | 2 => [0, 0, 1]
  | 3 => [0, 0, 2]
  | 4 => [0, 0, 3]
  | 5 => [0, 1, 1]
  | 6 => [0, 1, 2]
  | 7 => [0, 1, 3]
  | 8 => [0, 2, 2]
  | 9 => [0, 2, 3]
  | 10 => [0, 3, 3]
  | 11 => [1, 1, 2]
  | 12 => [1, 1, 3]
  | 13 => [1, 2, 2]
  | 14 => [1, 2, 3]
  | 15 => [1, 3, 3]
  | 16 => [2, 2, 3]
  | 17 => [2, 3, 3]
  | 18 => [1, 1, 2]
  | 19 => [1, 1, 3]
  | 20 => [1, 2, 2]
  | 21 => [1, 2, 3]
  | 22 => [1, 3, 3]
  | 23 => [2, 2, 3]
  | 24 => [2, 3, 3]
  | 25 => [2, 2, 3]
  | 26 => [2, 3, 3]
  | 27 => [0, 1, 1, 2]
  | 28 => [0, 1, 1, 3]
  | 29 => [0, 1, 2, 2]
  | 30 => [0, 1, 2, 3]
  | _ => [0, 1, 3, 3]

private def representativeTailChunk2 (index : Nat) :
    List (Fin 4) :=
  match index with
  | 0 => [0, 2, 2, 3]
  | 1 => [0, 2, 3, 3]
  | 2 => [1, 1, 2, 2]
  | 3 => [1, 1, 2, 3]
  | 4 => [1, 1, 3, 3]
  | 5 => [1, 2, 2, 3]
  | 6 => [1, 2, 3, 3]
  | 7 => [2, 2, 3, 3]
  | 8 => [1, 2, 2, 3]
  | 9 => [1, 2, 3, 3]
  | 10 => [2, 2, 3, 3]
  | 11 => [0, 1, 1, 2, 2]
  | 12 => [0, 1, 1, 2, 3]
  | 13 => [0, 1, 1, 3, 3]
  | 14 => [0, 1, 2, 2, 3]
  | 15 => [0, 1, 2, 3, 3]
  | 16 => [0, 2, 2, 3, 3]
  | 17 => [1, 1, 2, 2, 3]
  | 18 => [1, 1, 2, 3, 3]
  | 19 => [1, 2, 2, 3, 3]
  | 20 => [1, 2, 2, 3, 3]
  | 21 => [0, 1, 1, 2, 2, 3]
  | 22 => [0, 1, 1, 2, 3, 3]
  | 23 => [0, 1, 2, 2, 3, 3]
  | 24 => [1, 1, 2, 2, 3, 3]
  | _ => [0, 1, 1, 2, 2, 3, 3]

def representativeTail (state : Fin 90) :
    List (Fin 4) :=
  if state.val < 32 then representativeTailChunk0 state.val else
    if state.val < 64 then representativeTailChunk1 (state.val - 32) else
      representativeTailChunk2 (state.val - 64)

private def sourceLabelChunk0 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (5 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (3 : Fin 6)
  | 3 => (2 : Fin 6)
  | 4 => (5 : Fin 6)
  | 5 => (4 : Fin 6)
  | 6 => (0 : Fin 6)
  | 7 => (0 : Fin 6)
  | 8 => (0 : Fin 6)
  | 9 => (4 : Fin 6)
  | 10 => (4 : Fin 6)
  | 11 => (0 : Fin 6)
  | 12 => (1 : Fin 6)
  | 13 => (0 : Fin 6)
  | 14 => (5 : Fin 6)
  | 15 => (4 : Fin 6)
  | 16 => (0 : Fin 6)
  | 17 => (0 : Fin 6)
  | 18 => (0 : Fin 6)
  | 19 => (4 : Fin 6)
  | 20 => (4 : Fin 6)
  | 21 => (0 : Fin 6)
  | 22 => (0 : Fin 6)
  | 23 => (0 : Fin 6)
  | 24 => (4 : Fin 6)
  | 25 => (0 : Fin 6)
  | 26 => (0 : Fin 6)
  | 27 => (4 : Fin 6)
  | 28 => (4 : Fin 6)
  | 29 => (4 : Fin 6)
  | 30 => (0 : Fin 6)
  | _ => (0 : Fin 6)

private def sourceLabelChunk1 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (0 : Fin 6)
  | 1 => (0 : Fin 6)
  | 2 => (4 : Fin 6)
  | 3 => (0 : Fin 6)
  | 4 => (0 : Fin 6)
  | 5 => (0 : Fin 6)
  | 6 => (4 : Fin 6)
  | 7 => (4 : Fin 6)
  | 8 => (0 : Fin 6)
  | 9 => (0 : Fin 6)
  | 10 => (0 : Fin 6)
  | 11 => (0 : Fin 6)
  | 12 => (0 : Fin 6)
  | 13 => (4 : Fin 6)
  | 14 => (4 : Fin 6)
  | 15 => (4 : Fin 6)
  | 16 => (0 : Fin 6)
  | 17 => (0 : Fin 6)
  | 18 => (4 : Fin 6)
  | 19 => (4 : Fin 6)
  | 20 => (0 : Fin 6)
  | 21 => (0 : Fin 6)
  | 22 => (0 : Fin 6)
  | 23 => (4 : Fin 6)
  | 24 => (4 : Fin 6)
  | 25 => (0 : Fin 6)
  | 26 => (0 : Fin 6)
  | 27 => (0 : Fin 6)
  | 28 => (0 : Fin 6)
  | 29 => (4 : Fin 6)
  | 30 => (4 : Fin 6)
  | _ => (4 : Fin 6)

private def sourceLabelChunk2 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (0 : Fin 6)
  | 1 => (0 : Fin 6)
  | 2 => (0 : Fin 6)
  | 3 => (0 : Fin 6)
  | 4 => (0 : Fin 6)
  | 5 => (4 : Fin 6)
  | 6 => (4 : Fin 6)
  | 7 => (0 : Fin 6)
  | 8 => (0 : Fin 6)
  | 9 => (0 : Fin 6)
  | 10 => (4 : Fin 6)
  | 11 => (0 : Fin 6)
  | 12 => (0 : Fin 6)
  | 13 => (0 : Fin 6)
  | 14 => (4 : Fin 6)
  | 15 => (4 : Fin 6)
  | 16 => (0 : Fin 6)
  | 17 => (0 : Fin 6)
  | 18 => (0 : Fin 6)
  | 19 => (4 : Fin 6)
  | 20 => (0 : Fin 6)
  | 21 => (0 : Fin 6)
  | 22 => (0 : Fin 6)
  | 23 => (4 : Fin 6)
  | 24 => (0 : Fin 6)
  | _ => (0 : Fin 6)

def sourceLabel (state : Fin 90) : Fin 6 :=
  if state.val < 32 then sourceLabelChunk0 state.val else
    if state.val < 64 then sourceLabelChunk1 (state.val - 32) else
      sourceLabelChunk2 (state.val - 64)

def generatorSourceLabel (generator : Fin 4) : Fin 6 :=
  match generator.val with
  | 0 => (5 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (3 : Fin 6)
  | _ => (2 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 90 :=
  match value.val with
  | 0 => (6 : Fin 90)
  | 1 => (12 : Fin 90)
  | 2 => (3 : Fin 90)
  | 3 => (2 : Fin 90)
  | 4 => (1 : Fin 90)
  | _ => (0 : Fin 90)

private def stateVectorCode
    (vector : Fin 12 -> Fin 6) : Nat :=
  (vector (0 : Fin 12)).val + 6 * ((vector (1 : Fin 12)).val + 6 * ((vector (2 : Fin 12)).val + 6 * ((vector (3 : Fin 12)).val + 6 * ((vector (4 : Fin 12)).val + 6 * ((vector (5 : Fin 12)).val + 6 * ((vector (6 : Fin 12)).val + 6 * ((vector (7 : Fin 12)).val + 6 * ((vector (8 : Fin 12)).val + 6 * ((vector (9 : Fin 12)).val + 6 * ((vector (10 : Fin 12)).val + 6 * ((vector (11 : Fin 12)).val)))))))))))

private def decodeStateCode (code : Nat) : Fin 90 :=
  if code < 1370589984 then
    if code < 1305929430 then
      if code < 1300898592 then
        if code < 1300190619 then
          if code < 1300053888 then
            if code < 1300050648 then
              if code = 1300046112 then (89 : Fin 90) else (0 : Fin 90)
            else if code = 1300050648 then (75 : Fin 90) else
              (0 : Fin 90)
          else if code = 1300053888 then (88 : Fin 90) else
            if code < 1300186080 then
              if code = 1300058640 then (66 : Fin 90) else (0 : Fin 90)
            else if code = 1300186080 then (77 : Fin 90) else
              (0 : Fin 90)
        else if code = 1300190619 then (37 : Fin 90) else
          if code < 1300885920 then
            if code < 1300198611 then
              if code = 1300193856 then (68 : Fin 90) else (0 : Fin 90)
            else if code = 1300198611 then (18 : Fin 90) else
              (0 : Fin 90)
          else if code = 1300885920 then (80 : Fin 90) else
            if code < 1300893696 then
              if code = 1300890564 then (40 : Fin 90) else (0 : Fin 90)
            else if code = 1300893696 then (71 : Fin 90) else
              (0 : Fin 90)
      else if code = 1300898592 then (21 : Fin 90) else
        if code < 1305084960 then
          if code < 1301033664 then
            if code < 1301030535 then
              if code = 1301025888 then (42 : Fin 90) else (0 : Fin 90)
            else if code = 1301030535 then (4 : Fin 90) else
              (0 : Fin 90)
          else if code = 1301033664 then (23 : Fin 90) else
            if code < 1301041169 then
              if code = 1301038563 then (14 : Fin 90) else (0 : Fin 90)
            else if code = 1301041169 then (0 : Fin 90) else
              (0 : Fin 90)
        else if code = 1305084960 then (84 : Fin 90) else
          if code < 1305229485 then
            if code < 1305224928 then
              if code = 1305089514 then (52 : Fin 90) else (0 : Fin 90)
            else if code = 1305224928 then (54 : Fin 90) else
              (0 : Fin 90)
          else if code = 1305229485 then (8 : Fin 90) else
            if code = 1305924768 then (58 : Fin 90) else (0 : Fin 90)
    else if code = 1305929430 then (11 : Fin 90) else
      if code < 1316982240 then
        if code < 1311243552 then
          if code < 1310131584 then
            if code < 1310123808 then
              if code = 1306064736 then (13 : Fin 90) else (0 : Fin 90)
            else if code = 1310123808 then (85 : Fin 90) else
              (0 : Fin 90)
          else if code = 1310131584 then (81 : Fin 90) else
            if code < 1310271552 then
              if code = 1310263776 then (60 : Fin 90) else (0 : Fin 90)
            else if code = 1310271552 then (44 : Fin 90) else
              (0 : Fin 90)
        else if code = 1311243552 then (64 : Fin 90) else
          if code < 1311391296 then
            if code < 1311383520 then
              if code = 1311251328 then (48 : Fin 90) else (0 : Fin 90)
            else if code = 1311383520 then (17 : Fin 90) else
              (0 : Fin 90)
          else if code = 1311391296 then (36 : Fin 90) else
            if code < 1316842272 then
              if code = 1311392592 then (7 : Fin 90) else (0 : Fin 90)
            else if code = 1316842272 then (72 : Fin 90) else
              (0 : Fin 90)
      else if code = 1316982240 then (26 : Fin 90) else
        if code < 1361632032 then
          if code < 1318104660 then
            if code < 1318101984 then
              if code = 1317962016 then (31 : Fin 90) else (0 : Fin 90)
            else if code = 1318101984 then (33 : Fin 90) else
              (0 : Fin 90)
          else if code = 1318104660 then (3 : Fin 90) else
            if code < 1360520064 then
              if code = 1360512288 then (76 : Fin 90) else (0 : Fin 90)
            else if code = 1360520064 then (67 : Fin 90) else
              (0 : Fin 90)
        else if code = 1361632032 then (41 : Fin 90) else
          if code < 1366670880 then
            if code < 1365551136 then
              if code = 1361639808 then (22 : Fin 90) else (0 : Fin 90)
            else if code = 1365551136 then (53 : Fin 90) else
              (0 : Fin 90)
          else if code = 1366670880 then (57 : Fin 90) else
            if code = 1366670916 then (12 : Fin 90) else (0 : Fin 90)
  else if code = 1370589984 then (86 : Fin 90) else
    if code < 1672928640 then
      if code < 1378153140 then
        if code < 1371437568 then
          if code < 1370602296 then
            if code < 1370597760 then
              if code = 1370594736 then (59 : Fin 90) else (0 : Fin 90)
            else if code = 1370597760 then (82 : Fin 90) else
              (0 : Fin 90)
          else if code = 1370602296 then (43 : Fin 90) else
            if code < 1371434652 then
              if code = 1371429792 then (65 : Fin 90) else (0 : Fin 90)
            else if code = 1371434652 then (16 : Fin 90) else
              (0 : Fin 90)
        else if code = 1371437568 then (49 : Fin 90) else
          if code < 1377308448 then
            if code < 1371442249 then
              if code = 1371442248 then (35 : Fin 90) else (0 : Fin 90)
            else if code = 1371442249 then (6 : Fin 90) else
              (0 : Fin 90)
          else if code = 1377308448 then (73 : Fin 90) else
            if code < 1378148256 then
              if code = 1377313224 then (25 : Fin 90) else (0 : Fin 90)
            else if code = 1378148256 then (32 : Fin 90) else
              (0 : Fin 90)
      else if code = 1378153140 then (30 : Fin 90) else
        if code < 1669561632 then
          if code < 1662850944 then
            if code < 1662843168 then
              if code = 1378153214 then (2 : Fin 90) else (0 : Fin 90)
            else if code = 1662843168 then (78 : Fin 90) else
              (0 : Fin 90)
          else if code = 1662850944 then (69 : Fin 90) else
            if code < 1663037568 then
              if code = 1663029792 then (39 : Fin 90) else (0 : Fin 90)
            else if code = 1663037568 then (20 : Fin 90) else
              (0 : Fin 90)
        else if code = 1669561632 then (55 : Fin 90) else
          if code < 1672920864 then
            if code < 1669748262 then
              if code = 1669748256 then (51 : Fin 90) else (0 : Fin 90)
            else if code = 1669748262 then (10 : Fin 90) else
              (0 : Fin 90)
          else if code = 1672920864 then (87 : Fin 90) else
            if code = 1672926912 then (61 : Fin 90) else (0 : Fin 90)
    else if code = 1672928640 then (83 : Fin 90) else
      if code < 1678152490 then
        if code < 1673121106 then
          if code < 1673113540 then
            if code < 1673107488 then
              if code = 1672934472 then (45 : Fin 90) else (0 : Fin 90)
            else if code = 1673107488 then (63 : Fin 90) else
              (0 : Fin 90)
          else if code = 1673113540 then (15 : Fin 90) else
            if code < 1673121100 then
              if code = 1673115264 then (47 : Fin 90) else (0 : Fin 90)
            else if code = 1673121100 then (34 : Fin 90) else
              (0 : Fin 90)
        else if code = 1673121106 then (5 : Fin 90) else
          if code < 1678146336 then
            if code < 1677965778 then
              if code = 1677959712 then (74 : Fin 90) else (0 : Fin 90)
            else if code = 1677965778 then (27 : Fin 90) else
              (0 : Fin 90)
          else if code = 1678146336 then (29 : Fin 90) else
            if code = 1678152406 then (24 : Fin 90) else (0 : Fin 90)
      else if code = 1678152490 then (1 : Fin 90) else
        if code < 1730033664 then
          if code < 1723317120 then
            if code < 1723315176 then
              if code = 1723309344 then (79 : Fin 90) else (0 : Fin 90)
            else if code = 1723315176 then (38 : Fin 90) else
              (0 : Fin 90)
          else if code = 1723317120 then (70 : Fin 90) else
            if code < 1730027808 then
              if code = 1723323168 then (19 : Fin 90) else (0 : Fin 90)
            else if code = 1730027808 then (56 : Fin 90) else
              (0 : Fin 90)
        else if code = 1730033664 then (50 : Fin 90) else
          if code < 1733394816 then
            if code < 1733387040 then
              if code = 1730033700 then (9 : Fin 90) else (0 : Fin 90)
            else if code = 1733387040 then (62 : Fin 90) else
              (0 : Fin 90)
          else if code = 1733394816 then (46 : Fin 90) else
            if code = 1738425888 then (28 : Fin 90) else (0 : Fin 90)

private def decodeState
    (vector : Fin 12 -> Fin 6) : Fin 90 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 90) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 90)
      (generator : Fin 4)
      (coordinate : Fin 12),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem representativeMap :
    forall (state : Fin 90)
      (coordinate : Fin 12),
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
    (U := Fin 90)
    (G := Fin 4)
    (I := Fin 12) oppositeTable.semigroup where
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
    forall (state : Fin 90)
      (generator : Fin 4),
      sourceLabel (transition state generator) =
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul (sourceLabel state)
          (generatorSourceLabel generator) := by
  intro state generator
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem sourceLabelRepresentative :
    forall state : Fin 90,
      sourceLabel state =
        (representativeTail state).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (generatorSourceLabel (representativeHead state)) := by
  intro state
  apply Fin.ext
  exact by decide +revert

private theorem sourceLabelRightMultiplyWord
    (state : Fin 90)
    (word : List (Fin 4)) :
    sourceLabel (powerCertificate.rightMultiplyWord state word) =
      word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul value
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
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul value
                (generatorSourceLabel nextGenerator))
            (SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul (sourceLabel state)
              (generatorSourceLabel generator))
      rw [inductionHypothesis]
      rw [sourceLabelTransition]

private theorem sourceFoldlGeneratorAssoc
    (left right : Fin 6)
    (word : List (Fin 4)) :
    word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul value
            (generatorSourceLabel generator))
        (SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul left right) =
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul left
        (word.foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          right) := by
  induction word generalizing right with
  | nil => rfl
  | cons generator word inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.assoc]
      exact inductionHypothesis
        (SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul right (generatorSourceLabel generator))

private theorem sourceLabelMapMul :
    forall (left right : Fin 90),
      sourceLabel (powerCertificate.semigroup.mul left right) =
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul (sourceLabel left) (sourceLabel right) := by
  intro left right
  calc
    sourceLabel (powerCertificate.semigroup.mul left right) =
        sourceLabel
          (powerCertificate.rightMultiplyWord
            (transition left (representativeHead right))
            (representativeTail right)) := rfl
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (sourceLabel (transition left (representativeHead right))) :=
      sourceLabelRightMultiplyWord _ _
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul (sourceLabel left)
            (generatorSourceLabel (representativeHead right))) :=
      congrArg
        (fun initial =>
          (representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul value
                (generatorSourceLabel generator))
            initial)
        (sourceLabelTransition left (representativeHead right))
    _ = SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul (sourceLabel left)
          ((representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul value
                (generatorSourceLabel generator))
            (generatorSourceLabel (representativeHead right))) :=
      sourceFoldlGeneratorAssoc _ _ _
    _ = SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul (sourceLabel left) (sourceLabel right) :=
      congrArg (SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup.mul (sourceLabel left))
        (sourceLabelRepresentative right).symm

set_option maxHeartbeats 1000000 in
private theorem sourceLabelRightInverse :
    forall value : Fin 6, sourceLabel (sourcePreimage value) = value := by
  intro value
  apply Fin.ext
  exact by decide +revert

/-- The generated term-function semigroup maps onto the selected root. -/
def quotient : SplitSurjection powerCertificate.semigroup
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup where
  toFun := sourceLabel
  map_mul := sourceLabelMapMul
  preimage := sourcePreimage
  right_inverse := sourceLabelRightInverse

private def targetLaw0ToFinite : Nat -> Fin 1
  | 0 => (0 : Fin 1)
  | _ => (0 : Fin 1)

private def targetLaw0FromFinite (index : Fin 1) : Nat :=
  match index.val with
  | 0 => 0
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw0Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law0.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law0
    targetLaw0ToFinite targetLaw0FromFinite (by decide) (by decide)

private def targetLaw1ToFinite : Nat -> Fin 2
  | 0 => (0 : Fin 2)
  | 1 => (1 : Fin 2)
  | _ => (0 : Fin 2)

private def targetLaw1FromFinite (index : Fin 2) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw1Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law1.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law1
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law2.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law2
    targetLaw2ToFinite targetLaw2FromFinite (by decide) (by decide)

private def targetLaw3ToFinite : Nat -> Fin 3
  | 0 => (0 : Fin 3)
  | 1 => (1 : Fin 3)
  | 2 => (2 : Fin 3)
  | _ => (0 : Fin 3)

private def targetLaw3FromFinite (index : Fin 3) : Nat :=
  match index.val with
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | _ => 0

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 8192 in
private theorem targetLaw3Valid :
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law3.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.law3
    targetLaw3ToFinite targetLaw3FromFinite (by decide) (by decide)

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.basis := by
  unfold SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_cons targetLaw2Valid <|
          FiniteNilpotentCounterexample.models_cons targetLaw3Valid <|
            FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

/-- Exact identity-theory transfer authenticated by the finite certificate. -/
theorem sameIdentityTheory :
    SameIdentityTheoryOver SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.oppositeTable.semigroup
      oppositeTable.semigroup Nat := by
  intro identity
  constructor
  · intro sourceValid valuation
    exact Derives.sound targetModels
      (SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_1250.basisFor.2 identity sourceValid) valuation
  · intro targetValid
    have powerValid :=
      identity.satisfiedByPi oppositeTable.semigroup
        (Fin 12) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_5790`. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.basis := by
  have transferred :
      BasisFor oppositeTable.semigroup SemigroupBasis.Generated.Order6GenericCASRootData.S6_1250.basis :=
    (basisFor_iff_of_sameIdentityTheoryOver sameIdentityTheory).mp
      SemigroupBasis.CoRoots.Order6GenericCASSubdirectS6_1250.basisFor
  simpa only [oppositeTable_semigroup] using transferred

end SemigroupBasis.Generated.Order6GenericCASRootWrappers.S6_5790
