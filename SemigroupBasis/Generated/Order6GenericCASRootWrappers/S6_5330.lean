import SemigroupBasis.CoRoots.Order6GenericCASMonoidPower
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate

set_option maxRecDepth 2048

namespace SemigroupBasis.Generated.Order6GenericCASRootWrappers.S6_5330

open SemigroupBasis

def routeManifestRowSHA256 : String := "cdf7c7a88b7919a097b84a8e9e5afa5ec915f9efe6f0f9c36f8adb3d899bc972"
def witnessRecordSHA256 : String := "7cf05c22973993a9f7279c87b200f658676e3f0fdd88b4e10f044eff38b5541f"
def transferComponentSHA256 : String := "dfc3a83681c0846546288bf0c99805d4b138d258754f51638d65ccb76e7bbf21"
def powerCertificateSHA256 : String := "2c1e694e81b28a43a6abf6559fce85c3b28c53eaaea5180ec2209cbf460c0762"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 1 3 4 0 right else
    if left = 1 then row6 1 0 0 4 3 1 right else
      if left = 2 then row6 1 0 0 4 3 2 right else
        if left = 3 then row6 3 4 4 1 0 3 right else
          if left = 4 then row6 4 3 3 0 1 4 right else
            row6 0 1 2 3 4 5 right

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
  "e2ff6c4e8aabdb77f44970c6f6034e35cee3a5fe31b70c2e0718146587b54205"

private def stateVectorChunk0 (index : Nat)
    (coordinate : Fin 6) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (2 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (5 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (2 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (2 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (5 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (2 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (5 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (2 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (2 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (1 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (5 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (2 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (2 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (5 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (2 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (1 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (2 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (0 : Fin 6)

private def stateVectorChunk1 (index : Nat)
    (coordinate : Fin 6) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (1 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (5 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (2 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (5 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (2 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (2 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (5 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (2 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (1 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (2 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (1 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (1 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (5 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (2 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (2 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (5 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (2 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)

private def stateVectorChunk2 (index : Nat)
    (coordinate : Fin 6) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (2 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (5 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (2 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (1 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (1 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (2 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (1 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (1 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (5 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (2 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (2 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (5 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (2 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (2 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)

private def stateVectorChunk3 (index : Nat)
    (coordinate : Fin 6) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (2 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (1 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (1 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (1 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (1 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (5 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (2 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (2 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (5 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (2 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (2 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (0 : Fin 6)

private def stateVectorChunk4 (index : Nat)
    (coordinate : Fin 6) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (1 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (1 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (1 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (1 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (5 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (2 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (5 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (2 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (2 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (1 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (1 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (0 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (1 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (5 : Fin 6)

private def stateVectorChunk5 (index : Nat)
    (coordinate : Fin 6) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (2 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (2 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (0 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (1 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (1 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (2 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 22 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 23 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 24 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 25 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 26 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 27 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 28 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 29 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 30 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)

private def stateVectorChunk6 (index : Nat)
    (coordinate : Fin 6) : Fin 6 :=
  match index with
  | 0 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (1 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 5 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 6 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 7 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 8 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 9 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 10 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 11 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 12 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 13 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (4 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 14 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 15 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 16 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 17 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | 18 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 19 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (0 : Fin 6)
  | 20 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)
  | 21 =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | _ => (1 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (4 : Fin 6)
      | 1 => (4 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (1 : Fin 6)
      | _ => (1 : Fin 6)

def stateVector (state : Fin 215)
    (coordinate : Fin 6) : Fin 6 :=
  if state.val < 32 then stateVectorChunk0 state.val coordinate else
    if state.val < 64 then stateVectorChunk1 (state.val - 32) coordinate else
      if state.val < 96 then stateVectorChunk2 (state.val - 64) coordinate else
        if state.val < 128 then stateVectorChunk3 (state.val - 96) coordinate else
          if state.val < 160 then stateVectorChunk4 (state.val - 128) coordinate else
            if state.val < 192 then stateVectorChunk5 (state.val - 160) coordinate else
              stateVectorChunk6 (state.val - 192) coordinate

def generatorVector (generator : Fin 3)
    (coordinate : Fin 6) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (2 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (2 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (2 : Fin 6)
      | 1 => (2 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (5 : Fin 6)
      | _ => (2 : Fin 6)

private def transitionChunk0 (index : Nat)
    (generator : Fin 3) : Fin 215 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (3 : Fin 215)
      | 1 => (4 : Fin 215)
      | _ => (5 : Fin 215)
  | 1 =>
      match generator.val with
      | 0 => (4 : Fin 215)
      | 1 => (6 : Fin 215)
      | _ => (7 : Fin 215)
  | 2 =>
      match generator.val with
      | 0 => (5 : Fin 215)
      | 1 => (7 : Fin 215)
      | _ => (8 : Fin 215)
  | 3 =>
      match generator.val with
      | 0 => (9 : Fin 215)
      | 1 => (10 : Fin 215)
      | _ => (11 : Fin 215)
  | 4 =>
      match generator.val with
      | 0 => (10 : Fin 215)
      | 1 => (12 : Fin 215)
      | _ => (13 : Fin 215)
  | 5 =>
      match generator.val with
      | 0 => (11 : Fin 215)
      | 1 => (13 : Fin 215)
      | _ => (14 : Fin 215)
  | 6 =>
      match generator.val with
      | 0 => (12 : Fin 215)
      | 1 => (15 : Fin 215)
      | _ => (16 : Fin 215)
  | 7 =>
      match generator.val with
      | 0 => (13 : Fin 215)
      | 1 => (16 : Fin 215)
      | _ => (17 : Fin 215)
  | 8 =>
      match generator.val with
      | 0 => (14 : Fin 215)
      | 1 => (17 : Fin 215)
      | _ => (18 : Fin 215)
  | 9 =>
      match generator.val with
      | 0 => (19 : Fin 215)
      | 1 => (20 : Fin 215)
      | _ => (21 : Fin 215)
  | 10 =>
      match generator.val with
      | 0 => (20 : Fin 215)
      | 1 => (22 : Fin 215)
      | _ => (23 : Fin 215)
  | 11 =>
      match generator.val with
      | 0 => (21 : Fin 215)
      | 1 => (23 : Fin 215)
      | _ => (24 : Fin 215)
  | 12 =>
      match generator.val with
      | 0 => (22 : Fin 215)
      | 1 => (25 : Fin 215)
      | _ => (26 : Fin 215)
  | 13 =>
      match generator.val with
      | 0 => (23 : Fin 215)
      | 1 => (26 : Fin 215)
      | _ => (27 : Fin 215)
  | 14 =>
      match generator.val with
      | 0 => (24 : Fin 215)
      | 1 => (27 : Fin 215)
      | _ => (28 : Fin 215)
  | 15 =>
      match generator.val with
      | 0 => (25 : Fin 215)
      | 1 => (29 : Fin 215)
      | _ => (30 : Fin 215)
  | 16 =>
      match generator.val with
      | 0 => (26 : Fin 215)
      | 1 => (30 : Fin 215)
      | _ => (31 : Fin 215)
  | 17 =>
      match generator.val with
      | 0 => (27 : Fin 215)
      | 1 => (31 : Fin 215)
      | _ => (32 : Fin 215)
  | 18 =>
      match generator.val with
      | 0 => (28 : Fin 215)
      | 1 => (32 : Fin 215)
      | _ => (33 : Fin 215)
  | 19 =>
      match generator.val with
      | 0 => (34 : Fin 215)
      | 1 => (35 : Fin 215)
      | _ => (36 : Fin 215)
  | 20 =>
      match generator.val with
      | 0 => (35 : Fin 215)
      | 1 => (37 : Fin 215)
      | _ => (38 : Fin 215)
  | 21 =>
      match generator.val with
      | 0 => (36 : Fin 215)
      | 1 => (38 : Fin 215)
      | _ => (39 : Fin 215)
  | 22 =>
      match generator.val with
      | 0 => (37 : Fin 215)
      | 1 => (40 : Fin 215)
      | _ => (41 : Fin 215)
  | 23 =>
      match generator.val with
      | 0 => (38 : Fin 215)
      | 1 => (41 : Fin 215)
      | _ => (42 : Fin 215)
  | 24 =>
      match generator.val with
      | 0 => (39 : Fin 215)
      | 1 => (42 : Fin 215)
      | _ => (43 : Fin 215)
  | 25 =>
      match generator.val with
      | 0 => (40 : Fin 215)
      | 1 => (44 : Fin 215)
      | _ => (45 : Fin 215)
  | 26 =>
      match generator.val with
      | 0 => (41 : Fin 215)
      | 1 => (45 : Fin 215)
      | _ => (46 : Fin 215)
  | 27 =>
      match generator.val with
      | 0 => (42 : Fin 215)
      | 1 => (46 : Fin 215)
      | _ => (47 : Fin 215)
  | 28 =>
      match generator.val with
      | 0 => (43 : Fin 215)
      | 1 => (47 : Fin 215)
      | _ => (48 : Fin 215)
  | 29 =>
      match generator.val with
      | 0 => (44 : Fin 215)
      | 1 => (49 : Fin 215)
      | _ => (50 : Fin 215)
  | 30 =>
      match generator.val with
      | 0 => (45 : Fin 215)
      | 1 => (50 : Fin 215)
      | _ => (51 : Fin 215)
  | _ =>
      match generator.val with
      | 0 => (46 : Fin 215)
      | 1 => (51 : Fin 215)
      | _ => (52 : Fin 215)

private def transitionChunk1 (index : Nat)
    (generator : Fin 3) : Fin 215 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (47 : Fin 215)
      | 1 => (52 : Fin 215)
      | _ => (53 : Fin 215)
  | 1 =>
      match generator.val with
      | 0 => (48 : Fin 215)
      | 1 => (53 : Fin 215)
      | _ => (54 : Fin 215)
  | 2 =>
      match generator.val with
      | 0 => (3 : Fin 215)
      | 1 => (55 : Fin 215)
      | _ => (56 : Fin 215)
  | 3 =>
      match generator.val with
      | 0 => (55 : Fin 215)
      | 1 => (57 : Fin 215)
      | _ => (58 : Fin 215)
  | 4 =>
      match generator.val with
      | 0 => (56 : Fin 215)
      | 1 => (58 : Fin 215)
      | _ => (59 : Fin 215)
  | 5 =>
      match generator.val with
      | 0 => (57 : Fin 215)
      | 1 => (60 : Fin 215)
      | _ => (61 : Fin 215)
  | 6 =>
      match generator.val with
      | 0 => (58 : Fin 215)
      | 1 => (61 : Fin 215)
      | _ => (62 : Fin 215)
  | 7 =>
      match generator.val with
      | 0 => (59 : Fin 215)
      | 1 => (62 : Fin 215)
      | _ => (63 : Fin 215)
  | 8 =>
      match generator.val with
      | 0 => (60 : Fin 215)
      | 1 => (64 : Fin 215)
      | _ => (65 : Fin 215)
  | 9 =>
      match generator.val with
      | 0 => (61 : Fin 215)
      | 1 => (65 : Fin 215)
      | _ => (66 : Fin 215)
  | 10 =>
      match generator.val with
      | 0 => (62 : Fin 215)
      | 1 => (66 : Fin 215)
      | _ => (67 : Fin 215)
  | 11 =>
      match generator.val with
      | 0 => (63 : Fin 215)
      | 1 => (67 : Fin 215)
      | _ => (68 : Fin 215)
  | 12 =>
      match generator.val with
      | 0 => (64 : Fin 215)
      | 1 => (69 : Fin 215)
      | _ => (70 : Fin 215)
  | 13 =>
      match generator.val with
      | 0 => (65 : Fin 215)
      | 1 => (70 : Fin 215)
      | _ => (71 : Fin 215)
  | 14 =>
      match generator.val with
      | 0 => (66 : Fin 215)
      | 1 => (71 : Fin 215)
      | _ => (72 : Fin 215)
  | 15 =>
      match generator.val with
      | 0 => (67 : Fin 215)
      | 1 => (72 : Fin 215)
      | _ => (73 : Fin 215)
  | 16 =>
      match generator.val with
      | 0 => (68 : Fin 215)
      | 1 => (73 : Fin 215)
      | _ => (74 : Fin 215)
  | 17 =>
      match generator.val with
      | 0 => (69 : Fin 215)
      | 1 => (6 : Fin 215)
      | _ => (75 : Fin 215)
  | 18 =>
      match generator.val with
      | 0 => (70 : Fin 215)
      | 1 => (75 : Fin 215)
      | _ => (76 : Fin 215)
  | 19 =>
      match generator.val with
      | 0 => (71 : Fin 215)
      | 1 => (76 : Fin 215)
      | _ => (77 : Fin 215)
  | 20 =>
      match generator.val with
      | 0 => (72 : Fin 215)
      | 1 => (77 : Fin 215)
      | _ => (78 : Fin 215)
  | 21 =>
      match generator.val with
      | 0 => (73 : Fin 215)
      | 1 => (78 : Fin 215)
      | _ => (79 : Fin 215)
  | 22 =>
      match generator.val with
      | 0 => (74 : Fin 215)
      | 1 => (79 : Fin 215)
      | _ => (8 : Fin 215)
  | 23 =>
      match generator.val with
      | 0 => (10 : Fin 215)
      | 1 => (80 : Fin 215)
      | _ => (81 : Fin 215)
  | 24 =>
      match generator.val with
      | 0 => (11 : Fin 215)
      | 1 => (81 : Fin 215)
      | _ => (82 : Fin 215)
  | 25 =>
      match generator.val with
      | 0 => (80 : Fin 215)
      | 1 => (83 : Fin 215)
      | _ => (84 : Fin 215)
  | 26 =>
      match generator.val with
      | 0 => (81 : Fin 215)
      | 1 => (84 : Fin 215)
      | _ => (85 : Fin 215)
  | 27 =>
      match generator.val with
      | 0 => (82 : Fin 215)
      | 1 => (85 : Fin 215)
      | _ => (86 : Fin 215)
  | 28 =>
      match generator.val with
      | 0 => (83 : Fin 215)
      | 1 => (87 : Fin 215)
      | _ => (88 : Fin 215)
  | 29 =>
      match generator.val with
      | 0 => (84 : Fin 215)
      | 1 => (88 : Fin 215)
      | _ => (89 : Fin 215)
  | 30 =>
      match generator.val with
      | 0 => (85 : Fin 215)
      | 1 => (89 : Fin 215)
      | _ => (90 : Fin 215)
  | _ =>
      match generator.val with
      | 0 => (86 : Fin 215)
      | 1 => (90 : Fin 215)
      | _ => (91 : Fin 215)

private def transitionChunk2 (index : Nat)
    (generator : Fin 3) : Fin 215 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (87 : Fin 215)
      | 1 => (92 : Fin 215)
      | _ => (93 : Fin 215)
  | 1 =>
      match generator.val with
      | 0 => (88 : Fin 215)
      | 1 => (93 : Fin 215)
      | _ => (94 : Fin 215)
  | 2 =>
      match generator.val with
      | 0 => (89 : Fin 215)
      | 1 => (94 : Fin 215)
      | _ => (95 : Fin 215)
  | 3 =>
      match generator.val with
      | 0 => (90 : Fin 215)
      | 1 => (95 : Fin 215)
      | _ => (96 : Fin 215)
  | 4 =>
      match generator.val with
      | 0 => (91 : Fin 215)
      | 1 => (96 : Fin 215)
      | _ => (97 : Fin 215)
  | 5 =>
      match generator.val with
      | 0 => (92 : Fin 215)
      | 1 => (12 : Fin 215)
      | _ => (98 : Fin 215)
  | 6 =>
      match generator.val with
      | 0 => (93 : Fin 215)
      | 1 => (98 : Fin 215)
      | _ => (99 : Fin 215)
  | 7 =>
      match generator.val with
      | 0 => (94 : Fin 215)
      | 1 => (99 : Fin 215)
      | _ => (100 : Fin 215)
  | 8 =>
      match generator.val with
      | 0 => (95 : Fin 215)
      | 1 => (100 : Fin 215)
      | _ => (101 : Fin 215)
  | 9 =>
      match generator.val with
      | 0 => (96 : Fin 215)
      | 1 => (101 : Fin 215)
      | _ => (102 : Fin 215)
  | 10 =>
      match generator.val with
      | 0 => (97 : Fin 215)
      | 1 => (102 : Fin 215)
      | _ => (14 : Fin 215)
  | 11 =>
      match generator.val with
      | 0 => (98 : Fin 215)
      | 1 => (16 : Fin 215)
      | _ => (103 : Fin 215)
  | 12 =>
      match generator.val with
      | 0 => (99 : Fin 215)
      | 1 => (103 : Fin 215)
      | _ => (104 : Fin 215)
  | 13 =>
      match generator.val with
      | 0 => (100 : Fin 215)
      | 1 => (104 : Fin 215)
      | _ => (105 : Fin 215)
  | 14 =>
      match generator.val with
      | 0 => (101 : Fin 215)
      | 1 => (105 : Fin 215)
      | _ => (106 : Fin 215)
  | 15 =>
      match generator.val with
      | 0 => (102 : Fin 215)
      | 1 => (106 : Fin 215)
      | _ => (17 : Fin 215)
  | 16 =>
      match generator.val with
      | 0 => (22 : Fin 215)
      | 1 => (107 : Fin 215)
      | _ => (108 : Fin 215)
  | 17 =>
      match generator.val with
      | 0 => (23 : Fin 215)
      | 1 => (108 : Fin 215)
      | _ => (109 : Fin 215)
  | 18 =>
      match generator.val with
      | 0 => (24 : Fin 215)
      | 1 => (109 : Fin 215)
      | _ => (110 : Fin 215)
  | 19 =>
      match generator.val with
      | 0 => (107 : Fin 215)
      | 1 => (111 : Fin 215)
      | _ => (112 : Fin 215)
  | 20 =>
      match generator.val with
      | 0 => (108 : Fin 215)
      | 1 => (112 : Fin 215)
      | _ => (113 : Fin 215)
  | 21 =>
      match generator.val with
      | 0 => (109 : Fin 215)
      | 1 => (113 : Fin 215)
      | _ => (114 : Fin 215)
  | 22 =>
      match generator.val with
      | 0 => (110 : Fin 215)
      | 1 => (114 : Fin 215)
      | _ => (115 : Fin 215)
  | 23 =>
      match generator.val with
      | 0 => (111 : Fin 215)
      | 1 => (116 : Fin 215)
      | _ => (117 : Fin 215)
  | 24 =>
      match generator.val with
      | 0 => (112 : Fin 215)
      | 1 => (117 : Fin 215)
      | _ => (118 : Fin 215)
  | 25 =>
      match generator.val with
      | 0 => (113 : Fin 215)
      | 1 => (118 : Fin 215)
      | _ => (119 : Fin 215)
  | 26 =>
      match generator.val with
      | 0 => (114 : Fin 215)
      | 1 => (119 : Fin 215)
      | _ => (120 : Fin 215)
  | 27 =>
      match generator.val with
      | 0 => (115 : Fin 215)
      | 1 => (120 : Fin 215)
      | _ => (121 : Fin 215)
  | 28 =>
      match generator.val with
      | 0 => (116 : Fin 215)
      | 1 => (22 : Fin 215)
      | _ => (122 : Fin 215)
  | 29 =>
      match generator.val with
      | 0 => (117 : Fin 215)
      | 1 => (122 : Fin 215)
      | _ => (123 : Fin 215)
  | 30 =>
      match generator.val with
      | 0 => (118 : Fin 215)
      | 1 => (123 : Fin 215)
      | _ => (124 : Fin 215)
  | _ =>
      match generator.val with
      | 0 => (119 : Fin 215)
      | 1 => (124 : Fin 215)
      | _ => (125 : Fin 215)

private def transitionChunk3 (index : Nat)
    (generator : Fin 3) : Fin 215 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (120 : Fin 215)
      | 1 => (125 : Fin 215)
      | _ => (126 : Fin 215)
  | 1 =>
      match generator.val with
      | 0 => (121 : Fin 215)
      | 1 => (126 : Fin 215)
      | _ => (24 : Fin 215)
  | 2 =>
      match generator.val with
      | 0 => (122 : Fin 215)
      | 1 => (26 : Fin 215)
      | _ => (127 : Fin 215)
  | 3 =>
      match generator.val with
      | 0 => (123 : Fin 215)
      | 1 => (127 : Fin 215)
      | _ => (128 : Fin 215)
  | 4 =>
      match generator.val with
      | 0 => (124 : Fin 215)
      | 1 => (128 : Fin 215)
      | _ => (129 : Fin 215)
  | 5 =>
      match generator.val with
      | 0 => (125 : Fin 215)
      | 1 => (129 : Fin 215)
      | _ => (130 : Fin 215)
  | 6 =>
      match generator.val with
      | 0 => (126 : Fin 215)
      | 1 => (130 : Fin 215)
      | _ => (27 : Fin 215)
  | 7 =>
      match generator.val with
      | 0 => (127 : Fin 215)
      | 1 => (31 : Fin 215)
      | _ => (131 : Fin 215)
  | 8 =>
      match generator.val with
      | 0 => (128 : Fin 215)
      | 1 => (131 : Fin 215)
      | _ => (132 : Fin 215)
  | 9 =>
      match generator.val with
      | 0 => (129 : Fin 215)
      | 1 => (132 : Fin 215)
      | _ => (133 : Fin 215)
  | 10 =>
      match generator.val with
      | 0 => (130 : Fin 215)
      | 1 => (133 : Fin 215)
      | _ => (31 : Fin 215)
  | 11 =>
      match generator.val with
      | 0 => (40 : Fin 215)
      | 1 => (134 : Fin 215)
      | _ => (135 : Fin 215)
  | 12 =>
      match generator.val with
      | 0 => (41 : Fin 215)
      | 1 => (135 : Fin 215)
      | _ => (136 : Fin 215)
  | 13 =>
      match generator.val with
      | 0 => (42 : Fin 215)
      | 1 => (136 : Fin 215)
      | _ => (137 : Fin 215)
  | 14 =>
      match generator.val with
      | 0 => (43 : Fin 215)
      | 1 => (137 : Fin 215)
      | _ => (138 : Fin 215)
  | 15 =>
      match generator.val with
      | 0 => (134 : Fin 215)
      | 1 => (139 : Fin 215)
      | _ => (140 : Fin 215)
  | 16 =>
      match generator.val with
      | 0 => (135 : Fin 215)
      | 1 => (140 : Fin 215)
      | _ => (141 : Fin 215)
  | 17 =>
      match generator.val with
      | 0 => (136 : Fin 215)
      | 1 => (141 : Fin 215)
      | _ => (142 : Fin 215)
  | 18 =>
      match generator.val with
      | 0 => (137 : Fin 215)
      | 1 => (142 : Fin 215)
      | _ => (143 : Fin 215)
  | 19 =>
      match generator.val with
      | 0 => (138 : Fin 215)
      | 1 => (143 : Fin 215)
      | _ => (144 : Fin 215)
  | 20 =>
      match generator.val with
      | 0 => (139 : Fin 215)
      | 1 => (37 : Fin 215)
      | _ => (145 : Fin 215)
  | 21 =>
      match generator.val with
      | 0 => (140 : Fin 215)
      | 1 => (145 : Fin 215)
      | _ => (146 : Fin 215)
  | 22 =>
      match generator.val with
      | 0 => (141 : Fin 215)
      | 1 => (146 : Fin 215)
      | _ => (147 : Fin 215)
  | 23 =>
      match generator.val with
      | 0 => (142 : Fin 215)
      | 1 => (147 : Fin 215)
      | _ => (148 : Fin 215)
  | 24 =>
      match generator.val with
      | 0 => (143 : Fin 215)
      | 1 => (148 : Fin 215)
      | _ => (149 : Fin 215)
  | 25 =>
      match generator.val with
      | 0 => (144 : Fin 215)
      | 1 => (149 : Fin 215)
      | _ => (39 : Fin 215)
  | 26 =>
      match generator.val with
      | 0 => (145 : Fin 215)
      | 1 => (41 : Fin 215)
      | _ => (150 : Fin 215)
  | 27 =>
      match generator.val with
      | 0 => (146 : Fin 215)
      | 1 => (150 : Fin 215)
      | _ => (151 : Fin 215)
  | 28 =>
      match generator.val with
      | 0 => (147 : Fin 215)
      | 1 => (151 : Fin 215)
      | _ => (152 : Fin 215)
  | 29 =>
      match generator.val with
      | 0 => (148 : Fin 215)
      | 1 => (152 : Fin 215)
      | _ => (153 : Fin 215)
  | 30 =>
      match generator.val with
      | 0 => (149 : Fin 215)
      | 1 => (153 : Fin 215)
      | _ => (42 : Fin 215)
  | _ =>
      match generator.val with
      | 0 => (150 : Fin 215)
      | 1 => (46 : Fin 215)
      | _ => (154 : Fin 215)

private def transitionChunk4 (index : Nat)
    (generator : Fin 3) : Fin 215 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (151 : Fin 215)
      | 1 => (154 : Fin 215)
      | _ => (155 : Fin 215)
  | 1 =>
      match generator.val with
      | 0 => (152 : Fin 215)
      | 1 => (155 : Fin 215)
      | _ => (156 : Fin 215)
  | 2 =>
      match generator.val with
      | 0 => (153 : Fin 215)
      | 1 => (156 : Fin 215)
      | _ => (46 : Fin 215)
  | 3 =>
      match generator.val with
      | 0 => (154 : Fin 215)
      | 1 => (52 : Fin 215)
      | _ => (157 : Fin 215)
  | 4 =>
      match generator.val with
      | 0 => (155 : Fin 215)
      | 1 => (157 : Fin 215)
      | _ => (158 : Fin 215)
  | 5 =>
      match generator.val with
      | 0 => (156 : Fin 215)
      | 1 => (158 : Fin 215)
      | _ => (51 : Fin 215)
  | 6 =>
      match generator.val with
      | 0 => (64 : Fin 215)
      | 1 => (159 : Fin 215)
      | _ => (160 : Fin 215)
  | 7 =>
      match generator.val with
      | 0 => (65 : Fin 215)
      | 1 => (160 : Fin 215)
      | _ => (161 : Fin 215)
  | 8 =>
      match generator.val with
      | 0 => (66 : Fin 215)
      | 1 => (161 : Fin 215)
      | _ => (162 : Fin 215)
  | 9 =>
      match generator.val with
      | 0 => (67 : Fin 215)
      | 1 => (162 : Fin 215)
      | _ => (163 : Fin 215)
  | 10 =>
      match generator.val with
      | 0 => (68 : Fin 215)
      | 1 => (163 : Fin 215)
      | _ => (164 : Fin 215)
  | 11 =>
      match generator.val with
      | 0 => (159 : Fin 215)
      | 1 => (57 : Fin 215)
      | _ => (165 : Fin 215)
  | 12 =>
      match generator.val with
      | 0 => (160 : Fin 215)
      | 1 => (165 : Fin 215)
      | _ => (166 : Fin 215)
  | 13 =>
      match generator.val with
      | 0 => (161 : Fin 215)
      | 1 => (166 : Fin 215)
      | _ => (167 : Fin 215)
  | 14 =>
      match generator.val with
      | 0 => (162 : Fin 215)
      | 1 => (167 : Fin 215)
      | _ => (168 : Fin 215)
  | 15 =>
      match generator.val with
      | 0 => (163 : Fin 215)
      | 1 => (168 : Fin 215)
      | _ => (169 : Fin 215)
  | 16 =>
      match generator.val with
      | 0 => (164 : Fin 215)
      | 1 => (169 : Fin 215)
      | _ => (59 : Fin 215)
  | 17 =>
      match generator.val with
      | 0 => (165 : Fin 215)
      | 1 => (61 : Fin 215)
      | _ => (170 : Fin 215)
  | 18 =>
      match generator.val with
      | 0 => (166 : Fin 215)
      | 1 => (170 : Fin 215)
      | _ => (171 : Fin 215)
  | 19 =>
      match generator.val with
      | 0 => (167 : Fin 215)
      | 1 => (171 : Fin 215)
      | _ => (172 : Fin 215)
  | 20 =>
      match generator.val with
      | 0 => (168 : Fin 215)
      | 1 => (172 : Fin 215)
      | _ => (173 : Fin 215)
  | 21 =>
      match generator.val with
      | 0 => (169 : Fin 215)
      | 1 => (173 : Fin 215)
      | _ => (62 : Fin 215)
  | 22 =>
      match generator.val with
      | 0 => (170 : Fin 215)
      | 1 => (66 : Fin 215)
      | _ => (174 : Fin 215)
  | 23 =>
      match generator.val with
      | 0 => (171 : Fin 215)
      | 1 => (174 : Fin 215)
      | _ => (175 : Fin 215)
  | 24 =>
      match generator.val with
      | 0 => (172 : Fin 215)
      | 1 => (175 : Fin 215)
      | _ => (176 : Fin 215)
  | 25 =>
      match generator.val with
      | 0 => (173 : Fin 215)
      | 1 => (176 : Fin 215)
      | _ => (66 : Fin 215)
  | 26 =>
      match generator.val with
      | 0 => (174 : Fin 215)
      | 1 => (72 : Fin 215)
      | _ => (177 : Fin 215)
  | 27 =>
      match generator.val with
      | 0 => (175 : Fin 215)
      | 1 => (177 : Fin 215)
      | _ => (178 : Fin 215)
  | 28 =>
      match generator.val with
      | 0 => (176 : Fin 215)
      | 1 => (178 : Fin 215)
      | _ => (71 : Fin 215)
  | 29 =>
      match generator.val with
      | 0 => (177 : Fin 215)
      | 1 => (78 : Fin 215)
      | _ => (179 : Fin 215)
  | 30 =>
      match generator.val with
      | 0 => (178 : Fin 215)
      | 1 => (179 : Fin 215)
      | _ => (76 : Fin 215)
  | _ =>
      match generator.val with
      | 0 => (92 : Fin 215)
      | 1 => (80 : Fin 215)
      | _ => (180 : Fin 215)

private def transitionChunk5 (index : Nat)
    (generator : Fin 3) : Fin 215 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (93 : Fin 215)
      | 1 => (180 : Fin 215)
      | _ => (181 : Fin 215)
  | 1 =>
      match generator.val with
      | 0 => (94 : Fin 215)
      | 1 => (181 : Fin 215)
      | _ => (182 : Fin 215)
  | 2 =>
      match generator.val with
      | 0 => (95 : Fin 215)
      | 1 => (182 : Fin 215)
      | _ => (183 : Fin 215)
  | 3 =>
      match generator.val with
      | 0 => (96 : Fin 215)
      | 1 => (183 : Fin 215)
      | _ => (184 : Fin 215)
  | 4 =>
      match generator.val with
      | 0 => (97 : Fin 215)
      | 1 => (184 : Fin 215)
      | _ => (82 : Fin 215)
  | 5 =>
      match generator.val with
      | 0 => (180 : Fin 215)
      | 1 => (84 : Fin 215)
      | _ => (185 : Fin 215)
  | 6 =>
      match generator.val with
      | 0 => (181 : Fin 215)
      | 1 => (185 : Fin 215)
      | _ => (186 : Fin 215)
  | 7 =>
      match generator.val with
      | 0 => (182 : Fin 215)
      | 1 => (186 : Fin 215)
      | _ => (187 : Fin 215)
  | 8 =>
      match generator.val with
      | 0 => (183 : Fin 215)
      | 1 => (187 : Fin 215)
      | _ => (188 : Fin 215)
  | 9 =>
      match generator.val with
      | 0 => (184 : Fin 215)
      | 1 => (188 : Fin 215)
      | _ => (85 : Fin 215)
  | 10 =>
      match generator.val with
      | 0 => (185 : Fin 215)
      | 1 => (89 : Fin 215)
      | _ => (189 : Fin 215)
  | 11 =>
      match generator.val with
      | 0 => (186 : Fin 215)
      | 1 => (189 : Fin 215)
      | _ => (190 : Fin 215)
  | 12 =>
      match generator.val with
      | 0 => (187 : Fin 215)
      | 1 => (190 : Fin 215)
      | _ => (191 : Fin 215)
  | 13 =>
      match generator.val with
      | 0 => (188 : Fin 215)
      | 1 => (191 : Fin 215)
      | _ => (89 : Fin 215)
  | 14 =>
      match generator.val with
      | 0 => (189 : Fin 215)
      | 1 => (95 : Fin 215)
      | _ => (192 : Fin 215)
  | 15 =>
      match generator.val with
      | 0 => (190 : Fin 215)
      | 1 => (192 : Fin 215)
      | _ => (193 : Fin 215)
  | 16 =>
      match generator.val with
      | 0 => (191 : Fin 215)
      | 1 => (193 : Fin 215)
      | _ => (94 : Fin 215)
  | 17 =>
      match generator.val with
      | 0 => (192 : Fin 215)
      | 1 => (101 : Fin 215)
      | _ => (194 : Fin 215)
  | 18 =>
      match generator.val with
      | 0 => (193 : Fin 215)
      | 1 => (194 : Fin 215)
      | _ => (99 : Fin 215)
  | 19 =>
      match generator.val with
      | 0 => (194 : Fin 215)
      | 1 => (106 : Fin 215)
      | _ => (103 : Fin 215)
  | 20 =>
      match generator.val with
      | 0 => (122 : Fin 215)
      | 1 => (108 : Fin 215)
      | _ => (195 : Fin 215)
  | 21 =>
      match generator.val with
      | 0 => (123 : Fin 215)
      | 1 => (195 : Fin 215)
      | _ => (196 : Fin 215)
  | 22 =>
      match generator.val with
      | 0 => (124 : Fin 215)
      | 1 => (196 : Fin 215)
      | _ => (197 : Fin 215)
  | 23 =>
      match generator.val with
      | 0 => (125 : Fin 215)
      | 1 => (197 : Fin 215)
      | _ => (198 : Fin 215)
  | 24 =>
      match generator.val with
      | 0 => (126 : Fin 215)
      | 1 => (198 : Fin 215)
      | _ => (109 : Fin 215)
  | 25 =>
      match generator.val with
      | 0 => (195 : Fin 215)
      | 1 => (113 : Fin 215)
      | _ => (199 : Fin 215)
  | 26 =>
      match generator.val with
      | 0 => (196 : Fin 215)
      | 1 => (199 : Fin 215)
      | _ => (200 : Fin 215)
  | 27 =>
      match generator.val with
      | 0 => (197 : Fin 215)
      | 1 => (200 : Fin 215)
      | _ => (201 : Fin 215)
  | 28 =>
      match generator.val with
      | 0 => (198 : Fin 215)
      | 1 => (201 : Fin 215)
      | _ => (113 : Fin 215)
  | 29 =>
      match generator.val with
      | 0 => (199 : Fin 215)
      | 1 => (119 : Fin 215)
      | _ => (202 : Fin 215)
  | 30 =>
      match generator.val with
      | 0 => (200 : Fin 215)
      | 1 => (202 : Fin 215)
      | _ => (203 : Fin 215)
  | _ =>
      match generator.val with
      | 0 => (201 : Fin 215)
      | 1 => (203 : Fin 215)
      | _ => (118 : Fin 215)

private def transitionChunk6 (index : Nat)
    (generator : Fin 3) : Fin 215 :=
  match index with
  | 0 =>
      match generator.val with
      | 0 => (202 : Fin 215)
      | 1 => (125 : Fin 215)
      | _ => (204 : Fin 215)
  | 1 =>
      match generator.val with
      | 0 => (203 : Fin 215)
      | 1 => (204 : Fin 215)
      | _ => (123 : Fin 215)
  | 2 =>
      match generator.val with
      | 0 => (204 : Fin 215)
      | 1 => (130 : Fin 215)
      | _ => (127 : Fin 215)
  | 3 =>
      match generator.val with
      | 0 => (150 : Fin 215)
      | 1 => (136 : Fin 215)
      | _ => (205 : Fin 215)
  | 4 =>
      match generator.val with
      | 0 => (151 : Fin 215)
      | 1 => (205 : Fin 215)
      | _ => (206 : Fin 215)
  | 5 =>
      match generator.val with
      | 0 => (152 : Fin 215)
      | 1 => (206 : Fin 215)
      | _ => (207 : Fin 215)
  | 6 =>
      match generator.val with
      | 0 => (153 : Fin 215)
      | 1 => (207 : Fin 215)
      | _ => (136 : Fin 215)
  | 7 =>
      match generator.val with
      | 0 => (205 : Fin 215)
      | 1 => (142 : Fin 215)
      | _ => (208 : Fin 215)
  | 8 =>
      match generator.val with
      | 0 => (206 : Fin 215)
      | 1 => (208 : Fin 215)
      | _ => (209 : Fin 215)
  | 9 =>
      match generator.val with
      | 0 => (207 : Fin 215)
      | 1 => (209 : Fin 215)
      | _ => (141 : Fin 215)
  | 10 =>
      match generator.val with
      | 0 => (208 : Fin 215)
      | 1 => (148 : Fin 215)
      | _ => (210 : Fin 215)
  | 11 =>
      match generator.val with
      | 0 => (209 : Fin 215)
      | 1 => (210 : Fin 215)
      | _ => (146 : Fin 215)
  | 12 =>
      match generator.val with
      | 0 => (210 : Fin 215)
      | 1 => (153 : Fin 215)
      | _ => (150 : Fin 215)
  | 13 =>
      match generator.val with
      | 0 => (174 : Fin 215)
      | 1 => (162 : Fin 215)
      | _ => (211 : Fin 215)
  | 14 =>
      match generator.val with
      | 0 => (175 : Fin 215)
      | 1 => (211 : Fin 215)
      | _ => (212 : Fin 215)
  | 15 =>
      match generator.val with
      | 0 => (176 : Fin 215)
      | 1 => (212 : Fin 215)
      | _ => (161 : Fin 215)
  | 16 =>
      match generator.val with
      | 0 => (211 : Fin 215)
      | 1 => (168 : Fin 215)
      | _ => (213 : Fin 215)
  | 17 =>
      match generator.val with
      | 0 => (212 : Fin 215)
      | 1 => (213 : Fin 215)
      | _ => (166 : Fin 215)
  | 18 =>
      match generator.val with
      | 0 => (213 : Fin 215)
      | 1 => (173 : Fin 215)
      | _ => (170 : Fin 215)
  | 19 =>
      match generator.val with
      | 0 => (192 : Fin 215)
      | 1 => (183 : Fin 215)
      | _ => (214 : Fin 215)
  | 20 =>
      match generator.val with
      | 0 => (193 : Fin 215)
      | 1 => (214 : Fin 215)
      | _ => (181 : Fin 215)
  | 21 =>
      match generator.val with
      | 0 => (214 : Fin 215)
      | 1 => (188 : Fin 215)
      | _ => (185 : Fin 215)
  | _ =>
      match generator.val with
      | 0 => (204 : Fin 215)
      | 1 => (198 : Fin 215)
      | _ => (195 : Fin 215)

def transition (state : Fin 215)
    (generator : Fin 3) : Fin 215 :=
  if state.val < 32 then transitionChunk0 state.val generator else
    if state.val < 64 then transitionChunk1 (state.val - 32) generator else
      if state.val < 96 then transitionChunk2 (state.val - 64) generator else
        if state.val < 128 then transitionChunk3 (state.val - 96) generator else
          if state.val < 160 then transitionChunk4 (state.val - 128) generator else
            if state.val < 192 then transitionChunk5 (state.val - 160) generator else
              transitionChunk6 (state.val - 192) generator

private def representativeHeadChunk0 (index : Nat) : Fin 3 :=
  match index with
  | 0 => (0 : Fin 3)
  | 1 => (1 : Fin 3)
  | 2 => (2 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (0 : Fin 3)
  | 5 => (0 : Fin 3)
  | 6 => (1 : Fin 3)
  | 7 => (1 : Fin 3)
  | 8 => (2 : Fin 3)
  | 9 => (0 : Fin 3)
  | 10 => (0 : Fin 3)
  | 11 => (0 : Fin 3)
  | 12 => (0 : Fin 3)
  | 13 => (0 : Fin 3)
  | 14 => (0 : Fin 3)
  | 15 => (1 : Fin 3)
  | 16 => (1 : Fin 3)
  | 17 => (1 : Fin 3)
  | 18 => (2 : Fin 3)
  | 19 => (0 : Fin 3)
  | 20 => (0 : Fin 3)
  | 21 => (0 : Fin 3)
  | 22 => (0 : Fin 3)
  | 23 => (0 : Fin 3)
  | 24 => (0 : Fin 3)
  | 25 => (0 : Fin 3)
  | 26 => (0 : Fin 3)
  | 27 => (0 : Fin 3)
  | 28 => (0 : Fin 3)
  | 29 => (1 : Fin 3)
  | 30 => (1 : Fin 3)
  | _ => (1 : Fin 3)

private def representativeHeadChunk1 (index : Nat) : Fin 3 :=
  match index with
  | 0 => (1 : Fin 3)
  | 1 => (2 : Fin 3)
  | 2 => (0 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (0 : Fin 3)
  | 5 => (0 : Fin 3)
  | 6 => (0 : Fin 3)
  | 7 => (0 : Fin 3)
  | 8 => (0 : Fin 3)
  | 9 => (0 : Fin 3)
  | 10 => (0 : Fin 3)
  | 11 => (0 : Fin 3)
  | 12 => (0 : Fin 3)
  | 13 => (0 : Fin 3)
  | 14 => (0 : Fin 3)
  | 15 => (0 : Fin 3)
  | 16 => (0 : Fin 3)
  | 17 => (1 : Fin 3)
  | 18 => (1 : Fin 3)
  | 19 => (1 : Fin 3)
  | 20 => (1 : Fin 3)
  | 21 => (1 : Fin 3)
  | 22 => (2 : Fin 3)
  | 23 => (0 : Fin 3)
  | 24 => (0 : Fin 3)
  | 25 => (0 : Fin 3)
  | 26 => (0 : Fin 3)
  | 27 => (0 : Fin 3)
  | 28 => (0 : Fin 3)
  | 29 => (0 : Fin 3)
  | 30 => (0 : Fin 3)
  | _ => (0 : Fin 3)

private def representativeHeadChunk2 (index : Nat) : Fin 3 :=
  match index with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (0 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (0 : Fin 3)
  | 5 => (0 : Fin 3)
  | 6 => (0 : Fin 3)
  | 7 => (0 : Fin 3)
  | 8 => (0 : Fin 3)
  | 9 => (0 : Fin 3)
  | 10 => (0 : Fin 3)
  | 11 => (1 : Fin 3)
  | 12 => (1 : Fin 3)
  | 13 => (1 : Fin 3)
  | 14 => (1 : Fin 3)
  | 15 => (1 : Fin 3)
  | 16 => (0 : Fin 3)
  | 17 => (0 : Fin 3)
  | 18 => (0 : Fin 3)
  | 19 => (0 : Fin 3)
  | 20 => (0 : Fin 3)
  | 21 => (0 : Fin 3)
  | 22 => (0 : Fin 3)
  | 23 => (0 : Fin 3)
  | 24 => (0 : Fin 3)
  | 25 => (0 : Fin 3)
  | 26 => (0 : Fin 3)
  | 27 => (0 : Fin 3)
  | 28 => (0 : Fin 3)
  | 29 => (0 : Fin 3)
  | 30 => (0 : Fin 3)
  | _ => (0 : Fin 3)

private def representativeHeadChunk3 (index : Nat) : Fin 3 :=
  match index with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (0 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (0 : Fin 3)
  | 5 => (0 : Fin 3)
  | 6 => (0 : Fin 3)
  | 7 => (1 : Fin 3)
  | 8 => (1 : Fin 3)
  | 9 => (1 : Fin 3)
  | 10 => (1 : Fin 3)
  | 11 => (0 : Fin 3)
  | 12 => (0 : Fin 3)
  | 13 => (0 : Fin 3)
  | 14 => (0 : Fin 3)
  | 15 => (0 : Fin 3)
  | 16 => (0 : Fin 3)
  | 17 => (0 : Fin 3)
  | 18 => (0 : Fin 3)
  | 19 => (0 : Fin 3)
  | 20 => (0 : Fin 3)
  | 21 => (0 : Fin 3)
  | 22 => (0 : Fin 3)
  | 23 => (0 : Fin 3)
  | 24 => (0 : Fin 3)
  | 25 => (0 : Fin 3)
  | 26 => (0 : Fin 3)
  | 27 => (0 : Fin 3)
  | 28 => (0 : Fin 3)
  | 29 => (0 : Fin 3)
  | 30 => (0 : Fin 3)
  | _ => (0 : Fin 3)

private def representativeHeadChunk4 (index : Nat) : Fin 3 :=
  match index with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (0 : Fin 3)
  | 3 => (1 : Fin 3)
  | 4 => (1 : Fin 3)
  | 5 => (1 : Fin 3)
  | 6 => (0 : Fin 3)
  | 7 => (0 : Fin 3)
  | 8 => (0 : Fin 3)
  | 9 => (0 : Fin 3)
  | 10 => (0 : Fin 3)
  | 11 => (0 : Fin 3)
  | 12 => (0 : Fin 3)
  | 13 => (0 : Fin 3)
  | 14 => (0 : Fin 3)
  | 15 => (0 : Fin 3)
  | 16 => (0 : Fin 3)
  | 17 => (0 : Fin 3)
  | 18 => (0 : Fin 3)
  | 19 => (0 : Fin 3)
  | 20 => (0 : Fin 3)
  | 21 => (0 : Fin 3)
  | 22 => (0 : Fin 3)
  | 23 => (0 : Fin 3)
  | 24 => (0 : Fin 3)
  | 25 => (0 : Fin 3)
  | 26 => (0 : Fin 3)
  | 27 => (0 : Fin 3)
  | 28 => (0 : Fin 3)
  | 29 => (1 : Fin 3)
  | 30 => (1 : Fin 3)
  | _ => (0 : Fin 3)

private def representativeHeadChunk5 (index : Nat) : Fin 3 :=
  match index with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (0 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (0 : Fin 3)
  | 5 => (0 : Fin 3)
  | 6 => (0 : Fin 3)
  | 7 => (0 : Fin 3)
  | 8 => (0 : Fin 3)
  | 9 => (0 : Fin 3)
  | 10 => (0 : Fin 3)
  | 11 => (0 : Fin 3)
  | 12 => (0 : Fin 3)
  | 13 => (0 : Fin 3)
  | 14 => (0 : Fin 3)
  | 15 => (0 : Fin 3)
  | 16 => (0 : Fin 3)
  | 17 => (0 : Fin 3)
  | 18 => (0 : Fin 3)
  | 19 => (1 : Fin 3)
  | 20 => (0 : Fin 3)
  | 21 => (0 : Fin 3)
  | 22 => (0 : Fin 3)
  | 23 => (0 : Fin 3)
  | 24 => (0 : Fin 3)
  | 25 => (0 : Fin 3)
  | 26 => (0 : Fin 3)
  | 27 => (0 : Fin 3)
  | 28 => (0 : Fin 3)
  | 29 => (0 : Fin 3)
  | 30 => (0 : Fin 3)
  | _ => (0 : Fin 3)

private def representativeHeadChunk6 (index : Nat) : Fin 3 :=
  match index with
  | 0 => (0 : Fin 3)
  | 1 => (0 : Fin 3)
  | 2 => (0 : Fin 3)
  | 3 => (0 : Fin 3)
  | 4 => (0 : Fin 3)
  | 5 => (0 : Fin 3)
  | 6 => (0 : Fin 3)
  | 7 => (0 : Fin 3)
  | 8 => (0 : Fin 3)
  | 9 => (0 : Fin 3)
  | 10 => (0 : Fin 3)
  | 11 => (0 : Fin 3)
  | 12 => (0 : Fin 3)
  | 13 => (0 : Fin 3)
  | 14 => (0 : Fin 3)
  | 15 => (0 : Fin 3)
  | 16 => (0 : Fin 3)
  | 17 => (0 : Fin 3)
  | 18 => (0 : Fin 3)
  | 19 => (0 : Fin 3)
  | 20 => (0 : Fin 3)
  | 21 => (0 : Fin 3)
  | _ => (0 : Fin 3)

def representativeHead (state : Fin 215) : Fin 3 :=
  if state.val < 32 then representativeHeadChunk0 state.val else
    if state.val < 64 then representativeHeadChunk1 (state.val - 32) else
      if state.val < 96 then representativeHeadChunk2 (state.val - 64) else
        if state.val < 128 then representativeHeadChunk3 (state.val - 96) else
          if state.val < 160 then representativeHeadChunk4 (state.val - 128) else
            if state.val < 192 then representativeHeadChunk5 (state.val - 160) else
              representativeHeadChunk6 (state.val - 192)

private def representativeTailChunk0 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => []
  | 1 => []
  | 2 => []
  | 3 => [0]
  | 4 => [1]
  | 5 => [2]
  | 6 => [1]
  | 7 => [2]
  | 8 => [2]
  | 9 => [0, 0]
  | 10 => [0, 1]
  | 11 => [0, 2]
  | 12 => [1, 1]
  | 13 => [1, 2]
  | 14 => [2, 2]
  | 15 => [1, 1]
  | 16 => [1, 2]
  | 17 => [2, 2]
  | 18 => [2, 2]
  | 19 => [0, 0, 0]
  | 20 => [0, 0, 1]
  | 21 => [0, 0, 2]
  | 22 => [0, 1, 1]
  | 23 => [0, 1, 2]
  | 24 => [0, 2, 2]
  | 25 => [1, 1, 1]
  | 26 => [1, 1, 2]
  | 27 => [1, 2, 2]
  | 28 => [2, 2, 2]
  | 29 => [1, 1, 1]
  | 30 => [1, 1, 2]
  | _ => [1, 2, 2]

private def representativeTailChunk1 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [2, 2, 2]
  | 1 => [2, 2, 2]
  | 2 => [0, 0, 0, 0]
  | 3 => [0, 0, 0, 1]
  | 4 => [0, 0, 0, 2]
  | 5 => [0, 0, 1, 1]
  | 6 => [0, 0, 1, 2]
  | 7 => [0, 0, 2, 2]
  | 8 => [0, 1, 1, 1]
  | 9 => [0, 1, 1, 2]
  | 10 => [0, 1, 2, 2]
  | 11 => [0, 2, 2, 2]
  | 12 => [1, 1, 1, 1]
  | 13 => [1, 1, 1, 2]
  | 14 => [1, 1, 2, 2]
  | 15 => [1, 2, 2, 2]
  | 16 => [2, 2, 2, 2]
  | 17 => [1, 1, 1, 1]
  | 18 => [1, 1, 1, 2]
  | 19 => [1, 1, 2, 2]
  | 20 => [1, 2, 2, 2]
  | 21 => [2, 2, 2, 2]
  | 22 => [2, 2, 2, 2]
  | 23 => [0, 0, 0, 0, 1]
  | 24 => [0, 0, 0, 0, 2]
  | 25 => [0, 0, 0, 1, 1]
  | 26 => [0, 0, 0, 1, 2]
  | 27 => [0, 0, 0, 2, 2]
  | 28 => [0, 0, 1, 1, 1]
  | 29 => [0, 0, 1, 1, 2]
  | 30 => [0, 0, 1, 2, 2]
  | _ => [0, 0, 2, 2, 2]

private def representativeTailChunk2 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [0, 1, 1, 1, 1]
  | 1 => [0, 1, 1, 1, 2]
  | 2 => [0, 1, 1, 2, 2]
  | 3 => [0, 1, 2, 2, 2]
  | 4 => [0, 2, 2, 2, 2]
  | 5 => [1, 1, 1, 1, 1]
  | 6 => [1, 1, 1, 1, 2]
  | 7 => [1, 1, 1, 2, 2]
  | 8 => [1, 1, 2, 2, 2]
  | 9 => [1, 2, 2, 2, 2]
  | 10 => [2, 2, 2, 2, 2]
  | 11 => [1, 1, 1, 1, 2]
  | 12 => [1, 1, 1, 2, 2]
  | 13 => [1, 1, 2, 2, 2]
  | 14 => [1, 2, 2, 2, 2]
  | 15 => [2, 2, 2, 2, 2]
  | 16 => [0, 0, 0, 0, 1, 1]
  | 17 => [0, 0, 0, 0, 1, 2]
  | 18 => [0, 0, 0, 0, 2, 2]
  | 19 => [0, 0, 0, 1, 1, 1]
  | 20 => [0, 0, 0, 1, 1, 2]
  | 21 => [0, 0, 0, 1, 2, 2]
  | 22 => [0, 0, 0, 2, 2, 2]
  | 23 => [0, 0, 1, 1, 1, 1]
  | 24 => [0, 0, 1, 1, 1, 2]
  | 25 => [0, 0, 1, 1, 2, 2]
  | 26 => [0, 0, 1, 2, 2, 2]
  | 27 => [0, 0, 2, 2, 2, 2]
  | 28 => [0, 1, 1, 1, 1, 1]
  | 29 => [0, 1, 1, 1, 1, 2]
  | 30 => [0, 1, 1, 1, 2, 2]
  | _ => [0, 1, 1, 2, 2, 2]

private def representativeTailChunk3 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [0, 1, 2, 2, 2, 2]
  | 1 => [0, 2, 2, 2, 2, 2]
  | 2 => [1, 1, 1, 1, 1, 2]
  | 3 => [1, 1, 1, 1, 2, 2]
  | 4 => [1, 1, 1, 2, 2, 2]
  | 5 => [1, 1, 2, 2, 2, 2]
  | 6 => [1, 2, 2, 2, 2, 2]
  | 7 => [1, 1, 1, 1, 2, 2]
  | 8 => [1, 1, 1, 2, 2, 2]
  | 9 => [1, 1, 2, 2, 2, 2]
  | 10 => [1, 2, 2, 2, 2, 2]
  | 11 => [0, 0, 0, 0, 1, 1, 1]
  | 12 => [0, 0, 0, 0, 1, 1, 2]
  | 13 => [0, 0, 0, 0, 1, 2, 2]
  | 14 => [0, 0, 0, 0, 2, 2, 2]
  | 15 => [0, 0, 0, 1, 1, 1, 1]
  | 16 => [0, 0, 0, 1, 1, 1, 2]
  | 17 => [0, 0, 0, 1, 1, 2, 2]
  | 18 => [0, 0, 0, 1, 2, 2, 2]
  | 19 => [0, 0, 0, 2, 2, 2, 2]
  | 20 => [0, 0, 1, 1, 1, 1, 1]
  | 21 => [0, 0, 1, 1, 1, 1, 2]
  | 22 => [0, 0, 1, 1, 1, 2, 2]
  | 23 => [0, 0, 1, 1, 2, 2, 2]
  | 24 => [0, 0, 1, 2, 2, 2, 2]
  | 25 => [0, 0, 2, 2, 2, 2, 2]
  | 26 => [0, 1, 1, 1, 1, 1, 2]
  | 27 => [0, 1, 1, 1, 1, 2, 2]
  | 28 => [0, 1, 1, 1, 2, 2, 2]
  | 29 => [0, 1, 1, 2, 2, 2, 2]
  | 30 => [0, 1, 2, 2, 2, 2, 2]
  | _ => [1, 1, 1, 1, 1, 2, 2]

private def representativeTailChunk4 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [1, 1, 1, 1, 2, 2, 2]
  | 1 => [1, 1, 1, 2, 2, 2, 2]
  | 2 => [1, 1, 2, 2, 2, 2, 2]
  | 3 => [1, 1, 1, 1, 2, 2, 2]
  | 4 => [1, 1, 1, 2, 2, 2, 2]
  | 5 => [1, 1, 2, 2, 2, 2, 2]
  | 6 => [0, 0, 0, 0, 1, 1, 1, 1]
  | 7 => [0, 0, 0, 0, 1, 1, 1, 2]
  | 8 => [0, 0, 0, 0, 1, 1, 2, 2]
  | 9 => [0, 0, 0, 0, 1, 2, 2, 2]
  | 10 => [0, 0, 0, 0, 2, 2, 2, 2]
  | 11 => [0, 0, 0, 1, 1, 1, 1, 1]
  | 12 => [0, 0, 0, 1, 1, 1, 1, 2]
  | 13 => [0, 0, 0, 1, 1, 1, 2, 2]
  | 14 => [0, 0, 0, 1, 1, 2, 2, 2]
  | 15 => [0, 0, 0, 1, 2, 2, 2, 2]
  | 16 => [0, 0, 0, 2, 2, 2, 2, 2]
  | 17 => [0, 0, 1, 1, 1, 1, 1, 2]
  | 18 => [0, 0, 1, 1, 1, 1, 2, 2]
  | 19 => [0, 0, 1, 1, 1, 2, 2, 2]
  | 20 => [0, 0, 1, 1, 2, 2, 2, 2]
  | 21 => [0, 0, 1, 2, 2, 2, 2, 2]
  | 22 => [0, 1, 1, 1, 1, 1, 2, 2]
  | 23 => [0, 1, 1, 1, 1, 2, 2, 2]
  | 24 => [0, 1, 1, 1, 2, 2, 2, 2]
  | 25 => [0, 1, 1, 2, 2, 2, 2, 2]
  | 26 => [1, 1, 1, 1, 1, 2, 2, 2]
  | 27 => [1, 1, 1, 1, 2, 2, 2, 2]
  | 28 => [1, 1, 1, 2, 2, 2, 2, 2]
  | 29 => [1, 1, 1, 1, 2, 2, 2, 2]
  | 30 => [1, 1, 1, 2, 2, 2, 2, 2]
  | _ => [0, 0, 0, 0, 1, 1, 1, 1, 1]

private def representativeTailChunk5 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [0, 0, 0, 0, 1, 1, 1, 1, 2]
  | 1 => [0, 0, 0, 0, 1, 1, 1, 2, 2]
  | 2 => [0, 0, 0, 0, 1, 1, 2, 2, 2]
  | 3 => [0, 0, 0, 0, 1, 2, 2, 2, 2]
  | 4 => [0, 0, 0, 0, 2, 2, 2, 2, 2]
  | 5 => [0, 0, 0, 1, 1, 1, 1, 1, 2]
  | 6 => [0, 0, 0, 1, 1, 1, 1, 2, 2]
  | 7 => [0, 0, 0, 1, 1, 1, 2, 2, 2]
  | 8 => [0, 0, 0, 1, 1, 2, 2, 2, 2]
  | 9 => [0, 0, 0, 1, 2, 2, 2, 2, 2]
  | 10 => [0, 0, 1, 1, 1, 1, 1, 2, 2]
  | 11 => [0, 0, 1, 1, 1, 1, 2, 2, 2]
  | 12 => [0, 0, 1, 1, 1, 2, 2, 2, 2]
  | 13 => [0, 0, 1, 1, 2, 2, 2, 2, 2]
  | 14 => [0, 1, 1, 1, 1, 1, 2, 2, 2]
  | 15 => [0, 1, 1, 1, 1, 2, 2, 2, 2]
  | 16 => [0, 1, 1, 1, 2, 2, 2, 2, 2]
  | 17 => [1, 1, 1, 1, 1, 2, 2, 2, 2]
  | 18 => [1, 1, 1, 1, 2, 2, 2, 2, 2]
  | 19 => [1, 1, 1, 1, 2, 2, 2, 2, 2]
  | 20 => [0, 0, 0, 0, 1, 1, 1, 1, 1, 2]
  | 21 => [0, 0, 0, 0, 1, 1, 1, 1, 2, 2]
  | 22 => [0, 0, 0, 0, 1, 1, 1, 2, 2, 2]
  | 23 => [0, 0, 0, 0, 1, 1, 2, 2, 2, 2]
  | 24 => [0, 0, 0, 0, 1, 2, 2, 2, 2, 2]
  | 25 => [0, 0, 0, 1, 1, 1, 1, 1, 2, 2]
  | 26 => [0, 0, 0, 1, 1, 1, 1, 2, 2, 2]
  | 27 => [0, 0, 0, 1, 1, 1, 2, 2, 2, 2]
  | 28 => [0, 0, 0, 1, 1, 2, 2, 2, 2, 2]
  | 29 => [0, 0, 1, 1, 1, 1, 1, 2, 2, 2]
  | 30 => [0, 0, 1, 1, 1, 1, 2, 2, 2, 2]
  | _ => [0, 0, 1, 1, 1, 2, 2, 2, 2, 2]

private def representativeTailChunk6 (index : Nat) :
    List (Fin 3) :=
  match index with
  | 0 => [0, 1, 1, 1, 1, 1, 2, 2, 2, 2]
  | 1 => [0, 1, 1, 1, 1, 2, 2, 2, 2, 2]
  | 2 => [1, 1, 1, 1, 1, 2, 2, 2, 2, 2]
  | 3 => [0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2]
  | 4 => [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2]
  | 5 => [0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2]
  | 6 => [0, 0, 0, 0, 1, 1, 2, 2, 2, 2, 2]
  | 7 => [0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2]
  | 8 => [0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2]
  | 9 => [0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2]
  | 10 => [0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2]
  | 11 => [0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2]
  | 12 => [0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]
  | 13 => [0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2]
  | 14 => [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2]
  | 15 => [0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2]
  | 16 => [0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2]
  | 17 => [0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2]
  | 18 => [0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]
  | 19 => [0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2]
  | 20 => [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2]
  | 21 => [0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]
  | _ => [0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2]

def representativeTail (state : Fin 215) :
    List (Fin 3) :=
  if state.val < 32 then representativeTailChunk0 state.val else
    if state.val < 64 then representativeTailChunk1 (state.val - 32) else
      if state.val < 96 then representativeTailChunk2 (state.val - 64) else
        if state.val < 128 then representativeTailChunk3 (state.val - 96) else
          if state.val < 160 then representativeTailChunk4 (state.val - 128) else
            if state.val < 192 then representativeTailChunk5 (state.val - 160) else
              representativeTailChunk6 (state.val - 192)

private def sourceLabelChunk0 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (5 : Fin 6)
  | 1 => (3 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (5 : Fin 6)
  | 4 => (3 : Fin 6)
  | 5 => (2 : Fin 6)
  | 6 => (1 : Fin 6)
  | 7 => (3 : Fin 6)
  | 8 => (0 : Fin 6)
  | 9 => (5 : Fin 6)
  | 10 => (3 : Fin 6)
  | 11 => (2 : Fin 6)
  | 12 => (1 : Fin 6)
  | 13 => (3 : Fin 6)
  | 14 => (0 : Fin 6)
  | 15 => (4 : Fin 6)
  | 16 => (1 : Fin 6)
  | 17 => (3 : Fin 6)
  | 18 => (0 : Fin 6)
  | 19 => (5 : Fin 6)
  | 20 => (3 : Fin 6)
  | 21 => (2 : Fin 6)
  | 22 => (1 : Fin 6)
  | 23 => (3 : Fin 6)
  | 24 => (0 : Fin 6)
  | 25 => (4 : Fin 6)
  | 26 => (1 : Fin 6)
  | 27 => (3 : Fin 6)
  | 28 => (0 : Fin 6)
  | 29 => (0 : Fin 6)
  | 30 => (4 : Fin 6)
  | _ => (1 : Fin 6)

private def sourceLabelChunk1 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (3 : Fin 6)
  | 1 => (0 : Fin 6)
  | 2 => (5 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (2 : Fin 6)
  | 5 => (1 : Fin 6)
  | 6 => (3 : Fin 6)
  | 7 => (0 : Fin 6)
  | 8 => (4 : Fin 6)
  | 9 => (1 : Fin 6)
  | 10 => (3 : Fin 6)
  | 11 => (0 : Fin 6)
  | 12 => (0 : Fin 6)
  | 13 => (4 : Fin 6)
  | 14 => (1 : Fin 6)
  | 15 => (3 : Fin 6)
  | 16 => (0 : Fin 6)
  | 17 => (3 : Fin 6)
  | 18 => (0 : Fin 6)
  | 19 => (4 : Fin 6)
  | 20 => (1 : Fin 6)
  | 21 => (3 : Fin 6)
  | 22 => (0 : Fin 6)
  | 23 => (3 : Fin 6)
  | 24 => (2 : Fin 6)
  | 25 => (1 : Fin 6)
  | 26 => (3 : Fin 6)
  | 27 => (0 : Fin 6)
  | 28 => (4 : Fin 6)
  | 29 => (1 : Fin 6)
  | 30 => (3 : Fin 6)
  | _ => (0 : Fin 6)

private def sourceLabelChunk2 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (0 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (1 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (0 : Fin 6)
  | 5 => (3 : Fin 6)
  | 6 => (0 : Fin 6)
  | 7 => (4 : Fin 6)
  | 8 => (1 : Fin 6)
  | 9 => (3 : Fin 6)
  | 10 => (0 : Fin 6)
  | 11 => (3 : Fin 6)
  | 12 => (0 : Fin 6)
  | 13 => (4 : Fin 6)
  | 14 => (1 : Fin 6)
  | 15 => (3 : Fin 6)
  | 16 => (1 : Fin 6)
  | 17 => (3 : Fin 6)
  | 18 => (0 : Fin 6)
  | 19 => (4 : Fin 6)
  | 20 => (1 : Fin 6)
  | 21 => (3 : Fin 6)
  | 22 => (0 : Fin 6)
  | 23 => (0 : Fin 6)
  | 24 => (4 : Fin 6)
  | 25 => (1 : Fin 6)
  | 26 => (3 : Fin 6)
  | 27 => (0 : Fin 6)
  | 28 => (3 : Fin 6)
  | 29 => (0 : Fin 6)
  | 30 => (4 : Fin 6)
  | _ => (1 : Fin 6)

private def sourceLabelChunk3 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (3 : Fin 6)
  | 1 => (0 : Fin 6)
  | 2 => (3 : Fin 6)
  | 3 => (0 : Fin 6)
  | 4 => (4 : Fin 6)
  | 5 => (1 : Fin 6)
  | 6 => (3 : Fin 6)
  | 7 => (3 : Fin 6)
  | 8 => (0 : Fin 6)
  | 9 => (4 : Fin 6)
  | 10 => (1 : Fin 6)
  | 11 => (4 : Fin 6)
  | 12 => (1 : Fin 6)
  | 13 => (3 : Fin 6)
  | 14 => (0 : Fin 6)
  | 15 => (0 : Fin 6)
  | 16 => (4 : Fin 6)
  | 17 => (1 : Fin 6)
  | 18 => (3 : Fin 6)
  | 19 => (0 : Fin 6)
  | 20 => (3 : Fin 6)
  | 21 => (0 : Fin 6)
  | 22 => (4 : Fin 6)
  | 23 => (1 : Fin 6)
  | 24 => (3 : Fin 6)
  | 25 => (0 : Fin 6)
  | 26 => (3 : Fin 6)
  | 27 => (0 : Fin 6)
  | 28 => (4 : Fin 6)
  | 29 => (1 : Fin 6)
  | 30 => (3 : Fin 6)
  | _ => (3 : Fin 6)

private def sourceLabelChunk4 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (0 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (1 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (0 : Fin 6)
  | 5 => (4 : Fin 6)
  | 6 => (0 : Fin 6)
  | 7 => (4 : Fin 6)
  | 8 => (1 : Fin 6)
  | 9 => (3 : Fin 6)
  | 10 => (0 : Fin 6)
  | 11 => (3 : Fin 6)
  | 12 => (0 : Fin 6)
  | 13 => (4 : Fin 6)
  | 14 => (1 : Fin 6)
  | 15 => (3 : Fin 6)
  | 16 => (0 : Fin 6)
  | 17 => (3 : Fin 6)
  | 18 => (0 : Fin 6)
  | 19 => (4 : Fin 6)
  | 20 => (1 : Fin 6)
  | 21 => (3 : Fin 6)
  | 22 => (3 : Fin 6)
  | 23 => (0 : Fin 6)
  | 24 => (4 : Fin 6)
  | 25 => (1 : Fin 6)
  | 26 => (3 : Fin 6)
  | 27 => (0 : Fin 6)
  | 28 => (4 : Fin 6)
  | 29 => (3 : Fin 6)
  | 30 => (0 : Fin 6)
  | _ => (3 : Fin 6)

private def sourceLabelChunk5 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (0 : Fin 6)
  | 1 => (4 : Fin 6)
  | 2 => (1 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (0 : Fin 6)
  | 5 => (3 : Fin 6)
  | 6 => (0 : Fin 6)
  | 7 => (4 : Fin 6)
  | 8 => (1 : Fin 6)
  | 9 => (3 : Fin 6)
  | 10 => (3 : Fin 6)
  | 11 => (0 : Fin 6)
  | 12 => (4 : Fin 6)
  | 13 => (1 : Fin 6)
  | 14 => (3 : Fin 6)
  | 15 => (0 : Fin 6)
  | 16 => (4 : Fin 6)
  | 17 => (3 : Fin 6)
  | 18 => (0 : Fin 6)
  | 19 => (3 : Fin 6)
  | 20 => (3 : Fin 6)
  | 21 => (0 : Fin 6)
  | 22 => (4 : Fin 6)
  | 23 => (1 : Fin 6)
  | 24 => (3 : Fin 6)
  | 25 => (3 : Fin 6)
  | 26 => (0 : Fin 6)
  | 27 => (4 : Fin 6)
  | 28 => (1 : Fin 6)
  | 29 => (3 : Fin 6)
  | 30 => (0 : Fin 6)
  | _ => (4 : Fin 6)

private def sourceLabelChunk6 (index : Nat) : Fin 6 :=
  match index with
  | 0 => (3 : Fin 6)
  | 1 => (0 : Fin 6)
  | 2 => (3 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (0 : Fin 6)
  | 5 => (4 : Fin 6)
  | 6 => (1 : Fin 6)
  | 7 => (3 : Fin 6)
  | 8 => (0 : Fin 6)
  | 9 => (4 : Fin 6)
  | 10 => (3 : Fin 6)
  | 11 => (0 : Fin 6)
  | 12 => (3 : Fin 6)
  | 13 => (3 : Fin 6)
  | 14 => (0 : Fin 6)
  | 15 => (4 : Fin 6)
  | 16 => (3 : Fin 6)
  | 17 => (0 : Fin 6)
  | 18 => (3 : Fin 6)
  | 19 => (3 : Fin 6)
  | 20 => (0 : Fin 6)
  | 21 => (3 : Fin 6)
  | _ => (3 : Fin 6)

def sourceLabel (state : Fin 215) : Fin 6 :=
  if state.val < 32 then sourceLabelChunk0 state.val else
    if state.val < 64 then sourceLabelChunk1 (state.val - 32) else
      if state.val < 96 then sourceLabelChunk2 (state.val - 64) else
        if state.val < 128 then sourceLabelChunk3 (state.val - 96) else
          if state.val < 160 then sourceLabelChunk4 (state.val - 128) else
            if state.val < 192 then sourceLabelChunk5 (state.val - 160) else
              sourceLabelChunk6 (state.val - 192)

def generatorSourceLabel (generator : Fin 3) : Fin 6 :=
  match generator.val with
  | 0 => (5 : Fin 6)
  | 1 => (3 : Fin 6)
  | _ => (2 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 215 :=
  match value.val with
  | 0 => (8 : Fin 215)
  | 1 => (6 : Fin 215)
  | 2 => (2 : Fin 215)
  | 3 => (1 : Fin 215)
  | 4 => (15 : Fin 215)
  | _ => (0 : Fin 215)

private def stateVectorCode
    (vector : Fin 6 -> Fin 6) : Nat :=
  (vector (0 : Fin 6)).val + 6 * ((vector (1 : Fin 6)).val + 6 * ((vector (2 : Fin 6)).val + 6 * ((vector (3 : Fin 6)).val + 6 * ((vector (4 : Fin 6)).val + 6 * ((vector (5 : Fin 6)).val)))))

private def decodeStateCode (code : Nat) : Fin 215 :=
  if code < 9424 then
    if code < 2830 then
      if code < 1320 then
        if code < 256 then
          if code < 42 then
            if code < 7 then
              if code < 1 then
                if code = 0 then (200 : Fin 215) else (0 : Fin 215)
              else if code = 1 then (168 : Fin 215) else
                if code = 6 then (175 : Fin 215) else (0 : Fin 215)
            else if code = 7 then (125 : Fin 215) else
              if code < 37 then
                if code = 36 then (166 : Fin 215) else (0 : Fin 215)
              else if code = 37 then (113 : Fin 215) else
                (0 : Fin 215)
          else if code = 42 then (123 : Fin 215) else
            if code < 225 then
              if code < 219 then
                if code = 43 then (66 : Fin 215) else (0 : Fin 215)
              else if code = 219 then (208 : Fin 215) else
                if code = 220 then (187 : Fin 215) else (0 : Fin 215)
            else if code = 225 then (192 : Fin 215) else
              if code < 255 then
                if code = 226 then (152 : Fin 215) else (0 : Fin 215)
              else if code = 255 then (185 : Fin 215) else
                (0 : Fin 215)
        else if code = 256 then (141 : Fin 215) else
          if code < 1080 then
            if code < 441 then
              if code < 262 then
                if code = 261 then (150 : Fin 215) else (0 : Fin 215)
              else if code = 262 then (94 : Fin 215) else
                if code = 435 then (143 : Fin 215) else (0 : Fin 215)
            else if code = 441 then (96 : Fin 215) else
              if code < 477 then
                if code = 471 then (85 : Fin 215) else (0 : Fin 215)
              else if code = 477 then (42 : Fin 215) else
                (0 : Fin 215)
          else if code = 1080 then (115 : Fin 215) else
            if code < 1122 then
              if code < 1116 then
                if code = 1086 then (68 : Fin 215) else (0 : Fin 215)
              else if code = 1116 then (59 : Fin 215) else
                (0 : Fin 215)
            else if code = 1122 then (24 : Fin 215) else
              if code < 1315 then
                if code = 1314 then (206 : Fin 215) else (0 : Fin 215)
              else if code = 1315 then (183 : Fin 215) else
                (0 : Fin 215)
      else if code = 1320 then (190 : Fin 215) else
        if code < 1749 then
          if code < 1534 then
            if code < 1356 then
              if code < 1350 then
                if code = 1321 then (148 : Fin 215) else (0 : Fin 215)
              else if code = 1350 then (181 : Fin 215) else
                if code = 1351 then (136 : Fin 215) else (0 : Fin 215)
            else if code = 1356 then (146 : Fin 215) else
              if code < 1533 then
                if code = 1357 then (89 : Fin 215) else (0 : Fin 215)
              else if code = 1533 then (211 : Fin 215) else
                (0 : Fin 215)
          else if code = 1534 then (197 : Fin 215) else
            if code < 1570 then
              if code < 1540 then
                if code = 1539 then (202 : Fin 215) else (0 : Fin 215)
              else if code = 1540 then (172 : Fin 215) else
                if code = 1569 then (195 : Fin 215) else (0 : Fin 215)
            else if code = 1570 then (161 : Fin 215) else
              if code < 1576 then
                if code = 1575 then (170 : Fin 215) else (0 : Fin 215)
              else if code = 1576 then (118 : Fin 215) else
                (0 : Fin 215)
        else if code = 1749 then (163 : Fin 215) else
          if code < 2436 then
            if code < 2394 then
              if code < 1785 then
                if code = 1755 then (120 : Fin 215) else (0 : Fin 215)
              else if code = 1785 then (109 : Fin 215) else
                if code = 1791 then (62 : Fin 215) else (0 : Fin 215)
            else if code = 2394 then (138 : Fin 215) else
              if code < 2430 then
                if code = 2400 then (91 : Fin 215) else (0 : Fin 215)
              else if code = 2430 then (82 : Fin 215) else
                (0 : Fin 215)
          else if code = 2436 then (39 : Fin 215) else
            if code < 2646 then
              if code < 2611 then
                if code = 2610 then (155 : Fin 215) else (0 : Fin 215)
              else if code = 2611 then (101 : Fin 215) else
                (0 : Fin 215)
            else if code = 2646 then (99 : Fin 215) else
              if code < 2829 then
                if code = 2647 then (46 : Fin 215) else (0 : Fin 215)
              else if code = 2829 then (177 : Fin 215) else
                (0 : Fin 215)
    else if code = 2830 then (129 : Fin 215) else
      if code < 8103 then
        if code < 6736 then
          if code < 6480 then
            if code < 3081 then
              if code < 2866 then
                if code = 2865 then (127 : Fin 215) else (0 : Fin 215)
              else if code = 2866 then (71 : Fin 215) else
                if code = 3045 then (73 : Fin 215) else (0 : Fin 215)
            else if code = 3081 then (27 : Fin 215) else
              if code < 3726 then
                if code = 3690 then (48 : Fin 215) else (0 : Fin 215)
              else if code = 3726 then (14 : Fin 215) else
                (0 : Fin 215)
          else if code = 6480 then (132 : Fin 215) else
            if code < 6699 then
              if code < 6516 then
                if code = 6481 then (78 : Fin 215) else (0 : Fin 215)
              else if code = 6516 then (76 : Fin 215) else
                if code = 6517 then (31 : Fin 215) else (0 : Fin 215)
            else if code = 6699 then (157 : Fin 215) else
              if code < 6735 then
                if code = 6700 then (105 : Fin 215) else (0 : Fin 215)
              else if code = 6735 then (103 : Fin 215) else
                (0 : Fin 215)
        else if code = 6736 then (51 : Fin 215) else
          if code < 7890 then
            if code < 7596 then
              if code < 6951 then
                if code = 6915 then (53 : Fin 215) else (0 : Fin 215)
              else if code = 6951 then (17 : Fin 215) else
                if code = 7560 then (33 : Fin 215) else (0 : Fin 215)
            else if code = 7596 then (8 : Fin 215) else
              if code < 7885 then
                if code = 7884 then (153 : Fin 215) else (0 : Fin 215)
              else if code = 7885 then (193 : Fin 215) else
                (0 : Fin 215)
          else if code = 7890 then (188 : Fin 215) else
            if code < 7921 then
              if code < 7920 then
                if code = 7891 then (209 : Fin 215) else (0 : Fin 215)
              else if code = 7920 then (95 : Fin 215) else
                (0 : Fin 215)
            else if code = 7921 then (151 : Fin 215) else
              if code < 7927 then
                if code = 7926 then (142 : Fin 215) else (0 : Fin 215)
              else if code = 7927 then (186 : Fin 215) else
                (0 : Fin 215)
      else if code = 8103 then (176 : Fin 215) else
        if code < 9001 then
          if code < 8146 then
            if code < 8139 then
              if code < 8109 then
                if code = 8104 then (204 : Fin 215) else (0 : Fin 215)
              else if code = 8109 then (201 : Fin 215) else
                if code = 8110 then (213 : Fin 215) else (0 : Fin 215)
            else if code = 8139 then (124 : Fin 215) else
              if code < 8145 then
                if code = 8140 then (174 : Fin 215) else (0 : Fin 215)
              else if code = 8145 then (167 : Fin 215) else
                (0 : Fin 215)
          else if code = 8146 then (199 : Fin 215) else
            if code < 8362 then
              if code < 8326 then
                if code = 8320 then (126 : Fin 215) else (0 : Fin 215)
              else if code = 8326 then (169 : Fin 215) else
                if code = 8356 then (67 : Fin 215) else (0 : Fin 215)
            else if code = 8362 then (114 : Fin 215) else
              if code < 8971 then
                if code = 8965 then (97 : Fin 215) else (0 : Fin 215)
              else if code = 8971 then (144 : Fin 215) else
                (0 : Fin 215)
        else if code = 9001 then (43 : Fin 215) else
          if code < 9235 then
            if code < 9204 then
              if code < 9198 then
                if code = 9007 then (86 : Fin 215) else (0 : Fin 215)
              else if code = 9198 then (173 : Fin 215) else
                if code = 9199 then (203 : Fin 215) else (0 : Fin 215)
            else if code = 9204 then (198 : Fin 215) else
              if code < 9234 then
                if code = 9205 then (212 : Fin 215) else (0 : Fin 215)
              else if code = 9234 then (119 : Fin 215) else
                (0 : Fin 215)
          else if code = 9235 then (171 : Fin 215) else
            if code < 9417 then
              if code < 9241 then
                if code = 9240 then (162 : Fin 215) else (0 : Fin 215)
              else if code = 9241 then (196 : Fin 215) else
                (0 : Fin 215)
            else if code = 9417 then (191 : Fin 215) else
              if code < 9423 then
                if code = 9418 then (210 : Fin 215) else (0 : Fin 215)
              else if code = 9423 then (207 : Fin 215) else
                (0 : Fin 215)
  else if code = 9424 then (214 : Fin 215) else
    if code < 17194 then
      if code < 14406 then
        if code < 10501 then
          if code < 9670 then
            if code < 9460 then
              if code < 9454 then
                if code = 9453 then (147 : Fin 215) else (0 : Fin 215)
              else if code = 9454 then (189 : Fin 215) else
                if code = 9459 then (182 : Fin 215) else (0 : Fin 215)
            else if code = 9460 then (205 : Fin 215) else
              if code < 9640 then
                if code = 9634 then (149 : Fin 215) else (0 : Fin 215)
              else if code = 9640 then (184 : Fin 215) else
                (0 : Fin 215)
          else if code = 9670 then (90 : Fin 215) else
            if code < 10315 then
              if code < 10279 then
                if code = 9676 then (137 : Fin 215) else (0 : Fin 215)
              else if code = 10279 then (121 : Fin 215) else
                if code = 10285 then (164 : Fin 215) else (0 : Fin 215)
            else if code = 10315 then (63 : Fin 215) else
              if code < 10500 then
                if code = 10321 then (110 : Fin 215) else (0 : Fin 215)
              else if code = 10500 then (130 : Fin 215) else
                (0 : Fin 215)
        else if code = 10501 then (178 : Fin 215) else
          if code < 10936 then
            if code < 10720 then
              if code < 10537 then
                if code = 10536 then (72 : Fin 215) else (0 : Fin 215)
              else if code = 10537 then (128 : Fin 215) else
                if code = 10719 then (156 : Fin 215) else (0 : Fin 215)
            else if code = 10720 then (194 : Fin 215) else
              if code < 10756 then
                if code = 10755 then (100 : Fin 215) else (0 : Fin 215)
              else if code = 10756 then (154 : Fin 215) else
                (0 : Fin 215)
          else if code = 10936 then (102 : Fin 215) else
            if code < 11617 then
              if code < 11581 then
                if code = 10972 then (47 : Fin 215) else (0 : Fin 215)
              else if code = 11581 then (74 : Fin 215) else
                (0 : Fin 215)
            else if code = 11617 then (28 : Fin 215) else
              if code < 14371 then
                if code = 14370 then (106 : Fin 215) else (0 : Fin 215)
              else if code = 14371 then (158 : Fin 215) else
                (0 : Fin 215)
      else if code = 14406 then (52 : Fin 215) else
        if code < 15879 then
          if code < 14842 then
            if code < 14625 then
              if code < 14589 then
                if code = 14407 then (104 : Fin 215) else (0 : Fin 215)
              else if code = 14589 then (133 : Fin 215) else
                if code = 14590 then (179 : Fin 215) else (0 : Fin 215)
            else if code = 14625 then (77 : Fin 215) else
              if code < 14806 then
                if code = 14626 then (131 : Fin 215) else (0 : Fin 215)
              else if code = 14806 then (79 : Fin 215) else
                (0 : Fin 215)
          else if code = 14842 then (32 : Fin 215) else
            if code < 15661 then
              if code < 15487 then
                if code = 15451 then (54 : Fin 215) else (0 : Fin 215)
              else if code = 15487 then (18 : Fin 215) else
                if code = 15660 then (41 : Fin 215) else (0 : Fin 215)
            else if code = 15661 then (93 : Fin 215) else
              if code < 15667 then
                if code = 15666 then (84 : Fin 215) else (0 : Fin 215)
              else if code = 15667 then (140 : Fin 215) else
                (0 : Fin 215)
        else if code = 15879 then (65 : Fin 215) else
          if code < 16748 then
            if code < 16096 then
              if code < 15885 then
                if code = 15880 then (122 : Fin 215) else (0 : Fin 215)
              else if code = 15885 then (112 : Fin 215) else
                if code = 15886 then (165 : Fin 215) else (0 : Fin 215)
            else if code = 16096 then (23 : Fin 215) else
              if code < 16742 then
                if code = 16102 then (58 : Fin 215) else (0 : Fin 215)
              else if code = 16742 then (11 : Fin 215) else
                (0 : Fin 215)
          else if code = 16748 then (36 : Fin 215) else
            if code < 16980 then
              if code < 16975 then
                if code = 16974 then (61 : Fin 215) else (0 : Fin 215)
              else if code = 16975 then (117 : Fin 215) else
                (0 : Fin 215)
            else if code = 16980 then (108 : Fin 215) else
              if code < 17193 then
                if code = 16981 then (160 : Fin 215) else (0 : Fin 215)
              else if code = 17193 then (88 : Fin 215) else
                (0 : Fin 215)
    else if code = 17194 then (145 : Fin 215) else
      if code < 39495 then
        if code < 22153 then
          if code < 18276 then
            if code < 17416 then
              if code < 17200 then
                if code = 17199 then (135 : Fin 215) else (0 : Fin 215)
              else if code = 17200 then (180 : Fin 215) else
                if code = 17410 then (38 : Fin 215) else (0 : Fin 215)
            else if code = 17416 then (81 : Fin 215) else
              if code < 18062 then
                if code = 18056 then (21 : Fin 215) else (0 : Fin 215)
              else if code = 18062 then (56 : Fin 215) else
                (0 : Fin 215)
          else if code = 18276 then (26 : Fin 215) else
            if code < 18712 then
              if code < 18495 then
                if code = 18277 then (70 : Fin 215) else (0 : Fin 215)
              else if code = 18495 then (45 : Fin 215) else
                if code = 18496 then (98 : Fin 215) else (0 : Fin 215)
            else if code = 18712 then (13 : Fin 215) else
              if code < 22152 then
                if code = 19358 then (5 : Fin 215) else (0 : Fin 215)
              else if code = 22152 then (16 : Fin 215) else
                (0 : Fin 215)
        else if code = 22153 then (50 : Fin 215) else
          if code < 39066 then
            if code < 23234 then
              if code < 22372 then
                if code = 22371 then (30 : Fin 215) else (0 : Fin 215)
              else if code = 22372 then (75 : Fin 215) else
                if code = 22588 then (7 : Fin 215) else (0 : Fin 215)
            else if code = 23234 then (2 : Fin 215) else
              if code < 39061 then
                if code = 39060 then (111 : Fin 215) else (0 : Fin 215)
              else if code = 39061 then (57 : Fin 215) else
                (0 : Fin 215)
          else if code = 39066 then (64 : Fin 215) else
            if code < 39280 then
              if code < 39279 then
                if code = 39067 then (22 : Fin 215) else (0 : Fin 215)
              else if code = 39279 then (139 : Fin 215) else
                (0 : Fin 215)
            else if code = 39280 then (83 : Fin 215) else
              if code < 39286 then
                if code = 39285 then (92 : Fin 215) else (0 : Fin 215)
              else if code = 39286 then (40 : Fin 215) else
                (0 : Fin 215)
      else if code = 39495 then (35 : Fin 215) else
        if code < 41459 then
          if code < 40381 then
            if code < 40374 then
              if code < 40145 then
                if code = 39501 then (10 : Fin 215) else (0 : Fin 215)
              else if code = 40145 then (19 : Fin 215) else
                if code = 40151 then (3 : Fin 215) else (0 : Fin 215)
            else if code = 40374 then (134 : Fin 215) else
              if code < 40380 then
                if code = 40375 then (80 : Fin 215) else (0 : Fin 215)
              else if code = 40380 then (87 : Fin 215) else
                (0 : Fin 215)
          else if code = 40381 then (37 : Fin 215) else
            if code < 40600 then
              if code < 40594 then
                if code = 40593 then (159 : Fin 215) else (0 : Fin 215)
              else if code = 40594 then (107 : Fin 215) else
                if code = 40599 then (116 : Fin 215) else (0 : Fin 215)
            else if code = 40600 then (60 : Fin 215) else
              if code < 40815 then
                if code = 40809 then (55 : Fin 215) else (0 : Fin 215)
              else if code = 40815 then (20 : Fin 215) else
                (0 : Fin 215)
        else if code = 41459 then (34 : Fin 215) else
          if code < 42755 then
            if code < 41889 then
              if code < 41670 then
                if code = 41465 then (9 : Fin 215) else (0 : Fin 215)
              else if code = 41670 then (44 : Fin 215) else
                if code = 41671 then (12 : Fin 215) else (0 : Fin 215)
            else if code = 41889 then (69 : Fin 215) else
              if code < 42105 then
                if code = 41890 then (25 : Fin 215) else (0 : Fin 215)
              else if code = 42105 then (4 : Fin 215) else
                (0 : Fin 215)
          else if code = 42755 then (0 : Fin 215) else
            if code < 45789 then
              if code < 45571 then
                if code = 45570 then (29 : Fin 215) else (0 : Fin 215)
              else if code = 45571 then (6 : Fin 215) else
                (0 : Fin 215)
            else if code = 45789 then (49 : Fin 215) else
              if code < 46005 then
                if code = 45790 then (15 : Fin 215) else (0 : Fin 215)
              else if code = 46005 then (1 : Fin 215) else
                (0 : Fin 215)

private def decodeState
    (vector : Fin 6 -> Fin 6) : Fin 215 :=
  decodeStateCode (stateVectorCode vector)

set_option maxHeartbeats 2000000 in
private theorem decodeState_stateVector (state : Fin 215) :
    decodeState (stateVector state) = state := by
  decide +revert

set_option maxHeartbeats 2000000 in
private theorem transitionMap :
    forall (state : Fin 215)
      (generator : Fin 3)
      (coordinate : Fin 6),
      stateVector (transition state generator) coordinate =
        oppositeTable.semigroup.mul (stateVector state coordinate)
          (generatorVector generator coordinate) := by
  intro state generator coordinate
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem representativeMap :
    forall (state : Fin 215)
      (coordinate : Fin 6),
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
    (U := Fin 215)
    (G := Fin 3)
    (I := Fin 6) oppositeTable.semigroup where
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
    forall (state : Fin 215)
      (generator : Fin 3),
      sourceLabel (transition state generator) =
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul (sourceLabel state)
          (generatorSourceLabel generator) := by
  intro state generator
  apply Fin.ext
  exact by decide +revert

set_option maxHeartbeats 2000000 in
private theorem sourceLabelRepresentative :
    forall state : Fin 215,
      sourceLabel state =
        (representativeTail state).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (generatorSourceLabel (representativeHead state)) := by
  intro state
  apply Fin.ext
  exact by decide +revert

private theorem sourceLabelRightMultiplyWord
    (state : Fin 215)
    (word : List (Fin 3)) :
    sourceLabel (powerCertificate.rightMultiplyWord state word) =
      word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul value
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
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul value
                (generatorSourceLabel nextGenerator))
            (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul (sourceLabel state)
              (generatorSourceLabel generator))
      rw [inductionHypothesis]
      rw [sourceLabelTransition]

private theorem sourceFoldlGeneratorAssoc
    (left right : Fin 6)
    (word : List (Fin 3)) :
    word.foldl
        (fun value generator =>
          SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul value
            (generatorSourceLabel generator))
        (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul left right) =
      SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul left
        (word.foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          right) := by
  induction word generalizing right with
  | nil => rfl
  | cons generator word inductionHypothesis =>
      simp only [List.foldl_cons]
      rw [SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.assoc]
      exact inductionHypothesis
        (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul right (generatorSourceLabel generator))

private theorem sourceLabelMapMul :
    forall (left right : Fin 215),
      sourceLabel (powerCertificate.semigroup.mul left right) =
        SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul (sourceLabel left) (sourceLabel right) := by
  intro left right
  calc
    sourceLabel (powerCertificate.semigroup.mul left right) =
        sourceLabel
          (powerCertificate.rightMultiplyWord
            (transition left (representativeHead right))
            (representativeTail right)) := rfl
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (sourceLabel (transition left (representativeHead right))) :=
      sourceLabelRightMultiplyWord _ _
    _ = (representativeTail right).foldl
          (fun value generator =>
            SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul value
              (generatorSourceLabel generator))
          (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul (sourceLabel left)
            (generatorSourceLabel (representativeHead right))) :=
      congrArg
        (fun initial =>
          (representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul value
                (generatorSourceLabel generator))
            initial)
        (sourceLabelTransition left (representativeHead right))
    _ = SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul (sourceLabel left)
          ((representativeTail right).foldl
            (fun value generator =>
              SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul value
                (generatorSourceLabel generator))
            (generatorSourceLabel (representativeHead right))) :=
      sourceFoldlGeneratorAssoc _ _ _
    _ = SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul (sourceLabel left) (sourceLabel right) :=
      congrArg (SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup.mul (sourceLabel left))
        (sourceLabelRepresentative right).symm

set_option maxHeartbeats 1000000 in
private theorem sourceLabelRightInverse :
    forall value : Fin 6, sourceLabel (sourcePreimage value) = value := by
  intro value
  apply Fin.ext
  exact by decide +revert

/-- The generated term-function semigroup maps onto the selected root. -/
def quotient : SplitSurjection powerCertificate.semigroup
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup where
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.law0.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.law0
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
    SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.law1.SatisfiedBy oppositeTable.semigroup :=
  FiniteNilpotentCounterexample.identitySatisfiedByNat_of_fused_check
    oppositeTable SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.law1
    targetLaw1ToFinite targetLaw1FromFinite (by decide) (by decide)

/-- Exact finite checks that the selected target models the root basis. -/
theorem targetModels :
    Models oppositeTable.semigroup SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.basis := by
  unfold SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.basis
  exact
    FiniteNilpotentCounterexample.models_cons targetLaw0Valid <|
      FiniteNilpotentCounterexample.models_cons targetLaw1Valid <|
        FiniteNilpotentCounterexample.models_nil oppositeTable.semigroup

/-- Exact identity-theory transfer authenticated by the finite certificate. -/
theorem sameIdentityTheory :
    SameIdentityTheoryOver SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.oppositeTable.semigroup
      oppositeTable.semigroup Nat := by
  intro identity
  constructor
  · intro sourceValid valuation
    exact Derives.sound targetModels
      (SemigroupBasis.CoRoots.Order6GenericCASMonoidPower.S6_5326_oppositeBasisFor.2 identity sourceValid) valuation
  · intro targetValid
    have powerValid :=
      identity.satisfiedByPi oppositeTable.semigroup
        (Fin 6) targetValid
    have subValid :=
      powerCertificate.embedding.pullback_identity identity powerValid
    exact quotient.pushforwardIdentity identity subValid

/-- First-layer generic-CAS basis wrapper for `S6_5330`. -/
theorem opposite_basis :
    BasisFor table.semigroup.opposite SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.basis := by
  have transferred :
      BasisFor oppositeTable.semigroup SemigroupBasis.Generated.Order6GenericCASRootData.S6_5326.basis :=
    (basisFor_iff_of_sameIdentityTheoryOver sameIdentityTheory).mp
      SemigroupBasis.CoRoots.Order6GenericCASMonoidPower.S6_5326_oppositeBasisFor
  simpa only [oppositeTable_semigroup] using transferred

end SemigroupBasis.Generated.Order6GenericCASRootWrappers.S6_5330
