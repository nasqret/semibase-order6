import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards.SourceLabel
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards.StateVector
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182.Shards.Transition
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182

open SemigroupBasis

def routeManifestRowSHA256 : String := "95105f347c14cd534941a11fb398e5d3061c2a55c8b8e5d341880a1329ca3911"
def witnessRecordSHA256 : String := "e6c343df0b4bc1f4374edf83d69aa3aa60d397eef27eb4f4c319e74a5433c114"
def transferComponentSHA256 : String := "e6c343df0b4bc1f4374edf83d69aa3aa60d397eef27eb4f4c319e74a5433c114"
def powerCertificateSHA256 : String := "b670a7484b386b385e0e1508310850fba615f38a4041688ea3b6fb530e5475ff"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 3 0 0 right else
    if left = 1 then row6 0 0 0 3 1 0 right else
      if left = 2 then row6 0 0 2 3 2 2 right else
        if left = 3 then row6 0 0 0 3 0 0 right else
          if left = 4 then row6 0 0 2 3 4 5 right else
            row6 0 0 5 3 5 5 right

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
  "3bef1a887746fc90533612dc3bde866a15edb73d75f57f709963b305b4cc5859"

def stateVector (state : Fin 17622)
    (coordinate : Fin 46) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 6)
    (coordinate : Fin 46) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (1 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (2 : Fin 6)
      | 8 => (2 : Fin 6)
      | 9 => (2 : Fin 6)
      | 10 => (2 : Fin 6)
      | 11 => (2 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (4 : Fin 6)
      | 18 => (4 : Fin 6)
      | 19 => (4 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (4 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (4 : Fin 6)
      | 24 => (4 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (4 : Fin 6)
      | 27 => (1 : Fin 6)
      | 28 => (4 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (4 : Fin 6)
      | 31 => (4 : Fin 6)
      | 32 => (0 : Fin 6)
      | 33 => (4 : Fin 6)
      | 34 => (4 : Fin 6)
      | 35 => (5 : Fin 6)
      | 36 => (5 : Fin 6)
      | 37 => (5 : Fin 6)
      | 38 => (4 : Fin 6)
      | 39 => (4 : Fin 6)
      | 40 => (4 : Fin 6)
      | 41 => (5 : Fin 6)
      | 42 => (0 : Fin 6)
      | 43 => (4 : Fin 6)
      | 44 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (2 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (2 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (4 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (2 : Fin 6)
      | 19 => (4 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (4 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (4 : Fin 6)
      | 24 => (4 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (2 : Fin 6)
      | 27 => (4 : Fin 6)
      | 28 => (5 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (4 : Fin 6)
      | 31 => (4 : Fin 6)
      | 32 => (0 : Fin 6)
      | 33 => (4 : Fin 6)
      | 34 => (1 : Fin 6)
      | 35 => (2 : Fin 6)
      | 36 => (4 : Fin 6)
      | 37 => (4 : Fin 6)
      | 38 => (5 : Fin 6)
      | 39 => (5 : Fin 6)
      | 40 => (4 : Fin 6)
      | 41 => (4 : Fin 6)
      | 42 => (0 : Fin 6)
      | 43 => (4 : Fin 6)
      | 44 => (4 : Fin 6)
      | _ => (2 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (1 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (2 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (4 : Fin 6)
      | 17 => (4 : Fin 6)
      | 18 => (5 : Fin 6)
      | 19 => (4 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (4 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (1 : Fin 6)
      | 24 => (4 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (4 : Fin 6)
      | 27 => (4 : Fin 6)
      | 28 => (4 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (5 : Fin 6)
      | 31 => (4 : Fin 6)
      | 32 => (0 : Fin 6)
      | 33 => (5 : Fin 6)
      | 34 => (4 : Fin 6)
      | 35 => (2 : Fin 6)
      | 36 => (4 : Fin 6)
      | 37 => (4 : Fin 6)
      | 38 => (2 : Fin 6)
      | 39 => (4 : Fin 6)
      | 40 => (4 : Fin 6)
      | 41 => (4 : Fin 6)
      | 42 => (0 : Fin 6)
      | 43 => (5 : Fin 6)
      | 44 => (2 : Fin 6)
      | _ => (4 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (1 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (2 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (2 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (4 : Fin 6)
      | 17 => (4 : Fin 6)
      | 18 => (2 : Fin 6)
      | 19 => (5 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (4 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (4 : Fin 6)
      | 24 => (1 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (5 : Fin 6)
      | 27 => (4 : Fin 6)
      | 28 => (4 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (4 : Fin 6)
      | 31 => (4 : Fin 6)
      | 32 => (3 : Fin 6)
      | 33 => (4 : Fin 6)
      | 34 => (4 : Fin 6)
      | 35 => (4 : Fin 6)
      | 36 => (2 : Fin 6)
      | 37 => (4 : Fin 6)
      | 38 => (4 : Fin 6)
      | 39 => (2 : Fin 6)
      | 40 => (5 : Fin 6)
      | 41 => (4 : Fin 6)
      | 42 => (0 : Fin 6)
      | 43 => (2 : Fin 6)
      | 44 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (1 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (2 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (4 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (4 : Fin 6)
      | 19 => (4 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (4 : Fin 6)
      | 22 => (1 : Fin 6)
      | 23 => (4 : Fin 6)
      | 24 => (4 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (2 : Fin 6)
      | 27 => (4 : Fin 6)
      | 28 => (4 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (2 : Fin 6)
      | 31 => (5 : Fin 6)
      | 32 => (0 : Fin 6)
      | 33 => (4 : Fin 6)
      | 34 => (4 : Fin 6)
      | 35 => (4 : Fin 6)
      | 36 => (4 : Fin 6)
      | 37 => (2 : Fin 6)
      | 38 => (4 : Fin 6)
      | 39 => (4 : Fin 6)
      | 40 => (2 : Fin 6)
      | 41 => (4 : Fin 6)
      | 42 => (3 : Fin 6)
      | 43 => (4 : Fin 6)
      | 44 => (4 : Fin 6)
      | _ => (4 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (1 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (2 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (4 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (4 : Fin 6)
      | 18 => (4 : Fin 6)
      | 19 => (2 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (1 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (4 : Fin 6)
      | 24 => (4 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (4 : Fin 6)
      | 27 => (4 : Fin 6)
      | 28 => (2 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (4 : Fin 6)
      | 31 => (2 : Fin 6)
      | 32 => (0 : Fin 6)
      | 33 => (2 : Fin 6)
      | 34 => (4 : Fin 6)
      | 35 => (4 : Fin 6)
      | 36 => (4 : Fin 6)
      | 37 => (4 : Fin 6)
      | 38 => (4 : Fin 6)
      | 39 => (4 : Fin 6)
      | 40 => (4 : Fin 6)
      | 41 => (2 : Fin 6)
      | 42 => (0 : Fin 6)
      | 43 => (4 : Fin 6)
      | 44 => (4 : Fin 6)
      | _ => (4 : Fin 6)

def transition (state : Fin 17622)
    (generator : Fin 6) : Fin 17622 :=
  Shards.transition state generator

def representativeHead (state : Fin 17622) : Fin 6 :=
  Shards.representativeHead state

def representativeTail (state : Fin 17622) :
    List (Fin 6) :=
  Shards.representativeTail state

def sourceLabel (state : Fin 17622) : Fin 6 :=
  Shards.sourceLabel state

def generatorSourceLabel (generator : Fin 6) : Fin 6 :=
  match generator.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (4 : Fin 6)
  | _ => (5 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 17622 :=
  match value.val with
  | 0 => (0 : Fin 17622)
  | 1 => (1 : Fin 17622)
  | 2 => (2 : Fin 17622)
  | 3 => (3 : Fin 17622)
  | 4 => (4 : Fin 17622)
  | _ => (5 : Fin 17622)

abbrev decodeState :
    (Fin 46 -> Fin 6) -> Fin 17622 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 17622) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 6) :
    Fin 17622 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_12182
