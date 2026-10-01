import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7183Representative
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.Shards.SourceLabel
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.Shards.StateVector
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056.Shards.Transition
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056

open SemigroupBasis

def routeManifestRowSHA256 : String := "4f9a5d4bfcff501d91491d392c85ea794e979dc8eb1fa3bab50a861a095d66ae"
def witnessRecordSHA256 : String := "ce994ee0629d7996e7339952f917d293519c8fec090cc6f01f8ef016314d5316"
def transferComponentSHA256 : String := "ce994ee0629d7996e7339952f917d293519c8fec090cc6f01f8ef016314d5316"
def powerCertificateSHA256 : String := "cbe37a121775af446269ab061d3945f6db8782d180acbbfa9cbf76766328cfe5"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 0 3 0 3 right else
    if left = 1 then row6 0 0 1 3 0 3 right else
      if left = 2 then row6 0 0 2 3 0 3 right else
        if left = 3 then row6 0 0 0 3 0 3 right else
          if left = 4 then row6 4 4 4 5 4 5 right else
            row6 4 4 4 5 4 5 right

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
  "078a947eb0b23c83a4c8c79e1a38b814239bae2e73e15e798b742a2d94e732c4"

def stateVector (state : Fin 1158)
    (coordinate : Fin 32) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 6)
    (coordinate : Fin 32) : Fin 6 :=
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
      | 11 => (0 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (2 : Fin 6)
      | 19 => (2 : Fin 6)
      | 20 => (2 : Fin 6)
      | 21 => (1 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (4 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (0 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (0 : Fin 6)
      | _ => (0 : Fin 6)
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
      | 11 => (2 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (2 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (2 : Fin 6)
      | 19 => (2 : Fin 6)
      | 20 => (1 : Fin 6)
      | 21 => (2 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (3 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (4 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (0 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (0 : Fin 6)
      | _ => (0 : Fin 6)
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
      | 11 => (2 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (2 : Fin 6)
      | 19 => (1 : Fin 6)
      | 20 => (2 : Fin 6)
      | 21 => (2 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (4 : Fin 6)
      | 28 => (0 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (0 : Fin 6)
      | _ => (0 : Fin 6)
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
      | 12 => (2 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (1 : Fin 6)
      | 18 => (2 : Fin 6)
      | 19 => (2 : Fin 6)
      | 20 => (2 : Fin 6)
      | 21 => (2 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (4 : Fin 6)
      | 30 => (0 : Fin 6)
      | _ => (0 : Fin 6)
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
      | 13 => (2 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (1 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (2 : Fin 6)
      | 19 => (2 : Fin 6)
      | 20 => (2 : Fin 6)
      | 21 => (2 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (0 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (3 : Fin 6)
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
      | 7 => (2 : Fin 6)
      | 8 => (2 : Fin 6)
      | 9 => (2 : Fin 6)
      | 10 => (2 : Fin 6)
      | 11 => (2 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (2 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (1 : Fin 6)
      | 19 => (2 : Fin 6)
      | 20 => (2 : Fin 6)
      | 21 => (2 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (0 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (0 : Fin 6)
      | _ => (0 : Fin 6)

def transition (state : Fin 1158)
    (generator : Fin 6) : Fin 1158 :=
  Shards.transition state generator

def representativeHead (state : Fin 1158) : Fin 6 :=
  Shards.representativeHead state

def representativeTail (state : Fin 1158) :
    List (Fin 6) :=
  Shards.representativeTail state

def sourceLabel (state : Fin 1158) : Fin 6 :=
  Shards.sourceLabel state

def generatorSourceLabel (generator : Fin 6) : Fin 6 :=
  match generator.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (4 : Fin 6)
  | _ => (5 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 1158 :=
  match value.val with
  | 0 => (0 : Fin 1158)
  | 1 => (1 : Fin 1158)
  | 2 => (2 : Fin 1158)
  | 3 => (3 : Fin 1158)
  | 4 => (4 : Fin 1158)
  | _ => (5 : Fin 1158)

abbrev decodeState :
    (Fin 32 -> Fin 6) -> Fin 1158 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 1158) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 6) :
    Fin 1158 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14056
