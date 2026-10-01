import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7637Opposite
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.Shards.SourceLabel
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.Shards.StateVector
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057.Shards.Transition
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057

open SemigroupBasis

def routeManifestRowSHA256 : String := "3cfc46829452ff8f54c3648d99d66c6bdc05554b175951149fa1bd2db95a27fa"
def witnessRecordSHA256 : String := "ee3f57391996d0ee831c329dd9a8535ca2d48a81283aa3cd90e7e87ccdf6141e"
def transferComponentSHA256 : String := "ee3f57391996d0ee831c329dd9a8535ca2d48a81283aa3cd90e7e87ccdf6141e"
def powerCertificateSHA256 : String := "f5416b328b954aebfdf24c316da78cd6628e1d62e1e881b8a2ce4a19238f84c5"

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
      if left = 2 then row6 0 0 2 3 4 5 right else
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
  "0f2e07caca68574b09c7f4d303e0b82bd6acba0aef3f2ff156e7195bb95aaf67"

def stateVector (state : Fin 17622)
    (coordinate : Fin 39) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 6)
    (coordinate : Fin 39) : Fin 6 :=
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
      | 10 => (0 : Fin 6)
      | 11 => (4 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (4 : Fin 6)
      | 20 => (2 : Fin 6)
      | 21 => (4 : Fin 6)
      | 22 => (2 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (2 : Fin 6)
      | 25 => (4 : Fin 6)
      | 26 => (2 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (2 : Fin 6)
      | 29 => (2 : Fin 6)
      | 30 => (2 : Fin 6)
      | 31 => (1 : Fin 6)
      | 32 => (2 : Fin 6)
      | 33 => (2 : Fin 6)
      | 34 => (4 : Fin 6)
      | 35 => (0 : Fin 6)
      | 36 => (2 : Fin 6)
      | 37 => (2 : Fin 6)
      | _ => (2 : Fin 6)
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
      | 10 => (2 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (1 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (2 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (2 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (2 : Fin 6)
      | 26 => (4 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (2 : Fin 6)
      | 29 => (2 : Fin 6)
      | 30 => (2 : Fin 6)
      | 31 => (2 : Fin 6)
      | 32 => (2 : Fin 6)
      | 33 => (4 : Fin 6)
      | 34 => (2 : Fin 6)
      | 35 => (0 : Fin 6)
      | 36 => (2 : Fin 6)
      | 37 => (2 : Fin 6)
      | _ => (4 : Fin 6)
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
      | 9 => (4 : Fin 6)
      | 10 => (2 : Fin 6)
      | 11 => (2 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (1 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (2 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (2 : Fin 6)
      | 23 => (3 : Fin 6)
      | 24 => (2 : Fin 6)
      | 25 => (2 : Fin 6)
      | 26 => (2 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (4 : Fin 6)
      | 29 => (4 : Fin 6)
      | 30 => (2 : Fin 6)
      | 31 => (2 : Fin 6)
      | 32 => (2 : Fin 6)
      | 33 => (0 : Fin 6)
      | 34 => (2 : Fin 6)
      | 35 => (0 : Fin 6)
      | 36 => (2 : Fin 6)
      | 37 => (4 : Fin 6)
      | _ => (2 : Fin 6)
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
      | 10 => (2 : Fin 6)
      | 11 => (2 : Fin 6)
      | 12 => (1 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (4 : Fin 6)
      | 21 => (2 : Fin 6)
      | 22 => (2 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (4 : Fin 6)
      | 25 => (2 : Fin 6)
      | 26 => (2 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (2 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (4 : Fin 6)
      | 31 => (2 : Fin 6)
      | 32 => (2 : Fin 6)
      | 33 => (2 : Fin 6)
      | 34 => (2 : Fin 6)
      | 35 => (0 : Fin 6)
      | 36 => (4 : Fin 6)
      | 37 => (2 : Fin 6)
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
      | 9 => (2 : Fin 6)
      | 10 => (4 : Fin 6)
      | 11 => (2 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (1 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (2 : Fin 6)
      | 20 => (2 : Fin 6)
      | 21 => (2 : Fin 6)
      | 22 => (2 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (2 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (0 : Fin 6)
      | 29 => (2 : Fin 6)
      | 30 => (2 : Fin 6)
      | 31 => (2 : Fin 6)
      | 32 => (4 : Fin 6)
      | 33 => (2 : Fin 6)
      | 34 => (0 : Fin 6)
      | 35 => (3 : Fin 6)
      | 36 => (0 : Fin 6)
      | 37 => (2 : Fin 6)
      | _ => (2 : Fin 6)
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
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (2 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (1 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (2 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (2 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (2 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (2 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (2 : Fin 6)
      | 29 => (2 : Fin 6)
      | 30 => (0 : Fin 6)
      | 31 => (2 : Fin 6)
      | 32 => (0 : Fin 6)
      | 33 => (2 : Fin 6)
      | 34 => (2 : Fin 6)
      | 35 => (0 : Fin 6)
      | 36 => (2 : Fin 6)
      | 37 => (0 : Fin 6)
      | _ => (2 : Fin 6)

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
    (Fin 39 -> Fin 6) -> Fin 17622 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 17622) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 6) :
    Fin 17622 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14057
