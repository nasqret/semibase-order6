import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4022Representative
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.SourceLabel
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.StateVector
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979.Shards.Transition
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979

open SemigroupBasis

def routeManifestRowSHA256 : String := "531246bef752888c3593ed8c91265a398b909561cf70ef5791473cc91a08bb1d"
def witnessRecordSHA256 : String := "d1763f4a75ca47435692ec308e21d4f64f7e0c7b2319f958060cb0ff3d60fcb3"
def transferComponentSHA256 : String := "d1763f4a75ca47435692ec308e21d4f64f7e0c7b2319f958060cb0ff3d60fcb3"
def powerCertificateSHA256 : String := "643f87306a96de9d9ca6d86769d84143a0584d0ea7986d2a9c061e154e964971"

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
        if left = 3 then row6 0 1 1 3 4 0 right else
          if left = 4 then row6 1 0 0 4 3 1 right else
            row6 0 1 1 3 4 5 right

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
  "b267ebc916cc18af231a311cfac73b7ea59fdb327be2cb7d76bb780276b630a4"

def stateVector (state : Fin 7782)
    (coordinate : Fin 22) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 6)
    (coordinate : Fin 22) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (2 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (0 : Fin 6)
      | _ => (0 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (3 : Fin 6)
      | _ => (0 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (2 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | _ => (3 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (5 : Fin 6)
      | 1 => (5 : Fin 6)
      | 2 => (5 : Fin 6)
      | 3 => (5 : Fin 6)
      | 4 => (5 : Fin 6)
      | 5 => (5 : Fin 6)
      | 6 => (5 : Fin 6)
      | 7 => (5 : Fin 6)
      | 8 => (5 : Fin 6)
      | 9 => (5 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (2 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | _ => (0 : Fin 6)

def transition (state : Fin 7782)
    (generator : Fin 6) : Fin 7782 :=
  Shards.transition state generator

def representativeHead (state : Fin 7782) : Fin 6 :=
  Shards.representativeHead state

def representativeTail (state : Fin 7782) :
    List (Fin 6) :=
  Shards.representativeTail state

def sourceLabel (state : Fin 7782) : Fin 6 :=
  Shards.sourceLabel state

def generatorSourceLabel (generator : Fin 6) : Fin 6 :=
  match generator.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (4 : Fin 6)
  | _ => (5 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 7782 :=
  match value.val with
  | 0 => (0 : Fin 7782)
  | 1 => (1 : Fin 7782)
  | 2 => (2 : Fin 7782)
  | 3 => (3 : Fin 7782)
  | 4 => (4 : Fin 7782)
  | _ => (5 : Fin 7782)

abbrev decodeState :
    (Fin 22 -> Fin 6) -> Fin 7782 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 7782) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 6) :
    Fin 7782 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6979
