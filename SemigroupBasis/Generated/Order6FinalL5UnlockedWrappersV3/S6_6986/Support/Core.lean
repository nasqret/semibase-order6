import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.Shards.SourceLabel
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.Shards.StateVector
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986.Shards.Transition
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986

open SemigroupBasis

def routeManifestRowSHA256 : String := "f9e6ce9935705cb5047b8d75ca1b02ba799a65fd4a8b1a8dd29129da60eeab08"
def witnessRecordSHA256 : String := "4d6354094b671746d3e684123b62620de6802967eea59c58cbcd3c55e5f6434d"
def transferComponentSHA256 : String := "4d6354094b671746d3e684123b62620de6802967eea59c58cbcd3c55e5f6434d"
def powerCertificateSHA256 : String := "bbfc650698c4ebecf85be55824fba03d4981543621e208f8f283620338df4af2"

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
  "2e919653fc91aa8bdd1602cc715ed071f956d9eed0e3a52456a4900b47133319"

def stateVector (state : Fin 18432)
    (coordinate : Fin 28) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 6)
    (coordinate : Fin 28) : Fin 6 :=
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
      | 12 => (0 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (5 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (5 : Fin 6)
      | 21 => (2 : Fin 6)
      | 22 => (5 : Fin 6)
      | 23 => (5 : Fin 6)
      | 24 => (5 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (0 : Fin 6)
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
      | 11 => (5 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (5 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (5 : Fin 6)
      | 21 => (5 : Fin 6)
      | 22 => (5 : Fin 6)
      | 23 => (2 : Fin 6)
      | 24 => (5 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (0 : Fin 6)
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
      | 13 => (5 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (5 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (5 : Fin 6)
      | 21 => (5 : Fin 6)
      | 22 => (5 : Fin 6)
      | 23 => (5 : Fin 6)
      | 24 => (2 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (0 : Fin 6)
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
      | 12 => (5 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (5 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (5 : Fin 6)
      | 21 => (5 : Fin 6)
      | 22 => (2 : Fin 6)
      | 23 => (5 : Fin 6)
      | 24 => (5 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (3 : Fin 6)
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
      | 11 => (5 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (5 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (2 : Fin 6)
      | 21 => (5 : Fin 6)
      | 22 => (5 : Fin 6)
      | 23 => (5 : Fin 6)
      | 24 => (5 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (0 : Fin 6)
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
      | 11 => (5 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (5 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (2 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (5 : Fin 6)
      | 21 => (5 : Fin 6)
      | 22 => (5 : Fin 6)
      | 23 => (5 : Fin 6)
      | 24 => (5 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (0 : Fin 6)
      | _ => (0 : Fin 6)

def transition (state : Fin 18432)
    (generator : Fin 6) : Fin 18432 :=
  Shards.transition state generator

def representativeHead (state : Fin 18432) : Fin 6 :=
  Shards.representativeHead state

def representativeTail (state : Fin 18432) :
    List (Fin 6) :=
  Shards.representativeTail state

def sourceLabel (state : Fin 18432) : Fin 6 :=
  Shards.sourceLabel state

def generatorSourceLabel (generator : Fin 6) : Fin 6 :=
  match generator.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (4 : Fin 6)
  | _ => (5 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 18432 :=
  match value.val with
  | 0 => (0 : Fin 18432)
  | 1 => (1 : Fin 18432)
  | 2 => (2 : Fin 18432)
  | 3 => (3 : Fin 18432)
  | 4 => (4 : Fin 18432)
  | _ => (5 : Fin 18432)

abbrev decodeState :
    (Fin 28 -> Fin 6) -> Fin 18432 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 18432) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 6) :
    Fin 18432 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_6986
