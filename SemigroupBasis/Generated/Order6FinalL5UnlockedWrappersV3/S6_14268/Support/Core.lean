import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.SourceLabel
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.StateVector
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268.Shards.Transition
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268

open SemigroupBasis

def routeManifestRowSHA256 : String := "015ac0ab3a871856b597a11f92b6682a488ba4bb12403961493f7a2ec43adde0"
def witnessRecordSHA256 : String := "b14915dd5d0afe5d292ee5a0a33e3db491711b1178c52e155e94fc572ee99b13"
def transferComponentSHA256 : String := "b14915dd5d0afe5d292ee5a0a33e3db491711b1178c52e155e94fc572ee99b13"
def powerCertificateSHA256 : String := "064fb0d45c446ac4e1e3b0086a99b83bb3192f6982fa493b9a34e83017ee0e7e"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 2 4 5 right else
    if left = 1 then row6 0 0 2 2 4 5 right else
      if left = 2 then row6 0 0 2 2 4 5 right else
        if left = 3 then row6 0 1 2 3 4 5 right else
          if left = 4 then row6 4 4 4 4 4 4 right else
            row6 5 5 5 5 5 5 right

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
  "78495b495b1e6ef244e99d04ca16fcfccf068ba31896e54634152ffc9f136d63"

def stateVector (state : Fin 11742)
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
      | 6 => (3 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (1 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (1 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (5 : Fin 6)
      | 20 => (5 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (5 : Fin 6)
      | 25 => (5 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (1 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (5 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (4 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (1 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (3 : Fin 6)
      | _ => (3 : Fin 6)
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
      | 8 => (3 : Fin 6)
      | 9 => (1 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (4 : Fin 6)
      | 17 => (4 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (5 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (5 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (1 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (3 : Fin 6)
      | _ => (3 : Fin 6)
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
      | 9 => (3 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (4 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (5 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (0 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (4 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (1 : Fin 6)
      | 30 => (3 : Fin 6)
      | _ => (3 : Fin 6)
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
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (4 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (4 : Fin 6)
      | 19 => (4 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (4 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (5 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (0 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (1 : Fin 6)
      | _ => (3 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (1 : Fin 6)
      | 6 => (1 : Fin 6)
      | 7 => (1 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (4 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (4 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (4 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (0 : Fin 6)
      | 23 => (4 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (4 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (3 : Fin 6)
      | _ => (1 : Fin 6)

def transition (state : Fin 11742)
    (generator : Fin 6) : Fin 11742 :=
  Shards.transition state generator

def representativeHead (state : Fin 11742) : Fin 6 :=
  Shards.representativeHead state

def representativeTail (state : Fin 11742) :
    List (Fin 6) :=
  Shards.representativeTail state

def sourceLabel (state : Fin 11742) : Fin 6 :=
  Shards.sourceLabel state

def generatorSourceLabel (generator : Fin 6) : Fin 6 :=
  match generator.val with
  | 0 => (0 : Fin 6)
  | 1 => (1 : Fin 6)
  | 2 => (2 : Fin 6)
  | 3 => (3 : Fin 6)
  | 4 => (4 : Fin 6)
  | _ => (5 : Fin 6)

def sourcePreimage (value : Fin 6) : Fin 11742 :=
  match value.val with
  | 0 => (0 : Fin 11742)
  | 1 => (1 : Fin 11742)
  | 2 => (2 : Fin 11742)
  | 3 => (3 : Fin 11742)
  | 4 => (4 : Fin 11742)
  | _ => (5 : Fin 11742)

abbrev decodeState :
    (Fin 32 -> Fin 6) -> Fin 11742 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 11742) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 6) :
    Fin 11742 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14268
