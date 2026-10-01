import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.SourceLabel
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.StateVector
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155.Shards.Transition
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155

open SemigroupBasis

def routeManifestRowSHA256 : String := "16c7b13f018325a89fa569ba2bf06272d26ea6d1619bddf7967bdbf645e68cc7"
def witnessRecordSHA256 : String := "483eeb2a48ee83db91674be9c9be7fe11dc6f02785155606bd1e3b83e8a4e5f3"
def transferComponentSHA256 : String := "483eeb2a48ee83db91674be9c9be7fe11dc6f02785155606bd1e3b83e8a4e5f3"
def powerCertificateSHA256 : String := "1ddb5f37d85316161835180bb1e9b4573de8d10f01c7d9c55e830658db53fb62"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 2 0 2 right else
    if left = 1 then row6 0 0 2 2 0 2 right else
      if left = 2 then row6 0 0 2 2 0 2 right else
        if left = 3 then row6 0 1 2 3 4 5 right else
          if left = 4 then row6 4 4 5 5 4 5 right else
            row6 4 4 5 5 4 5 right

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
  "5d64725f8520a77f83bdd789aba8b2c2b017fe851e901f5e636d2fac7266dbe8"

def stateVector (state : Fin 11742)
    (coordinate : Fin 33) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 6)
    (coordinate : Fin 33) : Fin 6 :=
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
      | 10 => (4 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (4 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (4 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (4 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (1 : Fin 6)
      | 23 => (3 : Fin 6)
      | 24 => (3 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (3 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (4 : Fin 6)
      | 30 => (3 : Fin 6)
      | 31 => (3 : Fin 6)
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
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (1 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (4 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (4 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (3 : Fin 6)
      | 24 => (4 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (3 : Fin 6)
      | 27 => (4 : Fin 6)
      | 28 => (4 : Fin 6)
      | 29 => (0 : Fin 6)
      | 30 => (3 : Fin 6)
      | 31 => (3 : Fin 6)
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
      | 9 => (3 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (4 : Fin 6)
      | 15 => (4 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (4 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (3 : Fin 6)
      | 24 => (0 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (1 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (4 : Fin 6)
      | 31 => (3 : Fin 6)
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
      | 8 => (4 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (4 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (1 : Fin 6)
      | 24 => (3 : Fin 6)
      | 25 => (4 : Fin 6)
      | 26 => (3 : Fin 6)
      | 27 => (0 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (0 : Fin 6)
      | 31 => (3 : Fin 6)
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
      | 8 => (3 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (4 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (0 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (0 : Fin 6)
      | 21 => (0 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (3 : Fin 6)
      | 24 => (3 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (3 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (3 : Fin 6)
      | 31 => (1 : Fin 6)
      | _ => (3 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (1 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (0 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (0 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (0 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (3 : Fin 6)
      | 24 => (3 : Fin 6)
      | 25 => (0 : Fin 6)
      | 26 => (3 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (0 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (3 : Fin 6)
      | 31 => (3 : Fin 6)
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
    (Fin 33 -> Fin 6) -> Fin 11742 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 11742) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 6) :
    Fin 11742 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_14155
