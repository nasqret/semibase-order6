import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_7214Opposite
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.SourceLabel
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.StateVector
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745.Shards.Transition
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745

open SemigroupBasis

def routeManifestRowSHA256 : String := "ae1ae58d2021fa7292a655aa99c075e0bd5aec4277fd4ecde0cdd284407e82c0"
def witnessRecordSHA256 : String := "303b9e85096ca32f56e62115ce74fd02fe3a60f3ee4d28ee643b95795fbca528"
def transferComponentSHA256 : String := "303b9e85096ca32f56e62115ce74fd02fe3a60f3ee4d28ee643b95795fbca528"
def powerCertificateSHA256 : String := "31e8fc466198b5b61f076fb8fe7362fb0dcfe0da8d7770865adaaa4bfd7dd786"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 0 2 2 2 2 right else
    if left = 1 then row6 0 0 2 2 2 2 right else
      if left = 2 then row6 0 0 2 2 2 2 right else
        if left = 3 then row6 0 1 2 3 3 3 right else
          if left = 4 then row6 0 1 2 3 4 5 right else
            row6 0 1 2 5 5 5 right

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
  "0ff0084e7dc422bf1d487140af6a03c98e7834a3542c8939ad28e6771c3cf264"

def stateVector (state : Fin 11742)
    (coordinate : Fin 36) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 6)
    (coordinate : Fin 36) : Fin 6 :=
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
      | 9 => (4 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (4 : Fin 6)
      | 12 => (4 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (1 : Fin 6)
      | 15 => (4 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (4 : Fin 6)
      | 18 => (4 : Fin 6)
      | 19 => (5 : Fin 6)
      | 20 => (4 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (3 : Fin 6)
      | 24 => (3 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (5 : Fin 6)
      | 27 => (5 : Fin 6)
      | 28 => (5 : Fin 6)
      | 29 => (4 : Fin 6)
      | 30 => (4 : Fin 6)
      | 31 => (4 : Fin 6)
      | 32 => (5 : Fin 6)
      | 33 => (5 : Fin 6)
      | 34 => (5 : Fin 6)
      | _ => (5 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (1 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (1 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (4 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (4 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (4 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (4 : Fin 6)
      | 18 => (5 : Fin 6)
      | 19 => (4 : Fin 6)
      | 20 => (4 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (1 : Fin 6)
      | 24 => (3 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (4 : Fin 6)
      | 27 => (4 : Fin 6)
      | 28 => (3 : Fin 6)
      | 29 => (5 : Fin 6)
      | 30 => (4 : Fin 6)
      | 31 => (5 : Fin 6)
      | 32 => (4 : Fin 6)
      | 33 => (4 : Fin 6)
      | 34 => (4 : Fin 6)
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
      | 8 => (3 : Fin 6)
      | 9 => (4 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (4 : Fin 6)
      | 12 => (5 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (3 : Fin 6)
      | 17 => (4 : Fin 6)
      | 18 => (4 : Fin 6)
      | 19 => (4 : Fin 6)
      | 20 => (5 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (3 : Fin 6)
      | 24 => (3 : Fin 6)
      | 25 => (1 : Fin 6)
      | 26 => (4 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (4 : Fin 6)
      | 29 => (4 : Fin 6)
      | 30 => (4 : Fin 6)
      | 31 => (3 : Fin 6)
      | 32 => (3 : Fin 6)
      | 33 => (4 : Fin 6)
      | 34 => (4 : Fin 6)
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
      | 9 => (4 : Fin 6)
      | 10 => (4 : Fin 6)
      | 11 => (3 : Fin 6)
      | 12 => (4 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (3 : Fin 6)
      | 16 => (4 : Fin 6)
      | 17 => (5 : Fin 6)
      | 18 => (4 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (4 : Fin 6)
      | 21 => (1 : Fin 6)
      | 22 => (5 : Fin 6)
      | 23 => (3 : Fin 6)
      | 24 => (3 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (4 : Fin 6)
      | 27 => (3 : Fin 6)
      | 28 => (4 : Fin 6)
      | 29 => (4 : Fin 6)
      | 30 => (4 : Fin 6)
      | 31 => (4 : Fin 6)
      | 32 => (4 : Fin 6)
      | 33 => (3 : Fin 6)
      | 34 => (4 : Fin 6)
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
      | 9 => (5 : Fin 6)
      | 10 => (4 : Fin 6)
      | 11 => (4 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (3 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (4 : Fin 6)
      | 16 => (4 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (4 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (4 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (4 : Fin 6)
      | 23 => (3 : Fin 6)
      | 24 => (1 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (3 : Fin 6)
      | 27 => (4 : Fin 6)
      | 28 => (4 : Fin 6)
      | 29 => (3 : Fin 6)
      | 30 => (5 : Fin 6)
      | 31 => (4 : Fin 6)
      | 32 => (4 : Fin 6)
      | 33 => (4 : Fin 6)
      | 34 => (3 : Fin 6)
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
      | 7 => (1 : Fin 6)
      | 8 => (1 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (3 : Fin 6)
      | 11 => (4 : Fin 6)
      | 12 => (4 : Fin 6)
      | 13 => (1 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (4 : Fin 6)
      | 16 => (4 : Fin 6)
      | 17 => (4 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (4 : Fin 6)
      | 20 => (3 : Fin 6)
      | 21 => (3 : Fin 6)
      | 22 => (3 : Fin 6)
      | 23 => (3 : Fin 6)
      | 24 => (3 : Fin 6)
      | 25 => (3 : Fin 6)
      | 26 => (3 : Fin 6)
      | 27 => (4 : Fin 6)
      | 28 => (4 : Fin 6)
      | 29 => (4 : Fin 6)
      | 30 => (3 : Fin 6)
      | 31 => (4 : Fin 6)
      | 32 => (4 : Fin 6)
      | 33 => (4 : Fin 6)
      | 34 => (4 : Fin 6)
      | _ => (3 : Fin 6)

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
    (Fin 36 -> Fin 6) -> Fin 11742 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 11742) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 6) :
    Fin 11742 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_13745
