import SemigroupBasis.FiniteNilpotentCounterexample
import SemigroupBasis.Generated.Order6FinalL5UnlockedSourceAdapters.S6_4055Representative
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.DecodeState
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.DecodeStateProof
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.RepresentativeHead
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.RepresentativeTail
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.SourceLabel
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.StateVector
import SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052.Shards.Transition
import SemigroupBasis.Nonfinite
import SemigroupBasis.Opposite
import SemigroupBasis.RightGeneratedPowerCertificate
import Std.Tactic

set_option maxRecDepth 8192

namespace SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052

open SemigroupBasis

def routeManifestRowSHA256 : String := "793e028703be320f8569476f134b91ba1f02c92915bd30c9aa3e8371da8fb835"
def witnessRecordSHA256 : String := "f50270129deb47e2fd86a1795985af53d5dc4c4b205701ba1ffe23102c45a094"
def transferComponentSHA256 : String := "f50270129deb47e2fd86a1795985af53d5dc4c4b205701ba1ffe23102c45a094"
def powerCertificateSHA256 : String := "803e3cdaf1ebef7593b3492b93ac929dac5c225937523dcd15719bd39fbd4d79"

private def row6
    (c0 c1 c2 c3 c4 c5 : Fin 6) (column : Fin 6) : Fin 6 :=
  if column = 0 then c0 else
    if column = 1 then c1 else
      if column = 2 then c2 else
        if column = 3 then c3 else
          if column = 4 then c4 else c5

/-- Exact one-based catalogue table committed by the portable witness. -/
def mul (left right : Fin 6) : Fin 6 :=
  if left = 0 then row6 0 1 1 0 4 5 right else
    if left = 1 then row6 1 0 0 1 4 5 right else
      if left = 2 then row6 1 0 0 2 4 5 right else
        if left = 3 then row6 0 1 2 3 4 5 right else
          if left = 4 then row6 4 4 4 4 4 5 right else
            row6 4 4 4 4 4 5 right

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
  "c81977f5b0c62ddb99eb104e8dae4d9c8269d0c4b2091fb0e45e348e7c077ccc"

def stateVector (state : Fin 18432)
    (coordinate : Fin 22) : Fin 6 :=
  Shards.stateVector state coordinate

def generatorVector (generator : Fin 6)
    (coordinate : Fin 22) : Fin 6 :=
  match generator.val with
  | 0 =>
      match coordinate.val with
      | 0 => (3 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (2 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (5 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (2 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 1 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (3 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (2 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (0 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (5 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (2 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 2 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (3 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (2 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (0 : Fin 6)
      | 13 => (5 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (2 : Fin 6)
      | _ => (3 : Fin 6)
  | 3 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (3 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (2 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (5 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (2 : Fin 6)
      | 20 => (3 : Fin 6)
      | _ => (3 : Fin 6)
  | 4 =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (3 : Fin 6)
      | 5 => (0 : Fin 6)
      | 6 => (0 : Fin 6)
      | 7 => (0 : Fin 6)
      | 8 => (0 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (2 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (3 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (5 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (3 : Fin 6)
      | _ => (2 : Fin 6)
  | _ =>
      match coordinate.val with
      | 0 => (0 : Fin 6)
      | 1 => (0 : Fin 6)
      | 2 => (0 : Fin 6)
      | 3 => (0 : Fin 6)
      | 4 => (0 : Fin 6)
      | 5 => (2 : Fin 6)
      | 6 => (3 : Fin 6)
      | 7 => (3 : Fin 6)
      | 8 => (3 : Fin 6)
      | 9 => (3 : Fin 6)
      | 10 => (0 : Fin 6)
      | 11 => (0 : Fin 6)
      | 12 => (3 : Fin 6)
      | 13 => (0 : Fin 6)
      | 14 => (2 : Fin 6)
      | 15 => (0 : Fin 6)
      | 16 => (0 : Fin 6)
      | 17 => (3 : Fin 6)
      | 18 => (3 : Fin 6)
      | 19 => (3 : Fin 6)
      | 20 => (3 : Fin 6)
      | _ => (3 : Fin 6)

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
    (Fin 22 -> Fin 6) -> Fin 18432 :=
  Shards.decodeState

theorem decodeState_stateVector (state : Fin 18432) :
    decodeState (stateVector state) = state :=
  Shards.decodeState_stateVector state

def generatorState
    (generator : Fin 6) :
    Fin 18432 :=
  ⟨generator.val, by omega⟩

end SemigroupBasis.Generated.Order6FinalL5UnlockedWrappersV3.S6_9052
